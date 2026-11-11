-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Deployed,DeployedWired,WiringSetup}.lean` of this repository (the setup
-- computing the circuit's commitment with the oracle, the deployed run with each opening's stage logged, each
-- opening's doom bounded by F2's soundness on the composed run viewed as its adversary) to the EIP's PCS claims of
-- the deployed protocol: two commitments with out-of-domain answers (`formal/ComposePcs/ComposePcs/Chain2.lean`),
-- the claims of `reduceWith` (`formal/Statement/PcsQuotient/Reduction.lean`'s `claimsAt`), three one-point
-- openings.
import SoundPcs.Tables

/-!
# The deployed verifier of the EIP's PCS claims, and its doomed openings

**The openings** are abstract here (`OpenSpec`): a verifier `V n` of a version-1 PCS claim on `n` variables
(`WhirBridge.Pcs.Claim1 n`) and its proof, the out-of-domain point read off Keccak-256 by the verifier, with
its doom event `Doom n` (every candidate of the word extracted for the claim's root violates `f(z) = ood` or
`f(point) = value`), what F2 proves of it (`sound`: `openingBound` of the adversary's queries), and three facts
the composition reads: the event reads Keccak-256's answers only, an undoomed opening whose out-of-domain inputs
were asked has a candidate satisfying both claims, and an accepting run asks the out-of-domain inputs.
`Opening.lean` instantiates it with the deployed opening.

**The setup** (`setupPcs q₀`) computes the circuit's commitment with the oracle: the Merkle tree of the wiring
table's word (`Compose.wiringSetup` of `stackWord`: version 1 commits the table of `24` variables as itself), then
its out-of-domain point, coordinate `j` read off Keccak-256 at `oodInput 24 root j` (`oodPointO`), and the table's
polynomial there.

**The deployed run** (`dExp`), each stage logged from the start (`Stages.lean`):

1. the setup, then the adversary, given the circuit's commitment (`withSetup2`), outputs the reduction's proof
   (statement, two commitments, four values; `ComposePcs.RootProof2`, its circuit commitment overwritten by the
   setup's) and the three openings' proofs (`Rest`); its Keccak-256 queries are logged (the extractor reads them);
2. the chain over Keccak-256 (`ComposePcs.chainWith2`) gives the challenges (`DA2`);
3. the claims: `PcsQuotient.claimsAt` at `2^22` rows (`claimsD`), the Statement's `reduceWith` after its
   transcript;
4. the three openings, in the Rust's order (`Claims::on`): the witness claim on `W` (`24` variables), the wiring
   claim on the circuit's commitment (`24`), the copy claim on `T` (`28`); each run only if the claims exist, its
   point has the commitment's number of variables and every earlier opening accepted (`checkAllWith` stops at the
   first failure).

**The verifier accepts** (`AccD`) when the three openings accept. **Each opening's doom** at its end (`EW`, `Eσ`,
`ET`) is bounded by `OpenSpec.sound` for the run up to it as its adversary (`prEvent_EW_le`, …); **the binding
events** (`EBn n`: some root's list on `n` variables not separated at its out-of-domain point at the end; `n = 24`
for `W`, `28` for `T`) by `WhirBridge.Pcs.ood_binding_coords` on the whole run (`prEvent_EBn_le`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs
open LeanVM.Protocol.Rom (romExperiment romExperiment_map)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The openings -/

/-- **An opening of version-1 PCS claims, and what F2 proves of it.** -/
structure OpenSpec where
  /-- The verifier of a claim on `n` variables and its proof. -/
  V : (n : ℕ) → Claim1 n × Proof → OracleComp KeccakCalls Bool
  /-- The doom: every candidate of the word extracted for the claim's root violates one of its claims. -/
  Doom : (n : ℕ) → Claim1 n × Proof → KeccakCalls.QueryCache → Prop
  /-- The queries of one opening. -/
  QO : ℕ
  queryBound : ∀ n w, IsTotalQueryBound (V n w) QO
  /-- **F2's soundness**: an adversary of at most `QA` queries makes the opening accept while doomed with
  probability at most `openingBound QA`. -/
  sound : ∀ n, minVars ≤ n → n ≤ maxVars → ∀ (A : OracleComp KeccakCalls (Claim1 n × Proof)) (QA : ℕ),
    IsTotalQueryBound A QA → Pr{let z ← romExperiment A (V n)}[z.1.2 = true ∧ Doom n z.1.1 z.2] ≤
      openingBound QA
  /-- The doom reads Keccak-256's answers only. -/
  readsInl : ∀ n w (c c' : KeccakCalls.QueryCache), (∀ x, c (.inl x) = c' (.inl x)) →
    (Doom n w c ↔ Doom n w c')
  /-- An undoomed opening whose out-of-domain inputs are answered has a candidate satisfying both claims, the
  point read off the answers. -/
  undoomed : ∀ n w (c : KeccakCalls.QueryCache), ¬ Doom n w c →
    (∀ j : Fin n, (c (.inl (oodInput n w.1.root j))).isSome) →
    ∃ q ∈ rootList (n := n) (fun x => c (.inl x)) w.1.root, colEval q w.1.point = w.1.value ∧
      colEval q (oodPointWith (fun x => (c (.inl x)).getD default) n w.1.root).toList = w.1.ood
  /-- An accepting run asks the out-of-domain inputs. -/
  asks : ∀ n w (T : KTable), evalWithAnswerFn (QueryImpl.ofFn T) (V n w) = true →
    ∀ j : Fin n, (Sum.inl (oodInput n w.1.root j) : List UInt8 ⊕ KeccakState) ∈
      (tableQueryLog (V n w) T).map Sigma.fst

/-! ## The out-of-domain point, asked -/

/-- One coordinate, asked: the element the low `24` bytes of the answer at `oodInput n r j` encode. -/
def coordQ (n : ℕ) (r : Digest) (j : ℕ) : OracleComp KeccakCalls E :=
  coordOf <$> callKeccak256 (oodInput n r j)

/-- **The out-of-domain point of a root on `n` variables, asked of Keccak-256** (`ood_point`; the Statement's
`oodPointWith` over a hash): coordinate `j` the element the low `24` bytes of the answer at `oodInput n root j`
encode, `j = 0, …, n − 1`. -/
def oodPointO (n : ℕ) (r : Digest) : OracleComp KeccakCalls (List E) :=
  (List.range n).mapM (coordQ n r)

theorem coordQ_queryBound (n : ℕ) (r : Digest) (j : ℕ) : IsTotalQueryBound (coordQ n r j) 1 := by
  rw [coordQ]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩)

theorem mapM_queryBound (n : ℕ) (r : Digest) :
    ∀ l : List ℕ, IsTotalQueryBound (l.mapM (coordQ n r)) l.length
  | [] => trivial
  | j :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.add_comm]
    exact isTotalQueryBound_bind (coordQ_queryBound n r j) fun a =>
      (isTotalQueryBound_bind (n₂ := 0) (mapM_queryBound n r l) fun as => trivial)

theorem oodPointO_queryBound (n : ℕ) (r : Digest) : IsTotalQueryBound (oodPointO n r) n := by
  have := mapM_queryBound n r (List.range n)
  rwa [List.length_range] at this

/-- Against a table: the queries are the out-of-domain inputs, the result their coordinates. -/
theorem mapM_run (T : KTable) (n : ℕ) (r : Digest) :
    ∀ l : List ℕ,
      (tableQueryLog (l.mapM (coordQ n r)) T).map Sigma.fst = l.map (fun j => Sum.inl (oodInput n r j)) ∧
        evalWithAnswerFn (QueryImpl.ofFn T) (l.mapM (coordQ n r)) =
          l.map fun j => coordOf (T (.inl (oodInput n r j)))
  | [] => by simp
  | j :: l => by
    obtain ⟨h1, h2⟩ := mapM_run T n r l
    rw [List.mapM_cons]
    constructor
    · rw [tableQueryLog_bind, tableQueryLog_bind]
      simp only [coordQ, callKeccak256, tableQueryLog_map, tableQueryLog_query, tableQueryLog_pure,
        List.append_nil, List.map_append, List.map_cons, List.map_nil, h1, List.singleton_append]
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, h2, List.map_cons, coordQ,
        evalWithAnswerFn_map, callKeccak256, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]

theorem oodPointO_run (T : KTable) (n : ℕ) (r : Digest) :
    (tableQueryLog (oodPointO n r) T).map Sigma.fst =
        (List.range n).map (fun j => Sum.inl (oodInput n r j)) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (oodPointO n r) =
        (oodPointWith (fun x => T (.inl x)) n r).toList := by
  obtain ⟨h1, h2⟩ := mapM_run T n r (List.range n)
  refine ⟨h1, ?_⟩
  rw [oodPointO, h2]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range]
  simp [oodPointWith, coordOf]

/-! ## The setup -/

/-- **The setup**: the circuit's commitment computed with the oracle, the Merkle tree of the wiring table's word
(its root as 32 bytes), its out-of-domain point asked of Keccak-256, and the table's polynomial there. -/
noncomputable def setupPcs (q₀ : Column 24) : OracleComp KeccakCalls (Bytes32 × E) :=
  wiringSetup (rootHeight 24 logInvRate) (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀) >>= fun ir =>
    oodPointO 24 (ofB ir) >>= fun z => pure (ir, colEval q₀ z)

/-- The setup's queries: the tree's `2^20`, then the `24` coordinates. -/
theorem setupPcs_queryBound (q₀ : Column 24) : IsTotalQueryBound (setupPcs q₀) (2 ^ 20 + 24) := by
  have ht : IsTotalQueryBound (wiringSetup (rootHeight 24 logInvRate)
      (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀)) (2 ^ 20) :=
    (isQueryBound_map_iff _ (fun t : LeanVM.Prover.Tree => toB t.root) _ _ _).mpr
      (isTotalQueryBound_buildTreeM _ _)
  have := isTotalQueryBound_bind (ob := fun ir => oodPointO 24 (ofB ir) >>= fun z =>
      (pure (ir, colEval q₀ z) : OracleComp KeccakCalls (Bytes32 × E))) ht fun ir =>
    isTotalQueryBound_bind (ob := fun z => (pure (ir, colEval q₀ z) : OracleComp KeccakCalls (Bytes32 × E)))
      (n₂ := 0) (oodPointO_queryBound 24 (ofB ir)) fun z => trivial
  exact this

/-! ## The adversary, the chain -/

/-- What the adversary outputs besides the reduction's proof: the three openings' proofs, in the order of
`Claims::on`. -/
structure Rest where
  oW : Proof
  oσ : Proof
  oT : Proof

/-- **The setup, then the adversary**: the adversary is given the circuit's commitment (root and out-of-domain
answer), and the proof the verifier reads carries it, whatever the adversary put there. -/
def withSetup2 (setup : OracleComp KeccakCalls (Bytes32 × E))
    (A : Bytes32 × E → OracleComp KeccakCalls (RootProof2 E × Rest)) :
    OracleComp KeccakCalls (RootProof2 E × Rest) :=
  setup >>= fun c => (fun po => ({ po.1 with ir := c.1, io := c.2 }, po.2)) <$> A c

theorem isTotalQueryBound_withSetup2 (setup : OracleComp KeccakCalls (Bytes32 × E))
    (A : Bytes32 × E → OracleComp KeccakCalls (RootProof2 E × Rest)) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hA : ∀ c, IsTotalQueryBound (A c) Q) :
    IsTotalQueryBound (withSetup2 setup A) (QS + Q) :=
  isTotalQueryBound_bind hS fun c => (isQueryBound_map_iff _ _ _ _ _).mpr (hA c)

/-- The protocol up to the openings: the proof, the rest, the adversary's Keccak-256 transcript, the
challenges. -/
structure S0 where
  π : RootProof2 E
  rest : Rest
  tA : Transcript
  ch : Chals E

variable {P : Kc3.Params E} (W : Wire2 P)

/-- **The adversary, its log, and the chain.** -/
def DA2 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) : OracleComp KeccakCalls S0 :=
  loggedKC A >>= fun pt => chainWith2 W hash256 pt.1.1 >>= fun ch => pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩

theorem isTotalQueryBound_DA2 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) : IsTotalQueryBound (DA2 W A) (Q + 6) := by
  have h : ∀ pt : (RootProof2 E × Rest) × Transcript, IsTotalQueryBound
      (chainWith2 W hash256 pt.1.1 >>= fun ch =>
        (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ : OracleComp KeccakCalls S0)) (6 + 0) :=
    fun pt => isTotalQueryBound_bind (chain2_queryBound_kc W pt.1.1) fun ch =>
      (trivial : IsTotalQueryBound (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ : OracleComp KeccakCalls S0) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero] at this

/-! ## The claims -/

/-- The statement's 64 bytes as the Statement's `y` and `root`. -/
def stmtOf (sb : Vector UInt8 64) : PcsQuotient.Statement :=
  ⟨Vector.ofFn fun i : Fin 32 => sb.get ⟨i, by omega⟩, Vector.ofFn fun i : Fin 32 => sb.get ⟨32 + i, by omega⟩⟩

/-- **The claims** (`reduce` after its transcript, `PcsQuotient.claimsAt` at `2^22` rows) at the chain's
challenges and the proof's values; `none` when a denominator vanishes. -/
def claimsD (a : S0) : Option PcsQuotient.Claims :=
  PcsQuotient.claimsAt 22 (stmtOf a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.ch.ρ (Vector.ofFn a.π.v.1) a.π.v.2

-- The claims are field arithmetic: kept folded, so that no unification evaluates them.
attribute [irreducible] claimsD

/-- A claim on `n` variables against a commitment, and its proof; `none` if the point has another number of
coordinates. -/
def mkIn (n : ℕ) (root : Bytes32) (ood : E) (c : PcsQuotient.Claim) (pf : Proof) :
    Option (Claim1 n × Proof) :=
  if h : c.point.length = n then some (⟨ofB root, ood, c.point, c.value, h⟩, pf) else none

/-- The witness opening's input: `W`'s commitment, the witness claim (`24` variables). -/
def inW (a : S0) : Option (Claim1 24 × Proof) :=
  (claimsD a).bind fun cl => mkIn 24 a.π.rW a.π.oW cl.witness a.rest.oW

/-- The wiring opening's input: the circuit's commitment (the setup's), the wiring claim (`24` variables). -/
def inσ (a : S0) : Option (Claim1 24 × Proof) :=
  (claimsD a).bind fun cl => mkIn 24 a.π.ir a.π.io cl.wiring a.rest.oσ

/-- `T`'s opening, the copy claim (`28` variables). -/
def inT (a : S0) : Option (Claim1 28 × Proof) :=
  (claimsD a).bind fun cl => mkIn 28 a.π.rT a.π.oT cl.copy a.rest.oT

/-! ## The stages -/

/-- The run through the witness opening. -/
abbrev X1 : Type := (S0 × Bool) × Transcript
/-- Through the wiring opening. -/
abbrev X2 : Type := (X1 × Bool) × Transcript
/-- Through `T`'s: the whole run. -/
abbrev X3 : Type := (X2 × Bool) × Transcript

/-- The protocol up to the openings, in each stage. -/
def X1.s (x : X1) : S0 := x.1.1
def X2.s (x : X2) : S0 := X1.s x.1.1
def X3.s (x : X3) : S0 := X2.s x.1.1

/-- Every opening so far accepted. -/
def X1.ok (x : X1) : Bool := x.1.2
def X2.ok (x : X2) : Bool := X1.ok x.1.1 && x.1.2
def X3.ok (x : X3) : Bool := X2.ok x.1.1 && x.1.2

variable (O : OpenSpec)

/-- An opening's input once every earlier opening accepted. -/
def gate {β : Type} (ok : Bool) (o : Option β) : Option β := if ok then o else none

/-- The run through the witness opening. -/
def e1 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) : OracleComp KeccakCalls X1 :=
  stage (DA2 W A) fun a => optV (O.V 24) (inW a)

/-- Through the wiring opening. -/
def e2 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) : OracleComp KeccakCalls X2 :=
  stage (e1 W O A) fun x => optV (O.V 24) (gate x.ok (inσ x.s))

/-- **The deployed run**: the setup and the adversary, the chain, the claims, the three openings, each stage
logged from the start. -/
def dExp (A : OracleComp KeccakCalls (RootProof2 E × Rest)) : OracleComp KeccakCalls X3 :=
  stage (e2 W O A) fun x => optV (O.V 28) (gate x.ok (inT x.s))

/-! ## Query bounds -/

theorem isTotalQueryBound_stage_optV {α β : Type} (pre : OracleComp KeccakCalls α) (f : α → Option β)
    (V : β → OracleComp KeccakCalls Bool) (Qp QV : ℕ) (hp : IsTotalQueryBound pre Qp)
    (hV : ∀ w, IsTotalQueryBound (V w) QV) :
    IsTotalQueryBound (stage pre fun a => optV V (f a)) (Qp + QV) :=
  isTotalQueryBound_stage pre _ Qp QV hp fun a => isTotalQueryBound_optV V QV hV (f a)

theorem qb_e1 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e1 W O A) (Q + 6 + O.QO) := by
  unfold e1
  exact isTotalQueryBound_stage_optV (DA2 W A) inW (O.V 24) (Q + 6) O.QO (isTotalQueryBound_DA2 W A Q hQ)
    (O.queryBound 24)

theorem qb_e2 (A : OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e2 W O A) (Q + 6 + O.QO + O.QO) := by
  unfold e2
  exact isTotalQueryBound_stage (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) (Q + 6 + O.QO) O.QO
    (qb_e1 W O A Q hQ) fun x => isTotalQueryBound_optV (O.V 24) O.QO (O.queryBound 24) (gate x.ok (inσ x.s))

theorem qb_dExp (A : OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (dExp W O A) (Q + 6 + O.QO + O.QO + O.QO) := by
  unfold dExp
  exact isTotalQueryBound_stage (e2 W O A) (fun x => optV (O.V 28) (gate x.ok (inT x.s)))
    (Q + 6 + O.QO + O.QO) O.QO (qb_e2 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 28) O.QO (O.queryBound 28) (gate x.ok (inT x.s))

/-! ## The events -/

/-- An opening accepts while doomed at its end (its stage's verdict, input and cache). -/
def StageDoom {α : Type} (n : ℕ) (inp : α → Option (Claim1 n × Proof)) (x : (α × Bool) × Transcript) : Prop :=
  x.1.2 = true ∧ OptDoom (O.Doom n) (inp x.1.1) (cacheOfTr x.2)

/-- The witness opening accepts while doomed. -/
def EW (z : X3) : Prop := StageDoom O 24 inW z.1.1.1.1
/-- The wiring opening. -/
def Eσ (z : X3) : Prop := StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) z.1.1
/-- `T`'s opening. -/
def ET (z : X3) : Prop := StageDoom O 28 (fun x : X2 => gate x.ok (inT x.s)) z

/-- **The binding event at `n` variables**: at the end of the run, some root on `n` variables whose out-of-domain
inputs were all asked has a list not separated at its point. -/
def EBn (n : ℕ) (z : X3) : Prop := BindBadC n (cacheOfTr z.2)

/-- **The deployed verifier accepts**: all three openings accept. -/
def AccD (z : X3) : Prop := z.ok = true

/-! ## Each opening's term is F2's -/

theorem readsInl_stageDoom {α : Type} (n : ℕ) (inp : α → Option (Claim1 n × Proof)) :
    ReadsInl fun (a : α) (b : Bool) (c : KeccakCalls.QueryCache) => b = true ∧ OptDoom (O.Doom n) (inp a) c :=
  readsInl_optDoom inp (O.Doom n) (O.readsInl n)

/-- **One stage's term**: the stage's doom has probability at most `openingBound` of the queries before it. -/
theorem prEvent_stageDoom_le {α : Type} (pre : OracleComp KeccakCalls α) (Qp : ℕ)
    (hp : IsTotalQueryBound pre Qp) (n : ℕ) (h1 : minVars ≤ n) (h2 : n ≤ maxVars)
    (inp : α → Option (Claim1 n × Proof)) :
    Pr{let z ← (simulateQ randomOracle (stage pre fun a => optV (O.V n) (inp a))).run' ∅}[
      StageDoom O n inp z] ≤ openingBound Qp := by
  have hne : Inhabited (Claim1 n × Proof) := ⟨(dummy n, ⟨[], []⟩)⟩
  calc Pr{let z ← (simulateQ randomOracle (stage pre fun a => optV (O.V n) (inp a))).run' ∅}[
        StageDoom O n inp z]
      = Pr{let z ← (simulateQ randomOracle (stage pre fun a => optV (O.V n) (inp a))).run' ∅}[
          (fun (a : α) (b : Bool) (c : KeccakCalls.QueryCache) =>
            b = true ∧ OptDoom (O.Doom n) (inp a) c) z.1.1 z.1.2 (cacheOfTr z.2)] := rfl
    _ = Pr{let z ← romExperiment pre fun a => optV (O.V n) (inp a)}[
          z.1.2 = true ∧ OptDoom (O.Doom n) (inp z.1.1) z.2] :=
        prEvent_stage_now pre _ _ (readsInl_stageDoom O n inp)
    _ ≤ _ := prEvent_optV_le pre inp (O.V n) (O.Doom n)
    _ ≤ openingBound Qp := O.sound n h1 h2 _ Qp ((isQueryBound_map_iff _ _ _ _ _).mpr hp)

/-- A later stage keeps the bound of an earlier event. -/
theorem keep_le {α : Type} (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool)
    (E : α → Prop) {ε : ℝ≥0∞} (h : Pr{let z ← (simulateQ randomOracle pre).run' ∅}[E z] ≤ ε) :
    Pr{let z ← (simulateQ randomOracle (stage pre V)).run' ∅}[E z.1.1] ≤ ε :=
  (prEvent_stage_keep pre V E).trans_le h

variable (A : OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q)
include hQ

theorem prEvent_EW_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EW O z] ≤ openingBound (Q + 6) := by
  unfold EW dExp
  refine keep_le (e2 W O A) (fun x => optV (O.V 28) (gate x.ok (inT x.s)))
    (fun w : X2 => StageDoom O 24 inW w.1.1) ?_
  unfold e2
  refine keep_le (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) (fun w : X1 => StageDoom O 24 inW w) ?_
  exact prEvent_stageDoom_le O _ _ (isTotalQueryBound_DA2 W A Q hQ) 24 (by decide) (by decide) inW

theorem prEvent_Eσ_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[Eσ O z] ≤ openingBound (Q + 6 + O.QO) := by
  unfold Eσ dExp
  refine keep_le (e2 W O A) (fun x => optV (O.V 28) (gate x.ok (inT x.s)))
    (fun w : X2 => StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) w) ?_
  exact prEvent_stageDoom_le O _ _ (qb_e1 W O A Q hQ) 24 (by decide) (by decide)
    (fun x : X1 => gate x.ok (inσ x.s))

theorem prEvent_ET_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[ET O z] ≤
      openingBound (Q + 6 + O.QO + O.QO) := by
  unfold ET dExp
  exact prEvent_stageDoom_le O _ _ (qb_e2 W O A Q hQ) 28 (by decide) (by decide)
    (fun x : X2 => gate x.ok (inT x.s))

/-- **The binding term at `n` variables**: `ood_binding_coords` on the whole run. -/
theorem prEvent_EBn_le (n : ℕ) (hw : Whir.Admissible n logInvRate) :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EBn n z] ≤
      ((Q + 6 + O.QO + O.QO + O.QO : ℕ) : ℝ≥0∞) * δc n +
        (((Q + 6 + O.QO + O.QO + O.QO) * (Q + 6 + O.QO + O.QO + O.QO + 1) : ℕ) : ℝ≥0∞) /
          (2 : ℝ≥0∞) ^ 256 := by
  set v := e2 W O A >>= fun x => (x, ·) <$> optV (O.V 28) (gate x.ok (inT x.s)) with hvdef
  have hV : ∀ x : X2, IsTotalQueryBound ((x, ·) <$> optV (O.V 28) (gate x.ok (inT x.s))) O.QO :=
    fun x => by
      generalize gate x.ok (inT x.s) = o
      exact (isQueryBound_map_iff _ (fun b => (x, b)) _ _ _).mpr
        (isTotalQueryBound_optV (O.V 28) O.QO (O.queryBound 28) o)
  have hv : IsTotalQueryBound v (Q + 6 + O.QO + O.QO + O.QO) :=
    isTotalQueryBound_bind (qb_e2 W O A Q hQ) hV
  have hE : ∀ c c' : KeccakCalls.QueryCache, (∀ x, c (.inl x) = c' (.inl x)) →
      (BindBadC n c ↔ BindBadC n c') := fun c c' h => by
    unfold BindBadC
    have hc : (fun x => c (.inl x)) = fun x => c' (.inl x) := funext h
    rw [hc]
  have h1 := prEvent_logged_cache v (BindBadC n) hE
  have h2 := ood_binding_coords hw v _ hv
  unfold EBn dExp stage
  refine h1.trans_le ?_
  exact h2

end SoundPcs
