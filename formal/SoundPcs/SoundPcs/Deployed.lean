-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Deployed,DeployedWired,WiringSetup}.lean` of this repository (the setup
-- computing the circuit's commitment with the oracle, the deployed run with each opening's stage logged, each
-- opening's doom bounded by F2's soundness on the composed run viewed as its adversary) to the EIP's PCS claims:
-- four commitments with out-of-domain answers (`formal/ComposePcs`), the claims of `reduceWith`
-- (`formal/Statement/PcsQuotient/Reduction.lean`'s `claimsAt`), six one-point openings.
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
table's word (`Compose.wiringSetup` of `stackWord`, the old public wiring layout's word: version 1 commits the
table of `24` variables as itself), then its out-of-domain point, coordinate `j` read off Keccak-256 at
`oodInput 24 root j` (`oodPointO`), and the table's polynomial there.

**The deployed run** (`dExp`), each stage logged from the start (`Stages.lean`):

1. the setup, then the adversary, given the circuit's commitment (`withSetup4`), outputs the reduction's proof
   (statement, four commitments, five values; `ComposePcs.RootProof4`, its circuit commitment overwritten by the
   setup's), the parts' two values and the six openings' proofs (`Rest`); its Keccak-256 queries are logged
   (the extractor reads them);
2. the chain over Keccak-256 (`ComposePcs.chainWith4`) gives the challenges (`DA4`);
3. the claims: `PcsQuotient.claimsAt` at `2^22` rows (`claimsD`), the Statement's `reduceWith` after its
   transcript;
4. the six openings, in the Rust's order (`Claims::all`): the witness claim on `W`, the wiring claim on the
   circuit's commitment, `H`'s claim, `Q`'s, `G`'s, the sum claim on `H`; each run only if the claims exist,
   its point has the commitment's number of variables and every earlier opening accepted
   (`checkAllWith` stops at the first failure).

**The verifier accepts** (`AccD`) when all six openings accept. **Each opening's doom** at its end (`EW`, `Eσ`,
`EH`, `EQ`, `EG`, `ES`) is bounded by `OpenSpec.sound` for the run up to it as its adversary
(`prEvent_EW_le`, …); **the binding event** (`EB`: `H`'s list not separated at its out-of-domain point at the
end) by `WhirBridge.Pcs.ood_binding_coords` on the whole run (`prEvent_EB_le`).
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

/-- What the adversary outputs besides the reduction's proof: the parts' two values (`Q`'s and `G`'s, never
hashed) and the six openings' proofs, in the order of `Claims::all`. -/
structure Rest where
  qv : E
  gv : E
  oW : Proof
  oσ : Proof
  oH : Proof
  oQ : Proof
  oG : Proof
  oS : Proof

/-- **The setup, then the adversary**: the adversary is given the circuit's commitment (root and out-of-domain
answer), and the proof the verifier reads carries it, whatever the adversary put there. -/
def withSetup4 (setup : OracleComp KeccakCalls (Bytes32 × E))
    (A : Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) :
    OracleComp KeccakCalls (RootProof4 E × Rest) :=
  setup >>= fun c => (fun po => ({ po.1 with ir := c.1, io := c.2 }, po.2)) <$> A c

theorem isTotalQueryBound_withSetup4 (setup : OracleComp KeccakCalls (Bytes32 × E))
    (A : Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hA : ∀ c, IsTotalQueryBound (A c) Q) :
    IsTotalQueryBound (withSetup4 setup A) (QS + Q) :=
  isTotalQueryBound_bind hS fun c => (isQueryBound_map_iff _ _ _ _ _).mpr (hA c)

/-- The protocol up to the openings: the proof, the rest, the adversary's Keccak-256 transcript, the
challenges. -/
structure S0 where
  π : RootProof4 E
  rest : Rest
  tA : Transcript
  ch : Chals E

variable {P : Params E} {B : P.Bounds} (W : Wire P B)

/-- **The adversary, its log, and the chain.** -/
def DA4 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls S0 :=
  loggedKC A >>= fun pt => chainWith4 W hash256 pt.1.1 >>= fun ch => pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩

theorem isTotalQueryBound_DA4 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) : IsTotalQueryBound (DA4 W A) (Q + 6) := by
  have h : ∀ pt : (RootProof4 E × Rest) × Transcript, IsTotalQueryBound
      (chainWith4 W hash256 pt.1.1 >>= fun ch =>
        (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ : OracleComp KeccakCalls S0)) (6 + 0) :=
    fun pt => isTotalQueryBound_bind (chain4_queryBound_kc W pt.1.1) fun ch =>
      (trivial : IsTotalQueryBound (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ : OracleComp KeccakCalls S0) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero] at this

/-! ## The claims -/

/-- The statement's 64 bytes as the Statement's `y` and `root`. -/
def stmtOf (sb : Vector UInt8 64) : PcsQuotient.Statement :=
  ⟨Vector.ofFn fun i : Fin 32 => sb.get ⟨i, by omega⟩, Vector.ofFn fun i : Fin 32 => sb.get ⟨32 + i, by omega⟩⟩

/-- **The claims** (`reduce` after its transcript, `PcsQuotient.claimsAt` at `2^22` rows) at the chain's
challenges, the proof's values and the parts' two values; `none` when a denominator vanishes. -/
def claimsD (a : S0) : Option PcsQuotient.Claims :=
  PcsQuotient.claimsAt 22 (stmtOf a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.ch.ρ (Vector.ofFn a.π.v.1) a.π.v.2
    a.rest.qv a.rest.gv

-- The claims are field arithmetic: kept folded, so that no unification evaluates them.
attribute [irreducible] claimsD

/-- A claim on `n` variables against a commitment, and its proof; `none` if the point has another number of
coordinates. -/
def mkIn (n : ℕ) (root : Bytes32) (ood : E) (c : PcsQuotient.Claim) (pf : Proof) :
    Option (Claim1 n × Proof) :=
  if h : c.point.length = n then some (⟨ofB root, ood, c.point, c.value, h⟩, pf) else none

/-- The witness opening's input: `W`'s commitment, the witness claim (`25` variables). -/
def inW (a : S0) : Option (Claim1 25 × Proof) :=
  (claimsD a).bind fun cl => mkIn 25 a.π.rW a.π.oW cl.witness a.rest.oW

/-- The wiring opening's input: the circuit's commitment (the setup's), the wiring claim (`24` variables). -/
def inσ (a : S0) : Option (Claim1 24 × Proof) :=
  (claimsD a).bind fun cl => mkIn 24 a.π.ir a.π.io cl.wiring a.rest.oσ

/-- `H`'s opening at the quotient point (`27` variables). -/
def inH (a : S0) : Option (Claim1 27 × Proof) :=
  (claimsD a).bind fun cl => mkIn 27 a.π.rH a.π.oH cl.h a.rest.oH

/-- `Q`'s opening (`28` variables). -/
def inQ (a : S0) : Option (Claim1 28 × Proof) :=
  (claimsD a).bind fun cl => mkIn 28 a.π.rQ a.π.oQ cl.q a.rest.oQ

/-- `G`'s opening (`25` variables). -/
def inG (a : S0) : Option (Claim1 25 × Proof) :=
  (claimsD a).bind fun cl => mkIn 25 a.π.rG a.π.oG cl.g a.rest.oG

/-- `H`'s opening at the sum point (`27` variables). -/
def inS (a : S0) : Option (Claim1 27 × Proof) :=
  (claimsD a).bind fun cl => mkIn 27 a.π.rH a.π.oH cl.sum a.rest.oS

/-! ## The stages -/

/-- The run through the witness opening. -/
abbrev X1 : Type := (S0 × Bool) × Transcript
/-- Through the wiring opening. -/
abbrev X2 : Type := (X1 × Bool) × Transcript
/-- Through `H`'s first opening. -/
abbrev X3 : Type := (X2 × Bool) × Transcript
/-- Through `Q`'s. -/
abbrev X4 : Type := (X3 × Bool) × Transcript
/-- Through `G`'s. -/
abbrev X5 : Type := (X4 × Bool) × Transcript
/-- Through `H`'s second: the whole run. -/
abbrev X6 : Type := (X5 × Bool) × Transcript

/-- The protocol up to the openings, in each stage. -/
def X1.s (x : X1) : S0 := x.1.1
def X2.s (x : X2) : S0 := X1.s x.1.1
def X3.s (x : X3) : S0 := X2.s x.1.1
def X4.s (x : X4) : S0 := X3.s x.1.1
def X5.s (x : X5) : S0 := X4.s x.1.1
def X6.s (x : X6) : S0 := X5.s x.1.1

/-- Every opening so far accepted. -/
def X1.ok (x : X1) : Bool := x.1.2
def X2.ok (x : X2) : Bool := X1.ok x.1.1 && x.1.2
def X3.ok (x : X3) : Bool := X2.ok x.1.1 && x.1.2
def X4.ok (x : X4) : Bool := X3.ok x.1.1 && x.1.2
def X5.ok (x : X5) : Bool := X4.ok x.1.1 && x.1.2
def X6.ok (x : X6) : Bool := X5.ok x.1.1 && x.1.2

variable (O : OpenSpec)

/-- An opening's input once every earlier opening accepted. -/
def gate {β : Type} (ok : Bool) (o : Option β) : Option β := if ok then o else none

/-- The run through the witness opening. -/
def e1 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X1 :=
  stage (DA4 W A) fun a => optV (O.V 25) (inW a)

/-- Through the wiring opening. -/
def e2 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X2 :=
  stage (e1 W O A) fun x => optV (O.V 24) (gate x.ok (inσ x.s))

/-- Through `H`'s first opening. -/
def e3 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X3 :=
  stage (e2 W O A) fun x => optV (O.V 27) (gate x.ok (inH x.s))

/-- Through `Q`'s. -/
def e4 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X4 :=
  stage (e3 W O A) fun x => optV (O.V 28) (gate x.ok (inQ x.s))

/-- Through `G`'s. -/
def e5 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X5 :=
  stage (e4 W O A) fun x => optV (O.V 25) (gate x.ok (inG x.s))

/-- **The deployed run**: the setup and the adversary, the chain, the claims, the six openings, each stage
logged from the start. -/
def dExp (A : OracleComp KeccakCalls (RootProof4 E × Rest)) : OracleComp KeccakCalls X6 :=
  stage (e5 W O A) fun x => optV (O.V 27) (gate x.ok (inS x.s))

/-! ## Query bounds -/

theorem isTotalQueryBound_stage_optV {α β : Type} (pre : OracleComp KeccakCalls α) (f : α → Option β)
    (V : β → OracleComp KeccakCalls Bool) (Qp QV : ℕ) (hp : IsTotalQueryBound pre Qp)
    (hV : ∀ w, IsTotalQueryBound (V w) QV) :
    IsTotalQueryBound (stage pre fun a => optV V (f a)) (Qp + QV) :=
  isTotalQueryBound_stage pre _ Qp QV hp fun a => isTotalQueryBound_optV V QV hV (f a)

theorem qb_e1 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e1 W O A) (Q + 6 + O.QO) := by
  unfold e1
  exact isTotalQueryBound_stage_optV (DA4 W A) inW (O.V 25) (Q + 6) O.QO (isTotalQueryBound_DA4 W A Q hQ)
    (O.queryBound 25)

theorem qb_e2 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e2 W O A) (Q + 6 + O.QO + O.QO) := by
  unfold e2
  exact isTotalQueryBound_stage (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) (Q + 6 + O.QO) O.QO (qb_e1 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 24) O.QO (O.queryBound 24) (gate x.ok (inσ x.s))

theorem qb_e3 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e3 W O A) (Q + 6 + O.QO + O.QO + O.QO) := by
  unfold e3
  exact isTotalQueryBound_stage (e2 W O A) (fun x => optV (O.V 27) (gate x.ok (inH x.s))) (Q + 6 + O.QO + O.QO) O.QO (qb_e2 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 27) O.QO (O.queryBound 27) (gate x.ok (inH x.s))

theorem qb_e4 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e4 W O A) (Q + 6 + O.QO + O.QO + O.QO + O.QO) := by
  unfold e4
  exact isTotalQueryBound_stage (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) (Q + 6 + O.QO + O.QO + O.QO) O.QO (qb_e3 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 28) O.QO (O.queryBound 28) (gate x.ok (inQ x.s))

theorem qb_e5 (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (e5 W O A) (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO) := by
  unfold e5
  exact isTotalQueryBound_stage (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (Q + 6 + O.QO + O.QO + O.QO + O.QO) O.QO (qb_e4 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 25) O.QO (O.queryBound 25) (gate x.ok (inG x.s))

theorem qb_dExp (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (dExp W O A) (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO) := by
  unfold dExp
  exact isTotalQueryBound_stage (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO) O.QO (qb_e5 W O A Q hQ)
    fun x => isTotalQueryBound_optV (O.V 27) O.QO (O.queryBound 27) (gate x.ok (inS x.s))

/-! ## The events -/

/-- An opening accepts while doomed at its end (its stage's verdict, input and cache). -/
def StageDoom {α : Type} (n : ℕ) (inp : α → Option (Claim1 n × Proof)) (x : (α × Bool) × Transcript) : Prop :=
  x.1.2 = true ∧ OptDoom (O.Doom n) (inp x.1.1) (cacheOfTr x.2)

/-- The witness opening accepts while doomed. -/
def EW (z : X6) : Prop := StageDoom O 25 inW z.1.1.1.1.1.1.1.1.1.1
/-- The wiring opening. -/
def Eσ (z : X6) : Prop := StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) z.1.1.1.1.1.1.1.1
/-- `H`'s first opening. -/
def EH (z : X6) : Prop := StageDoom O 27 (fun x : X2 => gate x.ok (inH x.s)) z.1.1.1.1.1.1
/-- `Q`'s opening. -/
def EQ (z : X6) : Prop := StageDoom O 28 (fun x : X3 => gate x.ok (inQ x.s)) z.1.1.1.1
/-- `G`'s opening. -/
def EG (z : X6) : Prop := StageDoom O 25 (fun x : X4 => gate x.ok (inG x.s)) z.1.1
/-- `H`'s second opening. -/
def ES (z : X6) : Prop := StageDoom O 27 (fun x : X5 => gate x.ok (inS x.s)) z

/-- **The binding event**: at the end of the run, some root on `27` variables whose out-of-domain inputs were all
asked has a list not separated at its point. -/
def EB (z : X6) : Prop := BindBadC 27 (cacheOfTr z.2)

/-- **The binding event at `n` variables**: at the end of the run, some root on `n` variables whose out-of-domain
inputs were all asked has a list not separated at its point (`EB` is `EBn 27`). -/
def EBn (n : ℕ) (z : X6) : Prop := BindBadC n (cacheOfTr z.2)

/-- **The deployed verifier accepts**: all six openings accept. -/
def AccD (z : X6) : Prop := z.ok = true

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

variable (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ) (hQ : IsTotalQueryBound A Q)
include hQ

theorem prEvent_EW_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EW O z] ≤ openingBound (Q + 6) := by
  unfold EW dExp
  refine keep_le (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (fun w : X5 => StageDoom O 25 inW w.1.1.1.1.1.1.1.1) ?_
  unfold e5
  refine keep_le (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (fun w : X4 => StageDoom O 25 inW w.1.1.1.1.1.1) ?_
  unfold e4
  refine keep_le (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) (fun w : X3 => StageDoom O 25 inW w.1.1.1.1) ?_
  unfold e3
  refine keep_le (e2 W O A) (fun x => optV (O.V 27) (gate x.ok (inH x.s))) (fun w : X2 => StageDoom O 25 inW w.1.1) ?_
  unfold e2
  refine keep_le (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) (fun w : X1 => StageDoom O 25 inW w) ?_
  exact prEvent_stageDoom_le O _ _ (isTotalQueryBound_DA4 W A Q hQ) 25 (by decide) (by decide) inW

theorem prEvent_Eσ_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[Eσ O z] ≤ openingBound (Q + 6 + O.QO) := by
  unfold Eσ dExp
  refine keep_le (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (fun w : X5 => StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) w.1.1.1.1.1.1) ?_
  unfold e5
  refine keep_le (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (fun w : X4 => StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) w.1.1.1.1) ?_
  unfold e4
  refine keep_le (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) (fun w : X3 => StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) w.1.1) ?_
  unfold e3
  refine keep_le (e2 W O A) (fun x => optV (O.V 27) (gate x.ok (inH x.s))) (fun w : X2 => StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) w) ?_
  exact prEvent_stageDoom_le O _ _ (qb_e1 W O A Q hQ) 24 (by decide) (by decide) (fun x : X1 => gate x.ok (inσ x.s))

theorem prEvent_EH_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EH O z] ≤
      openingBound (Q + 6 + O.QO + O.QO) := by
  unfold EH dExp
  refine keep_le (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (fun w : X5 => StageDoom O 27 (fun x : X2 => gate x.ok (inH x.s)) w.1.1.1.1) ?_
  unfold e5
  refine keep_le (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (fun w : X4 => StageDoom O 27 (fun x : X2 => gate x.ok (inH x.s)) w.1.1) ?_
  unfold e4
  refine keep_le (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) (fun w : X3 => StageDoom O 27 (fun x : X2 => gate x.ok (inH x.s)) w) ?_
  exact prEvent_stageDoom_le O _ _ (qb_e2 W O A Q hQ) 27 (by decide) (by decide) (fun x : X2 => gate x.ok (inH x.s))

theorem prEvent_EQ_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EQ O z] ≤
      openingBound (Q + 6 + O.QO + O.QO + O.QO) := by
  unfold EQ dExp
  refine keep_le (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (fun w : X5 => StageDoom O 28 (fun x : X3 => gate x.ok (inQ x.s)) w.1.1) ?_
  unfold e5
  refine keep_le (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (fun w : X4 => StageDoom O 28 (fun x : X3 => gate x.ok (inQ x.s)) w) ?_
  exact prEvent_stageDoom_le O _ _ (qb_e3 W O A Q hQ) 28 (by decide) (by decide) (fun x : X3 => gate x.ok (inQ x.s))

theorem prEvent_EG_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EG O z] ≤
      openingBound (Q + 6 + O.QO + O.QO + O.QO + O.QO) := by
  unfold EG dExp
  refine keep_le (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (fun w : X5 => StageDoom O 25 (fun x : X4 => gate x.ok (inG x.s)) w) ?_
  exact prEvent_stageDoom_le O _ _ (qb_e4 W O A Q hQ) 25 (by decide) (by decide) (fun x : X4 => gate x.ok (inG x.s))

theorem prEvent_ES_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[ES O z] ≤
      openingBound (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO) := by
  unfold ES dExp
  exact prEvent_stageDoom_le O _ _ (qb_e5 W O A Q hQ) 27 (by decide) (by decide) (fun x : X5 => gate x.ok (inS x.s))

/-- **The binding term at `n` variables**: `ood_binding_coords` on the whole run. -/
theorem prEvent_EBn_le (n : ℕ) (hw : Whir.Admissible n logInvRate) :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EBn n z] ≤
      ((Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO : ℕ) : ℝ≥0∞) * δc n +
        (((Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO) *
          (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  set v := e5 W O A >>= fun x => (x, ·) <$> optV (O.V 27) (gate x.ok (inS x.s)) with hvdef
  have hV : ∀ x : X5, IsTotalQueryBound ((x, ·) <$> optV (O.V 27) (gate x.ok (inS x.s))) O.QO :=
    fun x => by
      generalize gate x.ok (inS x.s) = o
      exact (isQueryBound_map_iff _ (fun b => (x, b)) _ _ _).mpr
        (isTotalQueryBound_optV (O.V 27) O.QO (O.queryBound 27) o)
  have hv : IsTotalQueryBound v (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO) :=
    isTotalQueryBound_bind (qb_e5 W O A Q hQ) hV
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

/-- **The binding term**: `ood_binding_coords` at `27` variables on the whole run. -/
theorem prEvent_EB_le :
    Pr{let z ← (simulateQ randomOracle (dExp W O A)).run' ∅}[EB z] ≤
      ((Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO : ℕ) : ℝ≥0∞) * δc 27 +
        (((Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO) *
          (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  set v := e5 W O A >>= fun x => (x, ·) <$> optV (O.V 27) (gate x.ok (inS x.s)) with hvdef
  have hV : ∀ x : X5, IsTotalQueryBound ((x, ·) <$> optV (O.V 27) (gate x.ok (inS x.s))) O.QO :=
    fun x => by
      generalize gate x.ok (inS x.s) = o
      exact (isQueryBound_map_iff _ (fun b => (x, b)) _ _ _).mpr
        (isTotalQueryBound_optV (O.V 27) O.QO (O.queryBound 27) o)
  have hv : IsTotalQueryBound v (Q + 6 + O.QO + O.QO + O.QO + O.QO + O.QO + O.QO) :=
    isTotalQueryBound_bind (qb_e5 W O A Q hQ) hV
  have hE : ∀ c c' : KeccakCalls.QueryCache, (∀ x, c (.inl x) = c' (.inl x)) →
      (BindBadC 27 c ↔ BindBadC 27 c') := fun c c' h => by
    unfold BindBadC
    have hc : (fun x => c (.inl x)) = fun x => c' (.inl x) := funext h
    rw [hc]
  have h1 := prEvent_logged_cache v (BindBadC 27) hE
  have h2 := ood_binding_coords (admissible_v1 27 (by decide) (by decide)) v _ hv
  unfold EB dExp stage
  refine h1.trans_le ?_
  exact h2

end SoundPcs
