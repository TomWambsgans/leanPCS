-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Deployed,DeployedWired}.lean` (`trace_deployed`, `trace_wired`: the
-- undoomed openings' candidates read back to the adversary's log, the wiring discharged by the setup) and
-- `formal/ComposePcs/ComposePcs/AdversaryLog4.lean` (`trace_adv4`) of this repository, to the six openings of
-- the EIP's PCS claims and the binding of `H`'s two.
import SoundPcs.Deployed

/-!
# The trace of the deployed run

**`trace_dExp`**: on every table of both oracles, a run of the deployed verifier that accepts while the
adversary-log extractor finds no witness, with none of the six openings doomed at its end and the four roots' lists
separated at their out-of-domain points (`¬ EB`, `¬ EBn 25`, `¬ EBn 28`), asks a bad fresh query of
`ComposePcs.advBad4P`. Each undoomed opening has a candidate of its root's extracted word satisfying its claim and the
commitment's out-of-domain answer (`stage_undoomed`), read back as a candidate of the word the adversary's log
commits to (no collision, no root answered after the adversary's last query: `merkleWord_stable`); the wiring
opening's candidate is the setup's table (`extract_wiringSetup`, `candidates_honest`); `H`'s two candidates agree at
the out-of-domain point, so they are one; each root's list separated at its point, its candidate is its only pinned
one (`pin_mem`, `pin_one`, the pins `ClaimsMatch.KP`); the claims then hold of F1's messages read off the candidates
(`ClaimsMatch`) and `ComposePcs.trace_core4P` applies.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable {P : Params E} {B : P.Bounds} (W : Wire P B)

/-! ## The claims, read as F1's -/

theorem adm25 : Whir.Admissible 25 logInvRate := admissible_v1 25 (by decide) (by decide)
theorem adm24 : Whir.Admissible 24 logInvRate := admissible_v1 24 (by decide) (by decide)
theorem adm27 : Whir.Admissible 27 logInvRate := admissible_v1 27 (by decide) (by decide)
theorem adm28 : Whir.Admissible 28 logInvRate := admissible_v1 28 (by decide) (by decide)

/-- **What the claims say of F1's messages**: a witness table satisfying the witness claim reads (`readW`) as a
first message satisfying F1's witness claim; the wiring table `q₀` satisfying the wiring claim gives F1's wiring
claim; the claims exist only when the reduction's own check holds; the parts satisfying their four claims
assemble (`asm`) into a second message satisfying F1's two quotient claims. -/
structure ClaimsMatch (q₀ : Column 24) where
  readW : Column 25 → B.Msg₁
  asm : Column 27 → Column 28 → Column 25 → B.Msg₂
  witness : ∀ (a : S0) (cl : PcsQuotient.Claims) (q : Column 25), claimsD a = some cl →
    cl.witness.point.length = 25 → colEval q cl.witness.point = cl.witness.value →
    witnessClaim (readW q).1 a.ch.t a.ch.ρ a.π.v.1
  wiring : ∀ (a : S0) (cl : PcsQuotient.Claims), claimsD a = some cl → cl.wiring.point.length = 24 →
    colEval q₀ cl.wiring.point = cl.wiring.value → wiringClaim P a.ch.t a.π.v.2
  check : ∀ (a : S0) (cl : PcsQuotient.Claims), claimsD a = some cl →
    reductionCheck P a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2
  quotient : ∀ (a : S0) (cl : PcsQuotient.Claims) (qH : Column 27) (qQ : Column 28) (qG : Column 25),
    claimsD a = some cl → cl.h.point.length = 27 → cl.sum.point.length = 27 → cl.q.point.length = 28 →
    cl.g.point.length = 25 → colEval qH cl.h.point = cl.h.value → colEval qH cl.sum.point = cl.sum.value →
    colEval qQ cl.q.point = cl.q.value → colEval qG cl.g.point = cl.g.value →
    quotientClaims P (W.decode a.π.stmt) (asm qH qQ qG).1 a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1 a.π.v.2 a.ch.ρ

variable {W} {q₀ : Column 24}

/-- The witness table's code: the extractor's decoder. -/
def ClaimsMatch.cW (M : ClaimsMatch W q₀) : TableCode B.Msg₁ := colCode 25 adm25 M.readW

/-- **The four list commitments**: `W`'s through `readW`, the parts' as their columns, assembled by `asm`. -/
def ClaimsMatch.K (M : ClaimsMatch W q₀) : Commits4 B (Column 27) (Column 28) (Column 25) :=
  ⟨M.cW.commit, (colCode 27 adm27 id).commit, (colCode 28 adm28 id).commit, (colCode 25 adm25 id).commit,
    M.asm⟩

/-! ## The candidates pinned by the out-of-domain answers -/

/-- A column has the answer `o` at the out-of-domain point of the root `r` on `n` variables, the point read off the
table (Keccak-256 at `oodInput n r j`, `46` bytes). -/
def okCol (n : ℕ) (T : QuotientRpm.Table) (r : Bytes32) (o : E) (q : Column n) : Prop :=
  colEval q (oodPointWith (fun x => ofB (T x)) n (ofB r)).toList = o

/-- **A committed table's pin**: its root's candidate columns (`colCode n hw id`), pinned by the answer at the point,
which reads the table at the `46`-byte inputs only. -/
def pinCol (n : ℕ) (hw : Whir.Admissible n logInvRate) : Pin (fun x => x.length = 46) E (Column n) where
  C := (colCode n hw id).commit
  ok := okCol n
  ok_congr T T' r o q h hq := by
    unfold okCol at hq ⊢
    have e : oodPointWith (fun x => ofB (T' x)) n (ofB r) = oodPointWith (fun x => ofB (T x)) n (ofB r) := by
      unfold oodPointWith
      exact congrArg Vector.ofFn (funext fun j => by beta_reduce; rw [h _ (oodInput_length _ _)])
    rw [e]
    exact hq

/-- **The four commitments' pins**: `W` and `G` on `25` variables, `H` on `27`, `Q` on `28`; `W`'s column read as F1's
first message by `readW`, the parts assembled by `asm`. -/
def ClaimsMatch.KP (M : ClaimsMatch W q₀) : Pins4 B (Column 25) (Column 27) (Column 28) (Column 25) where
  zin x := x.length = 46
  zin_len x hx := by
    have h : x.length = 46 := hx
    omega
  pW := pinCol 25 adm25
  pH := pinCol 27 adm27
  pQ := pinCol 28 adm28
  pG := pinCol 25 adm25
  rdW := M.readW
  asm := M.asm

variable (W)

/-- **Knowledge soundness is broken**: the deployed verifier accepts while no message the extractor reads off the
adversary's Keccak-256 log and the proof (`adversaryExtractor4`, the witness root's Merkle word decoded by `cW`)
is a witness of the statement. -/
def BreaksD (cW : TableCode B.Msg₁) (z : X6) : Prop :=
  AccD z ∧ ∀ g ∈ adversaryExtractor4 cW z.s.tA z.s.π, ¬ P.Sat (W.decode z.s.π.stmt) (P.cells g.1)

/-! ## Runs against a table -/

/-- The adversary and the chain against a table. -/
theorem DA4_run (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := labelOf4 W p.1.pre
    let x₁ := afterW W (viewT T x₀) p.1.comW
    let x₂ := (viewT T x₁).toList
    let x₃ := (viewT T x₂).toList
    let x₄ := afterHQG W (viewT T x₃) p.1.comHQG
    let x₅ := W.afterValues (viewT T x₄) p.1.v
    (tableQueryLog (DA4 W A) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          [.inl x₀, .inl x₁, .inl x₂, .inl x₃, .inl x₄, .inl x₅] ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (DA4 W A) =
        ⟨p.1, p.2, (tableQueryLog A T).filterMap inlEntry,
          ⟨W.chal (viewT T x₁), W.chal (viewT T x₂), W.chal (viewT T x₃), W.chal (viewT T x₄),
            W.chal (viewT T x₅)⟩⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅
  obtain ⟨hl, he⟩ := run_logged A T
  have hl' : tableQueryLog (loggedKC A) T = tableQueryLog A T := hl
  have he' : evalWithAnswerFn (QueryImpl.ofFn T) (loggedKC A) =
      (p, (tableQueryLog A T).filterMap inlEntry) := he
  constructor
  · unfold DA4
    rw [tableQueryLog_bind, hl', he']
    simp only [chainWith4, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.map_append, List.append_nil,
      evalWithAnswerFn_liftM_query]
    rfl
  · unfold DA4
    rw [evalWithAnswerFn_bind, he']
    simp only [chainWith4, hash256, callKeccak256, bind_assoc, pure_bind,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- The chain's six inputs, on a table. -/
def chainIns (T : QuotientRpm.Table) (π : RootProof4 E) : List (List UInt8) :=
  let x₀ := labelOf4 W π.pre
  let x₁ := afterW W (T x₀) π.comW
  let x₂ := (T x₁).toList
  let x₃ := (T x₂).toList
  let x₄ := afterHQG W (T x₃) π.comHQG
  let x₅ := W.afterValues (T x₄) π.v
  [x₀, x₁, x₂, x₃, x₄, x₅]

/-- The chain's challenges, on a table. -/
def chalsOf (T : QuotientRpm.Table) (π : RootProof4 E) : Chals E :=
  let x₀ := labelOf4 W π.pre
  let x₁ := afterW W (T x₀) π.comW
  let x₂ := (T x₁).toList
  let x₃ := (T x₂).toList
  let x₄ := afterHQG W (T x₃) π.comHQG
  let x₅ := W.afterValues (T x₄) π.v
  ⟨W.chal (T x₁), W.chal (T x₂), W.chal (T x₃), W.chal (T x₄), W.chal (T x₅)⟩

/-- The adversary and the chain against a table, the chain's inputs and challenges folded. -/
theorem DA4_run' (A : OracleComp KeccakCalls (RootProof4 E × Rest)) (T : KTable) :
    (tableQueryLog (DA4 W A) T).map Sigma.fst = (tableQueryLog A T).map Sigma.fst ++
        (chainIns W (viewT T) (evalWithAnswerFn (QueryImpl.ofFn T) A).1).map Sum.inl ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (DA4 W A) =
        ⟨(evalWithAnswerFn (QueryImpl.ofFn T) A).1, (evalWithAnswerFn (QueryImpl.ofFn T) A).2,
          (tableQueryLog A T).filterMap inlEntry, chalsOf W (viewT T) (evalWithAnswerFn (QueryImpl.ofFn T) A).1⟩ := by
  obtain ⟨h1, h2⟩ := DA4_run W A T
  exact ⟨h1, h2⟩

/-- The setup, then the adversary, against a table: the setup's queries first, and the proof carries the
setup's commitment. -/
theorem withSetup4_run (setup : OracleComp KeccakCalls (Bytes32 × E))
    (A₀ : Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (T : KTable) :
    tableQueryLog (withSetup4 setup A₀) T = tableQueryLog setup T ++
        tableQueryLog (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)) T ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (withSetup4 setup A₀)).1.ir =
        (evalWithAnswerFn (QueryImpl.ofFn T) setup).1 := by
  constructor
  · rw [withSetup4, tableQueryLog_bind, map_eq_bind_pure_comp, tableQueryLog_bind,
      Function.comp_apply, tableQueryLog_pure, List.append_nil]
  · simp only [withSetup4, evalWithAnswerFn_bind, evalWithAnswerFn_map]

/-- The setup against a table: the tree's queries first; its root is the tree's. -/
theorem setupPcs_run (q₀ : Column 24) (T : KTable) :
    (∃ l, tableQueryLog (setupPcs q₀) T = tableQueryLog (wiringSetup (rootHeight 24 logInvRate)
      (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀)) T ++ l) ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (setupPcs q₀)).1 =
        evalWithAnswerFn (QueryImpl.ofFn T) (wiringSetup (rootHeight 24 logInvRate)
          (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀)) := by
  constructor
  · exact ⟨_, by rw [setupPcs, tableQueryLog_bind]⟩
  · simp only [setupPcs, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-! ## No collision -/

open Classical in
/-- No bad fresh query: the table is injective on the log. -/
theorem injOn_of_not_freshBad4 {MH MQ MG : Type} (K : Commits4 B MH MQ MG) {L : List (List UInt8)}
    {T : Table} (hnb : ¬ FreshBad (listBad4 W K) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBad4 W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4 W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz hyz
  have hy' := List.mem_toFinset.mp hy
  have hz' := List.mem_toFinset.mp hz
  by_contra hne
  rcases before_trichotomy L y z hy' hz' hne with h | h
  · exact nb z hz' (Or.inl (Or.inl ⟨y, h, hyz⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))

/-! ## An undoomed opening's candidate -/

/-- The history a log's Keccak-256 inputs make. -/
def histL (l : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d)) : List (List UInt8) :=
  (l.map Sigma.fst).filterMap Sum.getLeft?

theorem histL_append (l l' : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d)) :
    histL (l ++ l') = histL l ++ histL l' := by
  simp [histL, List.filterMap_append]

theorem ansOf_getD {H : QuotientRpm.Hist} {T : KTable} {x : List UInt8} (hx : x ∈ H) :
    (ansOf H (viewT T) x).getD default = T (.inl x) := by
  unfold ansOf
  rw [if_pos hx, Option.getD_some]
  exact LeanVM.Rpm.digestOfRpm_toRpm _

/-- **An undoomed accepting opening has a candidate**: in the word extracted from the stage's history under its
root, satisfying its claim, with the out-of-domain point of the table's answers; the out-of-domain inputs are in
the history. -/
theorem stage_undoomed (O : OpenSpec) {α : Type} (n : ℕ) (pre : OracleComp KeccakCalls α)
    (inp : α → Option (Claim1 n × Proof)) (T : KTable) (w : Claim1 n × Proof)
    (e : OracleComp KeccakCalls ((α × Bool) × Transcript))
    (he : e = stage pre fun a => optV (O.V n) (inp a))
    (hin : inp (evalWithAnswerFn (QueryImpl.ofFn T) pre) = some w)
    (hb : (evalWithAnswerFn (QueryImpl.ofFn T) e).1.2 = true)
    (hnd : ¬ StageDoom O n inp (evalWithAnswerFn (QueryImpl.ofFn T) e)) :
    (∃ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
        (Rom.extract (ansOf (histL (tableQueryLog e T)).toFinset
          (viewT T)) w.1.root (rootHeight n logInvRate) (2 ^ laneFold)),
      colEval q w.1.point = w.1.value ∧
        colEval q (oodPointWith (fun x => T (.inl x)) n w.1.root).toList = w.1.ood) ∧
      ∀ j : Fin n, oodInput n w.1.root j ∈ histL (tableQueryLog e T) := by
  subst he
  obtain ⟨hl, he⟩ := stage_run pre (fun a => optV (O.V n) (inp a)) T
  set a := evalWithAnswerFn (QueryImpl.ofFn T) pre
  set lg := tableQueryLog (stage pre fun a => optV (O.V n) (inp a)) T
  have hV : optV (O.V n) (inp a) = O.V n w := by rw [hin]; rfl
  rw [hV] at hl he
  have hb' : evalWithAnswerFn (QueryImpl.ofFn T) (O.V n w) = true := by rw [he] at hb; exact hb
  have hask : ∀ j : Fin n, oodInput n w.1.root j ∈ histL lg := by
    intro j
    have := O.asks n w T hb' j
    refine mem_filterMap_getLeft?.mpr ?_
    show Sum.inl _ ∈ lg.map Sigma.fst
    rw [hl, List.map_append]
    exact List.mem_append_right _ this
  refine ⟨?_, hask⟩
  have hsnd : ∀ q ∈ lg, q.2 = T q.1 := tableQueryLog_snd_dep T _
  have hc := cacheOfTr_eq_ansOf T lg hsnd
  have hnd' : ¬ O.Doom n w (cacheOfTr (lg.filterMap inlEntry)) := by
    intro h
    refine hnd ⟨hb, ?_⟩
    rw [he]
    show OptDoom (O.Doom n) (inp a) _
    rw [hin]
    rw [← hl]
    exact h
  have hsome : ∀ j : Fin n, (cacheOfTr (lg.filterMap inlEntry) (.inl (oodInput n w.1.root j))).isSome := by
    intro j
    have h := congrFun hc (oodInput n w.1.root j)
    rw [h]
    have hm : oodInput n w.1.root j ∈ ((lg.map Sigma.fst).filterMap Sum.getLeft?).toFinset :=
      List.mem_toFinset.mpr (hask j)
    unfold ansOf
    rw [if_pos hm]
    rfl
  obtain ⟨q, hq, hv, ho⟩ := O.undoomed n w _ hnd' hsome
  refine ⟨q, ?_, hv, ?_⟩
  · unfold rootList at hq
    rw [hc] at hq
    exact hq
  · set c := cacheOfTr (lg.filterMap inlEntry) with hcdef
    have hj : ∀ j : Fin n, (c.toFn (.inl (oodInput n w.1.root j))).getD default =
        T (.inl (oodInput n w.1.root j)) := fun j => by
      rw [show c.toFn (.inl (oodInput n w.1.root j)) =
        ansOf (histL lg).toFinset (viewT T) (oodInput n w.1.root j) from congrFun hc _]
      exact ansOf_getD (List.mem_toFinset.mpr (hask j))
    have hz : oodPointWith (fun x => (c.toFn (.inl x)).getD default) n w.1.root =
        oodPointWith (fun x => T (.inl x)) n w.1.root := by
      unfold oodPointWith
      exact congrArg Vector.ofFn (funext fun j =>
        congrArg (fun d => elemOf ((KeccakHash.digestBytes d).drop 8)) (hj j))
    rw [← hz]
    exact ho

/-! ## Pinned candidates, read off a run -/

theorem ofB_viewT (T : KTable) : (fun x => ofB (viewT T x)) = fun x => T (.inl x) :=
  funext fun x => LeanVM.Rpm.digestOfRpm_toRpm _

/-- A candidate column with the answer at the point is pinned. -/
theorem pin_mem {n : ℕ} (hw : Whir.Admissible n logInvRate) {L : List (List UInt8)} {T : KTable}
    (hinj : Set.InjOn (viewT T) ↑L.toFinset) (r : Bytes32) (o : E) (q : Column n)
    (hq : q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
      (Rom.extract (ansOf L.toFinset (viewT T)) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)))
    (ho : colEval q (oodPointWith (fun x => T (.inl x)) n (ofB r)).toList = o) :
    (pinCol n hw).Mem L.toFinset (viewT T) r o q := by
  refine ⟨(mem_cands_colCode hw id hinj r q).mpr ⟨q, hq, rfl⟩, ?_⟩
  show colEval q (oodPointWith (fun x => ofB (viewT T x)) n (ofB r)).toList = o
  rw [ofB_viewT]
  exact ho

/-- **A root's list separated at its point has one pinned candidate.** -/
theorem pin_one {n : ℕ} (hw : Whir.Admissible n logInvRate) {L : List (List UInt8)} {T : KTable}
    (hinj : Set.InjOn (viewT T) ↑L.toFinset) (r : Bytes32) (o : E)
    (hsep : SepAt (rootList (n := n) (ansOf L.toFinset (viewT T)) (ofB r))
      (oodPointWith (fun x => T (.inl x)) n (ofB r))) :
    (pinCol n hw).One L.toFinset (viewT T) r o := by
  intro a b ha hb
  obtain ⟨qa, hqa, rfl⟩ := (mem_cands_colCode hw id hinj r a).mp ha.1
  obtain ⟨qb, hqb, rfl⟩ := (mem_cands_colCode hw id hinj r b).mp hb.1
  have ea : colEval qa (oodPointWith (fun x => ofB (viewT T x)) n (ofB r)).toList = o := ha.2
  have eb : colEval qb (oodPointWith (fun x => ofB (viewT T x)) n (ofB r)).toList = o := hb.2
  rw [ofB_viewT] at ea eb
  exact hsep qa hqa qb hqb (ea.trans eb.symm)

/-! ## Small facts -/

/-- A stage's run, in four parts. -/
theorem stage_facts {α : Type} (e : OracleComp KeccakCalls ((α × Bool) × Transcript))
    (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool) (he : e = stage pre V)
    (T : KTable) :
    tableQueryLog e T = tableQueryLog pre T ++
        tableQueryLog (V (evalWithAnswerFn (QueryImpl.ofFn T) pre)) T ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) e).1.1 = evalWithAnswerFn (QueryImpl.ofFn T) pre ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) e).1.2 =
        evalWithAnswerFn (QueryImpl.ofFn T) (V (evalWithAnswerFn (QueryImpl.ofFn T) pre)) ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) e).2 = (tableQueryLog e T).filterMap inlEntry := by
  subst he
  obtain ⟨hl, hev⟩ := stage_run pre V T
  refine ⟨hl, ?_, ?_, ?_⟩ <;> rw [hev]
  rw [hl]

theorem optV_true {β : Type} (V : β → OracleComp KeccakCalls Bool) (o : Option β) (T : KTable)
    (h : evalWithAnswerFn (QueryImpl.ofFn T) (optV V o) = true) : ∃ w, o = some w := by
  cases o with
  | some w => exact ⟨w, rfl⟩
  | none => simp [optV] at h

theorem gate_some {β : Type} {b : Bool} {o : Option β} {w : β} (h : gate b o = some w) :
    b = true ∧ o = some w := by
  unfold gate at h
  split_ifs at h with hb
  · exact ⟨hb, h⟩

theorem mkIn_some {n : ℕ} {r : Bytes32} {o : E} {c : PcsQuotient.Claim} {pf : Proof}
    {w : Claim1 n × Proof} (h : mkIn n r o c pf = some w) :
    c.point.length = n ∧ w.1.root = ofB r ∧ w.1.ood = o ∧ w.1.point = c.point ∧ w.1.value = c.value := by
  unfold mkIn at h
  split_ifs at h with hl
  · cases h
    exact ⟨hl, rfl, rfl, rfl, rfl⟩

theorem bind_some {β γ : Type} {o : Option β} {f : β → Option γ} {w : γ} (h : o.bind f = some w) :
    ∃ b, o = some b ∧ f b = some w := by
  cases o with
  | none => simp at h
  | some b => exact ⟨b, rfl, h⟩

/-- With every coordinate of a root's out-of-domain point in the history, the point read off the history's
answers is the table's. -/
theorem oodPointOf_ansOf {H : QuotientRpm.Hist} {T : KTable} {n : ℕ} {r : Digest}
    (h : ∀ j : Fin n, oodInput n r j ∈ H) :
    oodPointOf (ansOf H (viewT T)) n r = some (oodPointWith (fun x => T (.inl x)) n r) := by
  have hs : ∀ j : Fin n, (ansOf H (viewT T) (oodInput n r j)).isSome := fun j => by
    unfold ansOf
    rw [if_pos (h j)]
    rfl
  unfold oodPointOf
  rw [dif_pos hs]
  refine congrArg some (congrArg Vector.ofFn (funext fun j => ?_))
  have hg : (ansOf H (viewT T) (oodInput n r j)).get (hs j) = T (.inl (oodInput n r j)) := by
    have := ansOf_getD (T := T) (h j)
    rw [Option.getD_eq_iff] at this
    rcases this with h1 | ⟨h1, -⟩
    · rw [Option.get_of_eq_some _ h1]
    · exact absurd h1 (Option.isSome_iff_ne_none.mp (hs j))
  rw [hg]
  rfl

/-- **The candidates of a root through two histories are one**, when the answers are injective on both and the
Merkle words under the root agree. -/
theorem cands_transfer {n : ℕ} {H H' : List (List UInt8)} {T : QuotientRpm.Table} (r : Bytes32)
    (hinj : Set.InjOn T ↑H.toFinset) (hinj' : Set.InjOn T ↑H'.toFinset)
    (hw : merkleWord H.toFinset T (rootHeight n logInvRate) leafBytes r =
      merkleWord H'.toFinset T (rootHeight n logInvRate) leafBytes r) :
    Candidates n logInvRate (code₀ n logInvRate).thr
        (Rom.extract (ansOf H.toFinset T) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) =
      Candidates n logInvRate (code₀ n logInvRate).thr
        (Rom.extract (ansOf H'.toFinset T) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) := by
  have hr : toB (ofB r) = r := LeanVM.Rpm.digestToRpm_ofRpm r
  rw [← candidates_wordOfMerkle hinj, ← candidates_wordOfMerkle hinj', hr, hw]

end SoundPcs

namespace SoundPcs

open Compose ComposePcs QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable {P : Params E} {B : P.Bounds} (W : Wire P B) {q₀ : Column 24}

theorem stage_facts' {α : Type} (e : OracleComp KeccakCalls ((α × Bool) × Transcript))
    (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool) (he : e = stage pre V)
    (T : KTable) (x : (α × Bool) × Transcript) (y : α) (hx : evalWithAnswerFn (QueryImpl.ofFn T) e = x)
    (hy : evalWithAnswerFn (QueryImpl.ofFn T) pre = y) :
    tableQueryLog e T = tableQueryLog pre T ++ tableQueryLog (V y) T ∧ x.1.1 = y ∧
      x.1.2 = evalWithAnswerFn (QueryImpl.ofFn T) (V y) ∧ x.2 = (tableQueryLog e T).filterMap inlEntry := by
  subst hx hy
  exact stage_facts e pre V he T

theorem stage_undoomed' (O : OpenSpec) {α : Type} (n : ℕ) (pre : OracleComp KeccakCalls α)
    (inp : α → Option (Claim1 n × Proof)) (T : KTable) (w : Claim1 n × Proof)
    (e : OracleComp KeccakCalls ((α × Bool) × Transcript))
    (he : e = stage pre fun a => optV (O.V n) (inp a)) (x : (α × Bool) × Transcript) (y : α)
    (hx : evalWithAnswerFn (QueryImpl.ofFn T) e = x) (hy : evalWithAnswerFn (QueryImpl.ofFn T) pre = y)
    (hin : inp y = some w) (hb : x.1.2 = true) (hnd : ¬ StageDoom O n inp x) :
    (∃ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
        (Rom.extract (ansOf (histL (tableQueryLog e T)).toFinset
          (viewT T)) w.1.root (rootHeight n logInvRate) (2 ^ laneFold)),
      colEval q w.1.point = w.1.value ∧
        colEval q (oodPointWith (fun x => T (.inl x)) n w.1.root).toList = w.1.ood) ∧
      ∀ j : Fin n, oodInput n w.1.root j ∈ histL (tableQueryLog e T) := by
  subst hx hy
  exact stage_undoomed O n pre inp T w e he hin hb hnd

theorem adversaryExtractor4_eq (c : TableCode B.Msg₁) (log : Transcript) (π : RootProof4 E) :
    adversaryExtractor4 c log π = c.commit.cands (histOfTr log) (tableOfTr log) π.rW := rfl

theorem histL_prefix {l l' r : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d)} (h : l' = l ++ r) :
    ∀ y ∈ histL l, y ∈ histL l' := fun y hy => by
  rw [h, histL_append]
  exact List.mem_append_left _ hy

/-! ## The trace -/

/-! ## The stages, unfolded once -/

theorem e1_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    e1 W O A = stage (DA4 W A) (fun a => optV (O.V 25) (inW a)) := rfl

theorem e2_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    e2 W O A = stage (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) := rfl

theorem e3_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    e3 W O A = stage (e2 W O A) (fun x => optV (O.V 27) (gate x.ok (inH x.s))) := rfl

theorem e4_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    e4 W O A = stage (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) := rfl

theorem e5_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    e5 W O A = stage (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) := rfl

theorem dExp_eq (O : OpenSpec) (A : OracleComp KeccakCalls (RootProof4 E × Rest)) :
    dExp W O A = stage (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) := rfl

-- The runs are kept folded in the trace: no unification evaluates them.
attribute [local irreducible] stage DA4 e1 e2 e3 e4 e5 dExp withSetup4 setupPcs loggedKC

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
open Classical in
/-- **The trace, for any adversary whose queries begin with the setup's tree** and whose proof carries the
tree's root. -/
theorem trace_dExpA (O : OpenSpec) (M : ClaimsMatch W q₀) (A : OracleComp KeccakCalls (RootProof4 E × Rest))
    (T : KTable) (r0 : Bytes32) (lw0 : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d))
    (hsl : ∃ l, tableQueryLog A T = lw0 ++ l)
    (hsir : (evalWithAnswerFn (QueryImpl.ofFn T) A).1.ir = r0)
    (hext : ∀ H : QuotientRpm.Hist, (∀ x, Sum.inl x ∈ lw0.map Sigma.fst → x ∈ H) →
      Set.InjOn (viewT T) ↑H → ∀ v < 2 ^ rootHeight 24 logInvRate,
        Rom.extract (ansOf H (viewT T)) (ofB r0) (rootHeight 24 logInvRate) (2 ^ laneFold) v =
          LeanVM.Protocol.Whir.Complete.stackWord 24 q₀ v)
    (hev : BreaksD W M.cW (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EW O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ Eσ O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EH O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EQ O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EG O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ ES O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EB (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EBn 25 (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A)) ∧
      ¬ EBn 28 (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A))) :
    FreshBad (advBad4P W M.KP A) T ∅ ((tableQueryLog (dExp W O A) T).map Sigma.fst) := by
  obtain ⟨lws, hsl⟩ := hsl
  -- The runs, every evaluation named.
  obtain ⟨h0l, h0e⟩ := DA4_run' W A T
  generalize hp : evalWithAnswerFn (QueryImpl.ofFn T) A = p at h0l h0e hsir
  generalize ha : evalWithAnswerFn (QueryImpl.ofFn T) (DA4 W A) = a at h0e
  generalize hx1 : evalWithAnswerFn (QueryImpl.ofFn T) (e1 W O A) = x1
  generalize hx2 : evalWithAnswerFn (QueryImpl.ofFn T) (e2 W O A) = x2
  generalize hx3 : evalWithAnswerFn (QueryImpl.ofFn T) (e3 W O A) = x3
  generalize hx4 : evalWithAnswerFn (QueryImpl.ofFn T) (e4 W O A) = x4
  generalize hx5 : evalWithAnswerFn (QueryImpl.ofFn T) (e5 W O A) = x5
  generalize hz : evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O A) = z at hev
  obtain ⟨f11, f12, f13, f14⟩ := stage_facts' (e1 W O A) (DA4 W A) (fun a => optV (O.V 25) (inW a)) (e1_eq W O A) T x1 a hx1 ha
  obtain ⟨f21, f22, f23, f24⟩ := stage_facts' (e2 W O A) (e1 W O A) (fun x => optV (O.V 24) (gate x.ok (inσ x.s))) (e2_eq W O A) T x2 x1 hx2 hx1
  obtain ⟨f31, f32, f33, f34⟩ := stage_facts' (e3 W O A) (e2 W O A) (fun x => optV (O.V 27) (gate x.ok (inH x.s))) (e3_eq W O A) T x3 x2 hx3 hx2
  obtain ⟨f41, f42, f43, f44⟩ := stage_facts' (e4 W O A) (e3 W O A) (fun x => optV (O.V 28) (gate x.ok (inQ x.s))) (e4_eq W O A) T x4 x3 hx4 hx3
  obtain ⟨f51, f52, f53, f54⟩ := stage_facts' (e5 W O A) (e4 W O A) (fun x => optV (O.V 25) (gate x.ok (inG x.s))) (e5_eq W O A) T x5 x4 hx5 hx4
  obtain ⟨f61, f62, f63, f64⟩ := stage_facts' (dExp W O A) (e5 W O A) (fun x => optV (O.V 27) (gate x.ok (inS x.s))) (dExp_eq W O A) T z x5 hz hx5
  obtain ⟨hB, hEW, hEσ, hEH, hEQ, hEG, hES, hEB, hEB25, hEB28⟩ := hev
  -- The protocol up to the openings, in every stage.
  have hs1 : x1.s = a := f12
  have hs2 : x2.s = a := by show X1.s x2.1.1 = a; rw [f22]; exact hs1
  have hs3 : x3.s = a := by show X2.s x3.1.1 = a; rw [f32]; exact hs2
  have hs4 : x4.s = a := by show X3.s x4.1.1 = a; rw [f42]; exact hs3
  have hs5 : x5.s = a := by show X4.s x5.1.1 = a; rw [f52]; exact hs4
  have hs6 : z.s = a := by show X5.s z.1.1 = a; rw [f62]; exact hs5
  have haπ : a.π = p.1 := by rw [h0e]
  have hatA : a.tA = (tableQueryLog A T).filterMap inlEntry := by rw [h0e]
  -- Every opening accepted.
  have hacc := hB.1
  unfold AccD X6.ok at hacc
  rw [Bool.and_eq_true, f62] at hacc
  obtain ⟨hok5, hb6⟩ := hacc
  unfold X5.ok at hok5
  rw [Bool.and_eq_true, f52] at hok5
  obtain ⟨hok4, hb5⟩ := hok5
  unfold X4.ok at hok4
  rw [Bool.and_eq_true, f42] at hok4
  obtain ⟨hok3, hb4⟩ := hok4
  unfold X3.ok at hok3
  rw [Bool.and_eq_true, f32] at hok3
  obtain ⟨hok2, hb3⟩ := hok3
  unfold X2.ok at hok2
  rw [Bool.and_eq_true, f22] at hok2
  obtain ⟨hok1, hb2⟩ := hok2
  have hb1 : x1.1.2 = true := hok1
  -- The openings' inputs.
  obtain ⟨w1, hin1⟩ := optV_true (O.V 25) (inW a) T (f13.symm.trans hb1)
  obtain ⟨w2, hg2⟩ := optV_true (O.V 24) (gate x1.ok (inσ x1.s)) T (f23.symm.trans hb2)
  obtain ⟨w3, hg3⟩ := optV_true (O.V 27) (gate x2.ok (inH x2.s)) T (f33.symm.trans hb3)
  obtain ⟨w4, hg4⟩ := optV_true (O.V 28) (gate x3.ok (inQ x3.s)) T (f43.symm.trans hb4)
  obtain ⟨w5, hg5⟩ := optV_true (O.V 25) (gate x4.ok (inG x4.s)) T (f53.symm.trans hb5)
  obtain ⟨w6, hg6⟩ := optV_true (O.V 27) (gate x5.ok (inS x5.s)) T (f63.symm.trans hb6)
  have hin2 : inσ a = some w2 := by rw [← hs1]; exact (gate_some hg2).2
  have hin3 : inH a = some w3 := by rw [← hs2]; exact (gate_some hg3).2
  have hin4 : inQ a = some w4 := by rw [← hs3]; exact (gate_some hg4).2
  have hin5 : inG a = some w5 := by rw [← hs4]; exact (gate_some hg5).2
  have hin6 : inS a = some w6 := by rw [← hs5]; exact (gate_some hg6).2
  obtain ⟨cl, hcl, hm1⟩ := bind_some (o := claimsD a) hin1
  obtain ⟨cl2, hcl2, hm2⟩ := bind_some (o := claimsD a) hin2
  obtain ⟨cl3, hcl3, hm3⟩ := bind_some (o := claimsD a) hin3
  obtain ⟨cl4, hcl4, hm4⟩ := bind_some (o := claimsD a) hin4
  obtain ⟨cl5, hcl5, hm5⟩ := bind_some (o := claimsD a) hin5
  obtain ⟨cl6, hcl6, hm6⟩ := bind_some (o := claimsD a) hin6
  obtain rfl : cl2 = cl := Option.some.inj (hcl2.symm.trans hcl)
  obtain rfl : cl3 = cl2 := Option.some.inj (hcl3.symm.trans hcl)
  obtain rfl : cl4 = cl3 := Option.some.inj (hcl4.symm.trans hcl)
  obtain rfl : cl5 = cl4 := Option.some.inj (hcl5.symm.trans hcl)
  obtain rfl : cl6 = cl5 := Option.some.inj (hcl6.symm.trans hcl)
  obtain ⟨l1, r1, o1, p1, v1⟩ := mkIn_some hm1
  obtain ⟨l2, r2, -, p2, v2⟩ := mkIn_some hm2
  obtain ⟨l3, r3, o3, p3, v3⟩ := mkIn_some hm3
  obtain ⟨l4, r4, o4, p4, v4⟩ := mkIn_some hm4
  obtain ⟨l5, r5, o5, p5, v5⟩ := mkIn_some hm5
  obtain ⟨l6, r6, o6, p6, v6⟩ := mkIn_some hm6
  -- No opening is doomed: each has a candidate.
  have hnd1 : ¬ StageDoom O 25 inW x1 := by
    unfold EW at hEW; rwa [f62, f52, f42, f32, f22] at hEW
  have hnd2 : ¬ StageDoom O 24 (fun x : X1 => gate x.ok (inσ x.s)) x2 := by
    unfold Eσ at hEσ; rwa [f62, f52, f42, f32] at hEσ
  have hnd3 : ¬ StageDoom O 27 (fun x : X2 => gate x.ok (inH x.s)) x3 := by
    unfold EH at hEH; rwa [f62, f52, f42] at hEH
  have hnd4 : ¬ StageDoom O 28 (fun x : X3 => gate x.ok (inQ x.s)) x4 := by
    unfold EQ at hEQ; rwa [f62, f52] at hEQ
  have hnd5 : ¬ StageDoom O 25 (fun x : X4 => gate x.ok (inG x.s)) x5 := by
    unfold EG at hEG; rwa [f62] at hEG
  obtain ⟨⟨q1, hq1, hv1, ho1⟩, hask1⟩ := stage_undoomed' O 25 (DA4 W A) inW T w1 (e1 W O A) (e1_eq W O A) x1 a hx1 ha
    hin1 hb1 hnd1
  obtain ⟨⟨q2, hq2, hv2, -⟩, -⟩ := stage_undoomed' O 24 (e1 W O A) (fun x : X1 => gate x.ok (inσ x.s)) T w2
    (e2 W O A) (e2_eq W O A) x2 x1 hx2 hx1 hg2 hb2 hnd2
  obtain ⟨⟨q3, hq3, hv3, ho3⟩, hask3⟩ := stage_undoomed' O 27 (e2 W O A)
    (fun x : X2 => gate x.ok (inH x.s)) T w3 (e3 W O A) (e3_eq W O A) x3 x2 hx3 hx2 hg3 hb3 hnd3
  obtain ⟨⟨q4, hq4, hv4, ho4⟩, hask4⟩ := stage_undoomed' O 28 (e3 W O A) (fun x : X3 => gate x.ok (inQ x.s)) T w4
    (e4 W O A) (e4_eq W O A) x4 x3 hx4 hx3 hg4 hb4 hnd4
  obtain ⟨⟨q5, hq5, hv5, ho5⟩, hask5⟩ := stage_undoomed' O 25 (e4 W O A) (fun x : X4 => gate x.ok (inG x.s)) T w5
    (e5 W O A) (e5_eq W O A) x5 x4 hx5 hx4 hg5 hb5 hnd5
  obtain ⟨⟨q6, hq6, hv6, ho6⟩, -⟩ := stage_undoomed' O 27 (e5 W O A) (fun x : X5 => gate x.ok (inS x.s)) T w6
    (dExp W O A) (dExp_eq W O A) z x5 hz hx5 hg6 hb6 hES
  -- The logs: the adversary's first, every stage's history inside the run's.
  have m10 := histL_prefix f11
  have m21 := histL_prefix f21
  have m32 := histL_prefix f31
  have m43 := histL_prefix f41
  have m54 := histL_prefix f51
  have m65 := histL_prefix f61
  have hH0 : histL (tableQueryLog (DA4 W A) T) = histL (tableQueryLog A T) ++ chainIns W (viewT T) p.1 := by
    unfold histL
    rw [h0l, List.filterMap_append, filterMap_getLeft?_map_inl]
  have hA0 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (DA4 W A) T) := fun y hy => by
    rw [hH0]; exact List.mem_append_left _ hy
  have hC0 : ∀ y ∈ chainIns W (viewT T) p.1, y ∈ histL (tableQueryLog (DA4 W A) T) := fun y hy => by
    rw [hH0]; exact List.mem_append_right _ hy
  have mL1 : ∀ y ∈ histL (tableQueryLog (e1 W O A) T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y (m54 y (m43 y (m32 y (m21 y hy))))
  have mL2 : ∀ y ∈ histL (tableQueryLog (e2 W O A) T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y (m54 y (m43 y (m32 y hy)))
  have mL3 : ∀ y ∈ histL (tableQueryLog (e3 W O A) T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y (m54 y (m43 y hy))
  have mL4 : ∀ y ∈ histL (tableQueryLog (e4 W O A) T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y (m54 y hy)
  have mL5 : ∀ y ∈ histL (tableQueryLog (e5 W O A) T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y hy
  have mA1 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (e1 W O A) T) :=
    fun y hy => m10 y (hA0 y hy)
  have mA2 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (e2 W O A) T) :=
    fun y hy => m21 y (mA1 y hy)
  have mA3 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (e3 W O A) T) :=
    fun y hy => m32 y (mA2 y hy)
  have mA4 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (e4 W O A) T) :=
    fun y hy => m43 y (mA3 y hy)
  have mA5 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (e5 W O A) T) :=
    fun y hy => m54 y (mA4 y hy)
  have mA6 : ∀ y ∈ histL (tableQueryLog A T), y ∈ histL (tableQueryLog (dExp W O A) T) :=
    fun y hy => m65 y (mA5 y hy)
  generalize hLA : histL (tableQueryLog A T) = LA at *
  generalize hL : histL (tableQueryLog (dExp W O A) T) = L at *
  -- The run's queries: the adversary's first.
  have hLk : ∃ rest, (tableQueryLog (dExp W O A) T).map Sigma.fst =
      (tableQueryLog A T).map Sigma.fst ++ rest := by
    refine ⟨?_, ?_⟩
    swap
    · rw [f61, f51, f41, f31, f21, f11]
      simp only [List.map_append, h0l, List.append_assoc]
      exact rfl
  obtain ⟨restk, hLk⟩ := hLk
  have hLsplit : L = LA ++ restk.filterMap Sum.getLeft? := by
    rw [← hL, ← hLA]
    unfold histL
    rw [hLk, List.filterMap_append]
  -- No bad fresh query, from here on.
  by_contra hnb
  have hk : ¬ FreshBad (kcBad4P W M.KP) T ∅ ((tableQueryLog (dExp W O A) T).map Sigma.fst) := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ _ h)
  have hr : ¬ FreshBad (rootBad4 A) T ∅ ((tableQueryLog (dExp W O A) T).map Sigma.fst) := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ _ h)
  have hl : ¬ FreshBad (listBad4P W M.KP) (viewT T) ∅ L := fun h =>
    hk (freshBad_kc4P W M.KP T ∅ _ (by rw [viewH_empty]; rw [← hL] at h; exact h))
  have hord := refers4_beforeP W M.KP hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := fun y hy z hz h =>
    injOn_of_not_freshBad4P W M.KP hl y (List.mem_toFinset.mp hy) z (List.mem_toFinset.mp hz) h
  have hAL : ∀ y ∈ LA, y ∈ L := mA6
  have hinjA : Set.InjOn (viewT T) ↑LA.toFinset :=
    hinj.mono fun y hy => List.mem_toFinset.mpr (hAL y (List.mem_toFinset.mp hy))
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ p.1.roots → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ (tableQueryLog (dExp W O A) T).map Sigma.fst := by
      rw [← hL] at hw; exact mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ (tableQueryLog A T).map Sigma.fst := fun h =>
      hwA (by rw [← hLA]; exact mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBad4 A) T ∅ _ hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, by rw [hp]; exact hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's words.
  have hstab : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ p.1.roots, ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr (hroot w (hHL w (List.mem_toFinset.mp hw)) (by rw [hwr]; exact hr')))
      (fun y hy w hw h => ?_) ht ℓ
    have hyA := List.mem_toFinset.mp hy
    have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y (hAL y hyA) (Or.inl h)
    rw [hLsplit, before_append_of_mem LA _ hyA] at hb
    exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  have toL : ∀ (n : ℕ) (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ p.1.roots,
        Candidates n logInvRate (code₀ n logInvRate).thr
            (Rom.extract (ansOf H.toFinset (viewT T)) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) =
          Candidates n logInvRate (code₀ n logInvRate).thr
            (Rom.extract (ansOf L.toFinset (viewT T)) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) :=
    fun n H h1 h2 r hr' => cands_transfer r
      (hinj.mono fun y hy => List.mem_toFinset.mpr (h2 y (List.mem_toFinset.mp hy))) hinj
      (by rw [hstab H h1 h2 r hr', hstab L hAL (fun y hy => hy) r hr'])
  have toA : ∀ (n : ℕ) (r : Bytes32), r ∈ p.1.roots →
        Candidates n logInvRate (code₀ n logInvRate).thr
            (Rom.extract (ansOf L.toFinset (viewT T)) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) =
          Candidates n logInvRate (code₀ n logInvRate).thr
            (Rom.extract (ansOf LA.toFinset (viewT T)) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)) :=
    fun n r hr' => (toL n LA (fun y hy => hy) hAL r hr').symm
  have rW : p.1.rW ∈ p.1.roots := by simp [RootProof4.roots]
  have rH : p.1.rH ∈ p.1.roots := by simp [RootProof4.roots]
  have rQ : p.1.rQ ∈ p.1.roots := by simp [RootProof4.roots]
  have rG : p.1.rG ∈ p.1.roots := by simp [RootProof4.roots]
  -- The candidates, read off the run's history.
  rw [r1, haπ, toL 25 _ mA1 mL1 _ rW] at hq1
  rw [r3, haπ, toL 27 _ mA3 mL3 _ rH] at hq3
  rw [r4, haπ, toL 28 _ mA4 mL4 _ rQ] at hq4
  rw [r5, haπ, toL 25 _ mA5 mL5 _ rG] at hq5
  rw [r6, haπ, toL 27 _ mA6 (fun y hy => hy) _ rH] at hq6
  -- The wiring opening's candidate is the setup's table.
  have hir : a.π.ir = r0 := by rw [haπ, hsir]
  rw [r2, hir] at hq2
  have hsetup : ∀ x, Sum.inl x ∈ lw0.map Sigma.fst →
        x ∈ (histL (tableQueryLog (e2 W O A) T)).toFinset := by
    intro x hx
    refine List.mem_toFinset.mpr (mA2 x ?_)
    rw [← hLA]
    refine mem_filterMap_getLeft?.mpr ?_
    rw [hsl, List.map_append]
    exact List.mem_append_left _ hx
  have hinj2 : Set.InjOn (viewT T) ↑(histL (tableQueryLog (e2 W O A) T)).toFinset :=
    hinj.mono fun y hy => List.mem_toFinset.mpr (mL2 y (List.mem_toFinset.mp hy))
  rw [candidates_congr (fun v hv => hext _ hsetup hinj2 v hv)] at hq2
  have hq20 : q2 = q₀ := candidates_honest adm24 (honest_stackWord 24 logInvRate q₀) hq2
  -- `H`'s two candidates are one: the binding.
  have hzT : ∀ j : Fin 27, oodInput 27 (ofB p.1.rH) j ∈ L.toFinset := fun j =>
    List.mem_toFinset.mpr (mL3 _ (by have := hask3 j; rwa [r3, haπ] at this))
  have hcache : (fun x => cacheOfTr ((tableQueryLog (dExp W O A) T).filterMap inlEntry) (.inl x)) =
      ansOf L.toFinset (viewT T) := by
    rw [← hL]
    exact cacheOfTr_eq_ansOf T _ (tableQueryLog_snd_dep T (dExp W O A))
  have hsep : SepAt (rootList (n := 27) (ansOf L.toFinset (viewT T)) (ofB p.1.rH))
      (oodPointWith (fun x => T (.inl x)) 27 (ofB p.1.rH)) := by
    by_contra hns
    apply hEB
    unfold EB BindBadC
    rw [f64, hcache]
    exact ⟨_, _, oodPointOf_ansOf hzT, hns⟩
  rw [r3, o3, haπ] at ho3
  rw [r6, o6, haπ] at ho6
  have h36 : q3 = q6 := hsep q3 hq3 q6 hq6 (by rw [ho3, ho6])
  -- The claims, as F1's.
  have hcW := M.witness a cl6 q1 hcl l1 (by rw [← p1, ← v1]; exact hv1)
  have hσc := M.wiring a cl6 hcl l2 (by rw [← p2, ← v2, ← hq20]; exact hv2)
  have hchk := M.check a cl6 hcl
  have hQc := M.quotient a cl6 q3 q4 q5 hcl l3 l6 l4 l5 (by rw [← p3, ← v3]; exact hv3)
    (by rw [← p6, ← v6, h36]; exact hv6) (by rw [← p4, ← v4]; exact hv4) (by rw [← p5, ← v5]; exact hv5)
  simp only [h0e] at hcW hσc hchk hQc
  have hacc : P.Accepts (W.decode p.1.stmt) (M.readW q1).1 (M.K.asm q3 q4 q5).1 (chalsOf W (viewT T) p.1).α
      (chalsOf W (viewT T) p.1).β (chalsOf W (viewT T) p.1).γ (chalsOf W (viewT T) p.1).t p.1.v.1 p.1.v.2
      (chalsOf W (viewT T) p.1).ρ :=
    (Compose.accepts_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨hcW, hσc, hchk, hQc⟩
  -- The witness candidate is one the extractor reads off the adversary's log.
  have hB2 := hB.2
  rw [hs6, hatA, haπ] at hB2
  have hgA : M.readW q1 ∈ adversaryExtractor4 M.cW ((tableQueryLog A T).filterMap inlEntry) p.1 := by
    have htrH : histOfTr ((tableQueryLog A T).filterMap inlEntry) = LA.toFinset := by
      simp only [histOfTr, map_fst_filterMap_inlEntry]
      rw [← hLA]
      rfl
    have htrT : ∀ d ∈ histOfTr ((tableQueryLog A T).filterMap inlEntry),
        tableOfTr ((tableQueryLog A T).filterMap inlEntry) d = viewT T d :=
      tableOfTr_inlEntry T _ fun q hq => tableQueryLog_snd_dep T _ _ hq
    rw [adversaryExtractor4_eq, (M.cW.commit).congr _ _ (viewT T) p.1.rW htrT, htrH]
    exact (mem_cands_colCode adm25 M.readW (H := LA.toFinset) hinjA p.1.rW _).mpr
      ⟨q1, by rw [← toA 25 _ rW]; exact hq1, rfl⟩
  have hsat := hB2 _ hgA
  -- The other three roots' lists are separated at their points: the binding.
  have hzW : ∀ j : Fin 25, oodInput 25 (ofB p.1.rW) j ∈ L.toFinset := fun j =>
    List.mem_toFinset.mpr (mL1 _ (by have := hask1 j; rwa [r1, haπ] at this))
  have hzQ : ∀ j : Fin 28, oodInput 28 (ofB p.1.rQ) j ∈ L.toFinset := fun j =>
    List.mem_toFinset.mpr (mL4 _ (by have := hask4 j; rwa [r4, haπ] at this))
  have hzG : ∀ j : Fin 25, oodInput 25 (ofB p.1.rG) j ∈ L.toFinset := fun j =>
    List.mem_toFinset.mpr (mL5 _ (by have := hask5 j; rwa [r5, haπ] at this))
  have hsepW : SepAt (rootList (n := 25) (ansOf L.toFinset (viewT T)) (ofB p.1.rW))
      (oodPointWith (fun x => T (.inl x)) 25 (ofB p.1.rW)) := by
    by_contra hns
    apply hEB25
    unfold EBn BindBadC
    rw [f64, hcache]
    exact ⟨_, _, oodPointOf_ansOf hzW, hns⟩
  have hsepQ : SepAt (rootList (n := 28) (ansOf L.toFinset (viewT T)) (ofB p.1.rQ))
      (oodPointWith (fun x => T (.inl x)) 28 (ofB p.1.rQ)) := by
    by_contra hns
    apply hEB28
    unfold EBn BindBadC
    rw [f64, hcache]
    exact ⟨_, _, oodPointOf_ansOf hzQ, hns⟩
  have hsepG : SepAt (rootList (n := 25) (ansOf L.toFinset (viewT T)) (ofB p.1.rG))
      (oodPointWith (fun x => T (.inl x)) 25 (ofB p.1.rG)) := by
    by_contra hns
    apply hEB25
    unfold EBn BindBadC
    rw [f64, hcache]
    exact ⟨_, _, oodPointOf_ansOf hzG, hns⟩
  -- The candidates, pinned by the answers the chain absorbed, each its root's only one.
  rw [r1, o1, haπ] at ho1
  rw [r4, o4, haπ] at ho4
  rw [r5, o5, haπ] at ho5
  have hWm : M.KP.pW.Mem L.toFinset (viewT T) p.1.rW p.1.oW q1 := pin_mem adm25 hinj _ _ q1 hq1 ho1
  have hHm : M.KP.pH.Mem L.toFinset (viewT T) p.1.rH p.1.oH q3 := pin_mem adm27 hinj _ _ q3 hq3 ho3
  have hQm : M.KP.pQ.Mem L.toFinset (viewT T) p.1.rQ p.1.oQ q4 := pin_mem adm28 hinj _ _ q4 hq4 ho4
  have hGm : M.KP.pG.Mem L.toFinset (viewT T) p.1.rG p.1.oG q5 := pin_mem adm25 hinj _ _ q5 hq5 ho5
  have hW1 : M.KP.pW.One L.toFinset (viewT T) p.1.rW p.1.oW := pin_one adm25 hinj _ _ hsepW
  have hH1 : M.KP.pH.One L.toFinset (viewT T) p.1.rH p.1.oH := pin_one adm27 hinj _ _ hsep
  have hQ1 : M.KP.pQ.One L.toFinset (viewT T) p.1.rQ p.1.oQ := pin_one adm28 hinj _ _ hsepQ
  have hG1 : M.KP.pG.One L.toFinset (viewT T) p.1.rG p.1.oG := pin_one adm25 hinj _ _ hsepG
  have hmem : ∀ y ∈ chainIns W (viewT T) p.1, y ∈ L := fun y hy => mL1 y (m10 y (hC0 y hy))
  exact hl (trace_core4P W M.KP L (viewT T) p.1 q1 q3 q4 q5 hmem hWm hW1 hHm hH1 hQm hQ1 hGm hG1 hacc hsat)

/-- **The trace of the deployed run**: on every table of both oracles, a run that breaks knowledge soundness
while none of the six openings is doomed at its end and `H`'s list is separated at its out-of-domain point asks a
bad fresh query. -/
theorem trace_dExp (O : OpenSpec) (M : ClaimsMatch W q₀)
    (A₀ : Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (T : KTable)
    (hev : BreaksD W M.cW (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EW O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ Eσ O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EH O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EQ O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EG O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ ES O (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EB (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EBn 25 (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀))) ∧
      ¬ EBn 28 (evalWithAnswerFn (QueryImpl.ofFn T) (dExp W O (withSetup4 (setupPcs q₀) A₀)))) :
    FreshBad (advBad4P W M.KP (withSetup4 (setupPcs q₀) A₀)) T ∅
      ((tableQueryLog (dExp W O (withSetup4 (setupPcs q₀) A₀)) T).map Sigma.fst) := by
  obtain ⟨hsl, hsir⟩ := withSetup4_run (setupPcs q₀) A₀ T
  obtain ⟨⟨lws, hws⟩, hws_eval⟩ := setupPcs_run q₀ T
  exact trace_dExpA W O M (withSetup4 (setupPcs q₀) A₀) T
    (evalWithAnswerFn (QueryImpl.ofFn T) (wiringSetup (rootHeight 24 logInvRate)
      (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀)))
    (tableQueryLog (wiringSetup (rootHeight 24 logInvRate) (LeanVM.Protocol.Whir.Complete.stackWord 24 q₀)) T)
    ⟨_, by rw [hsl, hws, List.append_assoc]⟩ (hsir.trans hws_eval)
    (fun H h1 h2 v hv => extract_wiringSetup _ _ _ (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀)
      T H h1 h2 v hv) hev

end SoundPcs
