-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsOps.lean` and `FsProof.lean`'s facts (`hok_uni`, `hcov_uni`, `hS_uni`, `maxErrK_uni`) to
-- π2's openings on the EIP's PCS claims, after `formal/UniKeccakSound/UniKeccakSound/Fs/ProofK.lean` (`hok_uniK`,
-- `hU_uniK`: the openings charged once through `WhirBridge.Pcs.pcs_union_sound`).
import RecCompose.FsDefs
import RecCompose.Tables
import Bridge.Verifier

/-!
# π2's openings: what the framework needs of them

* **the run's points** have their stacks' variables (`p2Out_witnessPoint_length`, …: `24`, `25`, `28`);
* **a PCS claim's point claim on a stack is `ClaimOn`** (`colEval_iff_claimOn`): the stack's polynomial
  (`WhirBridge.Pcs.colEval`, `eq` of the point and a word's bits) is its multilinear extension (`UniSound.mleStk`);
* **the openings' `OKP`** (`okp_W` for π1's three declared claims and `W`'s as one, `okp_Q`: the decoders list the
  candidates' stacks, a stack satisfying the opening's claims is good; the setup's, `okp_setupOp`); `hcov`, `hfit`, and
  **`hS`** (the setup's claim on its table, from its opening);
* **π2's four PCS openings once** (`prEvent_doomH_le`, after any openings `P`, here π1's three declared claims, whose
  queries are counted): each opening's statement is one of `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`'s union
  over version 1's sizes `2^23 ..= 2^28` at `εExact` (`UniKeccakSound.pcsKShapes`), the out-of-domain point read off
  Keccak-256 at `W`'s and `Q`'s sizes (`24`, `28`) and `oodPoint` at the setup's; an opening's doom (`PcsOp.DoomedH`)
  its PCS claim's two claims, the point read off the final cache (`ptAt`); for any list of `PcsOp`s, at most
  `bndU (QX + Σ QO) = (N + 10122) (εExact + 5 (N + 10122) / 2^256)` for a run before the openings of `QX` queries
  (`N = QX + Σ QO`, all the openings' queries);
* the decoders' lists (`L_W = 9952`, `L_Q = 3564`) and `maxErrK` (`maxErrK_p2`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

-- `Layers.lean`'s instance of `SampleableType E` (the one `Pi2FsLayer`'s protocols are at), not `Completeness`'s.
attribute [local instance high] LeanVM.Protocol.instSampleableTypeE

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge Finset
open OracleSpec OracleComp
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

theorem cc_logN : cc.logN = 24 := rfl

theorem cc_logRow : cc.logRow = 4 := rfl

/-! ## The run's points -/

theorem padded_length {F : Type} [Field F] (p : List F) (n : ℕ) : (padded p n).length = n := by
  simp [padded]

theorem p2Out_witnessPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).witnessPoint.length = 24 := by
  unfold p2Out
  rw [run_witnessPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_setupPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).setupPoint.length = 25 := by
  unfold p2Out
  rw [run_setupPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_quotientPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).quotientPoint.length = 28 := by
  unfold p2Out
  rw [run_quotientPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_pushesPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).pushesPoint.length = 28 := by
  unfold p2Out
  rw [run_pushesPoint, padded_length, spec_core_logN, cc_logN]
  rfl


/-! ## A PCS claim's point claim is `ClaimOn` -/

/-- **A stack's polynomial at a point of its variables is its multilinear extension** (`UniSound.mleStk`, `ClaimOn`'s),
for a stack whose words below `2^n` are the column's. -/
theorem colEval_eq_mle {n : ℕ} (q : Column n) (s : Stk) (hs : ∀ i < 2 ^ n, q.values.getD i 0 = s i)
    (pt : List E) (hp : pt.length = n) : Pcs.colEval q pt = UniSound.mleStk s n pt := by
  unfold Pcs.colEval UniSound.mleStk
  refine Finset.sum_congr rfl fun x _ => ?_
  have he := UniSound.eqEval_boolPoint x.val pt
  rw [hp] at he
  rw [LeanVM.Protocol.Whir.Complete.eqEval_comm, he, hs x.val x.isLt]

theorem colEval_iff_claimOn {n : ℕ} (q : Column n) (s : Stk) (hs : ∀ i < 2 ^ n, q.values.getD i 0 = s i)
    (pt : List E) (v : E) (hp : pt.length = n) : Pcs.colEval q pt = v ↔ ClaimOn n s (pt, v) := by
  rw [colEval_eq_mle q s hs pt hp]
  rfl

/-- A round's candidate read back is the column's words (`rdP`, the plain layout's table, `2^23 ..= 2^28` words). -/
theorem rdP_getD (n : ℕ) (h1 : 23 ≤ n) (h2 : n ≤ 28) (q : Column n) (i : ℕ) (hi : i < 2 ^ n) :
    q.values.getD i 0 = rdP n q i := by
  unfold rdP UniSound.rdTab
  have hi' : i < 2 ^ (UniSound.plainL n).vars := hi
  rw [dite_eq_left hi']
  simp only [tabOf, Vector.getElem_ofFn]
  exact (UniKeccakSound.plainL_tableK n h1 h2 q i hi).symm

/-- A column of an array's words is the array's words below `2^n`. -/
theorem colOf_getD (a : Array K) (n i : ℕ) (hi : i < 2 ^ n) :
    (UniSound.colOf a n).values.getD i 0 = a.getD i 0 := by
  simp [UniSound.colOf, Vector.getD, hi]

/-! ## The openings' `OKP` -/

section Facts

variable (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1)


theorem p2Tc_zero : p2Tc 0 = tableCode (UniSound.plainL 24) logInvRate (shK 24 (by norm_num) (by norm_num)).adm
    UniSound.rdTab := by
  unfold p2Tc
  rw [ite_eq_left rfl]

theorem p2Tc_one : p2Tc 1 = tableCode (UniSound.plainL 28) logInvRate (shK 28 (by norm_num) (by norm_num)).adm
    UniSound.rdTab := by
  unfold p2Tc
  rw [ite_eq_right (by decide)]

/-- **`W`'s opening's `OKP`** (π1's three declared claims and `W`'s as one, `wOpM`): its decoder lists the
candidates' stacks, and a stack its claim (`W`'s) holds of satisfies `W`'s claim (`ClaimOn`). -/
theorem okp_W : GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) wOpM := by
  refine gop_okp_tableCode (UniSound.plainL 24) logInvRate (shK 24 (by norm_num) (by norm_num)).adm _ _ _
    wOpM.queries wOpM.duplex 0 UniSound.rdTab p2Tc p2Tc_zero
    p2Good (fun π ch q h => ?_) _ _ _
  obtain ⟨ood, pt, v, hcl, hl, hv⟩ := h
  simp only [wPcs, wCl, Option.some.injEq, Prod.mk.injEq] at hcl
  obtain ⟨-, rfl, rfl⟩ := hcl
  rw [p2Good, ite_eq_left rfl]
  exact ⟨_, rfl, (colEval_iff_claimOn q _ (rdP_getD 24 (by norm_num) (by norm_num) q) _ _ hl).1 hv⟩

theorem claim_of_holdsQ (o : PcsOp) (ho : o.n = 28) (pt : List E) (v : E) {π : P2Pf} {ch : List (List E)}
    {q : Column 28} (hcl : ∀ ood pt' v', o.cl π ch = some (ood, pt', v') → pt' = pt ∧ v' = v)
    (h : o.holds π ch (cast (by rw [ho]) q)) : ClaimOn 28 (rdP 28 q) (pt, v) := by
  obtain ⟨n, lo, hi, cl, prf, tgt⟩ := o
  simp only at ho
  subst ho
  obtain ⟨ood, pt', v', hc, hl, hv⟩ := h
  obtain ⟨rfl, rfl⟩ := hcl _ _ _ hc
  exact (colEval_iff_claimOn q _ (rdP_getD 28 (by norm_num) (by norm_num) q) _ _ hl).1 hv

/-- **`Q`'s opening's `OKP`** (its two claims as one opening): its decoder lists the candidates' stacks, and a
stack its two claims hold of satisfies `Q`'s two (`ClaimOn`). -/
theorem okp_Q : GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) qOp := by
  refine gop_okp_tableCode (UniSound.plainL 28) logInvRate (shK 28 (by norm_num) (by norm_num)).adm _ _ _
    qOp.queries qOp.duplex 1 UniSound.rdTab p2Tc p2Tc_one p2Good (fun π ch q h => ?_) _ _ _
  obtain ⟨h1, h2⟩ := h
  rw [p2Good, ite_eq_right (by decide), ite_eq_left rfl]
  refine ⟨_, rfl, claim_of_holdsQ qIdOp rfl _ _ (fun _ _ _ hc => ?_) h1,
    claim_of_holdsQ qPushOp rfl _ _ (fun _ _ _ hc => ?_) h2⟩
  · simp only [qIdOp, qIdCl, Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.1.symm, hc.2.2.symm⟩
  · simp only [qPushOp, qPushCl, Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.1.symm, hc.2.2.symm⟩

/-- **The other openings carry no stack** (their stacks are not of `2^25` words). -/
theorem p2StkNone (o : GOp P2Pf E Stk) (h : o.μ ≠ 25) : p2Stk D o = none := by
  unfold p2Stk
  split
  · next h' => exact absurd h' h
  · rfl

/-- **Every round with a root is opened**: `W`'s and `Q`'s. -/
theorem hcov_p2 : ∀ i < pi2Spec.K.rounds.length, (pi2Spec.K.spec i).root →
    ∃ o ∈ p2Ops, ∃ rd, o.tgt = .round i rd := by
  intro i hi hr
  have hi3 : i < 3 := hi
  interval_cases i
  · exact ⟨wOpM, by simp [p2Ops], rdP 24, rfl⟩
  · exact ⟨qOp, by simp [p2Ops], rdP 28, rfl⟩
  · exact absurd hr (by decide)

/-- **The stream's messages fit the rounds.** -/
theorem hfit_p2 (π : P2Pf) : FitsAll pi2Spec.K.rounds (p2View π).2 :=
  UniSound.fitsAll_msgsAt _ _ _

/-- **The setup's claim on its table, from its opening's** (`GOp.SetupHoldsP` of the setup's opening, its stack the
setup's table at the proof's commitments). -/
theorem hS_p2 (π : P2Pf) (ch : List (List E))
    (h : ∀ o ∈ p2Ops, GOp.SetupHoldsP (p2Stk D) o π ch) : p2GoodS D π ch := by
  have hm : sPcs.gop ∈ p2Ops := by
    simp [p2Ops]
  have h5 := h _ hm
  unfold GOp.SetupHoldsP at h5
  obtain ⟨ood, pt, v, hcl, hl, hv⟩ := h5 (fun π => setupCol D π.roots.pi1) rfl
  simp only [sPcs, sCl, Option.some.injEq, Prod.mk.injEq] at hcl
  obtain ⟨-, rfl, rfl⟩ := hcl
  exact (colEval_iff_claimOn _ _ (fun i hi => colOf_getD _ 25 i hi) _ _ hl).1 hv

/-! ## The lists, `maxErrK` -/

theorem p2Tc_bound_zero : (p2Tc 0).commit.bound = 9952 := by
  rw [TableCode.commit_bound, p2Tc_zero]
  exact listHi_large 24 le_rfl (by decide)

theorem p2Tc_bound_one : (p2Tc 1).commit.bound = 3564 := by
  rw [TableCode.commit_bound, p2Tc_one]
  exact listHi_large 28 (by decide) le_rfl

/-- **The lists of the roots before round `j`** (`facL`): `L_W`, then `L_W L_Q`. -/
theorem facL_p2 : ∀ j < 3, facL (fun i => (p2Tc i).commit) 0 (pi2Spec.K.rounds.take (j + 1)) = pi2Fac j := by
  intro j hj
  interval_cases j
  · rw [show pi2Spec.K.rounds.take (0 + 1) = [⟨true, 1, 2⟩] from rfl]
    simp only [facL, ite_true, p2Tc_bound_zero, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (1 + 1) = [⟨true, 1, 2⟩, ⟨true, 1, 0⟩] from rfl]
    simp only [facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (2 + 1) = RecPiop.pi2Rounds 4 from rfl]
    simp only [RecPiop.pi2Rounds, facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one,
      Bool.false_eq_true, ite_false]
    rfl

/-- **The rounds' errors times their lists** are at most `e` when each round's error times `pi2Fac` is. -/
theorem maxErrK_p2 (R : Compose.Piop pi2Spec.K Stk) (e : ℝ≥0∞)
    (herr : ∀ j < 3, (pi2Fac j : ℝ≥0∞) * R.err j ≤ e) :
    maxErrK pi2Spec.K (fun i => (p2Tc i).commit) R ≤ e := by
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  have hj3 : j < 3 := Finset.mem_range.mp hj
  rw [facL_p2 j hj3]
  exact herr j hj3

end Facts

/-! ## The openings once: the PCS union, the point read off Keccak-256 at `W`'s and `Q`'s sizes -/

section Union

/-- **The out-of-domain point read off Keccak-256's answers `H`** (`WhirBridge.Pcs.zOfCache`'s: the default answer at a
coordinate not asked). -/
def zOfH (H : Bytes → Option Digest) (n : ℕ) (r : Digest) : Vector E n :=
  Vector.ofFn fun j ↦ Pcs.elemOf ((digestBytes ((H (Pcs.oodInput n r j)).getD default)).drop 8)

theorem zOfCache_eq (c : KeccakCalls.QueryCache) (n : ℕ) (r : Digest) :
    Pcs.zOfCache c n r = zOfH (fun x ↦ c (.inl x)) n r := rfl

/-- **An opening's out-of-domain point**: read off `H` at `W`'s and `Q`'s sizes (`RecStatement.oodRead`), `oodPoint` at the others. -/
def ptAt (n : ℕ) (H : Bytes → Option Digest) (r : Digest) : Vector E n :=
  if RecStatement.oodRead n then zOfH H n r else Pcs.oodPoint n r

/-- **An opening is doomed**, against Keccak-256's answers `H`: every candidate of the word under its root violates its
PCS claim's out-of-domain claim (at `ptAt`) or its point claim. -/
def PcsOp.DoomedH (o : PcsOp) (π : P2Pf) (ch : List (List E)) (H : Bytes → Option Digest) : Prop :=
  ∀ q ∈ Candidates o.n logInvRate (code₀ o.n logInvRate).thr
      (Rom.extract H (ofB (o.rootB π)) (rootHeight o.n logInvRate) (2 ^ laneFold)),
    ∀ ood pt v, o.cl π ch = some (ood, pt, v) → pt.length = o.n →
      Pcs.colEval q (ptAt o.n H (ofB (o.rootB π))).toList ≠ ood ∨ Pcs.colEval q pt ≠ v

/-- The root a `PcsOp`'s `GOp` reads is its `rootB`. -/
theorem PcsOp.root_gop (o : PcsOp) (π : P2Pf) : GOp.root p2View o.gop π = o.rootB π := by
  obtain ⟨n, lo, hi, cl, prf, tgt⟩ := o
  cases tgt <;> rfl

/-- **A single opening doomed** (`GDoomed`: its point claim fails on every candidate) **is doomed with its point.** -/
theorem PcsOp.doomedH_of_gDoomed (o : PcsOp) (π : P2Pf) (ch : List (List E)) (c : KeccakCalls.QueryCache)
    (hd : GDoomed p2View o.gop π ch c) : o.DoomedH π ch (fun x ↦ c (.inl x)) := by
  intro q hq ood pt v hc hl
  right
  intro hv
  refine hd q ?_ ⟨ood, pt, v, hc, hl, hv⟩
  show q ∈ Candidates o.n logInvRate (code₀ o.n logInvRate).thr
    (Rom.extract (fun x ↦ c (.inl x)) (ofB (GOp.root p2View o.gop π)) (rootHeight o.n logInvRate) (2 ^ laneFold))
  rw [PcsOp.root_gop]
  exact hq

/-- **An opening's statement in the PCS union**: its size's index, its PCS claim (the root it reads, the
out-of-domain answer, the point and value), its opening proof; a dummy claim where it has no claim or its point has not
its stack's variables (the opening rejects there). -/
noncomputable def PcsOp.stmt (o : PcsOp) (π : P2Pf) (ch : List (List E)) : Pcs.PSt UniKeccakSound.pcsKShapes × Proof :=
  match o.cl π ch with
  | some (ood, pt, v) =>
    if h : pt.length = o.n then
      (⟨UniKeccakSound.pcsIdxK o.n, ⟨ofB (o.rootB π), ood, pt, v,
        h.trans (UniKeccakSound.pcsIdxK_n _ o.lo o.hi).symm⟩⟩, o.prf π)
    else (⟨UniKeccakSound.pcsIdxK 23, Pcs.dummy _⟩, o.prf π)
  | none => (⟨UniKeccakSound.pcsIdxK 23, Pcs.dummy _⟩, o.prf π)

/-- An opening has a claim of its stack's variables. -/
def PcsOp.Ok (o : PcsOp) (π : P2Pf) (ch : List (List E)) : Prop :=
  ∃ ood pt v, o.cl π ch = some (ood, pt, v) ∧ pt.length = o.n

theorem pcsVerifierO_congrK {n n' : ℕ} (h : n' = n) (r : Digest) (ood : E) (pt : List E) (v : E)
    (h1 : pt.length = n) (h2 : pt.length = n') (p : Proof) :
    Pcs.pcsVerifierO ((⟨r, ood, pt, v, h2⟩ : Pcs.Claim1 n'), p) = Pcs.pcsVerifierO ((⟨r, ood, pt, v, h1⟩ : Pcs.Claim1 n), p) := by
  subst h
  rfl

theorem pcsDoomedO_congrK {n n' : ℕ} (h : n' = n) (r : Digest) (ood : E) (pt : List E) (v : E)
    (h1 : pt.length = n) (h2 : pt.length = n') (p : Proof) (c : KeccakCalls.QueryCache) :
    Pcs.PcsDoomedO ((⟨r, ood, pt, v, h2⟩ : Pcs.Claim1 n'), p) c ↔
      Pcs.PcsDoomedO ((⟨r, ood, pt, v, h1⟩ : Pcs.Claim1 n), p) c := by
  subst h
  rfl

theorem PcsOp.stmt_ok (o : PcsOp) (π : P2Pf) (ch : List (List E)) {ood : E} {pt : List E} {v : E}
    (hc : o.cl π ch = some (ood, pt, v)) (hl : pt.length = o.n) :
    o.stmt π ch = (⟨UniKeccakSound.pcsIdxK o.n, ⟨ofB (o.rootB π), ood, pt, v,
      hl.trans (UniKeccakSound.pcsIdxK_n _ o.lo o.hi).symm⟩⟩, o.prf π) := by
  unfold PcsOp.stmt
  rw [hc]
  dsimp only
  rw [dite_eq_left hl]

theorem oodRead_idx (o : PcsOp) :
    RecStatement.oodRead (UniKeccakSound.pcsKShapes.shs.get (UniKeccakSound.pcsIdxK o.n)).n =
      RecStatement.oodRead o.n := by
  rw [UniKeccakSound.pcsIdxK_n _ o.lo o.hi]

/-- **An opening's run is the union's verifier on its statement**, where it has a claim of its stack's variables: the
point read off Keccak-256 at `W`'s and `Q`'s sizes, `oodPoint` at the others. -/
theorem PcsOp.run_ok (o : PcsOp) (π : P2Pf) (ch : List (List E)) (hok : o.Ok π ch) :
    GOp.run p2View o.gop π ch =
      Pcs.UnionO.pUVerO UniKeccakSound.pcsKShapes RecStatement.oodRead Pcs.oodPoint (o.stmt π ch) := by
  obtain ⟨ood, pt, v, hc, hl⟩ := hok
  unfold GOp.run
  rw [PcsOp.root_gop]
  show o.ver _ π ch = _
  rw [PcsOp.stmt_ok o π ch hc hl]
  unfold PcsOp.ver
  rw [hc]
  unfold Pcs.UnionO.pUVerO
  dsimp only
  have hS := oodRead_idx o
  by_cases hs : RecStatement.oodRead o.n = true
  · rw [ite_eq_left hs, ite_eq_left (hS.trans hs)]
    unfold pcsOpenCO
    rw [dite_eq_left hl]
    exact (pcsVerifierO_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _).symm
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hS.symm.trans h))]
    unfold UniKeccakSound.pcsOpenC
    rw [dite_eq_left hl]
    exact (UniKeccakSound.pcsVerifier_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _).symm

/-- **An opening without a claim of its stack's variables rejects.** -/
theorem PcsOp.run_nok (o : PcsOp) (π : P2Pf) (ch : List (List E)) (hok : ¬ o.Ok π ch) :
    GOp.run p2View o.gop π ch = pure false := by
  unfold GOp.run
  show o.ver _ π ch = _
  unfold PcsOp.ver
  rcases hc : o.cl π ch with _ | ⟨ood, pt, v⟩
  · rfl
  · dsimp only
    have hl : ¬ pt.length = o.n := fun hl => hok ⟨ood, pt, v, hc, hl⟩
    split
    · unfold pcsOpenCO
      rw [dite_eq_right hl]
    · unfold UniKeccakSound.pcsOpenC
      rw [dite_eq_right hl]

/-- **An opening's doom is the union's on its statement**, where it has a claim of its stack's variables. -/
theorem PcsOp.doomedH_imp (o : PcsOp) (π : P2Pf) (ch : List (List E)) (c : KeccakCalls.QueryCache)
    (hok : o.Ok π ch) (hd : o.DoomedH π ch (fun x ↦ c (.inl x))) :
    Pcs.UnionO.PUDoomedO UniKeccakSound.pcsKShapes RecStatement.oodRead Pcs.oodPoint (o.stmt π ch) c := by
  obtain ⟨ood, pt, v, hc, hl⟩ := hok
  rw [PcsOp.stmt_ok o π ch hc hl]
  unfold Pcs.UnionO.PUDoomedO
  dsimp only
  have hS := oodRead_idx o
  by_cases hs : RecStatement.oodRead o.n = true
  · rw [ite_eq_left (hS.trans hs)]
    refine (pcsDoomedO_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _ c).2 fun q hq => ?_
    have h := hd q hq ood pt v hc hl
    unfold ptAt at h
    rw [ite_eq_left hs] at h
    exact h
  · rw [ite_eq_right (fun h => hs (hS.symm.trans h))]
    refine (UniKeccakSound.pcsDoomed_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _ c).2
      fun q hq => ?_
    have h := hd q hq ood pt v hc hl
    unfold ptAt at h
    rw [ite_eq_right hs] at h
    exact h

/-- The union's bound at `QA` queries: `(QA + 10122) (εExact + 5 (QA + 10122) / 2^256)`. -/
noncomputable def bndU (QA : ℕ) : ℝ≥0∞ :=
  ((QA + 10122 : ℕ) : ℝ≥0∞) * (εExact + ((5 * (QA + 10122) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- Some opening of `L`, after `pre` others, accepts while doomed, against Keccak-256's answers `H`. -/
def DoomH (pre : ℕ) (L : List PcsOp) (z : OutK P2Pf E (List Bool) × Transcript) (H : Bytes → Option Digest) :
    Prop :=
  ∃ k, ∃ hk : k < L.length, z.1.1.2.2.getD (pre + k) false = true ∧ L[k].DoomedH z.1.1.1 z.1.1.2.1 H

open Classical in
/-- **The first opening doomed**, `0` if none. -/
noncomputable def firstH (pre : ℕ) (L : List PcsOp) (z : OutK P2Pf E (List Bool) × Transcript) : ℕ :=
  if h : DoomH pre L z (fun x ↦ cacheOfTr z.2 (.inl x)) then
    Nat.find (p := fun k => ∃ hk : k < L.length, z.1.1.2.2.getD (pre + k) false = true ∧
      L[k].DoomedH z.1.1.1 z.1.1.2.1 (fun x ↦ cacheOfTr z.2 (.inl x))) h
  else 0

theorem firstH_spec (pre : ℕ) (L : List PcsOp) (z : OutK P2Pf E (List Bool) × Transcript)
    (h : DoomH pre L z (fun x ↦ cacheOfTr z.2 (.inl x))) :
    ∃ hk : firstH pre L z < L.length, z.1.1.2.2.getD (pre + firstH pre L z) false = true ∧
      L[firstH pre L z].DoomedH z.1.1.1 z.1.1.2.1 (fun x ↦ cacheOfTr z.2 (.inl x)) := by
  classical
  unfold firstH
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem firstH_lt (pre : ℕ) (L : List PcsOp) (hne : L ≠ []) (z : OutK P2Pf E (List Bool) × Transcript) :
    firstH pre L z < L.length := by
  classical
  by_cases h : DoomH pre L z (fun x ↦ cacheOfTr z.2 (.inl x))
  · exact (firstH_spec pre L z h).1
  · unfold firstH
    rw [dite_eq_right h]
    exact List.length_pos_iff.mpr hne

/-- The union adversary's output: the first doomed opening's statement. -/
noncomputable def pickH (pre : ℕ) (L : List PcsOp) (hne : L ≠ []) (z : OutK P2Pf E (List Bool) × Transcript) :
    Pcs.PSt UniKeccakSound.pcsKShapes × Proof :=
  (L[firstH pre L z]'(firstH_lt pre L hne z)).stmt z.1.1.1 z.1.1.2.1

/-- **Any list of PCS claims' openings, after any openings `P`, charged once**
(`WhirBridge.Pcs.UnionO.pcs_union_sound_oracle` over `UniKeccakSound.pcsKShapes`, the point read off Keccak-256 at
`W`'s and `Q`'s sizes): for a run before the openings of `QX` queries, some opening of `L` accepts while doomed at the
run's end (its point read off the final cache) with probability at most `bndU (QX + Σ QO)`, the sum over all the
openings. -/
theorem prEvent_doomH_le (P : List (GOp P2Pf E Stk)) (L : List PcsOp) (X : OracleComp KeccakCalls (PreK P2Pf E))
    (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    Pr{let p ← (simulateQ randomOracle (expLG p2View X (P ++ L.map PcsOp.gop))).run ∅}[
        DoomH P.length L p.1 (fun x ↦ p.2 (.inl x))] ≤
      bndU (QX + ((P ++ L.map PcsOp.gop).map fun o => o.QO).sum) := by
  classical
  rcases eq_or_ne L [] with rfl | hne
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun p hp ↦ ?_) bot_le
    obtain ⟨k, hk, -⟩ := hp
    exact absurd hk (Nat.not_lt_zero _)
  have hU := Pcs.UnionO.pcs_union_sound_oracle UniKeccakSound.pcsKShapes RecStatement.oodRead Pcs.oodPoint
    (pickH P.length L hne <$> expLG p2View X (P ++ L.map PcsOp.gop)) _
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_expLG p2View X _ QX hX)) 10122
    UniKeccakSound.pcsKShapes_QO
  refine le_trans ?_ hU
  rw [romExperiment_map, prEvent_map, romExperiment_eq]
  conv_lhs => rw [← bind_pure ((simulateQ randomOracle (expLG p2View X (P ++ L.map PcsOp.gop))).run ∅)]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ ?_
  obtain ⟨hcons, hrep⟩ := expLG_replayF p2View X (P ++ L.map PcsOp.gop) p hp
  have hc : (fun x ↦ p.2 (.inl x)) = fun x ↦ cacheOfTr p.1.2 (.inl x) :=
    funext fun x ↦ (hcons x).trans (cacheOfTr_inl _ _).symm
  by_cases hd : DoomH P.length L p.1 (fun x ↦ p.2 (.inl x))
  · rw [hc] at hd
    obtain ⟨hk, hacc, hdoom⟩ := firstH_spec P.length L p.1 hd
    set k := firstH P.length L p.1 with hkdef
    have hk' : P.length + k < (P ++ L.map PcsOp.gop).length := by simp; omega
    have hrk := hrep (P.length + k) hk'
    have hget : (P ++ L.map PcsOp.gop)[P.length + k] = (L[k]).gop := by
      rw [List.getElem_append_right (by omega)]
      simp
    rw [hget] at hrk
    have hok : (L[k]).Ok p.1.1.1.1 p.1.1.1.2.1 := by
      by_contra hn
      rw [PcsOp.run_nok _ _ _ hn] at hrk
      have hmem : ((false, p.2) : Bool × KeccakCalls.QueryCache) ∈
          support (pure (p.1.1.1.2.2.getD (P.length + k) false, p.2) :
            ProbComp (Bool × KeccakCalls.QueryCache)) := by
        rw [← hrk]
        simp
      rw [mem_support_pure_iff] at hmem
      simp only [Prod.mk.injEq] at hmem
      rw [← hmem.1] at hacc
      exact Bool.false_ne_true hacc
    have hv : (simulateQ randomOracle (Pcs.UnionO.pUVerO UniKeccakSound.pcsKShapes RecStatement.oodRead Pcs.oodPoint
        (pickH P.length L hne p.1))).run p.2 = pure (true, p.2) := by
      show (simulateQ randomOracle (Pcs.UnionO.pUVerO UniKeccakSound.pcsKShapes RecStatement.oodRead Pcs.oodPoint
        ((L[k]).stmt p.1.1.1.1 p.1.1.1.2.1))).run p.2 = _
      rw [← PcsOp.run_ok _ _ _ hok, hrk, hacc]
    refine (prEvent_le_one _).trans (le_of_eq ?_)
    rw [hv, map_pure, prEvent_pure, ite_eq_left]
    refine ⟨rfl, ?_⟩
    refine PcsOp.doomedH_imp _ _ _ p.2 hok ?_
    rw [hc]
    exact hdoom
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [mem_support_pure_iff] at hr
    subst hr
    exact hd hev

end Union

/-! ## The openings' runs -/

/-- The openings' verdicts have their count. -/
theorem length_of_mem_gopsRun (π : P2Pf) (ch : List (List E)) :
    ∀ (L : List (GOp P2Pf E Stk)) (bs : List Bool), bs ∈ support (gopsRun p2View L π ch) → bs.length = L.length
  | [], bs, h => by
    simp only [gopsRun, support_pure, Set.mem_singleton_iff] at h
    subst h
    rfl
  | o :: L, bs, h => by
    simp only [gopsRun, mem_support_bind_iff, support_map, Set.mem_image] at h
    obtain ⟨b, -, bs', hbs', rfl⟩ := h
    simp [length_of_mem_gopsRun π ch L bs' hbs']

/-- The seven verdicts as the composition's three: π1's three and `W`'s and-ed, the setup's, `Q`'s two and-ed. -/
def mergeB (bs : List Bool) : List Bool :=
  [bs.getD 0 false && (bs.getD 1 false && (bs.getD 2 false && bs.getD 3 false)), bs.getD 4 false,
    bs.getD 5 false && bs.getD 6 false]

/-- **The composition's openings run the seven**, π1's three with `W`'s and `Q`'s two as one each. -/
theorem gopsRun_p2Ops (π : P2Pf) (ch : List (List E)) :
    gopsRun p2View p2Ops π ch = mergeB <$> gopsRun p2View p2Ops7 π ch := by
  simp only [p2Ops, p2Ops7, p2Pcs, List.map_cons, List.map_nil, List.cons_append, List.nil_append, gopsRun,
    map_bind, map_pure]
  simp only [GOp.run, wOpM, qOp, declOp, PcsOp.gop, bind_assoc, pure_bind]
  rfl

end RecCompose

/-- info: 'RecCompose.hS_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hS_p2

/-- info: 'RecCompose.maxErrK_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.maxErrK_p2

/-- info: 'RecCompose.prEvent_doomH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.prEvent_doomH_le
