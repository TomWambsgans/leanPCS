-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The certificate is `WhirBridge/LargeParams.lean`'s and
-- `WhirBridge/Exact.lean`'s (`chkQ_large`, `costLE_large`, `isTotalQueryBound_large`, `ExactShape.large`) at the
-- one shape they leave out, `2^23` words; the shapes' union is `WhirBridge/Union.lean`'s (`largeShapes`).
import WhirBridge.Union
import Compose.ListChainKDoom

/-!
# WHIR at `2^23` words, certified as `2^24 ..= 2^28`

The Keccak verifier's setup stack has `2^23` words at every measured Keccak shape (the bytecode's tuples
`2^(18 + 4)` and the memory's addresses `2^20`, `setupLayout`), one below `WhirBridge`'s window `2^24 ..= 2^28`
(`largeShapes`). Everything `WhirBridge` certifies there holds at `2^23` too, decided by kernel evaluation on the same
objects (the ladder, the certificates' `Nat` bounds, the cost of one run):

* **`ladder_23`**: the deployed ladder at `μ = 23`, rate `1/2` (`Whir.ladder`, `derive_config`) is `ladder23`: folds
  `6, 4, 4, 4` at rate exponents `1, 4, 7, 10`, queries `224, 56, 32, 23`, a residual of `5` variables;
* **`chkQ_23`**: mumbai's check of its certificates passes at **`εExact = 269 · 2^-137`** per group, the bound
  `largeShapes` carries (`whirEps_le_exact23`); level 0's list is `L₀ = 12514` (`listHi_23`), so the batching
  lead `(J − 1) L₀ / 2^192 ≤ 2^46 · 12514 / 2^192` is below `εExact` too (`eBatch_le_exact23`);
* **`queries23_eq`**: `opening::verify` makes at most `QO = 6499` queries at `2^23` words (`isTotalQueryBound_23`),
  below the uniform `10122`;
* **`plainShapeE23`** (an `ExactShape εExact`) and **`plainShape23`** (a `WhirShape`, F2's `opening_sound_q` at
  `QO = 6499`): the plain layout of `2^23` words;
* **`kShapes`**: `largeShapes ++ [plainShapeE23]`, the plain layouts of `2^23 ..= 2^28` words at `εExact`, their
  verifier prefixes distinct (`kShapes_nodup`, their `log_n` are), their query counts at most `10122`.

So the union family of `Compose.prEvent_doomF_le` covers the Keccak verifier's three openings at the per-group bound
`εExact` of `uniBound128`, unchanged.
-/

namespace UniKeccakSound

open WhirBridge LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom LeanVM.Protocol.Whir.Sound OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The ladder and its certificate -/

/-- The shape `(23, 1)` is admissible (`15 ≤ μ ≤ 28`). -/
theorem admissible_23 : Whir.Admissible 23 logInvRate := by
  decide +kernel

/-- **The ladder at `μ = 23`**, rate `1/2`: `⟨fold, logInvRate, queries⟩` per level. -/
def ladder23 : List Whir.Level := [⟨6, 1, 224⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩]

/-- **The deployed ladder at `μ = 23`** (`derive_config`, mumbai's `Whir.ladder`) is `ladder23`. -/
theorem ladder_23 : Whir.ladder 23 logInvRate = some ladder23 := by
  decide +kernel

/-- mumbai's check of the deployed codes passes at `2^-128` per group at `μ = 23` (`shapeOK_all`'s instance). -/
theorem shapeOK_23 : Whir.Params.shapeOK 128 23 logInvRate = true := by
  decide +kernel

/-- **The check passes at `269 · 2^-137`** on the deployed certificates and ladder of `2^23` words. -/
theorem chkQ_23 : chkLevelsQ 269 137 (LeanVM.Protocol.Whir.Params.certOf 23 logInvRate) 0 ladder23 = true := by
  decide +kernel

/-- **The deployed per-group bound at `2^23`** is `εExact`. -/
theorem whirEps_le_exact23 {config : List Whir.Level} (hc : Whir.ladder 23 logInvRate = some config) :
    whirEps (LeanVM.Protocol.Whir.Params.deployedCodes 23 logInvRate) config ≤ εExact := by
  rw [ladder_23] at hc
  cases hc
  exact chkLevelsQ_sound (by norm_num) _ 0 chkQ_23

/-- **Level 0's certified list at `2^23`**: `L₀ = 12514` (`listHi` of level 0's certificate). -/
theorem listHi_23 : (LeanVM.Protocol.Whir.Params.certOf 23 logInvRate 0).listHi = 12514 := by
  decide +kernel

/-- Level 0's Johnson list at `2^23` has at most `12514` stacks. -/
theorem listMax_23 : (code₀ 23 logInvRate).listMax ≤ 12514 :=
  (listMax_le_listHi admissible_23).trans listHi_23.le

/-- **The batching lead at `2^23`**: `(J − 1)·L₀/2^192 ≤ 2^46 · 12514 / 2^192 ≤ 2^-132`, below `εExact`. -/
theorem eBatch_le_exact23 {J : ℕ} (hJ : J ≤ 2 ^ 46 + 1) : eBatch J (code₀ 23 logInvRate) ≤ εExact := by
  rw [eBatch, LeanVM.Protocol.Whir.Params.card_E_cast, εExact]
  refine nat_div_le_q 269 137 ?_
  calc (J - 1) * (code₀ 23 logInvRate).listMax * 2 ^ 137 ≤ 2 ^ 46 * 12514 * 2 ^ 137 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) listMax_23)
    _ ≤ 269 * 2 ^ 192 := by norm_num

/-! ## The verifier's queries -/

/-- The cost (mumbai's calculus, in quarters of a query) of the opening's program past its seed at `2^23`. -/
def cost23 : ℕ := 2 + (4 + (2 + whirCost (rootHeight 23 logInvRate) 23 ladder23))

/-- **`QO` at `2^23`**: the IV's hash, the seed's permutation, the program's cost. -/
def queries23 : ℕ := 1 + 1 + cost23 / 4

theorem queries23_eq : queries23 = 6499 := by
  decide +kernel

/-- What mumbai's cost lemmas need of the ladder at the commitments' height (decided). -/
theorem ladder_heights_23 :
    whirHeightsLE (rootHeight 23 logInvRate) 23 ladder23 = true ∧
      stackHeightLE (rootHeight 23 logInvRate) 23 ladder23 = true ∧
      queryDepthsLE 23 ladder23 = true := by
  decide +kernel

/-- **The opening's program costs at most `cost23`** at `2^23` words (as `costLE_large`). -/
theorem costLE_23 (L : Stacking) (h : L.logN = 23) (claims : List Claim) :
    (variantProg L logInvRate claims).CostLE (rootHeight L.logN logInvRate) cost23 := by
  have hl : Whir.ladder L.logN logInvRate = some ladder23 := h ▸ ladder_23
  have hh : whirHeightsLE (rootHeight L.logN logInvRate) L.logN ladder23 = true ∧
      stackHeightLE (rootHeight L.logN logInvRate) L.logN ladder23 = true ∧
      queryDepthsLE L.logN ladder23 = true := h ▸ ladder_heights_23
  have hc : cost23 = 2 + (4 + (2 + whirCost (rootHeight L.logN logInvRate) L.logN ladder23)) := by
    rw [h]; rfl
  have hW : ∀ levels, Whir.ladder L.logN logInvRate = some levels →
      whirHeightsLE (rootHeight L.logN logInvRate) L.logN levels = true ∧
        queryDepthsLE L.logN levels = true ∧
        whirCost (rootHeight L.logN logInvRate) L.logN levels ≤
          whirCost (rootHeight L.logN logInvRate) L.logN ladder23 := by
    intro levels h'
    rw [hl] at h'
    cases h'
    exact ⟨hh.1, hh.2.2, le_rfl⟩
  have hH : ∀ levels, Whir.ladder L.logN logInvRate = some levels →
      stackHeightLE (rootHeight L.logN logInvRate) L.logN levels = true := by
    intro levels h'
    rw [hl] at h'
    cases h'
    exact hh.2.1
  have hopen : Prog.Costs (rootHeight L.logN logInvRate) (L.check logInvRate claims)
      (4 + (2 + whirCost (rootHeight L.logN logInvRate) L.logN ladder23)) fun _ ↦ True := by
    refine Prog.Costs.seq (a := 0) (Prog.Costs.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
    exact (costs_verifyStackedOpening _ _ _ _ hW).mono (by omega) fun _ h ↦ h
  exact (Prog.Costs.bind' (costs_commitStack _ _ hH)
    fun _ _ ↦ Prog.Costs.bind' hopen fun _ _ ↦ Prog.Costs.pure0 true).mono
      (by rw [hc]; omega) fun _ _ ↦ trivial

/-- **The query count of `opening::verify` at `2^23` words**: at most `QO = queries23`. -/
theorem isTotalQueryBound_23 (L : WhirBridge.Layout) (h : L.logN = 23) (w : (Digest × Stmt L.stacking) × Proof) :
    IsTotalQueryBound (ourVerifier L logInvRate w) queries23 := by
  rw [ourVerifier_eq]
  by_cases hne : w.1.2.claims.isEmpty = false
  · rw [ite_eq_left hne, seedComp, bind_assoc]
    have h' : queries23 = cost23 / 4 + 1 + 1 := by
      unfold queries23; omega
    rw [h']
    refine isTotalQueryBound_queryH_bind _ fun iv ↦ isTotalQueryBound_queryF_bind _ fun seed ↦ ?_
    by_cases hr : rootOf w.2 = some w.1.1
    · rw [ite_eq_left hr]
      exact isTotalQueryBound_runProof (costLE_23 L.stacking h _) seed w.2
    · rw [ite_eq_right hr]
      exact isTotalQueryBound_pure' _ _
  · rw [ite_eq_right hne]
    exact isTotalQueryBound_pure' _ _

/-- The proven program's query count at `2^23` words. -/
theorem isTotalQueryBound_fam_23 (L : Stacking) (h : L.logN = 23) (pre : Bytes) (z : Stmt L × Proof) :
    IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L logInvRate) z) queries23 := by
  rw [verifierFam_fam pre]
  exact isTotalQueryBound_verifierComp (costLE_23 L h z.1.claims) (famSeed pre z.1) z.2

/-! ## The plain shape of `2^23` words -/

/-- The plain layout of `2^23` words is one `Layout::new` accepts. -/
theorem newOK_plain23 : NewOK 23 23 23 [(0, 2 ^ 23)] := by
  decide +kernel

/-- **The plain shape of `2^23` words** at `εExact`, `QO = queries23`. -/
@[reducible] noncomputable def plainShapeE23 : ExactShape εExact where
  L := Layout.new 23 23 23 [(0, 2 ^ 23)]
  R := logInvRate
  hL := Layout.new_valid newOK_plain23
  adm := admissible_23
  hε _ hc := whirEps_le_exact23 hc
  hB _ hJ := eBatch_le_exact23 hJ
  QO := queries23
  queries pre z := isTotalQueryBound_fam_23 _ rfl pre z

/-- **The plain shape of `2^23` words as an opening's shape** (F2's `opening_sound_q` at `QO = queries23`). -/
@[reducible] noncomputable def plainShape23 : Compose.WhirShape where
  L := Layout.new 23 23 23 [(0, 2 ^ 23)]
  R := logInvRate
  QO := queries23
  bnd := openingBoundAt queries23
  adm := admissible_23
  queries w := isTotalQueryBound_23 _ rfl w
  sound A QA hA := opening_sound_q _ (Layout.new_valid newOK_plain23) admissible_23 _
    (isTotalQueryBound_fam_23 _ rfl _) A QA hA

/-! ## The shapes `2^23 ..= 2^28` -/

/-- **The plain shapes of `2^23 ..= 2^28` words**, at `εExact`. -/
noncomputable def kShapes : List (ExactShape εExact) := largeShapes ++ [plainShapeE23]

theorem kShapes_logN : kShapes.map (fun s ↦ s.L.logN) = [24, 25, 26, 27, 28, 23] := rfl

/-- **Their prefixes are distinct** (their `log_n` are). -/
theorem kShapes_nodup : (kShapes.map fun s ↦ openingPrefix s.L s.R).Nodup := by
  refine nodup_prefix_of_logN (fun s hs ↦ ?_) (by rw [kShapes_logN]; decide)
  have h := List.mem_map_of_mem (f := fun s : ExactShape εExact ↦ s.L.logN) hs
  rw [kShapes_logN] at h
  simp at h
  omega

/-- Their query counts are at most `10122`. -/
theorem kShapes_QO_le : ∀ s ∈ kShapes, s.QO ≤ 10122 := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact largeShapes_QO_le s hs
  · rw [List.mem_singleton] at hs
    subst hs
    show queries23 ≤ 10122
    rw [queries23_eq]
    norm_num

/-- **Every plain layout of `2^24 ..= 2^28` words is a shape of `kShapes`.** -/
theorem kShapes_plain (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    ∃ s ∈ kShapes, s.L = Layout.new v v v [(0, 2 ^ v)] ∧ s.R = logInvRate := by
  obtain ⟨s, hs, h⟩ := largeShapes_plain v h1 h2
  exact ⟨s, List.mem_append_left _ hs, h⟩

/-- **The plain layout of `2^23` words is a shape of `kShapes`.** -/
theorem kShapes_plain23 :
    ∃ s ∈ kShapes, s.L = Layout.new 23 23 23 [(0, 2 ^ 23)] ∧ s.R = logInvRate :=
  ⟨plainShapeE23, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

/-- **Every plain layout of `2^23 ..= 2^28` words is a shape of `kShapes`.** -/
theorem kShapes_plainK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) :
    ∃ s ∈ kShapes, s.L = Layout.new v v v [(0, 2 ^ v)] ∧ s.R = logInvRate := by
  rcases Nat.lt_or_ge v 24 with h | h
  · obtain rfl : v = 23 := by omega
    exact kShapes_plain23
  · exact kShapes_plain v h h2

/-! ## The plain shapes of `2^23 ..= 2^28` words as openings -/

/-- `QO` at `2^v` words, `23 ≤ v ≤ 28`. -/
def kQueries (v : ℕ) : ℕ := if v = 23 then queries23 else largeQueries v

theorem kQueries_le (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) : kQueries v ≤ 10122 := by
  unfold kQueries
  split_ifs with h
  · rw [queries23_eq]; norm_num
  · exact (largeQueries_le v (by unfold largeMin; omega) h2).trans_eq variantQueries_eq

theorem admissible_k {v : ℕ} (h1 : 23 ≤ v) (h2 : v ≤ 28) : Whir.Admissible v logInvRate := by
  rcases Nat.lt_or_ge v 24 with h | h
  · obtain rfl : v = 23 := by omega
    exact admissible_23
  · exact admissible_large h h2

theorem isTotalQueryBound_k (L : WhirBridge.Layout) (h1 : 23 ≤ L.logN) (h2 : L.logN ≤ 28)
    (w : (Digest × Stmt L.stacking) × Proof) :
    IsTotalQueryBound (ourVerifier L logInvRate w) (kQueries L.logN) := by
  unfold kQueries
  split_ifs with h
  · exact isTotalQueryBound_23 L h w
  · exact isTotalQueryBound_large L (by unfold largeMin; omega) h2 w

theorem isTotalQueryBound_fam_k (L : Stacking) (h1 : 23 ≤ L.logN) (h2 : L.logN ≤ 28) (pre : Bytes)
    (z : Stmt L × Proof) :
    IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L logInvRate) z) (kQueries L.logN) := by
  unfold kQueries
  split_ifs with h
  · exact isTotalQueryBound_fam_23 L h pre z
  · exact isTotalQueryBound_fam_large L (by unfold largeMin; omega) h2 pre z

theorem newOK_plainK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) : NewOK v v v [(0, 2 ^ v)] := by
  interval_cases v <;> decide +kernel

/-- **The plain shape of `2^v` words**, `23 ≤ v ≤ 28`, as an opening's shape: F2's `opening_sound_q` at the shape's
own query count `kQueries v` (`WhirShape.large`'s, and `plainShape23`'s at `v = 23`). -/
@[reducible] noncomputable def plainShapeK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) : Compose.WhirShape where
  L := Layout.new v v v [(0, 2 ^ v)]
  R := logInvRate
  QO := kQueries v
  bnd := openingBoundAt (kQueries v)
  adm := admissible_k h1 h2
  queries w := isTotalQueryBound_k _ h1 h2 w
  sound A QA hA := opening_sound_q _ (Layout.new_valid (newOK_plainK v h1 h2)) (admissible_k h1 h2) _
    (isTotalQueryBound_fam_k _ h1 h2 _) A QA hA

end UniKeccakSound

/-- info: 'UniKeccakSound.chkQ_23' depends on axioms: [propext] -/
#guard_msgs in
#print axioms UniKeccakSound.chkQ_23

/-- info: 'UniKeccakSound.kShapes_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.kShapes_nodup

/-- info: 'UniKeccakSound.kShapes_QO_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.kShapes_QO_le
