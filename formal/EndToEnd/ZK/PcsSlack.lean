-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The multilinear evaluation as a sum is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Whir/Complete/Tables.lean`'s `multilinearEval_eq_sum`, `LeanVM/Prover/Mle.lean`'s
-- `mleK_eq`).
import ZK.PcsFSClosed
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The slack words: group 2 of the revealed scalars

The quotient table's four slack words (`Coins.slack`, `quotientTable`) sit at coefficients `slackAt k` of `q`'s low
half, limbs `0`, `1` and `3` (`SlackPos`). The table is the table without them plus the slack words there
(`quotientTable_getD`), so `T`'s out-of-domain answer is the answer without them plus `Σ_k s_k · slackWeight z k`
(`oodT_eq`), the weights functions of the out-of-domain point `z` alone. Where they span `E` over `K`
(`SlackSpan z`), `T`'s answer is uniform given the random rows and the blinding, so the revealed scalars are
uniform as soon as the other four (`W`'s answer, `C`, `V + Y`, `X`: `group1`) are (`rMass_eq`).

**`revealedUniform_of_group1`**: `Group1Uniform ε1 → RevealedUniform (ε1 + εspan) 0`, `εspan` the probability that
the slack's weights at a uniform out-of-domain point do not span `E` (`spanFail`; at most `2^-126`, `PcsSpan.lean`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-! ### The slack's place in the table -/

/-- **Word `w` of a quotient table of `2^m` coefficients a part holds slack word `k`**: kind `0`, low half,
coefficient `slackAt k`, limb `0`, `1` or `3`. -/
def SlackPos (n k w : ℕ) : Prop := w / (8 * n) = 0 ∧ w / n % 2 = 0 ∧ w % n = slackAt k ∧ w / (2 * n) % 4 ≠ 2

instance (n k w : ℕ) : Decidable (SlackPos n k w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The randomness with the slack words zero. -/
def _root_.PcsQuotient.Coins.noSlack (coins : Coins) : Coins := { coins with slack := 0 }

/-- Slack word `k`, zero past them. -/
def slackVal (coins : Coins) (k : ℕ) : K := if h : k < slackWords then coins.slack ⟨k, h⟩ else 0

/-- The table's fold over the slack words is their sum, at most one of them sitting at a coefficient. -/
theorem slack_fold (coins : Coins) (a b : Prop) [Decidable a] [Decidable b] (i : ℕ) :
    List.foldl (fun acc k ↦ if a ∧ b ∧ i = slackAt k then (if h : k < slackWords then coins.slack ⟨k, h⟩ else 0)
      else acc) 0 (List.range slackWords) =
      ∑ k ∈ Finset.range slackWords, if a ∧ b ∧ i = slackAt k then slackVal coins k else 0 := by
  simp only [show slackWords = 4 from rfl, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [← show slackWords = 4 from rfl]
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, true_and, false_and, ite_false, add_zero] <;>
    simp only [slackAt, slackVal] <;> split_ifs <;> simp_all <;> omega

/-- The slack words' contribution to a word. -/
def slackPart (n : ℕ) (coins : Coins) (w : ℕ) : K :=
  ∑ k ∈ Finset.range slackWords, if SlackPos n k w then slackVal coins k else 0

/-- **The table is the table without the slack words, plus them.** -/
theorem quotientTable_getD (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E)
    (w : ℕ) (hw : w < 16 * 2 ^ cellVars circuit.logRows) :
    (quotientTable circuit stmt cells₀ coins α β μ).getD w 0 =
      (quotientTable circuit stmt cells₀ coins.noSlack α β μ).getD w 0 +
        slackPart (2 ^ cellVars circuit.logRows) coins w := by
  have hq : quotientParts circuit stmt cells₀ coins.noSlack α β μ = quotientParts circuit stmt cells₀ coins α β μ := rfl
  have hb : ∀ i, blindAt coins.noSlack i = blindAt coins i := fun _ ↦ rfl
  unfold quotientTable
  rw [LeanVM.Prover.getD_ofFn _ _ hw, LeanVM.Prover.getD_ofFn _ _ hw]
  simp only [hq, hb, slack_fold, slackPart, SlackPos]
  have h0 : ∀ (a b : Prop) [Decidable a] [Decidable b] (i : ℕ),
      (∑ k ∈ Finset.range slackWords, if a ∧ b ∧ i = slackAt k then slackVal coins.noSlack k else 0) = 0 :=
    fun _ _ _ _ _ ↦ Finset.sum_eq_zero fun k _ ↦ by simp [slackVal, Coins.noSlack]
  rw [h0]
  have hl : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 2
  · have h3 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 3 := by omega
    have h2 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 ≠ 2 := by omega
    simp only [h1, h3, h2, ite_true, ne_eq, not_false_eq_true, and_true, add_zero]
  · by_cases h2 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 = 2
    · simp [h2]
    · have h3 : ¬ w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 3 := by omega
      simp only [h1, h3, h2, ite_false, ne_eq, not_false_eq_true, and_true, zero_add]

/-! ### `T`'s answer -/

theorem ofK_add₂ (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_zero₂ : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem ofK_sum₂ {ι : Type} (s : Finset ι) (f : ι → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

/-- **A table's multilinear as a sum** over its words. -/
theorem tableEval_sum (A : Array K) (V : ℕ) (hA : A.size = 2 ^ V) (z : List E) (hz : z.length = V) :
    tableEval A z = ∑ w ∈ Finset.range (2 ^ V), ofK (A.getD w 0) * eqEval (boolPoint V w) z := by
  rw [tableEval, LeanVM.Prover.mleK_eq,
    LeanVM.Protocol.Whir.Complete.multilinearEval_eq_sum V _ _ (by simp [hA]) hz]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ V := Finset.mem_range.1 hi
  have h2 : (A.toList.map ofK).getD i 0 = ofK (A.getD i 0) := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi', hA]
  rw [h2]

/-- The weight of slack word `k` in the quotient table's multilinear at `z` (`28` variables). -/
noncomputable def slackWeight (z : List E) (k : ℕ) : E :=
  ∑ w ∈ Finset.range (2 ^ 28), if SlackPos (2 ^ 24) k w then eqEval (boolPoint 28 w) z else 0

theorem cellVars_membership : cellVars (membership logRows).logRows = 24 := rfl

/-- **`T`'s out-of-domain answer is the answer without the slack words plus their weighted sum.** -/
theorem oodT_eq (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E) (z : List E)
    (hz : z.length = 28) :
    tableEval (quotientTable (membership logRows) stmt cells₀ coins α β μ) z =
      tableEval (quotientTable (membership logRows) stmt cells₀ coins.noSlack α β μ) z +
        ∑ k ∈ Finset.range slackWords, ofK (slackVal coins k) * slackWeight z k := by
  have hsz : ∀ c : Coins, (quotientTable (membership logRows) stmt cells₀ c α β μ).size = 2 ^ 28 := fun c ↦ by
    unfold quotientTable
    rw [Array.size_ofFn, cellVars_membership]
    norm_num
  rw [tableEval_sum _ 28 (hsz _) z hz, tableEval_sum _ 28 (hsz _) z hz]
  have hw : ∀ w ∈ Finset.range (2 ^ 28),
      ofK ((quotientTable (membership logRows) stmt cells₀ coins α β μ).getD w 0) * eqEval (boolPoint 28 w) z =
        ofK ((quotientTable (membership logRows) stmt cells₀ coins.noSlack α β μ).getD w 0) *
          eqEval (boolPoint 28 w) z +
        ∑ k ∈ Finset.range slackWords,
          ofK (slackVal coins k) * (if SlackPos (2 ^ 24) k w then eqEval (boolPoint 28 w) z else 0) := by
    intro w hw
    have hw' : w < 16 * 2 ^ cellVars (membership logRows).logRows := by
      rw [cellVars_membership]; have := Finset.mem_range.1 hw; omega
    rw [quotientTable_getD _ _ _ _ _ _ _ w hw', ofK_add₂, add_mul, slackPart, ofK_sum₂, Finset.sum_mul,
      cellVars_membership]
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    split_ifs <;> simp [ofK_zero₂]
  rw [Finset.sum_congr rfl hw, Finset.sum_add_distrib, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [slackWeight, Finset.mul_sum]

/-! ### The slack map -/

/-- Slack word `k` of a vector, zero past them. -/
def svAt (sw : Fin slackWords → K) (k : ℕ) : K := if h : k < slackWords then sw ⟨k, h⟩ else 0

/-- **The slack map** at the out-of-domain point `z`: the slack words' contribution to `T`'s answer. -/
noncomputable def slackMap (z : List E) : (Fin slackWords → K) →+ E where
  toFun sw := ∑ k ∈ Finset.range slackWords, ofK (svAt sw k) * slackWeight z k
  map_zero' := Finset.sum_eq_zero fun k _ ↦ by simp [svAt, ofK_zero₂]
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← add_mul, ← ofK_add₂]
    congr 2
    simp only [svAt]
    split_ifs <;> simp

/-- **The slack's weights span `E` over `K`** at the out-of-domain point `z`: the slack map is onto. -/
def SlackSpan (z : List E) : Prop := Function.Surjective (slackMap z)

theorem slackVal_eq (coins : Coins) (k : ℕ) : slackVal coins k = svAt coins.slack k := rfl

/-- The four slack words as the coins draw them. -/
noncomputable def slDist : ProbComp (Fin slackWords → K) :=
  (fun w2 : List UInt64 ↦ fun k : Fin slackWords ↦ K.ofLane (w2.getD k 0)) <$>
    (List.range slackWords).mapM fun _ ↦ cwDist

theorem length_of_mem_mapM {α δ : Type} (X : ProbComp α) :
    ∀ (l : List δ) (w : List α), w ∈ support (l.mapM fun _ ↦ X) → w.length = l.length
  | [], w, hw => by simp at hw; simp [hw]
  | d :: l, w, hw => by
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨a, -, w', hw', rfl⟩ := hw
    simp [length_of_mem_mapM X l w' hw']

/-- **Each slack vector has mass `c64⁴`.** -/
theorem prEvent_slDist (sw : Fin slackWords → K) : Pr{let x ← slDist}[x = sw] = c64 ^ 4 := by
  classical
  set ws : List UInt64 := (List.range slackWords).map fun k ↦ (svAt sw k).lane
  have hws : ws.length = slackWords := by simp [ws]
  rw [slDist, prEvent_map]
  rw [prEvent_congr_of_support _ _ (· = ws) fun w hw ↦ ?_]
  · rw [prEvent_mapM_const cwDist (List.range slackWords) ws (by simp [hws])]
    simp [ws, prEvent_cwDist, slackWords, Function.comp_def, List.map_const']
    ring
  · have hl : w.length = 4 := by
      have := length_of_mem_mapM cwDist (List.range slackWords) w hw
      simpa [slackWords] using this
    constructor
    · intro h
      apply List.ext_getElem (by simp [hl, hws, slackWords])
      intro i h1 h2
      have hi : i < slackWords := by simpa [slackWords, hl] using h1
      have := congrFun h ⟨i, hi⟩
      simp only at this
      simp only [ws, List.getElem_map, List.getElem_range, svAt, hi, dite_true, ← this]
      simp [List.getD_eq_getElem?_getD, h1]
    · rintro rfl
      funext k
      simp only [ws, svAt]
      simp [List.getD_eq_getElem?_getD, k.isLt]

/-- **Where the slack's weights span `E`, the slack words' contribution is a uniform element of `E`.** -/
theorem slackMap_uniform (z : List E) (hspan : SlackSpan z) (y : E) :
    Pr{let x ← slackMap z <$> slDist}[x = y] = Pr{let x ← eDist}[x = y] := by
  classical
  have hfib : ∀ y, Pr{let x ← slackMap z <$> slDist}[x = y] =
      c64 ^ 4 * (Finset.univ.filter fun sw ↦ slackMap z sw = (0 : E)).card := by
    intro y
    rw [prEvent_map, prEvent_eq_tsum_ite, tsum_fintype]
    simp only [prEvent_slDist]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    exact AddMonoidHom.card_fiber_eq_of_mem_range (slackMap z) (hspan y) (hspan 0)
  have h := evalDistEq_of_const (slackMap z <$> slDist) eDist _ _ hfib prEvent_eDist
  exact h.prEvent_eq (· = y)

/-! ### The coins: the rows and the blinding, then the slack -/

/-- The randomness the coins' words spell (`sampleCoins`). -/
def mkCoins (w : List UInt64) : Coins :=
  ⟨fun r ↦ K.ofLane (w.getD r.val 0), fun e i ↦ K.ofLane (w.getD (randomWords + freeBlind * e.val + i.val) 0),
    fun k ↦ K.ofLane (w.getD (randomWords + 3 * freeBlind + k.val) 0)⟩

/-- The randomness with the slack words `sw`. -/
def withSlack (c : Coins) (sw : Fin slackWords → K) : Coins := { c with slack := sw }

theorem coinsDist_eq : coinsDist = (do
    let w1 ← (List.range 38).mapM fun _ ↦ cwDist
    let sw ← slDist
    pure (withSlack (mkCoins w1) sw)) := by
  have h1 : coinsDist = (do let w ← (List.range 42).mapM fun _ ↦ cwDist; pure (mkCoins w)) := by
    simp only [coinsDist, sampleCoins, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
    rfl
  rw [h1, show (42 : ℕ) = 38 + 4 from rfl, List.range_add, List.mapM_append, List.mapM_map, bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun w1 hw1 ↦ ?_
  have hl : w1.length = 38 := by simpa using length_of_mem_mapM cwDist (List.range 38) w1 hw1
  rw [slDist, bind_map_left]
  simp only [bind_assoc, pure_bind]
  refine bind_congr_of_forall_mem_support _ fun w2 _ ↦ ?_
  congr 1
  simp only [mkCoins, withSlack, Function.comp_def]
  have hlo : ∀ j, j < 38 → (w1 ++ w2).getD j 0 = w1.getD j 0 := fun j hj ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]
  congr 1
  · funext r; rw [hlo _ (by have := r.isLt; simp [randomWords, randomRows] at this ⊢; omega)]
  · funext e i
    rw [hlo _ (by have := e.isLt; have := i.isLt; simp [randomWords, randomRows, freeBlind, hBlind] at *; omega)]
  · funext k
    rw [show randomWords + 3 * freeBlind + k.val = w1.length + k.val by simp [hl, randomWords, randomRows,
      freeBlind, hBlind]]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-! ### The revealed scalars, group by group -/

/-- **Group 1**: `W`'s answer, `C`, `V + Y`, `X`: the revealed scalars but `T`'s answer. -/
def group1 (stmt : Statement) (cells₀ : Array K) (coins : Coins) (c : Challenges) : List E :=
  [revealAnswer (membership logRows) stmt cells₀ coins (.oodW c.zW),
    revealAnswer (membership logRows) stmt cells₀ coins (.value 1 c.t),
    revealAnswer (membership logRows) stmt cells₀ coins (.value 2 c.t),
    revealAnswer (membership logRows) stmt cells₀ coins (.value 0 c.t)]

/-- **Group 1 is uniform at the challenges `c`**: with uniform randomness the four scalars are four uniform elements
of `E` (the rank-`12` condition on the random rows' words). -/
def Group1At (stmt : Statement) (cells₀ : Array K) (c : Challenges) : Prop :=
  ∀ r : List E, Pr{let x ← runWithRandomPermutation (do return group1 stmt cells₀ (← sampleCoins) c)}[x = r] =
    Pr{let x ← runWithRandomPermutation (coinEs 4)}[x = r]

/-- **Group 1 is uniform at all but `ε1` of the challenges**, for every statement and witness of the relation. -/
def Group1Uniform (ε1 : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let c ← sampleChallenges}[¬ Group1At stmt ((membership logRows).cells (membershipInputs w)) c] ≤ ε1

/-- **The slack's span failure**: the probability that the slack's weights at a uniform `T` point do not span `E`. -/
noncomputable def spanFail : ℝ≥0∞ := Pr{let c ← sampleChallenges}[¬ SlackSpan c.zT]

/-- The four scalars of a five-scalar list but its second. -/
def drop1 (r : List E) : List E := [r.getD 0 0, r.getD 2 0, r.getD 3 0, r.getD 4 0]

/-- The mass of a uniform element of `E`. -/
noncomputable abbrev κE : ℝ≥0∞ := c64 * (c64 * c64)

theorem revealed_withSlack (stmt : Statement) (cells₀ : Array K) (b : Coins) (sw : Fin slackWords → K)
    (c : Challenges) (hz : c.zT.length = 28) :
    revealed stmt cells₀ (withSlack b sw) c =
      [(group1 stmt cells₀ b c).getD 0 0,
        tableEval (quotientTable (membership logRows) stmt cells₀ b.noSlack c.α c.β c.μ) c.zT + slackMap c.zT sw,
        (group1 stmt cells₀ b c).getD 1 0, (group1 stmt cells₀ b c).getD 2 0, (group1 stmt cells₀ b c).getD 3 0] := by
  simp only [revealed, revealQueries, List.map_cons, List.map_nil, group1]
  have hT : revealAnswer (membership logRows) stmt cells₀ (withSlack b sw) (.oodT c.α c.β c.μ c.zT) =
      tableEval (quotientTable (membership logRows) stmt cells₀ b.noSlack c.α c.β c.μ) c.zT + slackMap c.zT sw := by
    show tableEval (quotientTable (membership logRows) stmt cells₀ (withSlack b sw) c.α c.β c.μ) c.zT = _
    rw [oodT_eq _ _ _ _ _ _ _ hz]
    rfl
  rw [hT]
  rfl

theorem prEvent_coinEs_n (n : ℕ) (rs : List E) :
    Pr{let x ← runWithRandomPermutation (coinEs n)}[x = rs] = if rs.length = n then κE ^ n else 0 := by
  rw [runWithRandomPermutation_coinEs]
  split_ifs with h
  · rw [prEvent_mapM_const eDist (List.range n) rs (by simp [h])]
    simp [prEvent_eDist, List.map_const', List.prod_replicate, h]
  · refine (prEvent_eq_zero_iff _ _).2 fun x hx hxr ↦ h ?_
    subst hxr
    simpa using length_of_mem_mapM eDist (List.range n) x hx

open Classical in
theorem prEvent_bind_pure_const {α β : Type} (X : ProbComp α) (g v : β) :
    Pr{let y ← (X >>= fun _ ↦ (pure g : ProbComp β))}[y = v] = if g = v then 1 else 0 := by
  rw [prEvent_bind_eq_tsum]
  simp only [RProg.prEvent_pure_eq]
  rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- An event on five scalars of which one is a translate. -/
theorem prEvent_five (X : ProbComp E) (g0 g1 g2 g3 T0 : E) (r : List E) :
    Pr{let y ← (fun x ↦ [g0, T0 + x, g1, g2, g3]) <$> X}[y = r] =
      if r.length = 5 ∧ [g0, g1, g2, g3] = drop1 r then Pr{let y ← X}[y = r.getD 1 0 + T0] else 0 := by
  classical
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  rw [prEvent_map]
  split_ifs with h
  · obtain ⟨h5, hg⟩ := h
    obtain ⟨a0, a1, a2, a3, a4, rfl⟩ : ∃ a0 a1 a2 a3 a4 : E, r = [a0, a1, a2, a3, a4] := by
      match r, h5 with
      | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩
    simp only [drop1, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true] at hg ⊢
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hg
    refine prEvent_congr_of_support _ _ _ fun x _ ↦ ?_
    simp only [true_and, and_true]
    constructor
    · intro hx; linear_combination hx + (-T0) * h2
    · intro hx; linear_combination hx + T0 * h2
  · refine (prEvent_eq_zero_iff _ _).2 fun x _ hx ↦ h ?_
    subst hx
    exact ⟨rfl, rfl⟩

/-- **The revealed scalars' mass factors** where the slack's weights span `E`: `T`'s answer is uniform given the
rest, so a list's mass is `κE` times group 1's mass of the list without its second scalar. -/
theorem rMass_eq (stmt : Statement) (cells₀ : Array K) (c : Challenges) (hz : c.zT.length = 28)
    (hspan : SlackSpan c.zT) (r : List E) :
    rMass stmt cells₀ c r =
      if r.length = 5 then
        κE * Pr{let x ← runWithRandomPermutation (do return group1 stmt cells₀ (← sampleCoins) c)}[x = drop1 r]
      else 0 := by
  classical
  have hX : (fun coins ↦ revealed stmt cells₀ coins c) <$> coinsDist =
      ((List.range 38).mapM (fun _ ↦ cwDist) >>= fun w1 ↦ slDist >>= fun sw ↦
        pure (revealed stmt cells₀ (withSlack (mkCoins w1) sw) c)) := by
    rw [coinsDist_eq]; simp only [map_bind, map_pure]
  have hY : (fun coins ↦ group1 stmt cells₀ coins c) <$> coinsDist =
      ((List.range 38).mapM (fun _ ↦ cwDist) >>= fun w1 ↦ slDist >>= fun sw ↦
        pure (group1 stmt cells₀ (withSlack (mkCoins w1) sw) c)) := by
    rw [coinsDist_eq]; simp only [map_bind, map_pure]
  rw [rMass, runWithRandomPermutation_sampleCoins_map, runWithRandomPermutation_sampleCoins_map, hX, hY,
    prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  -- Each `w1`: the slack map uniform.
  have hinner : ∀ w1 : List UInt64,
      Pr{let x ← (slDist >>= fun sw ↦ pure (revealed stmt cells₀ (withSlack (mkCoins w1) sw) c))}[x = r] =
        if r.length = 5 then κE * Pr{let x ← (slDist >>= fun sw ↦
          (pure (group1 stmt cells₀ (withSlack (mkCoins w1) sw) c) : ProbComp _))}[x = drop1 r] else 0 := by
    intro w1
    have hg : ∀ sw, group1 stmt cells₀ (withSlack (mkCoins w1) sw) c = group1 stmt cells₀ (mkCoins w1) c :=
      fun _ ↦ rfl
    simp only [revealed_withSlack _ _ _ _ _ hz, hg]
    rw [prEvent_bind_pure_const]
    have hmap : ∀ (g0 g1 g2 g3 T0 : E), (slDist >>= fun sw ↦
        (pure [g0, T0 + slackMap c.zT sw, g1, g2, g3] : ProbComp _)) =
          (fun x ↦ [g0, T0 + x, g1, g2, g3]) <$> (slackMap c.zT <$> slDist) := fun _ _ _ _ _ ↦ by
      rw [Functor.map_map, map_eq_bind_pure_comp]
      rfl
    rw [hmap, prEvent_five, slackMap_uniform _ hspan, prEvent_eDist]
    obtain ⟨g0, g1, g2, g3, hG⟩ : ∃ g0 g1 g2 g3 : E, group1 stmt cells₀ (mkCoins w1) c = [g0, g1, g2, g3] :=
      ⟨_, _, _, _, rfl⟩
    simp only [hG, List.getD_cons_zero, List.getD_cons_succ]
    by_cases h5 : r.length = 5 <;> by_cases hg : [g0, g1, g2, g3] = drop1 r <;>
      simp [h5, hg]
  simp only [hinner]
  split_ifs with h5
  · rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun w1 ↦ ?_
    ring
  · simp

/-! ### Group 2 proved: `RevealedUniform` from group 1 -/

/-- **Where group 1 is uniform and the slack's weights span `E`, the revealed scalars are exactly uniform.** -/
theorem uniformWithin_zero (stmt : Statement) (cells₀ : Array K) (c : Challenges) (hz : c.zT.length = 28)
    (hspan : SlackSpan c.zT) (hG : Group1At stmt cells₀ c) : UniformWithin stmt cells₀ c 0 := by
  have h : ∀ r, rMass stmt cells₀ c r = uMass r := by
    intro r
    rw [rMass_eq _ _ _ hz hspan, hG, prEvent_coinEs_n, uMass, prEvent_coinEs_n]
    have h4 : (drop1 r).length = 4 := rfl
    split_ifs with h5
    · ring
    · rfl
  change ∑' r, (uMass r - rMass stmt cells₀ c r) ≤ 0
  simp [h]

theorem zT_length_of_mem {c : Challenges} (hc : c ∈ support sampleChallenges) : c.zT.length = 28 := by
  rw [sampleChallenges_eq] at hc
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
  obtain ⟨zW, -, α, -, β, -, μ, -, zT, hzT, t, -, ρ, -, rfl⟩ := hc
  exact length_of_mem_iidE _ _ hzT

/-- **`RevealedUniform` at `δr = 0` from group 1's uniformity**: the group-2 half (`T`'s answer, through the slack
words) is proved, `εr` group 1's failure plus the slack's span failure (`spanFail`). -/
theorem revealedUniform_of_group1 (ε1 : ℝ≥0∞) (h : Group1Uniform ε1) : RevealedUniform (ε1 + spanFail) 0 := by
  intro stmt w hrel
  set cells₀ := (membership logRows).cells (membershipInputs w)
  refine (prEvent_mono_of_support _ _ (fun c ↦ ¬ Group1At stmt cells₀ c ∨ ¬ SlackSpan c.zT)
    fun c hc hbad ↦ ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add (h stmt w hrel) le_rfl))
  by_contra hn
  push Not at hn
  exact hbad (uniformWithin_zero _ _ _ (zT_length_of_mem hc) hn.2 hn.1)

/-- **Zero knowledge from the PCS hypothesis and group 1's uniformity**: `zeroKnowledge_pcs_closed` with
`RevealedUniform` discharged at `δr = 0` but for group 1 (`revealedUniform_of_group1`). -/
theorem zeroKnowledge_pcs_group1 (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (ε1 : ℝ≥0∞)
    (hpcs : PcsZeroKnowledge sim εpcs) (h1 : Group1Uniform ε1) :
    ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + (ε1 + spanFail) + 0 + εfs₀) :=
  zeroKnowledge_pcs_closed sim εpcs (ε1 + spanFail) 0 hpcs (revealedUniform_of_group1 ε1 h1)

end PcsQuotient.EndToEnd
