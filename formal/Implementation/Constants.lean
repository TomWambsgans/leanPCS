-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Bytes
import Implementation.Program
import Implementation.Tau
import Implementation.Formula

/-!
# The graph's constants are the Statement's

The constants the graph carries (`Graph.lean`, written by the Rust: `beta`, `tau`, `pinPoints`,
`pinWeights`, `y0`, `y1`, `scale`) are the elements the Statement computes (`PcsQuotient.Domain.betaAt`,
`rowVanishing 24`, `pinPoints`, `pinWeights`, `extension`): the words by kernel evaluation (`beta_lanes`,
`tau_lanes` through `Tau.lean`'s elimination steps, `pinPoints_lanes`), the inverses (the pins' weights, the
extension's three elements) by their defining products (`mulE` evaluated), and the constants `λ_k v_k` of the
anchors of `1` and `3` (`elem_pinConst`).
-/

set_option linter.unusedSectionVars false

namespace Implementation

open LeanVM.Parameters LeanVM.Protocol PcsQuotient PcsQuotient.Domain Program Emitted

local notation "W" => word limbsEquiv
local notation "EL" => elem limbsEquiv

/-! ## Words of `K` -/

/-- An entry of a list of `K` given by its words. -/
theorem getD_of_words {l : List K} {ws : List UInt64} (h : l.map K.lane = ws) (i : ℕ) :
    l.getD i 0 = K.ofLane (ws.getD i 0) := by
  subst h
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
    rfl

theorem word_ofK (a : K) : W (ofK a) = a.lane.toNat := by
  have e : ofK a = E.ofLimbs (K.ofLane a.lane) (K.ofLane 0) (K.ofLane 0) := rfl
  rw [e, word_ofLimbs]
  simp

theorem elem_lane {n : ℕ} (hn : n < 2 ^ 64) : EL n = ofK (K.ofLane n.toUInt64) := by
  apply elem_eq_of_word
  rw [word_ofK, show (K.ofLane n.toUInt64).lane = n.toUInt64 from rfl, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (lt_trans hn (by decide))]

theorem elem_list {l : List K} {ns : List ℕ} (h : l.map K.lane = ns.map Nat.toUInt64)
    (hs : ∀ x ∈ ns, x < 2 ^ 64) (i : ℕ) : EL (ns.getD i 0) = ofK (l.getD i 0) := by
  have hlt : ns.getD i 0 < 2 ^ 64 := by
    rw [List.getD_eq_getElem?_getD]
    cases hk : ns[i]? with
    | none => simp
    | some x => exact hs x (List.mem_of_getElem? hk)
  rw [getD_of_words h, elem_lane hlt]
  congr 2
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ns[i]? <;> rfl

theorem ofK_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)
theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)
theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-! ## The Cantor basis, the coordinates, the rows' polynomial -/

/-- **The basis's words** are the graph's (kernel evaluation of the Statement's pivots and solves). -/
theorem beta_lanes : PcsQuotient.Domain.beta.toList.map K.lane = Emitted.beta.map Nat.toUInt64 := by
  decide +kernel

theorem beta_small : ∀ x ∈ Emitted.beta, x < 2 ^ 64 := by decide +kernel

theorem betaAt_eq_getD (k : ℕ) : betaAt k = PcsQuotient.Domain.beta.toList.getD k 0 := by
  simp [betaAt, List.getD_eq_getElem?_getD]

theorem elem_theta : EL (Emitted.beta.getD 1 0) = ofK (betaAt 1) := by
  rw [elem_list beta_lanes beta_small, betaAt_eq_getD]

theorem elem_theta1 : EL (Emitted.beta.getD 1 0 ^^^ 1) = ofK (betaAt 1 + 1) := by
  rw [elem_xor isF192_primitives, elem_theta, elem_one isF192_primitives, ofK_add, ofK_one]

/-- **`rowVanishing 24`'s words** are the graph's `tau` (`Tau.lean`: the elimination, step by step). -/
theorem tau_lanes : (rowVanishing 24).map K.lane = Emitted.tau.map Nat.toUInt64 := by
  rw [Tau.rowVanishing_24_lanes]
  decide

theorem tau_small : ∀ x ∈ Emitted.tau, x < 2 ^ 64 := by decide +kernel

theorem elem_tau (k : ℕ) : EL (Emitted.tau.getD k 0) = ofK ((rowVanishing 24).getD k 0) :=
  elem_list tau_lanes tau_small k

/-! ## The pins -/

/-- **The pins' points** are the graph's (kernel evaluation of the Statement's `point (anchorCell k)`). -/
theorem pinPoints_lanes : PcsQuotient.pinPoints.map K.lane = Emitted.pinPoints.map Nat.toUInt64 := by
  decide +kernel

theorem pinPoints_small : ∀ x ∈ Emitted.pinPoints, x < 2 ^ 64 := by decide +kernel

theorem elem_pinPoint (k : ℕ) : EL (Emitted.pinPoints.getD k 0) = ofK (PcsQuotient.pinPoints.getD k 0) :=
  elem_list pinPoints_lanes pinPoints_small k

/-- `Π_(j ≠ k) (p_k + p_j)` on the graph's words. -/
def pinProd (k : ℕ) : ℕ :=
  (List.range 11).foldl (fun acc j ↦ if j = k then acc else
    mulE acc (Emitted.pinPoints.getD k 0 ^^^ Emitted.pinPoints.getD j 0)) 1

/-- **The graph's pin weights invert the products** (`mulE` evaluated in the kernel). -/
theorem pinWeights_mul : ∀ k < 11, mulE (Emitted.pinWeights.getD k 0) (pinProd k) = 1 := by
  decide +kernel

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem fold_pinProd (k : ℕ) : ∀ (l : List ℕ) (a : K) (n : ℕ), ofK a = EL n →
    ofK (l.foldl (fun acc j ↦ if j = k then acc else
        acc * (PcsQuotient.pinPoints.getD k 0 + PcsQuotient.pinPoints.getD j 0)) a) =
      EL (l.foldl (fun acc j ↦ if j = k then acc else
        mulE acc (Emitted.pinPoints.getD k 0 ^^^ Emitted.pinPoints.getD j 0)) n)
  | [], _, _, h => h
  | j :: l, a, n, h => by
    simp only [List.foldl_cons]
    apply fold_pinProd k l
    split_ifs
    · exact h
    · rw [ofK_mul, ofK_add, h, elem_mulE isF192_primitives, elem_xor isF192_primitives, elem_pinPoint,
        elem_pinPoint]

theorem pinWeights_getD (k : ℕ) (hk : k < 11) :
    PcsQuotient.pinWeights.getD k 0 = ((List.range 11).foldl (fun acc j ↦ if j = k then acc else
        acc * (PcsQuotient.pinPoints.getD k 0 + PcsQuotient.pinPoints.getD j 0)) 1)⁻¹ := by
  simp [PcsQuotient.pinWeights, List.getD_eq_getElem?_getD, hk, publicRows, publicWords]

/-- **The pins' Lagrange weights** are the graph's. -/
theorem elem_pinWeight (k : ℕ) (hk : k < 11) :
    EL (Emitted.pinWeights.getD k 0) = ofK (PcsQuotient.pinWeights.getD k 0) := by
  have hp : ofK ((List.range 11).foldl (fun acc j ↦ if j = k then acc else
        acc * (PcsQuotient.pinPoints.getD k 0 + PcsQuotient.pinPoints.getD j 0)) 1) = EL (pinProd k) :=
    fold_pinProd k _ 1 1 (by rw [ofK_one, elem_one isF192_primitives])
  have h1 : EL (Emitted.pinWeights.getD k 0) * EL (pinProd k) = 1 := by
    rw [← elem_mulE isF192_primitives, pinWeights_mul k hk, elem_one isF192_primitives]
  have hinv : ∀ x : K, ofK x⁻¹ = (ofK x)⁻¹ := fun x => map_inv₀ (algebraMap K E) x
  rw [pinWeights_getD k hk, hinv, hp]
  exact eq_inv_of_mul_eq_one_left h1

theorem elem_three : EL 3 = ofK three := by
  rw [elem_lane (by norm_num)]
  rfl

/-- The constants of anchors `9` and `10`, `λ_k · v_k`, are the graph's. -/
theorem elem_pinConst (k : ℕ) (hk : 9 ≤ k ∧ k < 11) (words : List K) :
    EL (mulE (Emitted.pinWeights.getD k 0) (if k = 9 then 1 else 3)) =
      ofK (PcsQuotient.pinWeights.getD k 0 * anchorValues words k) := by
  rw [elem_mulE isF192_primitives, elem_pinWeight k (by omega), ofK_mul]
  congr 1
  obtain ⟨h9, h11⟩ := hk
  rcases (by omega : k = 9 ∨ k = 10) with rfl | rfl
  · simp [anchorValues, publicWords, elem_one isF192_primitives, ofK_one]
  · simp [anchorValues, publicWords, elem_three]

/-! ## The extension -/

theorem elem_B64 : EL B64 = ey := by decide +kernel

theorem one_add_ey_ne : (1 : E) + ey ≠ 0 := by decide +kernel

theorem one_add_ey2_ne : (1 : E) + ey * ey ≠ 0 := by decide +kernel

theorem elem_1B64 : EL (1 ^^^ B64) = 1 + ey := by
  rw [elem_xor isF192_primitives, elem_one isF192_primitives, elem_B64]

theorem elem_B64sq : EL (mulE B64 B64) = ey * ey := by
  rw [elem_mulE isF192_primitives, elem_B64]

theorem elem_1B64sq : EL (1 ^^^ mulE B64 B64) = 1 + ey * ey := by
  rw [elem_xor isF192_primitives, elem_one isF192_primitives, elem_B64sq]

theorem mulE_y0 : mulE Emitted.y0 (1 ^^^ B64) = B64 := by decide +kernel

theorem mulE_y1 : mulE Emitted.y1 (1 ^^^ mulE B64 B64) = mulE B64 B64 := by decide +kernel

theorem mulE_scale : mulE Emitted.scale (mulE (1 ^^^ B64) (1 ^^^ mulE B64 B64)) = 1 := by
  decide +kernel

/-- `extension()`: `Y / (1 + Y)`. -/
theorem elem_y0 : EL Emitted.y0 = extension.1.1 := by
  show _ = ey * (1 + ey)⁻¹
  refine (eq_mul_inv_iff_mul_eq₀ one_add_ey_ne).mpr ?_
  rw [← elem_1B64, ← elem_mulE isF192_primitives, mulE_y0, elem_B64]

/-- `extension()`: `Y^2 / (1 + Y^2)`. -/
theorem elem_y1 : EL Emitted.y1 = extension.1.2 := by
  show _ = ey * ey * (1 + ey * ey)⁻¹
  refine (eq_mul_inv_iff_mul_eq₀ one_add_ey2_ne).mpr ?_
  rw [← elem_1B64sq, ← elem_mulE isF192_primitives, mulE_y1, elem_B64sq]

/-- `extension()`: `1 / ((1 + Y) (1 + Y^2))`. -/
theorem elem_scale : EL Emitted.scale = extension.2 := by
  show _ = ((1 + ey) * (1 + ey * ey))⁻¹
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← elem_1B64, ← elem_1B64sq, ← elem_mulE isF192_primitives, ← elem_mulE isF192_primitives,
    mulE_scale, elem_one isF192_primitives]

end Implementation
