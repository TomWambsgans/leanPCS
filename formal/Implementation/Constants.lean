-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Bytes
import Implementation.Program
import Implementation.Tau
import Implementation.Formula

/-!
# The graph's constants are the Statement's

The constants the graph carries (`Graph.lean`, written by the Rust: `beta`, `coords`, `tau`, `y0`,
`y1`, `scale`, and the slopes `1 + coordinate_weight(k)` that `Program.slopeConst` names) are the
elements the Statement computes (`PcsQuotient.Domain.betaAt`, `coordinates 11`, `rowVanishing 24`,
`extension`, `coordinateWeight`): the words by kernel evaluation (`beta_lanes`, `coords_lanes`,
`tau_lanes`, the last through `Tau.lean`'s elimination steps), the extension's three elements by their
defining products (`mulE` evaluated), the slopes by evaluation in `E`.
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

/-- **The coordinates' constants** are the graph's. -/
theorem coords_lanes : (coordinates region).map K.lane = Emitted.coords.map Nat.toUInt64 := by
  decide +kernel

theorem coords_small : ∀ x ∈ Emitted.coords, x < 2 ^ 64 := by decide +kernel

theorem elem_coords (d : ℕ) : EL (Emitted.coords.getD d 0) = ofK ((coordinates region).getD d 0) :=
  elem_list coords_lanes coords_small d

/-- **`rowVanishing 24`'s words** are the graph's `tau` (`Tau.lean`: the elimination, step by step). -/
theorem tau_lanes : (rowVanishing 24).map K.lane = Emitted.tau.map Nat.toUInt64 := by
  rw [Tau.rowVanishing_24_lanes]
  decide

theorem tau_small : ∀ x ∈ Emitted.tau, x < 2 ^ 64 := by decide +kernel

theorem elem_tau (k : ℕ) : EL (Emitted.tau.getD k 0) = ofK ((rowVanishing 24).getD k 0) :=
  elem_list tau_lanes tau_small k

/-! ## The slopes -/

/-- **`1 + coordinate_weight(k)`**, `k < 8`, is the graph's constant `slopeConst k`. -/
theorem slopes : ∀ k < 8, (coordinateWeight k).map (1 + ·) = some (EL (slopeConst k)) := by
  decide +kernel

theorem coordinateWeight_none {k : ℕ} (hk : ¬ k < 8) : coordinateWeight k = none := by
  unfold coordinateWeight
  simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, hk, if_false]

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
