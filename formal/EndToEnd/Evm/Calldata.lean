-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The calldata's layout is `crates/membership/evm/src/quotient.rs`'s `calldata`, which the tests' `parse`
-- (`crates/membership/evm/src/lean.rs`) inverts.
import Evm.Contract

/-!
# Every calldata the contract can accept is a proof's

The contract reverts on calldata of another length or selector (`accepts_of_not_wellFormed`), and every
other calldata is the calldata of a statement, a reduction proof and a frame's index
(`calldata_surjective`: the statement's `64` bytes, each root's bytes read as a digest and sent as its
halves, each other scalar's `24` bytes read as an element: the inverse of `quotient.rs`'s `calldata`, the
tests' `parse`). So over **all** calldata:

**`evm_accepts_iff_exists`**: with what the block proves of declared claim `k` the opening check `pcsOpen`
with the openings `o`, the contract accepts `cd` exactly when `cd` is the calldata of a statement and a
reduction proof that, with those openings, `PcsQuotient.verify` accepts.
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient PcsQuotient.Transcript
  Implementation

local notation "W" => word limbsEquiv

/-- The contract reverts on calldata of another length or selector. -/
theorem accepts_of_not_wellFormed (attest : ℕ → List UInt8 → Bool) (index : Commitment) {cd : List UInt8}
    (h : ¬ WellFormed cd) : accepts attest (deployed index cd) = false := by
  have hr : run (deployed index cd) = none := if_neg h
  rw [accepts, hr]

/-! ## Slices -/

/-- A list of `k · n` entries is its `n` chunks of `k`. -/
theorem chunks {α : Type} (k : ℕ) : ∀ (n : ℕ) (L : List α), L.length = k * n →
    (List.range n).flatMap (fun j => (L.drop (k * j)).take k) = L
  | 0, L, h => by simp_all
  | n + 1, L, h => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.mul_zero, List.drop_zero]
    have ih := chunks k n (L.drop k) (by simp [h]; ring_nf; omega)
    have e : (List.range n).flatMap (fun j => (L.drop (k * (j + 1))).take k) =
        (List.range n).flatMap (fun j => ((L.drop k).drop (k * j)).take k) := by
      refine List.flatMap_congr fun j _ => ?_
      rw [List.drop_drop, show k + k * j = k * (j + 1) by ring]
    rw [e, ih, List.take_append_drop]

theorem slice_sub {α : Type} (cd : List α) (a n s k : ℕ) (h : s + k ≤ n) :
    (((cd.drop a).take n).drop s).take k = (cd.drop (a + s)).take k := by
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem take_drop_append' {α : Type} (l : List α) (s n : ℕ) : l.drop s = (l.drop s).take n ++ l.drop (s + n) := by
  rw [← List.drop_drop, List.take_append_drop]

theorem elementBytes_elementOf (b : List UInt8) (hb : b.length = 24) : elementBytes (elementOf b) = b := by
  rw [elementBytes_eq]
  apply beBytes_eq_of_beNat hb
  have hc := chunks 8 3 b (by rw [hb])
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append] at hc
  have hc' : b.take 8 ++ ((b.drop 8).take 8 ++ (b.drop 16).take 8) = b := by simpa using hc
  rw [elementOf, word_ofLimbs, beWord_slice b 16 (by omega), beWord_slice b 8 (by omega),
    beWord_slice b 0 (by omega)]
  have h2 := congrArg beNat hc'
  rw [beNat_append, beNat_append] at h2
  simp only [List.length_append, List.length_take, List.length_drop, hb] at h2
  rw [← h2, List.drop_zero]
  norm_num
  ring

/-- **Every well-formed calldata is a proof's** (the tests' `parse` inverts `quotient.rs`'s `calldata`). -/
theorem calldata_surjective {cd : List UInt8} (h : WellFormed cd) :
    ∃ stmt p frame, calldata stmt p frame = some cd := by
  obtain ⟨hlen, hsel⟩ := h
  have hl : cd.length = 461 := by rw [hlen]; rfl
  let y : Vector UInt8 32 := ⟨((cd.drop 4).take 32).toArray, by simp; omega⟩
  let rt : Vector UInt8 32 := ⟨((cd.drop 36).take 32).toArray, by simp; omega⟩
  let R : ℕ → Digest := fun j => digestOf ((cd.drop (68 + 32 * j)).take 32)
  let X : ℕ → E := fun i => elementOf ((cd.drop (196 + 24 * i)).take 24)
  let p : ReductionProof := ⟨⟨rootHalves (R 0), X 0⟩, ⟨rootHalves (R 1), X 1⟩, ⟨rootHalves (R 2), X 2⟩,
    ⟨rootHalves (R 3), X 3⟩, #v[X 4, X 5, X 6, X 7], X 8, X 9, X 10⟩
  refine ⟨⟨y, rt⟩, p, cd.getD 460 0, ?_⟩
  have hR : ∀ j, j < 4 → digestBytes (R j) = (cd.drop (68 + 32 * j)).take 32 := fun j hj =>
    digestBytes_lanes _ (by simp; omega)
  have hX : ∀ i, i < 11 → elementBytes (X i) = (cd.drop (196 + 24 * i)).take 24 := fun i hi =>
    elementBytes_elementOf _ (by simp; omega)
  have hroots : [R 0, R 1, R 2, R 3].flatMap digestBytes = (cd.drop 68).take 128 := by
    have hc := chunks 32 4 ((cd.drop 68).take 128) (by simp; omega)
    rw [← hc]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_append, List.append_nil]
    rw [slice_sub _ _ _ _ _ (by norm_num), slice_sub _ _ _ _ _ (by norm_num),
      slice_sub _ _ _ _ _ (by norm_num), slice_sub _ _ _ _ _ (by norm_num),
      hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num), hR 3 (by norm_num)]
    simp only [List.append_assoc]
  have hsc : scalarsOf p = (List.range 11).map X := by
    simp [scalarsOf, p, List.range_succ]
  have hscalars : (scalarsOf p).flatMap elementBytes = (cd.drop 196).take 264 := by
    have hc := chunks 24 11 ((cd.drop 196).take 264) (by simp; omega)
    rw [← hc, hsc, List.flatMap_map]
    refine List.flatMap_congr fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [hX i hi', slice_sub _ _ _ _ _ (by omega)]
  have hframe : cd.drop 460 = [cd.getD 460 0] := by
    apply List.ext_getElem (by simp; omega)
    intro k h1 h2
    have : k = 0 := by simp at h2; omega
    subst this
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 460 < cd.length by omega)]
  simp only [calldata, p, rootOfHalves_rootHalves, Option.bind_eq_bind]
  show some _ = some cd
  congr 1
  rw [hroots, hscalars, ← hframe, ← hsel]
  show cd.take 4 ++ (cd.drop 4).take 32 ++ (cd.drop 36).take 32 ++
    ((cd.drop 68).take 128 ++ ((cd.drop 196).take 264 ++ cd.drop 460)) = cd
  rw [← take_drop_append' cd 196 264, ← take_drop_append' cd 68 128, List.append_assoc, List.append_assoc,
    ← take_drop_append' cd 36 32, ← take_drop_append' cd 4 32, List.take_append_drop]

/-- **On any calldata, the contract accepts exactly the proofs the Statement's verifier accepts**: with
what the block proves of declared claim `k` the opening check `pcsOpen` with the openings `o`, the deployed
contract (the graph, the deployed Keccak-256, the circuit's commitment `index` in storage) accepts the
calldata `cd` exactly when `cd` is the calldata of a statement, a reduction proof and a frame's index such
that, with the openings `o`, `PcsQuotient.verify` (`verifyWith` at Keccak-f[1600]) accepts. -/
theorem evm_accepts_iff_exists (index : Commitment) (o : Openings) (cd : List UInt8) :
    accepts (pcsOpen o) (deployed index cd) = true ↔
      ∃ stmt p frame, calldata stmt p frame = some cd ∧ verify 22 index stmt ⟨p, o⟩ = true := by
  constructor
  · intro h
    by_cases hw : WellFormed cd
    · obtain ⟨stmt, p, frame, hcd⟩ := calldata_surjective hw
      refine ⟨stmt, p, frame, hcd, ?_⟩
      rw [← evm_accepts_eq_verify index stmt ⟨p, o⟩ frame cd hcd]
      exact h
    · rw [accepts_of_not_wellFormed _ _ hw] at h
      cases h
  · rintro ⟨stmt, p, frame, hcd, hv⟩
    rw [evm_accepts_eq_verify index stmt ⟨p, o⟩ frame cd hcd]
    exact hv

end Evm
