-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. Byte lemmas from leanerVM `mumbai` (6175f1a0, MIT OR Apache-2.0: `common/Common/Lanes.lean`).
import PcsQuotient.Zk
import Common.Lanes

/-!
# A root's two scalars give the root back

`rootOfHalves (rootHalves r) = some r` (`rootOfHalves_rootHalves`): the membership stream carries a root as its two
128-bit halves (`rootHalves`), which the reduction reads back (`rootOfHalves`, `readCommitment`).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript

namespace PcsQuotient.EndToEnd

theorem or_step {a x : ℕ} (ha : a < 2 ^ 56) (hx : x < 256) :
    a * 256 % 18446744073709551616 ||| x = a * 256 + x := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, show (256 : ℕ) = 2 ^ 8 by rfl,
    LeanVM.Rpm.or_mul_two_pow _ (by omega)]
  ring

theorem beWord_eq_bytesLane (b : List UInt8) (k : ℕ) :
    beWord b k = LeanVM.Rpm.bytesLane (((List.range 8).map fun i ↦ b.getD (k + i) 0).reverse) := by
  apply UInt64.toNat_inj.mp
  simp only [beWord, LeanVM.Rpm.bytesLane, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.foldr_cons, List.foldr_nil,
    UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.toNat_ofNat,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero, Nat.shiftLeft_eq]
  have hb : ∀ i, (b.getD (k + i) 0).toNat < 256 := fun i ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  generalize (b.getD (k + 0) 0).toNat = x0 at *
  generalize (b.getD (k + 1) 0).toNat = x1 at *
  generalize (b.getD (k + 2) 0).toNat = x2 at *
  generalize (b.getD (k + 3) 0).toNat = x3 at *
  generalize (b.getD (k + 4) 0).toNat = x4 at *
  generalize (b.getD (k + 5) 0).toNat = x5 at *
  generalize (b.getD (k + 6) 0).toNat = x6 at *
  generalize (b.getD (k + 7) 0).toNat = x7 at *
  norm_num
  rw [or_step (by omega) h1, or_step (by omega) h2, or_step (by omega) h3, or_step (by omega) h4,
    or_step (by omega) h5, or_step (by omega) h6, or_step (by omega) h7, Nat.mod_eq_of_lt (by omega)]
  ring

theorem beBytes_beWord (b : List UInt8) (k : ℕ) :
    beBytes (beWord b k) = (List.range 8).map fun i ↦ b.getD (k + i) 0 := by
  rw [beWord_eq_bytesLane, beBytes, LeanVM.Rpm.wordBytes_bytesLane]
  simp [List.range_succ]

theorem digestBytes_windows (r : Digest) :
    ((List.range 8).map fun i ↦ (digestBytes r).getD (0 + i) 0) ++
        ((List.range 8).map fun i ↦ (digestBytes r).getD (8 + i) 0) ++
        ((List.range 8).map fun i ↦ (digestBytes r).getD (16 + i) 0) ++
        ((List.range 8).map fun i ↦ (digestBytes r).getD (24 + i) 0) = digestBytes r := by
  obtain ⟨⟨l⟩, hl⟩ := r
  match l, hl with
  | [w0, w1, w2, w3], _ => simp [digestBytes, wordBytes, List.range_succ]

/-- **A root's halves give the root back.** -/
theorem rootOfHalves_rootHalves (r : Digest) : rootOfHalves (rootHalves r) = some r := by
  have hb : (Digest.toBytes r).toList = digestBytes r := rfl
  have l0 : ∀ a b c : K, (E.ofLimbs a b c).limb 0 = a := fun _ _ _ ↦ rfl
  have l1 : ∀ a b c : K, (E.ofLimbs a b c).limb 1 = b := fun _ _ _ ↦ rfl
  have l2 : ∀ a b c : K, (E.ofLimbs a b c).limb 2 = c := fun _ _ _ ↦ rfl
  have hl : ∀ w : UInt64, (K.ofLane w).lane = w := fun _ ↦ rfl
  have key : beBytes (beWord (digestBytes r) 0) ++ beBytes (beWord (digestBytes r) 8) ++
      beBytes (beWord (digestBytes r) 16) ++ beBytes (beWord (digestBytes r) 24) = digestBytes r := by
    rw [beBytes_beWord, beBytes_beWord, beBytes_beWord, beBytes_beWord]
    exact digestBytes_windows r
  have hlanes : ∀ i (hi : i < 4), leLane (digestBytes r) i = r[i] := fun i hi ↦ by
    rw [show digestBytes r = LeanVM.Rpm.lanesBytes r.toList from rfl,
      LeanVM.Rpm.leLane_lanesBytes _ _ (by simpa using hi)]
    simp
  simp only [rootOfHalves, rootHalves, halves, hb, l0, l1, l2, hl, and_self, ite_true, Nat.reduceMul,
    Nat.reduceAdd, key, Option.some.injEq]
  apply Vector.ext
  intro i hi
  rw [← hlanes i hi]
  interval_cases i <;> rfl

end PcsQuotient.EndToEnd
