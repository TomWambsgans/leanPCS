-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsQuotient.Verifier
import Compose.Claims
import Compose.Rpm
import PcsQuotient.Security
import QuotientSecurity.Deployed
import Shared.SoundnessDefs

/-!
# The statement's transcript words are F4's

Byte for byte against `crates/membership/quotient/src/transcript.rs` as F4a transcribes it: a digest's bytes
(`toB_toList`), the low 192 bits read big-endian (`beWord_eq`: the statement's `beWord` is F4a's `ofBe64`), and
the challenge of a state (`challengeOf_eq`: the statement's `challengeOf` is F4's `chal` with the limbs `eLimbs`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientRpm QuotientSecurity

/-! ## Bytes -/

theorem toB_toList (d : Digest) : (Compose.toB d).toList = digestBytes d := by
  rw [Compose.toB, LeanVM.Rpm.toList_digestToRpm]
  rfl

/-! ## The challenge of a state -/

theorem shift_or_toNat (a : UInt64) (x : UInt8) (ha : a.toNat < 2 ^ 56) :
    ((a <<< 8) ||| x.toUInt64).toNat = x.toNat + 256 * a.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [h8, UInt8.toNat_toUInt64]
  have hlt : a.toNat <<< 8 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [Nat.mod_eq_of_lt hlt, ← Nat.shiftLeft_add_eq_or_of_lt (by have := x.toNat_lt; omega),
    Nat.shiftLeft_eq]
  omega

theorem foldl_shift_or_toNat : ∀ (l : List UInt8) (a : UInt64), l.length ≤ 8 →
    a.toNat < 256 ^ (8 - l.length) →
      (l.foldl (fun (acc : UInt64) (x : UInt8) => (acc <<< 8) ||| x.toUInt64) a).toNat =
        l.foldl (fun (acc : ℕ) (x : UInt8) => x.toNat + 256 * acc) a.toNat
  | [], a, _, _ => rfl
  | x :: l, a, hl, h => by
    simp only [List.length_cons] at hl h
    simp only [List.foldl_cons]
    have hk : 8 - l.length = (8 - (l.length + 1)) + 1 := by omega
    have hP : 256 ^ (8 - (l.length + 1)) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ha : a.toNat < 2 ^ 56 := by
      have : (256 : ℕ) ^ 7 = 2 ^ 56 := by norm_num
      omega
    have hs := shift_or_toNat a x ha
    rw [foldl_shift_or_toNat l _ (by omega) ?_, hs]
    rw [hs, hk, pow_succ]
    have hx := x.toNat_lt
    omega

theorem getD_take_drop (b : List UInt8) (s k : ℕ) (hk : k < 8) :
    ((b.drop s).take 8).getD k 0 = b.getD (s + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, List.getElem?_drop]

/-- **The low 192 bits read big-endian**: the statement's `beWord` of eight bytes is F4a's `ofBe64`. -/
theorem beWord_eq (b : List UInt8) (s : ℕ) (h : s + 8 ≤ b.length) :
    PcsQuotient.Transcript.beWord b s = ofBe64 (b.drop s) := by
  set l := (b.drop s).take 8 with hl
  have hlen : l.length = 8 := by simp [hl]; omega
  have hmap : (List.range 8).map (fun k => b.getD (s + k) 0) = l := by
    rw [← range_map_getD l hlen]
    refine List.map_congr_left fun k hk => ?_
    rw [getD_take_drop b s k (List.mem_range.mp hk)]
  have hL : PcsQuotient.Transcript.beWord b s =
      l.foldl (fun (acc : UInt64) (x : UInt8) => (acc <<< 8) ||| x.toUInt64) 0 := by
    rw [← hmap, List.foldl_map]
    rfl
  have hR : ofBe64 (b.drop s) =
      UInt64.ofNat (l.foldl (fun (acc : ℕ) (x : UInt8) => x.toNat + 256 * acc) 0) := by
    have hrev : (List.range 8).map (fun i => l.reverse.getD i 0) = l.reverse :=
      range_map_getD l.reverse (by simp [hlen])
    rw [ofBe64, ← hl, LeanVM.Rpm.bytesLane]
    refine congrArg UInt64.ofNat ?_
    rw [← List.foldr_reverse]
    conv_rhs => rw [← hrev]
    rw [List.foldr_map]
  rw [hL, hR]
  have hN := foldl_shift_or_toNat l 0 (by omega) (by simp [hlen])
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0] at hN
  refine UInt64.toNat_inj.mp ?_
  rw [hN, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (hN ▸ UInt64.toNat_lt _)]

/-- **The challenge of a state** (`Chain::sample`): the statement's `challengeOf` is F4's `chal` with
the limbs `eLimbs`, on the state's 32 bytes. -/
theorem challengeOf_eq (st : Digest) :
    PcsQuotient.Transcript.challengeOf st = Soundness.eLimbs.symm (stateLimbs (Compose.toB st)) := by
  have hlen : (digestBytes st).length = 32 := by
    simp [digestBytes, LeanVM.Rpm.wordBytes_len, List.length_flatMap]
  simp only [PcsQuotient.Transcript.challengeOf, stateLimbs, wordLimbs, toB_toList,
    beWord_eq _ _ (by omega : 24 + 8 ≤ (digestBytes st).length),
    beWord_eq _ _ (by omega : 16 + 8 ≤ (digestBytes st).length),
    beWord_eq _ _ (by omega : 8 + 8 ≤ (digestBytes st).length)]
  rfl

end Bridge

/-- info: 'Bridge.toB_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.toB_toList

/-- info: 'Bridge.beWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.beWord_eq

/-- info: 'Bridge.challengeOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.challengeOf_eq
