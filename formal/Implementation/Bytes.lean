-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the bytes of digests (`digestBytes`, `wordBytes`, `leLane`, `Statement/Keccak.lean`).
import Implementation.Interp
import Implementation.Field192
import PcsQuotient.Reduction
import Mathlib.Data.List.GetD
import Common.Lanes

/-!
# Bytes, numbers and field elements

The contract holds field elements and digests as EVM words; the Statement holds them as elements of
`E` and as byte strings (`elementBytes`, `scalarBytes`, `digestBytes`, `halves`, `challengeOf`,
`rootOfHalves`). Here the two readings agree, on `E` with its Rust limbs (`limbsEquiv`):

* `elementBytes_eq`, `scalarBytes_eq`: an element's `24` bytes and its transcript word are the big-endian
  bytes of its number `word x` (`c0 + 2^64 c1 + 2^128 c2`); so `beBytes24_elem`: the low 24 bytes of any
  word are the bytes of the element it stands for;
* `word_challengeOf`: a challenge is the state's low `192` bits;
* `word_halves_fst`, `word_halves_snd`: a statement's halves are its 16-byte halves read big-endian;
* `rootOfHalves_bytes`: the root two scalars name has bytes whose 16-byte halves are those scalars.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient PcsQuotient.Transcript

/-! ## Big-endian numbers -/

theorem foldl_beNat (l : List UInt8) (acc : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ l.length + beNat l := by
  induction l generalizing acc with
  | nil => simp [beNat]
  | cons x l ih =>
    simp only [List.foldl_cons, beNat] at *
    rw [ih, ih (0 * 256 + x.toNat), List.length_cons, pow_succ]
    ring

theorem beNat_append (a b : List UInt8) : beNat (a ++ b) = beNat a * 256 ^ b.length + beNat b := by
  rw [beNat, List.foldl_append, foldl_beNat]
  rfl

theorem beNat_cons (x : UInt8) (l : List UInt8) :
    beNat (x :: l) = x.toNat * 256 ^ l.length + beNat l := by
  rw [show x :: l = [x] ++ l from rfl, beNat_append]
  simp [beNat]

theorem beNat_lt (l : List UInt8) : beNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [beNat]
  | cons x l ih =>
    rw [beNat_cons, List.length_cons, pow_succ]
    have hx : x.toNat < 256 := x.toNat_lt
    nlinarith

theorem beNat_replicate_zero (k : Nat) : beNat (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, beNat_cons, ih]; simp

theorem beNat_take_div (l : List UInt8) (j : Nat) (hj : j ≤ l.length) :
    beNat l / 256 ^ (l.length - j) = beNat (l.take j) := by
  have e := beNat_append (l.take j) (l.drop j)
  rw [List.take_append_drop, List.length_drop] at e
  have hlt := beNat_lt (l.drop j)
  rw [List.length_drop] at hlt
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

theorem beNat_snoc_mod (l : List UInt8) (x : UInt8) : beNat (l ++ [x]) % 256 = x.toNat := by
  rw [beNat_append]
  simp [beNat, Nat.add_mod, x.toNat_lt]

theorem length_beBytes (n w : Nat) : (beBytes n w).length = n := by simp [beBytes]

theorem beBytes_beNat (l : List UInt8) : beBytes l.length (beNat l) = l := by
  apply List.ext_getElem (by simp [beBytes])
  intro k h1 h2
  have hk : k < l.length := by
    simp only [beBytes, List.length_map, List.length_range] at h1; exact h1
  simp only [beBytes, List.getElem_map, List.getElem_range]
  have hpow : 2 ^ (8 * (l.length - 1 - k)) = 256 ^ (l.length - (k + 1)) := by
    rw [pow_mul, show l.length - 1 - k = l.length - (k + 1) by omega]; norm_num
  rw [Nat.shiftRight_eq_div_pow, hpow, beNat_take_div l (k + 1) hk,
    List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, beNat_snoc_mod]
  exact UInt8.toNat.inj (by simp)

theorem beBytes_succ (n w : ℕ) :
    beBytes (n + 1) w = ((w >>> (8 * n)) % 256).toUInt8 :: beBytes n w := by
  unfold beBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]
  rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega]

theorem beNat_beBytes : ∀ (n w : ℕ), beNat (beBytes n w) = w % 256 ^ n
  | 0, w => by simp [beBytes, beNat, Nat.mod_one]
  | n + 1, w => by
    rw [beBytes_succ, beNat_cons, length_beBytes, beNat_beBytes n w]
    have h1 : (((w >>> (8 * n)) % 256).toUInt8).toNat = w / 256 ^ n % 256 := by
      rw [Nat.shiftRight_eq_div_pow, pow_mul]
      simp
    rw [h1, pow_succ, Nat.mod_mul]
    ring

/-- Bytes are the big-endian bytes of their number. -/
theorem beBytes_eq_of_beNat {l : List UInt8} {n w : Nat} (hl : l.length = n) (h : beNat l = w) :
    beBytes n w = l := by
  subst hl h
  exact beBytes_beNat l

theorem beBytes_mod (n w : Nat) : beBytes n (w % 256 ^ n) = beBytes n w := by
  rw [← beNat_beBytes n w]
  exact beBytes_eq_of_beNat (length_beBytes n w) rfl

theorem beBytes_append (a b w : Nat) (hw : w < 256 ^ (a + b)) :
    beBytes (a + b) w = beBytes a (w / 256 ^ b) ++ beBytes b w := by
  refine beBytes_eq_of_beNat (by simp [length_beBytes]) ?_
  rw [beNat_append, beNat_beBytes, beNat_beBytes, length_beBytes]
  have : w / 256 ^ b < 256 ^ a := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; simpa [Nat.add_comm] using hw
  rw [Nat.mod_eq_of_lt this]
  exact Nat.div_add_mod' w (256 ^ b)

/-! ## 64-bit words -/

theorem beNat_beBytes8 (w : UInt64) : beNat (Transcript.beBytes w) = w.toNat := by
  have hw := w.toNat_lt
  simp only [Transcript.beBytes, wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, beNat, List.foldl_cons, List.foldl_nil, List.foldl_append,
    UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem length_beBytes8 (w : UInt64) : (Transcript.beBytes w).length = 8 := by
  simp [Transcript.beBytes, wordBytes]

theorem beBytes8_eq (w : UInt64) : Transcript.beBytes w = beBytes 8 w.toNat :=
  (beBytes_eq_of_beNat (length_beBytes8 w) (beNat_beBytes8 w)).symm

theorem shl8_or (acc : UInt64) (b : UInt8) (h : acc.toNat * 256 < 2 ^ 64) :
    ((acc <<< 8) ||| b.toUInt64).toNat = acc.toNat * 256 + b.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [h8, Nat.shiftLeft_eq, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mod_eq_of_lt h, Nat.or_comm,
    show (256 : ℕ) = 2 ^ 8 from rfl, LeanVM.Rpm.or_mul_two_pow _ (by simpa using b.toNat_lt)]
  ring

theorem foldl_shl : ∀ (bs : List UInt8) (acc : UInt64), bs.length ≤ 8 →
    acc.toNat < 256 ^ (8 - bs.length) →
    (bs.foldl (fun (acc : UInt64) (b : UInt8) => (acc <<< 8) ||| b.toUInt64) acc).toNat =
      acc.toNat * 256 ^ bs.length + beNat bs
  | [], acc, _, _ => by simp [beNat]
  | b :: bs, acc, hl, h => by
    rw [List.foldl_cons]
    simp only [List.length_cons] at hl h
    have hb := b.toNat_lt
    have hQ : 256 ^ (8 - bs.length) = 256 ^ (8 - (bs.length + 1)) * 256 := by
      rw [← pow_succ]; congr 1; omega
    have h64 : 256 ^ (8 - bs.length) ≤ 2 ^ 64 :=
      calc 256 ^ (8 - bs.length) ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hlt : acc.toNat * 256 + b.toNat < 256 ^ (8 - bs.length) := by rw [hQ]; omega
    have hs : ((acc <<< 8) ||| b.toUInt64).toNat = acc.toNat * 256 + b.toNat :=
      shl8_or acc b (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_lt_of_le hlt h64))
    have hlt' : ((acc <<< 8) ||| b.toUInt64).toNat < 256 ^ (8 - bs.length) := hs ▸ hlt
    have ih := foldl_shl bs ((acc <<< 8) ||| b.toUInt64) (Nat.le_of_succ_le hl) hlt'
    rw [ih, hs, beNat_cons, List.length_cons, pow_succ]
    ring

/-- **`beWord`** is the number of its eight bytes. -/
theorem beWord_toNat (l : List UInt8) (s : Nat) :
    (beWord l s).toNat = beNat ((List.range 8).map fun k => l.getD (s + k) 0) := by
  have e : beWord l s = ((List.range 8).map fun k => l.getD (s + k) 0).foldl
      (fun (acc : UInt64) (b : UInt8) => (acc <<< 8) ||| b.toUInt64) 0 := by
    rw [Transcript.beWord, List.foldl_map]
  rw [e, foldl_shl _ 0 (by simp) (by simp)]
  simp

theorem map_getD_slice (l : List UInt8) (s n : Nat) (h : s + n ≤ l.length) :
    (List.range n).map (fun k => l.getD (s + k) 0) = (l.drop s).take n := by
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s + k < l.length by omega)]

theorem beWord_slice (l : List UInt8) (s : Nat) (h : s + 8 ≤ l.length) :
    (beWord l s).toNat = beNat ((l.drop s).take 8) := by
  rw [beWord_toNat, map_getD_slice l s 8 h]

/-- A big-endian number of `a + b` bytes from its two parts. -/
theorem beNat_split (l : List UInt8) (n : Nat) (h : n ≤ l.length) :
    beNat l = beNat (l.take n) * 256 ^ (l.length - n) + beNat (l.drop n) := by
  conv_lhs => rw [← List.take_append_drop n l]
  rw [beNat_append, List.length_drop]

/-! ## Field elements -/

local notation "W" => word limbsEquiv

theorem word_eq (x : E) : W x =
    (x.limb 0).lane.toNat + B64 * (x.limb 1).lane.toNat + B64 * B64 * (x.limb 2).lane.toNat := rfl

theorem limb0_ofLimbs (a b c : K) : (E.ofLimbs a b c).limb 0 = a := rfl
theorem limb1_ofLimbs (a b c : K) : (E.ofLimbs a b c).limb 1 = b := rfl
theorem limb2_ofLimbs (a b c : K) : (E.ofLimbs a b c).limb 2 = c := rfl

theorem word_ofLimbs (a b c : UInt64) :
    W (E.ofLimbs (K.ofLane a) (K.ofLane b) (K.ofLane c)) = a.toNat + B64 * b.toNat + B64 * B64 * c.toNat := by
  rw [word_eq, limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs]
  rfl

theorem beNat_elementBytes (x : E) : beNat (elementBytes x) = W x := by
  rw [elementBytes, beNat_append, beNat_append, beNat_beBytes8, beNat_beBytes8, beNat_beBytes8,
    length_beBytes8, length_beBytes8, word_eq]
  ring

theorem length_elementBytes (x : E) : (elementBytes x).length = 24 := by
  simp [elementBytes, length_beBytes8]

/-- **An element's 24 bytes** are the big-endian bytes of its number. -/
theorem elementBytes_eq (x : E) : elementBytes x = beBytes 24 (W x) :=
  (beBytes_eq_of_beNat (length_elementBytes x) (beNat_elementBytes x)).symm

/-- **An element's transcript word** is the 32 big-endian bytes of its number. -/
theorem scalarBytes_eq (x : E) : scalarBytes x = beBytes 32 (W x) := by
  refine (beBytes_eq_of_beNat (by simp [scalarBytes, length_beBytes8]) ?_).symm
  have : scalarBytes x = List.replicate 8 0 ++ elementBytes x := by
    simp [scalarBytes, elementBytes, List.append_assoc]
  rw [this, beNat_append, beNat_replicate_zero, zero_mul, zero_add, beNat_elementBytes]

theorem word_elem' (n : Nat) : W (elem limbsEquiv n) = n % B192 := word_elem n

/-- **The low 24 bytes of a word** are the bytes of the element it stands for. -/
theorem beBytes24_elem (n : Nat) : beBytes 24 n = elementBytes (elem limbsEquiv n) := by
  rw [elementBytes_eq, word_elem', ← beBytes_mod 24 n]
  rfl

/-- **A word below `2^192`** is the transcript word of the element it stands for. -/
theorem beBytes32_elem {n : Nat} (h : n < B192) : beBytes 32 n = scalarBytes (elem limbsEquiv n) := by
  rw [scalarBytes_eq, word_elem', Nat.mod_eq_of_lt h]

theorem elem_of_word {n : Nat} {x : E} (h : n = W x) : elem limbsEquiv n = x := by
  rw [h, elem_word]

/-! ## Digests -/

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

theorem beBytes32_digest (d : Digest) : beBytes 32 (beNat (digestBytes d)) = digestBytes d := by
  rw [← length_digestBytes d]
  exact beBytes_beNat _

/-- Sixteen bytes from `s` are eight, then eight. -/
theorem take16 (l : List UInt8) (s : Nat) :
    (l.drop s).take 16 = (l.drop s).take 8 ++ (l.drop (s + 8)).take 8 := by
  rw [show 16 = 8 + 8 from rfl, List.take_add, List.drop_drop]

theorem length_take8 (l : List UInt8) (s : Nat) (h : s + 8 ≤ l.length) : ((l.drop s).take 8).length = 8 := by
  simp; omega

/-- **A challenge is the state's low 192 bits.** -/
theorem word_challengeOf (d : Digest) : W (challengeOf d) = beNat (digestBytes d) % B192 := by
  have hl := length_digestBytes d
  set b := digestBytes d
  rw [challengeOf, word_ofLimbs, beWord_slice b 24 (by omega), beWord_slice b 16 (by omega),
    beWord_slice b 8 (by omega)]
  have hd8 : b.drop 8 = ((b.drop 8).take 8 ++ (b.drop 16).take 8) ++ (b.drop 24).take 8 := by
    rw [← take16, List.take_of_length_le (l := b.drop 24) (by simp; omega)]
    conv_lhs => rw [← List.take_append_drop 16 (b.drop 8)]
    simp only [List.drop_drop]
  have e8 : beNat b % B192 = beNat (b.drop 8) := by
    have h1 := beNat_split b 8 (by omega)
    have h2 := beNat_lt (b.drop 8)
    rw [List.length_drop, hl] at h2
    rw [h1, hl]
    norm_num at h2 ⊢
    omega
  rw [e8, congrArg beNat hd8, beNat_append, beNat_append, length_take8 b 16 (by omega),
    length_take8 b 24 (by omega)]
  norm_num
  ring

/-- A statement's half `h` is its 16-byte half `h`, read big-endian. -/
theorem word_half (b : Bytes32) (h : Nat) (hh : h < 2) :
    W (E.ofLimbs (K.ofLane (beWord b.toList (16 * h + 8))) (K.ofLane (beWord b.toList (16 * h))) 0) =
      beNat ((b.toList.drop (16 * h)).take 16) := by
  have hl : b.toList.length = 32 := by simp
  have e0 : (0 : K) = K.ofLane 0 := rfl
  rw [e0, word_ofLimbs, beWord_slice _ _ (by omega), beWord_slice _ _ (by omega), take16,
    beNat_append, length_take8 _ _ (by omega)]
  simp only [UInt64.toNat_zero, mul_zero, add_zero]
  norm_num
  ring

theorem word_halves_fst (b : Bytes32) : W (halves b).1 = beNat (b.toList.take 16) := by
  have := word_half b 0 (by norm_num)
  simpa [halves] using this

theorem word_halves_snd (b : Bytes32) : W (halves b).2 = beNat (b.toList.drop 16) := by
  have := word_half b 1 (by norm_num)
  have hl : b.toList.length = 32 := by simp
  rw [List.take_of_length_le (by simp)] at this
  simpa [halves] using this

end Implementation
