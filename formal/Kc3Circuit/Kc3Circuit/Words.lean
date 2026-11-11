-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- `shift_or_toNat`, `foldl_shift_or_toNat` are this repository's `formal/EndToEnd/Bridge/Chain.lean`'s, copied.
import Kc3Circuit.Secret
import Field.F192

/-!
# Bits in `E`, and the packed words

* `bE b`: a bit as an element of `E`; the gate on bits is the gate over `E` on bits (`gate_bE`), and a value `v`
  with `v + v + v + v v = 0` (an input row's gate) is a bit (`bit_of_input`);
* **the packing** (`packVal_eq`): `Σ_{t < 64} b_t x^t`, `x` the generator `2` of `K`, is the word whose bits are the
  `b_t` (`Primitives.F64.sum_testBit`): the packed word is the number its bits spell;
* `beWord_testBit`: bit `t` of the big-endian word of eight bytes is bit `t % 8` of byte `7 − t / 8`.
-/

set_option linter.unusedSectionVars false

namespace Kc3Words

open LeanVM.Parameters

/-- A bit as an element of `E`. -/
def bE (b : Bool) : E := if b then 1 else 0

theorem two_eq_zero : (2 : E) = 0 := CharTwo.two_eq_zero

theorem add_self (a : E) : a + a = 0 := CharTwo.add_self_eq_zero a

/-- **The gate on bits, over `E`**: `Y + C + X·C` of three bits is the bit `Y ⊕ (C ∧ ¬X)`. -/
theorem gate_bE (x y c : Bool) : bE y + bE c + bE x * bE c = bE (PcsQuotient.gateBits x y c) := by
  cases x <;> cases y <;> cases c <;> simp [bE, PcsQuotient.gateBits, add_self]

/-- **An input row's value is a bit**: `v + v + v + v·v = 0` in characteristic two is `v (1 + v) = 0`. -/
theorem bit_of_input (a : E) (h : a + a + a + a * a = 0) : a = 0 ∨ a = 1 := by
  have h' : a * (a + 1) = 0 := by linear_combination h - a * two_eq_zero
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    have : a = -1 := eq_neg_of_add_eq_zero_left h1
    rw [this, CharTwo.neg_eq]

theorem bE_bit (a : E) (h : a = 0 ∨ a = 1) : a = bE (decide (a = 1)) := by
  rcases h with rfl | rfl
  · simp [bE]
  · simp [bE]

theorem bE_inj {a b : Bool} (h : bE a = bE b) : a = b := by
  cases a <;> cases b <;> simp_all [bE]

theorem decide_bE (b : Bool) : decide (bE b = 1) = b := by
  cases b <;> simp [bE]

/-! ## Packing -/

/-- `x`, the generator `2` of `K`, in `E`. -/
def X2 : E := ofK (K.ofLane 2)

theorem one_add_three : (1 : E) + ofK PcsQuotient.three = X2 := by
  have h : (1 : K) + PcsQuotient.three = K.ofLane 2 := by decide
  rw [X2, ← h, show ofK ((1 : K) + PcsQuotient.three) = ofK 1 + ofK PcsQuotient.three from
    map_add (algebraMap K E) _ _, show ofK (1 : K) = 1 from map_one (algebraMap K E)]

/-- The packed value of 64 bits: `Σ_{t < 64} b_t x^t`. -/
noncomputable def packVal (b : ℕ → Bool) : E := ∑ t ∈ Finset.range 64, bE (b t) * X2 ^ t

theorem bE_mul_pow (b : Bool) (t : ℕ) :
    bE b * X2 ^ t = ofK (if b then Primitives.F64.G ^ t else 0) := by
  cases b
  · simp [bE]
  · simp only [bE, if_true, one_mul, X2]
    exact (map_pow (algebraMap K E) _ t).symm

/-- **The packed word is the number its bits spell**, as an element of `K`. -/
theorem packVal_eq (b : ℕ → Bool) :
    packVal b = ofK (Primitives.F64.ofNat (PcsCircuit.bitsToNat ((List.range 64).map b))) := by
  rw [← Primitives.F64.sum_testBit]
  unfold packVal
  simp only [bE_mul_pow]
  have hs : ∀ f : ℕ → K, ∑ x ∈ Finset.range 64, ofK (f x) = ofK (∑ x ∈ Finset.range 64, f x) :=
    fun f => (map_sum (algebraMap K E) f _).symm
  rw [hs]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun t => if b t then Primitives.F64.G ^ t else 0) 64]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [PcsCircuit.bitsToNat_testBit]
  simp [List.getD_eq_getElem?_getD, t.isLt]

theorem bitsToNat_lt64 (b : ℕ → Bool) : PcsCircuit.bitsToNat ((List.range 64).map b) < 2 ^ 64 := by
  have := PcsCircuit.bitsToNat_lt ((List.range 64).map b)
  simpa using this

/-- Two words of `K` from numbers below `2^64` are equal only if the numbers are. -/
theorem ofNat_eq_ofLane {N : ℕ} {L : UInt64} (hN : N < 2 ^ 64) (h : Primitives.F64.ofNat N = K.ofLane L) :
    N = L.toNat := by
  have h' := congrArg BF64.toBitVec h
  simp only [Primitives.F64.ofNat, K.ofLane, BF64.toBitVec_ofBitVec] at h'
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at this
  rw [this]; rfl

/-! ## Big-endian words -/

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

/-- The statement's big-endian word of eight bytes, as a number. -/
theorem beWord_toNat (bytes : List UInt8) (s : ℕ) :
    (PcsQuotient.Transcript.beWord bytes s).toNat =
      (List.range 8).foldl (fun acc k => acc * 256 + (bytes.getD (s + k) 0).toNat) 0 := by
  unfold PcsQuotient.Transcript.beWord
  have e : (List.range 8).foldl (fun (acc : UInt64) k => (acc <<< 8) ||| (bytes.getD (s + k) 0).toUInt64) 0 =
      ((List.range 8).map fun k => bytes.getD (s + k) 0).foldl
        (fun (acc : UInt64) (x : UInt8) => (acc <<< 8) ||| x.toUInt64) 0 := by
    rw [List.foldl_map]
  rw [e, foldl_shift_or_toNat _ 0 (by simp) (by simp), List.foldl_map]
  congr 1
  funext acc k
  ring

/-- **Bit `t < 64` of a big-endian word** is bit `t % 8` of byte `s + 7 − t / 8`. -/
theorem beWord_testBit (bytes : List UInt8) (s t : ℕ) (ht : t < 64) :
    (PcsQuotient.Transcript.beWord bytes s).toNat.testBit t = (bytes.getD (s + (7 - t / 8)) 0).toNat.testBit (t % 8) := by
  rw [beWord_toNat, PcsCircuit.foldl_bytes_testBit (fun k => (bytes.getD (s + k) 0).toNat)
    (fun k => UInt8.toNat_lt _) 8 t (by omega)]

end Kc3Words
