/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

The binding of version 1's commitment with the out-of-domain point read coordinate by coordinate off
Keccak-256 (`ood_point`, `crates/pcs_claim/src/lib.rs`; `oodPointWith`): the adversary has only
Keccak-256 and Keccak-f[1600], each root's list is extracted from the final Keccak-256 answers
(leanerVM `mumbai`'s `extract`, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
Apache-2.0: `lean_vm/LeanVM/Protocol/Compile/Rom/Extract.lean`), proved with mumbai's budgeted
potential bound (`lean_vm/LeanVM/Protocol/ToVCVio/Rom/Potential.lean`). The bytes of a lane
(`or_mul_two_pow`, `bytes8_or`, `bytesLane`, `leLane_eq_bytesLane`, `wordBytes_bytesLane`) are
copied from leanerVM `common/Common/Lanes.lean` (same commit), which this package does not import.
-/
import WhirBridge.PcsBindingRom

/-!
# Binding with the point read off Keccak-256

`ood_binding_rom` gives the out-of-domain point of a root in one query to a separate oracle. The
deployed point is Keccak-256's: coordinate `j` is the element the low 24 bytes of the answer at
`oodInput n root j` encode (`oodPointWith`). Here the adversary holds Keccak-256 and Keccak-f[1600]
only (`KeccakCalls`), and a root's point exists once its `n` coordinates are asked (`oodPointOf`).

The argument is a potential over the cache. A cache is good (`GoodC`) when, for every root and every
two distinct members of its list (read off the cache), the difference of their polynomials does not
vanish identically on the points consistent with the root's coordinates asked so far (`Cons`). A
good cache with all `n` coordinates of a root asked separates the root's list at its point
(`bindBadC_imp`). A fresh Keccak-256 answer `u` at `x` leaves a good cache good unless

* `u` is a root some coordinate of which is asked (or `x` is one), or a child digest of an
  answered input or of `x` (then the root's list may change; otherwise `extract_stable` freezes
  it): at most `2 k + 2` of the `2^256` answers for a cache of `k` entries (`keyDigestsC`);
* `x` is coordinate `j₀` of a root `r₀` and `u`'s coordinate is, for some pair of the list, the
  one value at which the difference, affine in coordinate `j₀` (`aff_colEval`), vanishes on the new
  consistent points (`pairBad_unique`): at most `C(L, 2)` values of `E` (`card_badVal`), each the
  coordinate of `2^64` digests (`card_coordOf_mem`).

* **`ood_binding_coords`**: a computation of at most `Q` queries to Keccak-256 and Keccak-f[1600]
  ends with some root whose `n` coordinates it asked and whose list, extracted from the final
  answers, is not separated at the point they give, with probability at most
  `Q · C(L, 2) / 2^192 + Q (Q + 1) / 2^256`, `L = listMax`;
* `δc_le`, `δc_27`: `C(L, 2) / 2^192 ≤ 2^-160` at version 1's shapes, `≤ 2^-168` at `n = 27`.
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

variable {n : ℕ}

/-! ## The point read off the cache -/

/-- The coordinate an answer gives: the element its low 24 bytes encode. -/
def coordOf (d : Digest) : E := elemOf ((digestBytes d).drop 8)

/-- The Keccak-256 answers of a cache of `KeccakCalls`. -/
def hOfC (c : KeccakCalls.QueryCache) : Bytes → Option Digest := fun x ↦ c (.inl x)

/-- **The point read off a cache's Keccak-256 answers**, if all `n` coordinates were asked. -/
def oodPointOf (Hc : Bytes → Option Digest) (n : ℕ) (r : Digest) : Option (Vector E n) :=
  if h : ∀ j : Fin n, (Hc (oodInput n r j)).isSome then
    some (Vector.ofFn fun j ↦ coordOf ((Hc (oodInput n r j)).get (h j)))
  else none

/-- With every answer present, the point is the deployed one, `oodPointWith`. -/
theorem oodPointOf_total (h : Bytes → Digest) (r : Digest) :
    oodPointOf (fun x ↦ some (h x)) n r = some (oodPointWith h n r) := by
  simp [oodPointOf, oodPointWith, coordOf]

/-- **The event**: some root whose `n` coordinates were all asked has a list (read off the final
answers) not separated at its point. -/
def BindBadC (n : ℕ) (c : KeccakCalls.QueryCache) : Prop :=
  ∃ r z, oodPointOf (fun x ↦ c (.inl x)) n r = some z ∧
    ¬ SepAt (rootList (n := n) (fun x ↦ c (.inl x)) r) z

/-! ## Encodings -/

theorem oodInput_length (r : Digest) (j : ℕ) : (oodInput n r j).length = 46 := by
  simp [oodInput, oodTag, digestBytes_length']

theorem oodInput_inj {r r' : Digest} {j j' : ℕ} (h : oodInput n r j = oodInput n r' j') :
    r = r' ∧ j.toUInt8 = j'.toUInt8 := by
  unfold oodInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [oodTag, digestBytes_length'])
  obtain ⟨-, h3⟩ := List.append_inj h1 (by simp [oodTag])
  exact ⟨digestBytes_injective h3, by simpa using h2⟩

theorem oodInput_inj_fin (hn : n ≤ 256) {r r' : Digest} {j j' : Fin n}
    (h : oodInput n r j = oodInput n r' j') : r = r' ∧ j = j' := by
  obtain ⟨h1, h2⟩ := oodInput_inj h
  refine ⟨h1, Fin.ext ?_⟩
  have := congrArg UInt8.toNat h2
  simp at this
  have hj := j.isLt
  have hj' := j'.isLt
  omega

theorem emb_length {y : Bytes} {d : Digest} (h : Emb y d) : y.length = 64 := by
  obtain ⟨s, h | h⟩ := h <;> subst h <;> simp [digestBytes_length']

theorem not_emb_oodInput (r d : Digest) (j : ℕ) : ¬ Emb (oodInput n r j) d := fun h ↦ by
  have := emb_length h
  rw [oodInput_length] at this
  omega

/-! ## A coordinate is the element of its answer's low 24 bytes: `2^64` answers each -/

private theorem or_mul_two_pow {a n : ℕ} (b : ℕ) (ha : a < 2 ^ n) :
    a ||| b * 2 ^ n = a + b * 2 ^ n := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha]; ring

private theorem bytes8_or {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} (h0 : x0 < 256) (h1 : x1 < 256)
    (h2 : x2 < 256) (h3 : x3 < 256) (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256)
    (h7 : x7 < 256) :
    (x0 % 18446744073709551616 ||| x1 * 256 % 18446744073709551616 |||
      x2 * 65536 % 18446744073709551616 ||| x3 * 16777216 % 18446744073709551616 |||
      x4 * 4294967296 % 18446744073709551616 ||| x5 * 1099511627776 % 18446744073709551616 |||
      x6 * 281474976710656 % 18446744073709551616 |||
      x7 * 72057594037927936 % 18446744073709551616) =
    (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7))))))) %
      18446744073709551616 := by
  rw [Nat.mod_eq_of_lt (by omega : x0 < _), Nat.mod_eq_of_lt (by omega : x1 * 256 < _),
    Nat.mod_eq_of_lt (by omega : x2 * 65536 < _), Nat.mod_eq_of_lt (by omega : x3 * 16777216 < _),
    Nat.mod_eq_of_lt (by omega : x4 * 4294967296 < _),
    Nat.mod_eq_of_lt (by omega : x5 * 1099511627776 < _),
    Nat.mod_eq_of_lt (by omega : x6 * 281474976710656 < _),
    Nat.mod_eq_of_lt (by omega : x7 * 72057594037927936 < _), Nat.mod_eq_of_lt (by omega)]
  rw [show (256 : ℕ) = 2 ^ 8 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (65536 : ℕ) = 2 ^ 16 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (16777216 : ℕ) = 2 ^ 24 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (4294967296 : ℕ) = 2 ^ 32 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (281474976710656 : ℕ) = 2 ^ 48 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (72057594037927936 : ℕ) = 2 ^ 56 by rfl, or_mul_two_pow _ (by omega)]
  ring

/-- The 64-bit word of eight little-endian bytes. -/
private def bytesLane (b : List UInt8) : UInt64 :=
  UInt64.ofNat ((List.range 8).foldr (fun i acc ↦ (b.getD i 0).toNat + 256 * acc) 0)

private theorem leLane_eq_bytesLane (bs : List UInt8) (i : ℕ) :
    leLane bs i = bytesLane (bs.drop (8 * i)) := by
  apply UInt64.toNat_inj.mp
  have hb : ∀ k, (bs[8 * i + k]?.getD 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have e : ∀ k, (bs.drop (8 * i)).getD k 0 = bs.getD (8 * i + k) 0 := fun k ↦ by
    simp [List.getD_eq_getElem?_getD]
  simp only [leLane, bytesLane, e, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldr_append, List.foldl_cons, List.foldl_nil, List.foldr_cons,
    List.foldr_nil, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    List.getD_eq_getElem?_getD, UInt64.zero_or]
  have h0 := hb 0
  simp only [Nat.add_zero] at h0
  have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
  have h6 := hb 6; have h7 := hb 7
  generalize (bs[8 * i]?.getD 0).toNat = x0 at *
  generalize (bs[8 * i + 1]?.getD 0).toNat = x1 at *
  generalize (bs[8 * i + 2]?.getD 0).toNat = x2 at *
  generalize (bs[8 * i + 3]?.getD 0).toNat = x3 at *
  generalize (bs[8 * i + 4]?.getD 0).toNat = x4 at *
  generalize (bs[8 * i + 5]?.getD 0).toNat = x5 at *
  generalize (bs[8 * i + 6]?.getD 0).toNat = x6 at *
  generalize (bs[8 * i + 7]?.getD 0).toNat = x7 at *
  simp only [Nat.shiftLeft_eq, Nat.mul_zero, Nat.add_zero]
  norm_num
  have := bytes8_or h0 h1 h2 h3 h4 h5 h6 h7
  rwa [Nat.mod_eq_of_lt (by omega : x0 < _), Nat.mod_eq_of_lt (by omega : x1 * 256 < _),
    Nat.mod_eq_of_lt (by omega : x2 * 65536 < _), Nat.mod_eq_of_lt (by omega : x3 * 16777216 < _),
    Nat.mod_eq_of_lt (by omega : x4 * 4294967296 < _),
    Nat.mod_eq_of_lt (by omega : x5 * 1099511627776 < _),
    Nat.mod_eq_of_lt (by omega : x6 * 281474976710656 < _),
    Nat.mod_eq_of_lt (by omega : x7 * 72057594037927936 < _), Nat.mod_eq_of_lt (by omega)] at this

private theorem wordBytes_bytesLane (b : List UInt8) :
    wordBytes (bytesLane b) = (List.range 8).map fun k ↦ b.getD k 0 := by
  have hb : ∀ k, (b.getD k 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [wordBytes, bytesLane, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;>
    generalize (b.getD 0 0).toNat = x0 at * <;>
    generalize (b.getD 1 0).toNat = x1 at * <;>
    generalize (b.getD 2 0).toNat = x2 at * <;>
    generalize (b.getD 3 0).toNat = x3 at * <;>
    generalize (b.getD 4 0).toNat = x4 at * <;>
    generalize (b.getD 5 0).toNat = x5 at * <;>
    generalize (b.getD 6 0).toNat = x6 at * <;>
    generalize (b.getD 7 0).toNat = x7 at * <;>
    norm_num <;> omega

/-- The lane of eight bytes gives them back. -/
theorem wordBytes_leLane_eight {b : Bytes} (hb : b.length = 8) : wordBytes (leLane b 0) = b := by
  rw [leLane_eq_bytesLane, Nat.mul_zero, List.drop_zero, wordBytes_bytesLane]
  refine List.ext_getElem (by simp [hb]) fun k h1 h2 ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem beK_wordBytes_injective {w w' : UInt64} (h : beK (wordBytes w) = beK (wordBytes w')) :
    w = w' := by
  have hl := congrArg (fun a ↦ wordBytes (K.lane a)) h
  simp only [beK, K.lane_ofLane] at hl
  rw [wordBytes_leLane_eight (by simp [wordBytes_length]),
    wordBytes_leLane_eight (by simp [wordBytes_length])] at hl
  exact wordBytes_injective (List.reverse_injective hl)

theorem elemOf_append {A B C : Bytes} (hA : A.length = 8) (hB : B.length = 8)
    (hC : C.length = 8) : elemOf (A ++ (B ++ C)) = E.ofLimbs (beK C) (beK B) (beK A) := by
  simp [elemOf, List.drop_append, List.drop_eq_nil_of_le, List.take_of_length_le, hA, hB, hC]

theorem vec4_eta (u : Digest) : u = #v[u[0], u[1], u[2], u[3]] := by
  ext i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- The coordinate of an answer: its words `1, 2, 3`, byte-reversed, are the limbs `c0, c1, c2`
from the last. -/
theorem coordOf_eq (u : Digest) :
    coordOf u = E.ofLimbs (beK (wordBytes u[3])) (beK (wordBytes u[2])) (beK (wordBytes u[1])) := by
  have h8 : (digestBytes #v[u[0], u[1], u[2], u[3]]).drop 8 =
      wordBytes u[1] ++ (wordBytes u[2] ++ wordBytes u[3]) := by
    simp only [digestBytes]
    simp [List.drop_left' (wordBytes_length _)]
  conv_lhs => rw [vec4_eta u]
  rw [coordOf, h8, elemOf_append (wordBytes_length _) (wordBytes_length _) (wordBytes_length _)]

/-- An answer is determined by its first word and its coordinate. -/
theorem eq_of_coordOf {u u' : Digest} (h : coordOf u = coordOf u') (h0 : u[0] = u'[0]) :
    u = u' := by
  rw [coordOf_eq, coordOf_eq] at h
  have e1 := congrArg (fun x : E ↦ x.limb 0) h
  have e2 := congrArg (fun x : E ↦ x.limb 1) h
  have e3 := congrArg (fun x : E ↦ x.limb 2) h
  simp only [limb_ofLimbs] at e1 e2 e3
  rw [vec4_eta u, vec4_eta u', h0, beK_wordBytes_injective e1, beK_wordBytes_injective e2,
    beK_wordBytes_injective e3]

open Classical in
/-- **At most `2^64` answers per coordinate value.** -/
theorem card_coordOf_mem (V : Finset E) :
    (Finset.univ.filter fun u : Digest ↦ coordOf u ∈ V).card ≤ V.card * 2 ^ 64 := by
  have hsub : (Finset.univ.filter fun u : Digest ↦ coordOf u ∈ V) ⊆
      V.biUnion fun e ↦ Finset.univ.filter fun u : Digest ↦ coordOf u = e := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact Finset.mem_biUnion.2 ⟨_, hu, by simp⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hfib : ∀ e, (Finset.univ.filter fun u : Digest ↦ coordOf u = e).card ≤ 2 ^ 64 := by
    intro e
    calc (Finset.univ.filter fun u : Digest ↦ coordOf u = e).card
        ≤ (Finset.univ : Finset UInt64).card := by
          refine Finset.card_le_card_of_injOn (fun u ↦ u[0]) (fun _ _ ↦ Finset.mem_univ _) ?_
          intro u hu u' hu' h0
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hu'
          exact eq_of_coordOf (hu.trans hu'.symm) h0
      _ = 2 ^ 64 := by rw [Finset.card_univ, card_uint64]
  calc ∑ e ∈ V, (Finset.univ.filter fun u : Digest ↦ coordOf u = e).card
      ≤ ∑ _e ∈ V, 2 ^ 64 := Finset.sum_le_sum fun e _ ↦ hfib e
    _ = V.card * 2 ^ 64 := by rw [Finset.sum_const, smul_eq_mul]

/-! ## A polynomial's value is affine in each coordinate -/

/-- `f` is affine. -/
def Aff (f : E → E) : Prop := ∀ t, f t = f 0 + (f 1 - f 0) * t

theorem aff_const (a : E) : Aff fun _ ↦ a := fun t ↦ by beta_reduce; ring

theorem Aff.mul_left {f : E → E} (h : Aff f) (a : E) : Aff fun t ↦ a * f t := fun t ↦ by
  simp only
  rw [h t]
  ring

theorem Aff.mul_right {f : E → E} (h : Aff f) (a : E) : Aff fun t ↦ f t * a := fun t ↦ by
  simp only
  rw [h t]
  ring

theorem Aff.sub {f g : E → E} (hf : Aff f) (hg : Aff g) : Aff fun t ↦ f t - g t := fun t ↦ by
  simp only
  rw [hf t, hg t]
  ring

theorem aff_sum {ι : Type} (s : Finset ι) (f : ι → E → E) (h : ∀ i, Aff (f i)) :
    Aff fun t ↦ ∑ i ∈ s, f i t := fun t ↦ by
  simp only
  calc ∑ i ∈ s, f i t = ∑ i ∈ s, (f i 0 + (f i 1 - f i 0) * t) :=
        Finset.sum_congr rfl fun i _ ↦ h i t
    _ = ∑ i ∈ s, f i 0 + (∑ i ∈ s, f i 1 - ∑ i ∈ s, f i 0) * t := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]

theorem foldl_mul_eq (a : E) : ∀ l : List E, l.foldl (· * ·) a = a * l.foldl (· * ·) 1
  | [] => by simp
  | y :: ys => by
    simp only [List.foldl_cons]
    rw [foldl_mul_eq (a * y) ys, foldl_mul_eq (1 * y) ys]
    ring

theorem eqEval_cons (a c : E) (l b : List E) :
    eqEval (a :: l) (c :: b) = (1 + a + c) * eqEval l b := by
  simp only [eqEval, List.zipWith_cons_cons, List.foldl_cons]
  rw [foldl_mul_eq]
  ring

theorem aff_eqEval : ∀ (l b : List E) (j : ℕ), Aff fun t ↦ eqEval (l.set j t) b
  | [], b, j => by simpa using aff_const (eqEval [] b)
  | a :: l, [], j => by
    have : ∀ t, eqEval ((a :: l).set j t) [] = 1 := fun t ↦ by
      cases j <;> simp [eqEval]
    simp only [this]
    exact aff_const 1
  | a :: l, c :: b, 0 => by
    simp only [List.set_cons_zero, eqEval_cons]
    exact fun t ↦ by beta_reduce; ring
  | a :: l, c :: b, j + 1 => by
    simp only [List.set_cons_succ, eqEval_cons]
    exact (aff_eqEval l b j).mul_left _

/-- **`f(p)` is affine in each coordinate of `p`.** -/
theorem aff_colEval (q : Column n) (l : List E) (j : ℕ) : Aff fun t ↦ colEval q (l.set j t) := by
  unfold colEval
  exact aff_sum _ _ fun x ↦ (aff_eqEval l _ j).mul_right _

/-- An affine function not identically zero vanishes at at most one point. -/
theorem Aff.root_unique {f : E → E} (h : Aff f) {a v w : E} (ha : f a ≠ 0) (hv : f v = 0)
    (hw : f w = 0) : v = w := by
  rw [h v] at hv
  rw [h w] at hw
  have hd : (f 1 - f 0) * (v - w) = 0 := by linear_combination hv - hw
  rcases mul_eq_zero.1 hd with h1 | h2
  · exfalso
    apply ha
    rw [h a, h1, zero_mul, add_zero]
    rw [h1, zero_mul, add_zero] at hv
    exact hv
  · exact sub_eq_zero.1 h2

/-! ## Two distinct stacks differ somewhere -/

theorem exists_sep (hn : n < 2 ^ 192) {q q' : Column n} (hne : q ≠ q') :
    ∃ z : Vector E n, colEval q z.toList ≠ colEval q' z.toList := by
  classical
  by_contra hall
  push Not at hall
  have hS : ({q, q'} : Set (Column n)).Finite := (Set.finite_singleton q').insert q
  have hL : ({q, q'} : Set (Column n)).ncard ≤ 2 := by rw [Set.ncard_pair hne]
  have hcount := card_not_sepAt_le _ hS hL
  have huniv : (Finset.univ.filter fun z : Vector E n ↦ ¬ SepAt {q, q'} z) = Finset.univ := by
    refine Finset.filter_true_of_mem fun z _ hsep ↦ hne ?_
    exact hsep q (by simp) q' (by simp) (hall z)
  rw [huniv, Finset.card_univ, LeanVM.Protocol.Whir.card_vector_eq_pow, card_E] at hcount
  simp only [Nat.choose_self, one_mul] at hcount
  rcases n with _ | m
  · simp at hcount
  · rw [pow_succ', show m + 1 - 1 = m from rfl, mul_comm (m + 1), mul_comm (2 ^ 192)] at hcount
    have hpos : 0 < (2 ^ 192) ^ m := by positivity
    have := Nat.le_of_mul_le_mul_left hcount hpos
    exact lt_irrefl _ (lt_of_lt_of_le hn this)

/-! ## Consistency with the asked coordinates, and the good caches -/

/-- `z` agrees with the coordinates of `r` the answers `Hc` give. -/
def Cons (Hc : Bytes → Option Digest) (n : ℕ) (r : Digest) (z : Vector E n) : Prop :=
  ∀ j : Fin n, ∀ d, Hc (oodInput n r j) = some d → z[j] = coordOf d

/-- **A good cache**: for every root and two distinct members of its list, their difference does
not vanish on all points consistent with the root's asked coordinates. -/
def GoodC (n : ℕ) (c : KeccakCalls.QueryCache) : Prop :=
  ∀ r, ∀ q ∈ rootList (n := n) (hOfC c) r, ∀ q' ∈ rootList (n := n) (hOfC c) r, q ≠ q' →
    ∃ z : Vector E n, Cons (hOfC c) n r z ∧ colEval q z.toList ≠ colEval q' z.toList

theorem goodC_empty (hn : n < 2 ^ 192) : GoodC n ∅ := by
  intro r q _ q' _ hne
  obtain ⟨z, hz⟩ := exists_sep hn hne
  exact ⟨z, fun j d h ↦ by simp [hOfC] at h, hz⟩

/-- **A bad cache is not good**: all coordinates asked, consistency is the point. -/
theorem bindBadC_imp {c : KeccakCalls.QueryCache} (h : BindBadC n c) : ¬ GoodC n c := by
  intro hg
  obtain ⟨r, z, hz, hsep⟩ := h
  simp only [SepAt, not_forall] at hsep
  obtain ⟨q, hq, q', hq', heq, hne⟩ := hsep
  obtain ⟨z', hcons, hne'⟩ := hg r q hq q' hq' hne
  unfold oodPointOf at hz
  split at hz
  · next hall =>
    rw [Option.some.injEq] at hz
    subst hz
    have : z' = Vector.ofFn fun j : Fin n ↦ coordOf ((hOfC c (oodInput n r j)).get (hall j)) := by
      refine Vector.ext fun i hi ↦ ?_
      rw [Vector.getElem_ofFn]
      exact hcons ⟨i, hi⟩ _ (Option.some_get _).symm
    subst this
    exact hne' heq
  · cases hz

/-! ## The bad values of a fresh coordinate -/

section Bad

variable (Hc : Bytes → Option Digest) (r₀ : Digest) (j₀ : Fin n)

/-- The pair `(q, q')` agrees at every point consistent with `r₀`'s coordinates and coordinate
`j₀` at `v`. -/
def PairBad (q q' : Column n) (v : E) : Prop :=
  ∀ z : Vector E n, Cons Hc n r₀ z → z[j₀] = v → colEval q z.toList = colEval q' z.toList

/-- Some pair of `r₀`'s list agrees once coordinate `j₀` is `v`. -/
def BadVal (v : E) : Prop :=
  ∃ q ∈ rootList (n := n) Hc r₀, ∃ q' ∈ rootList (n := n) Hc r₀, q ≠ q' ∧ PairBad Hc r₀ j₀ q q' v

variable {Hc r₀ j₀}

theorem cons_set (hfree : Hc (oodInput n r₀ j₀) = none) {z : Vector E n} (hz : Cons Hc n r₀ z)
    (t : E) : Cons Hc n r₀ (z.set j₀ t) := by
  intro j d hd
  have hj : (j₀ : ℕ) ≠ j := fun h ↦ by
    rw [show j = j₀ from Fin.ext h.symm, hfree] at hd
    cases hd
  rw [Fin.getElem_fin, Vector.getElem_set, ite_eq_right_iff.2 (fun h ↦ absurd h hj)]
  exact hz j d hd

/-- **At most one bad value per pair**, the pair differing somewhere consistent. -/
theorem pairBad_unique (hfree : Hc (oodInput n r₀ j₀) = none) {q q' : Column n}
    {z : Vector E n} (hz : Cons Hc n r₀ z) (hne : colEval q z.toList ≠ colEval q' z.toList)
    {v w : E} (hv : PairBad Hc r₀ j₀ q q' v) (hw : PairBad Hc r₀ j₀ q q' w) : v = w := by
  let f : E → E := fun t ↦ colEval q (z.toList.set j₀ t) - colEval q' (z.toList.set j₀ t)
  have hf : Aff f := (aff_colEval q _ _).sub (aff_colEval q' _ _)
  have hval : ∀ t, PairBad Hc r₀ j₀ q q' t → f t = 0 := fun t ht ↦ by
    have := ht (z.set j₀ t) (cons_set hfree hz t) (by simp)
    simp only [f]
    rw [Vector.toList_set j₀.isLt] at this
    exact sub_eq_zero.2 this
  have hs : z.toList.set j₀ z[j₀] = z.toList := by
    rw [← Vector.toList_set j₀.isLt]
    congr 1
    refine Vector.ext fun i hi ↦ ?_
    rw [Vector.getElem_set]
    split
    · next h => subst h; rfl
    · rfl
  refine hf.root_unique (a := z[j₀]) ?_ (hval v hv) (hval w hw)
  simp only [f, hs]
  exact fun h ↦ hne (sub_eq_zero.1 h)

open Classical in
/-- **At most `C(L, 2)` bad values.** -/
theorem card_badVal (hS : (rootList (n := n) Hc r₀).Finite) {L : ℕ}
    (hL : (rootList (n := n) Hc r₀).ncard ≤ L) (hfree : Hc (oodInput n r₀ j₀) = none)
    (hgood : ∀ q ∈ rootList (n := n) Hc r₀, ∀ q' ∈ rootList (n := n) Hc r₀, q ≠ q' →
      ∃ z : Vector E n, Cons Hc n r₀ z ∧ colEval q z.toList ≠ colEval q' z.toList) :
    (Finset.univ.filter (BadVal Hc r₀ j₀)).card ≤ L.choose 2 := by
  set T := hS.toFinset
  have hT : T.card ≤ L := by rw [← Set.ncard_eq_toFinset_card _ hS]; exact hL
  let W : Sym2 (Column n) → Finset E := Sym2.lift ⟨fun q q' ↦
    Finset.univ.filter (PairBad Hc r₀ j₀ q q'), fun q q' ↦ by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, PairBad]
      exact forall_congr' fun z ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ eq_comm⟩
  have hsub : Finset.univ.filter (BadVal Hc r₀ j₀) ⊆
      (T.offDiag.image Sym2.mk.uncurry).biUnion W := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, BadVal] at hv
    obtain ⟨q, hq, q', hq', hne, hb⟩ := hv
    refine Finset.mem_biUnion.2 ⟨s(q, q'), Finset.mem_image.2 ⟨(q, q'), ?_, rfl⟩, ?_⟩
    · simpa [T, Finset.mem_offDiag] using ⟨hq, hq', hne⟩
    · simp [W, hb]
  have hW : ∀ e ∈ T.offDiag.image Sym2.mk.uncurry, (W e).card ≤ 1 := by
    intro e he
    obtain ⟨⟨q, q'⟩, hp, rfl⟩ := Finset.mem_image.1 he
    simp only [Finset.mem_offDiag, T, Set.Finite.mem_toFinset] at hp
    obtain ⟨hq, hq', hne⟩ := hp
    obtain ⟨z, hz, hzne⟩ := hgood q hq q' hq' hne
    refine Finset.card_le_one.2 fun v hv w hw ↦ ?_
    simp only [W, Function.uncurry_apply_pair, Sym2.lift_mk, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv hw
    exact pairBad_unique hfree hz hzne hv hw
  calc (Finset.univ.filter (BadVal Hc r₀ j₀)).card
      ≤ ((T.offDiag.image Sym2.mk.uncurry).biUnion W).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ T.offDiag.image Sym2.mk.uncurry, (W e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ T.offDiag.image Sym2.mk.uncurry, 1 := Finset.sum_le_sum hW
    _ = T.card.choose 2 := by rw [Finset.sum_const, smul_eq_mul, mul_one, Sym2.card_image_offDiag]
    _ ≤ L.choose 2 := Nat.choose_le_choose 2 hT

end Bad

/-! ## The digests a key holds, and the bad answers of a coordinate -/

open Classical in
/-- The roots an input is a coordinate input of (at most one, `oodRoots_card`). -/
noncomputable def oodRoots (n : ℕ) (y : Bytes) : Finset Digest :=
  Finset.univ.filter fun r ↦ ∃ j : Fin n, y = oodInput n r j

theorem mem_oodRoots_self (r : Digest) (j : Fin n) : r ∈ oodRoots n (oodInput n r j) := by
  simp only [oodRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, rfl⟩

theorem oodRoots_card (y : Bytes) : (oodRoots n y).card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb ↦ by
    simp only [oodRoots, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨j', h⟩ := hb
    exact (oodInput_inj h).1

/-- The digests a key holds: an input's child digests, and the root it is a coordinate input of. -/
noncomputable def keyDigestsC (n : ℕ) : KeccakCalls.Domain → Finset Digest
  | .inl y => embSet y ∪ oodRoots n y
  | .inr _ => ∅

/-- At most two: a coordinate input (46 bytes) holds no child digest (64-byte inputs). -/
theorem keyDigestsC_card (t : KeccakCalls.Domain) : (keyDigestsC n t).card ≤ 2 := by
  rcases t with y | s
  · by_cases h : (oodRoots n y).Nonempty
    · obtain ⟨r, hr⟩ := h
      simp only [oodRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      obtain ⟨j, rfl⟩ := hr
      have : embSet (oodInput n r j) = ∅ :=
        Finset.eq_empty_of_forall_notMem fun d hd ↦ not_emb_oodInput r d j (mem_embSet.1 hd)
      simp only [keyDigestsC, this, Finset.empty_union]
      exact (oodRoots_card _).trans (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [keyDigestsC, h, Finset.union_empty]
      exact embSet_card y
  · simp [keyDigestsC]

open Classical in
/-- The coordinates an input is the input of (at most one, `oodKeys_card`). -/
noncomputable def oodKeys (n : ℕ) (x : Bytes) : Finset (Digest × Fin n) :=
  Finset.univ.filter fun p ↦ x = oodInput n p.1 p.2

theorem oodKeys_card (hn : n ≤ 256) (x : Bytes) : (oodKeys n x).card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb ↦ by
    simp only [oodKeys, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have := oodInput_inj_fin hn (ha.symm.trans hb)
    exact Prod.ext this.1 this.2

open Classical in
/-- The answers at `x` whose coordinate is a bad value of the coordinate `x` is the input of. -/
noncomputable def ptBad (n : ℕ) (c : KeccakCalls.QueryCache) (x : Bytes) : Finset Digest :=
  (oodKeys n x).biUnion fun p ↦ Finset.univ.filter fun u ↦ BadVal (hOfC c) p.1 p.2 (coordOf u)

theorem n_le_of_admissible (hw : Whir.Admissible n logInvRate) : n ≤ 28 := hw.2.1

/-- **At most `C(L, 2) · 2^64` bad answers of a coordinate.** -/
theorem ptBad_card (hw : Whir.Admissible n logInvRate) (c : KeccakCalls.QueryCache) (x : Bytes)
    (hc : c (.inl x) = none) (hg : GoodC n c) :
    (ptBad n c x).card ≤ (code₀ n logInvRate).listMax.choose 2 * 2 ^ 64 := by
  classical
  have hn : n ≤ 256 := (n_le_of_admissible hw).trans (by norm_num)
  refine Finset.card_biUnion_le.trans ?_
  have hp : ∀ p ∈ oodKeys n x, (Finset.univ.filter fun u ↦
      BadVal (hOfC c) p.1 p.2 (coordOf u)).card ≤ (code₀ n logInvRate).listMax.choose 2 * 2 ^ 64 := by
    intro p hp
    simp only [oodKeys, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hfree : hOfC c (oodInput n p.1 p.2) = none := by rw [← hp]; exact hc
    have hsub : (Finset.univ.filter fun u ↦ BadVal (hOfC c) p.1 p.2 (coordOf u)) =
        Finset.univ.filter fun u ↦ coordOf u ∈ Finset.univ.filter (BadVal (hOfC c) p.1 p.2) := by
      ext u
      simp
    rw [hsub]
    refine (card_coordOf_mem _).trans (Nat.mul_le_mul_right _ ?_)
    exact card_badVal (candidates_count hw _).1 (candidates_count hw _).2 hfree (hg p.1)
  calc ∑ p ∈ oodKeys n x, (Finset.univ.filter fun u ↦ BadVal (hOfC c) p.1 p.2 (coordOf u)).card
      ≤ ∑ _p ∈ oodKeys n x, (code₀ n logInvRate).listMax.choose 2 * 2 ^ 64 := Finset.sum_le_sum hp
    _ = (oodKeys n x).card * ((code₀ n logInvRate).listMax.choose 2 * 2 ^ 64) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 1 * ((code₀ n logInvRate).listMax.choose 2 * 2 ^ 64) :=
        Nat.mul_le_mul_right _ (oodKeys_card hn x)
    _ = _ := one_mul _

/-! ## The three kinds of fresh query -/

theorem hOfC_new (c : KeccakCalls.QueryCache) (x : Bytes) (u : Digest) :
    hOfC (c.cacheQuery (.inl x) u) x = some u := by
  simp [hOfC]

theorem hOfC_old (c : KeccakCalls.QueryCache) {x y : Bytes} (u : Digest) (h : y ≠ x) :
    hOfC (c.cacheQuery (.inl x) u) y = hOfC c y := by
  simp only [hOfC]
  rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]

theorem hOfC_perm (c : KeccakCalls.QueryCache) (s u : KeccakState) :
    hOfC (c.cacheQuery (.inr s) u) = hOfC c := funext fun y ↦ by
  simp only [hOfC]
  rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]

/-- A fresh Keccak-f[1600] answer changes no Keccak-256 answer. -/
theorem goodC_cacheQuery_perm {c : KeccakCalls.QueryCache} (hg : GoodC n c) (s u : KeccakState) :
    GoodC n (c.cacheQuery (.inr s) u) := by
  unfold GoodC
  rw [hOfC_perm]
  exact hg

/-- **A fresh Keccak-256 answer `u` at `x` leaves a good cache good**, unless `u` is a digest an
answered key or `x` holds, or a bad answer of the coordinate `x` is the input of. -/
theorem goodC_cacheQuery_hash (hn : n ≤ 256) (hn' : n < 2 ^ 192) (c : KeccakCalls.QueryCache)
    (x : Bytes) (hc : c (.inl x) = none) (hg : GoodC n c) (u : Digest)
    (S : Finset KeccakCalls.Domain) (hS : ∀ t, c t ≠ none → t ∈ S)
    (hu : u ∉ S.biUnion (keyDigestsC n) ∪ keyDigestsC n (.inl x) ∪ ptBad n c x) :
    GoodC n (c.cacheQuery (.inl x) u) := by
  classical
  have hnew := hOfC_new c x u
  have hold : ∀ y, y ≠ x → hOfC (c.cacheQuery (.inl x) u) y = hOfC c y :=
    fun y hy ↦ hOfC_old c u hy
  intro r q hq q' hq' hne
  by_cases hr : ∃ j : Fin n, hOfC (c.cacheQuery (.inl x) u) (oodInput n r j) ≠ none
  swap
  · push Not at hr
    obtain ⟨z, hz⟩ := exists_sep hn' hne
    exact ⟨z, (fun j d hd ↦ by rw [hr j] at hd; cases hd), hz⟩
  obtain ⟨j, hj⟩ := hr
  have hrB : r ∈ S.biUnion (keyDigestsC n) ∪ keyDigestsC n (.inl x) := by
    by_cases hjx : oodInput n r j = x
    · refine Finset.mem_union_right _ ?_
      simp only [keyDigestsC]
      exact Finset.mem_union_right _ (hjx ▸ mem_oodRoots_self r j)
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨.inl (oodInput n r j), hS _ ?_, ?_⟩)
      · rw [hold _ hjx] at hj
        exact hj
      · simp only [keyDigestsC]
        exact Finset.mem_union_right _ (mem_oodRoots_self r j)
  have hU : Unrelated (hOfC c) (hOfC (c.cacheQuery (.inl x) u)) x u r := by
    refine ⟨hc, hnew, hold, fun hur ↦ ?_, fun y hy hemb ↦ ?_, fun hemb ↦ ?_⟩
    · subst hur
      exact hu (Finset.mem_union_left _ hrB)
    · refine hu (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨.inl y, hS _ hy, ?_⟩)))
      simp only [keyDigestsC]
      exact Finset.mem_union_left _ (mem_embSet.2 hemb)
    · refine hu (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      simp only [keyDigestsC]
      exact Finset.mem_union_left _ (mem_embSet.2 hemb)
  have hl : rootList (n := n) (hOfC (c.cacheQuery (.inl x) u)) r = rootList (n := n) (hOfC c) r := by
    unfold rootList
    rw [extract_stable hU]
  rw [hl] at hq hq'
  by_cases hx : ∃ j₀ : Fin n, x = oodInput n r j₀
  · obtain ⟨j₀, hj₀⟩ := hx
    have hpt : ¬ BadVal (hOfC c) r j₀ (coordOf u) := fun hb ↦ hu (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨(r, j₀), by simp [oodKeys, hj₀], by simpa using hb⟩))
    have hpb : ¬ PairBad (hOfC c) r j₀ q q' (coordOf u) := fun hb ↦ hpt ⟨q, hq, q', hq', hne, hb⟩
    simp only [PairBad, not_forall] at hpb
    obtain ⟨z, hz, hzj, hzne⟩ := hpb
    refine ⟨z, fun j d hd ↦ ?_, hzne⟩
    by_cases hjx : oodInput n r j = x
    · obtain rfl := (oodInput_inj_fin hn (hjx.trans hj₀)).2
      rw [hjx, hnew, Option.some.injEq] at hd
      subst hd
      exact hzj
    · rw [hold _ hjx] at hd
      exact hz j d hd
  · push Not at hx
    obtain ⟨z, hz, hzne⟩ := hg r q hq q' hq' hne
    refine ⟨z, fun j d hd ↦ ?_, hzne⟩
    rw [hold _ (fun h ↦ hx j h.symm)] at hd
    exact hz j d hd

/-! ## The potential -/

/-- **The per-query error of a coordinate**: `C(L, 2) / 2^192`, `L = listMax`. -/
noncomputable def δc (n : ℕ) : ℝ≥0∞ :=
  (((code₀ n logInvRate).listMax.choose 2 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192

/-- The budget's terms: `δc + (2 (k + j) + 2) / 2^256` for a cache of `k` entries. -/
noncomputable def coordSum (n : ℕ) (k : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range m, (δc n + (2 * (k + j) + 2) / (2 : ℝ≥0∞) ^ 256)

open Classical in
/-- **The potential** with `m` queries left: one on a cache that is not good, otherwise the budget,
capped at one. -/
noncomputable def coordPot (n : ℕ) (m : ℕ) (c : KeccakCalls.QueryCache) : ℝ≥0∞ :=
  if GoodC n c then min 1 (coordSum n c.enncard m) else 1

theorem coordPot_le_one (m : ℕ) (c : KeccakCalls.QueryCache) : coordPot n m c ≤ 1 := by
  unfold coordPot
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem coordSum_succ (k : ℝ≥0∞) (m : ℕ) :
    coordSum n k (m + 1) = (δc n + (2 * k + 2) / (2 : ℝ≥0∞) ^ 256) + coordSum n (k + 1) m := by
  unfold coordSum
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [add_right_comm k, add_assoc k]

theorem coordSum_mono {k k' : ℝ≥0∞} (h : k ≤ k') (m : ℕ) : coordSum n k m ≤ coordSum n k' m := by
  unfold coordSum
  gcongr

theorem avg_le_one (m : ℕ) (c : KeccakCalls.QueryCache) (t : KeccakCalls.Domain) :
    (∑ u, coordPot n m (c.cacheQuery t u)) / Fintype.card (KeccakCalls.Range t) ≤ 1 := by
  have hcard : (Fintype.card (KeccakCalls.Range t) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc (∑ u, coordPot n m (c.cacheQuery t u)) / Fintype.card (KeccakCalls.Range t)
      ≤ (∑ _u : KeccakCalls.Range t, (1 : ℝ≥0∞)) / Fintype.card (KeccakCalls.Range t) :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ coordPot_le_one m _) _
    _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact ENNReal.div_self hcard (ENNReal.natCast_ne_top _)

/-- **The step, given the answers that spoil the cache**: from a good cache, if every answer
outside `B` leaves it good and `B` has probability at most `δc + (2k + 2)/2^256`, the potential is
a supermartingale step. -/
theorem coordPot_fresh_of (c : KeccakCalls.QueryCache) (hg : GoodC n c) (m : ℕ)
    (t : KeccakCalls.Domain) (B : Finset (KeccakCalls.Range t))
    (hB : ∀ u, u ∉ B → GoodC n (c.cacheQuery t u))
    (hβ : (B.card : ℝ≥0∞) / Fintype.card (KeccakCalls.Range t) ≤
      δc n + (2 * c.enncard + 2) / (2 : ℝ≥0∞) ^ 256) :
    (∑ u, coordPot n m (c.cacheQuery t u)) / Fintype.card (KeccakCalls.Range t) ≤
      coordPot n (m + 1) c := by
  classical
  have hpt : ∀ u, coordPot n m (c.cacheQuery t u) ≤
      (if u ∈ B then 1 else 0) + coordSum n (c.enncard + 1) m := by
    intro u
    by_cases hu : u ∈ B
    · simp only [hu, ↓reduceIte]
      exact (coordPot_le_one m _).trans le_self_add
    · simp only [hu, ↓reduceIte, zero_add, coordPot, hB u hu]
      exact (min_le_right _ _).trans (coordSum_mono (QueryCache.enncard_cacheQuery_le c t u) m)
  have havg : (∑ u, coordPot n m (c.cacheQuery t u)) / Fintype.card (KeccakCalls.Range t) ≤
      coordSum n c.enncard (m + 1) := by
    calc (∑ u, coordPot n m (c.cacheQuery t u)) / Fintype.card (KeccakCalls.Range t)
        ≤ (∑ u, ((if u ∈ B then 1 else 0) + coordSum n (c.enncard + 1) m)) /
            Fintype.card (KeccakCalls.Range t) :=
          ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
      _ = (B.card : ℝ≥0∞) / Fintype.card (KeccakCalls.Range t) +
            coordSum n (c.enncard + 1) m := by
          rw [sum_add_const_div_card (spec := KeccakCalls) t, Finset.sum_boole]
          simp
      _ ≤ (δc n + (2 * c.enncard + 2) / (2 : ℝ≥0∞) ^ 256) + coordSum n (c.enncard + 1) m := by
          gcongr
      _ = coordSum n c.enncard (m + 1) := (coordSum_succ _ m).symm
  simp only [coordPot, hg, ↓reduceIte]
  exact le_min (avg_le_one m c t) havg

/-- **The potential is budgeted.** -/
theorem isBudgetedPotential_coordPot (hw : Whir.Admissible n logInvRate) :
    IsBudgetedPotential (coordPot n) where
  mono m c := by
    unfold coordPot
    split_ifs
    · refine min_le_min le_rfl ?_
      unfold coordSum
      rw [Finset.sum_range_succ]
      exact le_self_add
    · exact le_rfl
  fresh m c t hc := by
    classical
    have hn : n ≤ 256 := (n_le_of_admissible hw).trans (by norm_num)
    have hn' : n < 2 ^ 192 := lt_of_le_of_lt hn (by norm_num)
    by_cases hg : GoodC n c
    swap
    · refine (avg_le_one m c t).trans ?_
      simp [coordPot, hg]
    by_cases htop : c.enncard = ⊤
    · have h1 : coordPot n (m + 1) c = 1 := by
        simp only [coordPot, hg, ↓reduceIte]
        refine min_eq_left ?_
        rw [coordSum_succ, htop]
        simp [ENNReal.top_div_of_ne_top]
      rw [h1]
      exact avg_le_one m c t
    have hfin : c.toSet.Finite := Set.encard_ne_top_iff.mp fun h ↦ htop (by
      simp [QueryCache.enncard, h])
    set S := hfin.toFinset.image Sigma.fst with hSdef
    have hS : ∀ t', c t' ≠ none → t' ∈ S := by
      intro t' ht'
      obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp ht'
      exact Finset.mem_image.mpr ⟨⟨t', u'⟩, hfin.mem_toFinset.mpr hu', rfl⟩
    have hSk : (S.card : ℝ≥0∞) ≤ c.enncard := by
      rw [QueryCache.enncard, hfin.encard_eq_coe_toFinset_card]
      exact_mod_cast Finset.card_image_le
    rcases t with x | s
    · -- Keccak-256
      refine coordPot_fresh_of c hg m _
        (S.biUnion (keyDigestsC n) ∪ keyDigestsC n (.inl x) ∪ ptBad n c x)
        (fun u hu ↦ goodC_cacheQuery_hash hn hn' c x hc hg u S hS hu) ?_
      have h1 : (S.biUnion (keyDigestsC n) ∪ keyDigestsC n (.inl x) ∪ ptBad n c x).card ≤
          (2 * S.card + 2) + (code₀ n logInvRate).listMax.choose 2 * 2 ^ 64 := by
        refine (Finset.card_union_le _ _).trans (add_le_add ?_ (ptBad_card hw c x hc hg))
        refine (Finset.card_union_le _ _).trans (add_le_add ?_ (keyDigestsC_card _))
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ t ∈ S, (keyDigestsC n t).card ≤ ∑ _t ∈ S, 2 :=
              Finset.sum_le_sum fun t _ ↦ keyDigestsC_card t
          _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hrange : Fintype.card (KeccakCalls.Range (.inl x)) = 2 ^ 256 := card_digest
      rw [hrange, Nat.cast_pow, Nat.cast_ofNat]
      have h2 : (2 : ℝ≥0∞) ^ 256 = 2 ^ 192 * 2 ^ 64 := by rw [← pow_add]
      calc ((S.biUnion (keyDigestsC n) ∪ keyDigestsC n (.inl x) ∪ ptBad n c x).card : ℝ≥0∞) /
            (2 : ℝ≥0∞) ^ 256
          ≤ (((2 * S.card + 2) + (code₀ n logInvRate).listMax.choose 2 * 2 ^ 64 : ℕ) : ℝ≥0∞) /
            (2 : ℝ≥0∞) ^ 256 := by gcongr
        _ = (2 * (S.card : ℝ≥0∞) + 2) / (2 : ℝ≥0∞) ^ 256 + δc n := by
            rw [Nat.cast_add, ENNReal.add_div, δc]
            congr 1
            · push_cast
              ring_nf
            · rw [Nat.cast_mul, h2, Nat.cast_pow, Nat.cast_ofNat,
                ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
        _ ≤ δc n + (2 * c.enncard + 2) / (2 : ℝ≥0∞) ^ 256 := by
            rw [add_comm]
            gcongr
    · -- Keccak-f[1600]
      refine coordPot_fresh_of c hg m _ ∅ (fun u _ ↦ goodC_cacheQuery_perm hg s u) ?_
      simp

/-! ## The binding -/

/-- **The out-of-domain answer binds, the point read off Keccak-256.** In the random-oracle model of
Keccak-256 and Keccak-f[1600], a computation of at most `Q` queries, from the empty cache, ends
with some root whose `n` coordinates it asked and whose list, extracted from the final Keccak-256
answers, is not separated at the point they give, with probability at most
`Q · C(L, 2) / 2^192 + Q (Q + 1) / 2^256`, `L = listMax`. -/
theorem ood_binding_coords (hw : Whir.Admissible n logInvRate) {α : Type}
    (oa : OracleComp KeccakCalls α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ KeccakCalls.randomOracle oa).run ∅}[BindBadC n z.2] ≤
      Q * δc n + ((Q * (Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  classical
  have hn' : n < 2 ^ 192 := lt_of_le_of_lt (n_le_of_admissible hw) (by norm_num)
  have h := prEvent_run_randomOracle_le_of_budgeted (isBudgetedPotential_coordPot hw) oa Q hQ ∅
    (fun _ c ↦ BindBadC n c) (fun z _ hz ↦ by simp [coordPot, bindBadC_imp hz])
  refine h.trans ?_
  simp only [coordPot, goodC_empty hn', ↓reduceIte, QueryCache.enncard_empty]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  rw [coordSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.sum_div, sum_budget]

/-! ## The numbers at version 1's shapes -/

/-- Level 0's certified list at version 1's shapes: `C(L, 2) ≤ 2^32` at each `15 ≤ n ≤ 28`
(`3,811,910,955` at `n = 15`). -/
theorem listHi_choose_v1 : ∀ n, minVars ≤ n → n ≤ maxVars →
    (LeanVM.Protocol.Whir.Params.certOf n logInvRate 0).listHi *
        ((LeanVM.Protocol.Whir.Params.certOf n logInvRate 0).listHi - 1) / 2 ≤ 2 ^ 32 := by
  decide +kernel

/-- At `n = 27`: `L = 4473`, `C(L, 2) = 10,001,628 ≤ 2^24`. -/
theorem listHi_choose_27 :
    (LeanVM.Protocol.Whir.Params.certOf 27 logInvRate 0).listHi *
        ((LeanVM.Protocol.Whir.Params.certOf 27 logInvRate 0).listHi - 1) / 2 ≤ 2 ^ 24 := by
  decide +kernel

theorem δc_le_of {k : ℕ} (hk : k ≤ 192) (hc : (code₀ n logInvRate).listMax.choose 2 ≤ 2 ^ k) :
    δc n ≤ (2 : ℝ≥0∞)⁻¹ ^ (192 - k) := by
  unfold δc
  calc (((code₀ n logInvRate).listMax.choose 2 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192
      ≤ ((2 ^ k : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (192 - k) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show 192 = k + (192 - k) by omega, two_pow_div_two_pow,
        Nat.add_sub_cancel_left]

/-- **A coordinate's error at version 1's shapes**: `C(L, 2) / 2^192 ≤ 2^-160` for every
`15 ≤ n ≤ 28`, `L` the certified list (`listMax ≤ listHi`). -/
theorem δc_le (h1 : minVars ≤ n) (h2 : n ≤ maxVars) : δc n ≤ (2 : ℝ≥0∞)⁻¹ ^ 160 := by
  have hw := admissible_v1 n h1 h2
  refine δc_le_of (k := 32) (by norm_num) ?_
  refine le_trans (Nat.choose_le_choose 2 (listMax_le_listHi hw)) ?_
  rw [Nat.choose_two_right]
  exact listHi_choose_v1 n h1 h2

/-- **At `n = 27`**: `C(L, 2) / 2^192 ≤ 2^-168`. -/
theorem δc_27 : δc 27 ≤ (2 : ℝ≥0∞)⁻¹ ^ 168 := by
  have hw := admissible_v1 27 (by decide) (by decide)
  refine δc_le_of (k := 24) (by norm_num) ?_
  refine le_trans (Nat.choose_le_choose 2 (listMax_le_listHi hw)) ?_
  rw [Nat.choose_two_right]
  exact listHi_choose_27

/-- **The binding at version 1's shapes**: at most `Q · 2^-160 + Q (Q + 1) / 2^256`. -/
theorem ood_binding_coords_v1 (h1 : minVars ≤ n) (h2 : n ≤ maxVars) {α : Type}
    (oa : OracleComp KeccakCalls α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ KeccakCalls.randomOracle oa).run ∅}[BindBadC n z.2] ≤
      Q * (2 : ℝ≥0∞)⁻¹ ^ 160 + ((Q * (Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
  (ood_binding_coords (admissible_v1 n h1 h2) oa Q hQ).trans (by gcongr; exact δc_le h1 h2)

end WhirBridge.Pcs
