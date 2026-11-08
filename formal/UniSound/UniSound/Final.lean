-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The numbers follow
-- `formal/Compose/Compose/ListChainKDoomExample.lean`.
import UniSound.Fs
import UniSound.Bus

/-!
# Knowledge soundness of the univariate verifier, end to end (main line)

**`uniKnowledgeSoundness`**: `UniKnowledgeSoundness D (uniBound e₃₂)` for every deployment `D`, the
rounds' errors at most `e₃₂ = 2^32 / |E|`, from

* **`hFlock : FlockSound κ`** — **the Flock hypothesis** (the one assumption about BLAKE2s by
  Flock, `FlockInterface.lean`): Flock's front is a chain program, round-by-round sound from
  `FlockRegion.Holds` to its ring-switch claim and its pending matrices' reduction;
* **`I : UniIds D hFlock`** — the identity model (`Piop.lean`): the bus and constraint state with
  its round-`0` error, the identities as polynomials of bounded degree, the relations at `t`, the
  batch's products; the bridges between them and Lv42's `M3Holds`;
* **`C : UniCode …`**, **`hFin : UniFinal …`** — the code-level links (`Fs.lean`);
* **`hFs : FsLayer …`** — the Fiat–Shamir layer (`Fs.lean`): `ListChainK`'s closed
  random-permutation theorem for the univariate transcript, openings, setup and extractor;
* the numbers: `errMain`, Flock's rounds' errors at most `2^32 / |E|`, the identities' degrees
  and the merge polynomial's at most `2^32` in all, at most `2^32 − 2` relations on a commitment.

The protocol is `uniPiop hFlock I` (`PiopSound.lean`, proved): its states' last one follows from the
verifier's checks with true claims (`hlink_uniPiop`, from `hFin`), its first is the relation
(`hpre_uniPiop`), and every round's error is at most `e₃₂` (`uniErr_le`).

**`uniBound_le_bits`**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and `π⁻¹`
(the five openings' doom terms, `≈ 5 · 2^-64`, dominate; the tag's `N · 2^-128 ≈ 2^-64`; the list term
is `≈ 2^-69.4`).
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset WhirBridge
open scoped ENNReal

variable {D : Deployment} {κ : ℕ}

/-! ## The opened transcript of a completed one -/

theorem length_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) :
    (openedOf nF c1 c2 done).length = done.length := by
  simp [openedOf]

theorem rd_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) (j : ℕ) (h : j < done.length) :
    rd (openedOf nF c1 c2 done) j =
      ((if j = 0 then some c1 else if j = nF + 1 then some c2 else none, (done[j]'h).1.2),
        (done[j]'h).2) := by
  simp [rd, openedOf, List.getD_eq_getElem?_getD, h]

theorem doneFits_append_take : ∀ (rs₁ rs₂ : List Compose.RoundSpec) (d : Done),
    DoneFits (rs₁ ++ rs₂) d → DoneFits rs₁ (d.take rs₁.length)
  | [], _, _, _ => by simp [DoneFits]
  | r :: rs₁, rs₂, [], h => by simp [DoneFits] at h
  | r :: rs₁, rs₂, x :: d, h => by
    simp only [List.cons_append, DoneFits] at h
    simp only [List.length_cons, List.take_succ_cons, DoneFits]
    exact ⟨h.1, h.2.1, doneFits_append_take rs₁ rs₂ d h.2.2⟩

theorem doneFits_map_noRoot : ∀ (rs : List Compose.RoundSpec) (d : Done),
    (∀ r ∈ rs, r.root = false) → DoneFits rs d →
      DoneFits rs (d.map fun y => ((none, y.1.2), y.2))
  | [], [], _, _ => trivial
  | r :: rs, y :: d, hr, h => by
    simp only [DoneFits, List.map_cons] at h ⊢
    refine ⟨⟨?_, h.1.2⟩, h.2.1, doneFits_map_noRoot rs d (fun r' hr' => hr r' (by simp [hr'])) h.2.2⟩
    simp [hr r (by simp)]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem take_map_zipIdx (nF : ℕ) (c1 c2 : Stk) : ∀ (l : Done) (k n : ℕ),
    ((((l.zipIdx k).map fun x : (UMsg × List E) × ℕ =>
        ((if x.2 = 0 then some c1 else if x.2 = nF + 1 then some c2 else none, x.1.1.2),
          x.1.2)).take n).map fun x : (Option Stk × List E) × List E =>
        (((none : Option (E × E)), x.1.2), x.2)) =
      (l.take n).map fun y : UMsg × List E => (((none : Option (E × E)), y.1.2), y.2)
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp
  | y :: l, k, n + 1 => by
    simp only [List.zipIdx_cons, List.map_cons, List.take_succ_cons, List.cons.injEq]
    exact ⟨by simp, take_map_zipIdx nF c1 c2 l (k + 1) n⟩

theorem fdOf_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) :
    fdOf nF (openedOf nF c1 c2 done) =
      ((done.drop 1).take nF).map fun y : UMsg × List E => (((none : Option (E × E)), y.1.2), y.2) := by
  rcases done with _ | ⟨x, d⟩
  · simp [fdOf, openedOf]
  · unfold fdOf openedOf
    simp only [List.zipIdx_cons, List.map_cons, List.drop_succ_cons, List.drop_zero]
    exact take_map_zipIdx nF c1 c2 d 1 nF

/-! ## The links of `uniPiop` -/

/-! ## The end theorem -/

/-! ## The bits -/

theorem cast_div_le_256 {a b : ℕ} (h : a ≤ b) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((b : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

theorem inv_two_pow_128' : (2 : ℝ≥0∞)⁻¹ ^ 128 = ((2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 128 + 128 from rfl, two_pow_div_two_pow]

/-- An opening's doom term at most `(X 2^128 + 5 X²) / 2^256` for `QA + QV ≤ X`. -/
theorem openingBoundAt_le' {QV QA X : ℕ} (h : QA + QV ≤ X) :
    openingBoundAt QV QA ≤ ((X * 2 ^ 128 + 5 * X * X : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold openingBoundAt
  rw [inv_two_pow_128', ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul]
  refine cast_div_le_256 ?_
  calc (QA + QV) * (2 ^ 128 + 5 * (QA + QV)) ≤ X * (2 ^ 128 + 5 * X) :=
        Nat.mul_le_mul h (by omega)
    _ = X * 2 ^ 128 + 5 * X * X := by ring

theorem div_192_eq' (a : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 192 = ((a * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 192 + 64 from rfl, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

theorem cardE_cast : (Fintype.card E : ℝ≥0∞) = 2 ^ 192 := by
  rw [LeanVM.Protocol.card_E, Nat.cast_pow, Nat.cast_ofNat]

/-- **The bound in bits**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and
`π⁻¹`. -/
theorem uniBound_le_bits (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 := by
  unfold uniBound uniN
  rw [cardE_cast, div_192_eq']
  have hX : 2 ^ 33 + Q + 10122 ≤ 18446744082299496586 := by
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  have b1 := openingBoundAt_le' (QV := 10122) (QA := 2 ^ 33 + Q) (X := 18446744082299496586) hX
  -- The list term.
  have hN : 2 ^ 33 + Q ≤ 18446744082299496586 := by omega
  have b2 : ((2 ^ 33 + Q : ℕ) : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) *
      (((2 ^ 32 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((2 ^ 128 + 8 * (2 ^ 33 + Q) : ℕ) : ℝ≥0∞) /
        2 ^ 256) ≤
      ((18446744082299496586 * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64)) +
        18446744082299496586 * (2 ^ 128 + 8 * 18446744082299496586) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ENNReal.div_add_div_same, ← Nat.cast_add,
      ← mul_div_assoc, ← Nat.cast_mul]
    refine cast_div_le_256 ?_
    calc (2 ^ 33 + Q) * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64) + (2 ^ 128 + 8 * (2 ^ 33 + Q)))
        ≤ 18446744082299496586 * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64) +
            (2 ^ 128 + 8 * 18446744082299496586)) :=
          Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  -- The random-permutation term.
  have b3 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    have e1 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 = (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_pow]
    rw [e1]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl,
            two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (mul_le_mul' le_rfl b1) b2) b3).trans ?_
  rw [show (5 : ℝ≥0∞) = ((5 : ℕ) : ℝ≥0∞) from rfl, ← mul_div_assoc, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  calc _ ≤ ((2 ^ 195 : ℕ) : ℝ≥0∞) / 2 ^ 256 := cast_div_le_256 (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 61 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 195 + 61 from rfl, two_pow_div_two_pow]

end UniSound
