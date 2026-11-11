-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New for the PCS claims: the quotient table assembled from the Statement's three parts (`PcsBridge.assemble`),
-- read as F1's second message (`QuotientSecurity.quotientsOfTable`, adapted from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import E2ECompleteness.PcsHonest
import PcsBridge.Parts

/-!
# The quotient table from the Statement's three parts

The prover commits `H`, `Q`, `G` (`hTableOf`, `qTableOf`, `gTableOf`, `PcsDefs.lean`); F1's claims are about
one quotient table of `m + 6` variables, `PcsBridge.assemble` of the three. **`quotientsOfTable_assemble`**:
the second message that table holds (`quotientsOfTable y`) is `R` as soon as `h`'s coefficients hold `R.h₀`,
the blinding `R.hHigh`, `q`'s coefficients `R.q`, the gate quotient's first `2^25` coefficients `R.qGate`,
and `R.junk = 0`: limb by limb, each slot's four limbs on `1, y, y², y³` rebuild the coefficients'
polynomial (`tablePoly_limbs`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters QuotientSecurity PcsQuotient

namespace E2ECompleteness.Pcs

/-- **A table's polynomial from its limbs**, the fourth limb zero. -/
theorem tablePoly_limbs {M : ℕ} (c : (Fin M → Bool) → E) :
    tablePoly (fun b ↦ ofK ((c b).limb 0)) + C y * tablePoly (fun b ↦ ofK ((c b).limb 1)) +
      C (y ^ 2) * tablePoly (fun b ↦ ofK ((c b).limb 2)) +
      C (y ^ 3) * tablePoly (fun _ : Fin M → Bool ↦ (0 : E)) = tablePoly c := by
  rw [Completeness.tablePoly_zero, mul_zero, add_zero]
  unfold tablePoly
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  conv_rhs => rw [E.eq_sum_limbs (c b)]
  simp only [map_add, map_mul, map_pow]
  ring

theorem idx_snoc3 {M : ℕ} (b : Fin M → Bool) (x u v : Bool) :
    Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc b x) u) v : Fin (M + 1 + 1 + 1) → Bool) =
      Completeness.idx b + (if x then 2 ^ M else 0) + (if u then 2 ^ (M + 1) else 0) +
        (if v then 2 ^ (M + 1 + 1) else 0) := by
  rw [Completeness.idx_snoc, Completeness.idx_snoc, Completeness.idx_snoc]

theorem idx_snoc4 {M : ℕ} (b : Fin M → Bool) (x w u v : Bool) :
    Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b x) w) u) v :
        Fin (M + 1 + 1 + 1 + 1) → Bool) =
      Completeness.idx b + (if x then 2 ^ M else 0) + (if w then 2 ^ (M + 1) else 0) +
        (if u then 2 ^ (M + 1 + 1) else 0) + (if v then 2 ^ (M + 1 + 1 + 1) else 0) := by
  rw [Completeness.idx_snoc, Completeness.idx_snoc, Completeness.idx_snoc, Completeness.idx_snoc]

theorem getD_ofFn₂ {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The limb `e₀ + 2 e₁`. -/
def limbN (e₀ e₁ : Bool) : ℕ := (if e₀ then 1 else 0) + 2 * (if e₁ then 1 else 0)

/-! ## The three parts by their bits -/

section Parts

variable (hHat : Array E) (blind : Fin 3 → Fin hBlind → K) (qHat : Array E) (qGateHat : Array K)

theorem cellVars22 : cellVars 22 = 24 := rfl

/-- `H` by limb and coefficient (`N = 2^24` cells). -/
theorem hTable_getD (e jj : ℕ) (he : e < 4) (hj : jj < 2 * 2 ^ cellVars 22) :
    (hTableOf 22 hHat blind).getD (e * (2 * 2 ^ cellVars 22) + jj) 0 =
      if 3 ≤ e then 0 else if jj < 2 ^ cellVars 22 then limbOf (hHat.getD jj 0) e
      else if h : jj - 2 ^ cellVars 22 < hBlind ∧ e < 3 then
        blind ⟨e, h.2⟩ ⟨jj - 2 ^ cellVars 22, h.1⟩ else 0 := by
  have hlt : e * (2 * 2 ^ cellVars 22) + jj < 8 * 2 ^ cellVars 22 := by
    have : e * (2 * 2 ^ cellVars 22) ≤ 3 * (2 * 2 ^ cellVars 22) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpos : 0 < 2 * 2 ^ cellVars 22 := by positivity
  have h1 : (e * (2 * 2 ^ cellVars 22) + jj) / (2 * 2 ^ cellVars 22) = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (e * (2 * 2 ^ cellVars 22) + jj) % (2 * 2 ^ cellVars 22) = jj := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold hTableOf
  rw [getD_ofFn₂ _ _ hlt]
  dsimp only
  rw [h1, h2]

/-- The index of `(low, d₀, e₀, e₁)`. -/
theorem idx_hbits (low : Fin 24 → Bool) (d₀ e₀ e₁ : Bool) :
    Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc low d₀) e₀) e₁ : Fin (24 + 1 + 1 + 1) → Bool) =
      limbN e₀ e₁ * (2 * 2 ^ 24) + (Completeness.idx low + if d₀ then 2 ^ 24 else 0) := by
  rw [idx_snoc3]
  unfold limbN
  cases d₀ <;> cases e₀ <;> cases e₁ <;> simp <;> ring

theorem limbN_lt (e₀ e₁ : Bool) : limbN e₀ e₁ < 4 := by
  unfold limbN; cases e₀ <;> cases e₁ <;> simp

end Parts


/-! ## The assembled table's second message -/

section Assemble

variable {m : ℕ} (cH : (Fin (m + 1 + 1 + 1) → Bool) → E) (cQ : (Fin (m + 1 + 1 + 1 + 1) → Bool) → E)
  (cG : (Fin (m + 1) → Bool) → E)

/-- `assemble` on a slot of a point. -/
theorem subTable_assemble (k₀ k₁ e₀ e₁ : Bool) :
    subTable (PcsBridge.assemble cH cQ cG) k₀ k₁ e₀ e₁ = fun b ↦
      if !k₀ && !k₁ && !(b (Fin.last _)) then cH (Fin.snoc (Fin.snoc (Fin.init b) e₀) e₁)
      else if k₀ && !k₁ then cQ (Fin.snoc (Fin.snoc b e₀) e₁)
      else if !k₀ && k₁ && !(b (Fin.last _)) && !e₀ && !e₁ then cG (Fin.init b)
      else 0 := by
  funext b
  simp only [subTable, PcsBridge.assemble, Fin.init_snoc, Fin.snoc_last, Fin.snoc_init_self]

/-- The four limbs on `1, y, y², y³`. -/
noncomputable def limbSum {M : ℕ} (c : Bool → Bool → (Fin M → Bool) → E) : E[X] :=
  tablePoly (c false false) + C y * tablePoly (c true false) + C (y ^ 2) * tablePoly (c false true) +
    C (y ^ 3) * tablePoly (c true true)

theorem lowChunk_eq {F' : Type*} {M : ℕ} (c : (Fin (M + 1 + 1) → Bool) → F') :
    lowChunk c = fun b ↦ c (Fin.snoc (Fin.snoc b false) false) := rfl

theorem tablePoly_zero' {M : ℕ} : tablePoly (fun _ : Fin M → Bool ↦ (0 : E)) = 0 :=
  Completeness.tablePoly_zero

/-- **The second message the assembled table holds.** -/
theorem quotientsOfTable_assemble (R : Params.Quotients E)
    (hh : limbSum (fun e₀ e₁ (b : Fin m → Bool) ↦ cH (Fin.snoc (Fin.snoc (Fin.snoc b false) e₀) e₁)) =
      R.h₀)
    (hb : limbSum (fun e₀ e₁ (b : Fin m → Bool) ↦ cH (Fin.snoc (Fin.snoc (Fin.snoc b true) e₀) e₁)) =
      R.hHigh)
    (hq : limbSum (fun e₀ e₁ (b : Fin (m + 1 + 1) → Bool) ↦ cQ (Fin.snoc (Fin.snoc b e₀) e₁)) = R.q)
    (hg : tablePoly cG = R.qGate) (hj : R.junk = 0) :
    quotientsOfTable y (PcsBridge.assemble cH cQ cG) = R := by
  obtain ⟨h₀, hHigh, q, qGate, junk⟩ := R
  dsimp only at hh hb hq hg hj
  simp only [quotientsOfTable, Params.Quotients.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hh]
    simp [sumPolyLow, lowChunk_eq, subTable_assemble, limbSum]
  · rw [← hb]
    simp [sumPolyHigh, highPart, subTable_assemble, tablePoly_zero', limbSum]
  · rw [← hq]
    simp [slotPoly, subTable_assemble, limbSum]
  · rw [← hg]
    simp [slotPoly, subTable_assemble, tablePoly_zero']
    rw [tablePoly_snoc]
    simp [tablePoly_zero']
  · rw [hj]
    simp [slotPoly, subTable_assemble, tablePoly_zero']

end Assemble

end E2ECompleteness.Pcs
