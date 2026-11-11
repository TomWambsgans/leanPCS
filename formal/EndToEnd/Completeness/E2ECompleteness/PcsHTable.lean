-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the Statement's quotient table (`quotientTable`) read as F1's second message (`PcsBridge.Kc3.readTM`).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import E2ECompleteness.PcsHQuot

/-!
# The quotient table as F1's second message

`tableOf n hHat qHat b₂ coins` is `quotientTable`'s body for `n` cells (`quotientTable_eq`). Its entry at the
bits `(b, d, l₀, l₁, κ)` (coefficient `b`, digit `d`, limb `l₀ + 2 l₁`, kind `κ`) is limb `l₀ + 2 l₁` of slot
`(d, κ)`'s coefficient `b` (`tableOf_getD`): `q`'s (`(0, 0)`), `A₁ = divX q_h`'s (`(1, 0)`), `B₀ = mulX hHat`'s
(`(0, 1)`), `B₁ = (b₀, b₁, b₂)` (`(1, 1)`). `limbPoly_of`: a digit's four limbs on `1, y, y², y³` rebuild the
slot's polynomial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

/-- `Q_h`'s coefficients from `q`'s (`quotientTable`'s `qh`). -/
def qhOf (n : ℕ) (qHat : Array E) : Array E :=
  Array.ofFn (n := 2 * n) fun j ↦
    if j.val = 0 then qHat.getD n 0 + qHat.getD (2 * n) 0
    else if j.val < n then qHat.getD (n + j.val) 0
    else if j.val = n then qHat.getD (2 * n) 0
    else 0

/-- `B₁`'s coefficients. -/
def b1Of (coins : Coins) (b2 : E) (i : ℕ) : E :=
  if i < freeBlind then blindAt coins i else if i = freeBlind then b2 else 0

/-- The slot `(d, κ)`'s coefficient `i`. -/
def slotOf (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) (d κ : Bool) (i : ℕ) : E :=
  if κ = false then (if d = false then qHat.getD i 0 else (divX (qhOf n qHat)).getD i 0)
  else (if d = false then (mulX hHat).getD i 0 else b1Of coins b2 i)

/-- The slack word of coefficient `i` of half `half` of kind `kind` (`quotientTable`'s `slack`): coins' slack word `k`
at kind `0`, half `0`, coefficient `slackAt k`, zero elsewhere. -/
def slackOf (coins : Coins) (kind half i : ℕ) : K :=
  (List.range slackWords).foldl
    (fun acc k ↦ if kind = 0 ∧ half = 0 ∧ i = slackAt k then
        (if h : k < slackWords then coins.slack ⟨k, h⟩ else 0) else acc) 0

/-- `quotientTable`'s body for `n` cells. -/
def tableOf (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) : Array K :=
  let qh : Array E := qhOf n qHat
  let a1 := divX qh
  let b0 := mulX hHat
  Array.ofFn (n := 16 * n) fun w ↦
    let i := w.val % n
    let half := w.val / n % 2
    let limb := w.val / (2 * n) % 4
    let kind := w.val / (8 * n)
    let x : E :=
      if kind = 0 then (if half = 0 then qHat.getD i 0 else a1.getD i 0)
      else (if half = 0 then b0.getD i 0 else b1Of coins b2 i)
    let slack : K := (List.range slackWords).foldl
      (fun acc k ↦ if kind = 0 ∧ half = 0 ∧ i = slackAt k then
          (if h : k < slackWords then coins.slack ⟨k, h⟩ else 0) else acc) 0
    if limb < 3 then limbOf x limb + (if limb < 2 then slack else 0) else slack

theorem quotientTable_eq (cir : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E) :
    quotientTable cir stmt cells₀ coins α β μ =
      tableOf (2 ^ cellVars cir.logRows) (hHatOf cir cells₀ coins α β) (qHatOf cir stmt cells₀ coins α β μ)
        (b2Of cir stmt cells₀ coins α β μ) coins := by
  unfold quotientTable
  rw [quotientParts_eq]
  rfl

/-- The limb `l₀ + 2 l₁`. -/
def limbN (l₀ l₁ : Bool) : ℕ := (if l₀ then 1 else 0) + 2 * (if l₁ then 1 else 0)

theorem idx_snoc4 {M : ℕ} (b : Fin M → Bool) (x w u v : Bool) :
    Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b x) w) u) v : Fin (M + 1 + 1 + 1 + 1) → Bool) =
      Completeness.idx b + (if x then 2 ^ M else 0) + (if w then 2 ^ (M + 1) else 0) +
        (if u then 2 ^ (M + 1 + 1) else 0) + (if v then 2 ^ (M + 1 + 1 + 1) else 0) := by
  rw [Completeness.idx_snoc, Completeness.idx_snoc, Completeness.idx_snoc, Completeness.idx_snoc]

/-- **The table's entry** at `(b, d, l₀, l₁, κ)`. -/
theorem tableOf_getD (n : ℕ) (hn : n = 2 ^ 24) (hHat qHat : Array E) (b2 : E) (coins : Coins)
    (b : Fin 24 → Bool) (d l₀ l₁ κ : Bool) :
    (tableOf n hHat qHat b2 coins).getD
        (Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b d) l₀) l₁) κ : Fin (24 + 1 + 1 + 1 + 1) → Bool)) 0 =
      if limbN l₀ l₁ < 3 then limbOf (slotOf n hHat qHat b2 coins d κ (Completeness.idx b)) (limbN l₀ l₁) +
        (if limbN l₀ l₁ < 2 then slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b) else 0)
      else slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b) := by
  subst hn
  have hb := Completeness.idx_lt b
  rw [idx_snoc4]
  have hw : Completeness.idx b + (if d then 2 ^ 24 else 0) + (if l₀ then 2 ^ (24 + 1) else 0) +
      (if l₁ then 2 ^ (24 + 1 + 1) else 0) + (if κ then 2 ^ (24 + 1 + 1 + 1) else 0) < 16 * 2 ^ 24 := by
    cases d <;> cases l₀ <;> cases l₁ <;> cases κ <;> simp <;> omega
  unfold tableOf
  rw [getD_ofFn _ hw]
  dsimp only
  have e1 : (Completeness.idx b + (if d then 2 ^ 24 else 0) + (if l₀ then 2 ^ (24 + 1) else 0) +
      (if l₁ then 2 ^ (24 + 1 + 1) else 0) + (if κ then 2 ^ (24 + 1 + 1 + 1) else 0)) % 2 ^ 24 = Completeness.idx b := by
    cases d <;> cases l₀ <;> cases l₁ <;> cases κ <;> simp <;> omega
  have e2 : (Completeness.idx b + (if d then 2 ^ 24 else 0) + (if l₀ then 2 ^ (24 + 1) else 0) +
      (if l₁ then 2 ^ (24 + 1 + 1) else 0) + (if κ then 2 ^ (24 + 1 + 1 + 1) else 0)) / 2 ^ 24 % 2 =
      if d then 1 else 0 := by
    cases d <;> cases l₀ <;> cases l₁ <;> cases κ <;> simp <;> omega
  have e3 : (Completeness.idx b + (if d then 2 ^ 24 else 0) + (if l₀ then 2 ^ (24 + 1) else 0) +
      (if l₁ then 2 ^ (24 + 1 + 1) else 0) + (if κ then 2 ^ (24 + 1 + 1 + 1) else 0)) / (2 * 2 ^ 24) % 4 =
      limbN l₀ l₁ := by
    unfold limbN
    cases d <;> cases l₀ <;> cases l₁ <;> cases κ <;> simp <;> omega
  have e4 : (Completeness.idx b + (if d then 2 ^ 24 else 0) + (if l₀ then 2 ^ (24 + 1) else 0) +
      (if l₁ then 2 ^ (24 + 1 + 1) else 0) + (if κ then 2 ^ (24 + 1 + 1 + 1) else 0)) / (8 * 2 ^ 24) =
      if κ then 1 else 0 := by
    cases d <;> cases l₀ <;> cases l₁ <;> cases κ <;> simp <;> omega
  rw [e1, e2, e3, e4]
  unfold slotOf slackOf
  cases d <;> cases κ <;> simp

theorem limbOf_lt (x : E) (e : ℕ) (he : e < 3) : limbOf x e = x.limb ⟨e, he⟩ := by
  unfold limbOf LeanVM.Prover.limbAt
  interval_cases e <;> rfl

theorem tablePoly_zero' {M : ℕ} : tablePoly (fun _ : Fin M → Bool => (0 : E)) = 0 := by
  simp [tablePoly]

/-- **A table's polynomial from its limbs.** -/
theorem tablePoly_limbs {M : ℕ} (x : (Fin M → Bool) → E) :
    tablePoly (fun b ↦ ofK ((x b).limb 0)) + C ey * tablePoly (fun b ↦ ofK ((x b).limb 1)) +
      C (ey ^ 2) * tablePoly (fun b ↦ ofK ((x b).limb 2)) = tablePoly x := by
  unfold tablePoly
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  conv_rhs => rw [E.eq_sum_limbs (x b)]
  rw [PcsBridge.Kc3.ey_eq_y]
  simp only [C_add, C_mul, C_pow]
  ring

theorem tablePoly_add' {M : ℕ} (f g : (Fin M → Bool) → E) :
    tablePoly (fun b => f b + g b) = tablePoly f + tablePoly g := by
  simp only [tablePoly, C_add, add_mul, Finset.sum_add_distrib]

theorem ey_cube : ey ^ 3 = ey + 1 := by
  rw [PcsBridge.Kc3.ey_eq_y]
  exact BF64.ext3Gen_pow_three

/-- A digit's polynomial from its limbs, for any number of variables: limbs `(l₀ + s, l₁ + s, l₂, s)` read the
polynomial of `l₀ + y l₁ + y² l₂`, `1 + y + y³ = 0`. -/
theorem limbPoly_eq {k : ℕ} (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → E) (x : (Fin k → Bool) → E)
    (sl : (Fin k → Bool) → E) (d κ : Bool)
    (h0 : PcsBridge.Kc3.subT c d false false κ = fun b => ofK ((x b).limb 0) + sl b)
    (h1 : PcsBridge.Kc3.subT c d true false κ = fun b => ofK ((x b).limb 1) + sl b)
    (h2 : PcsBridge.Kc3.subT c d false true κ = fun b => ofK ((x b).limb 2))
    (h3 : PcsBridge.Kc3.subT c d true true κ = sl) :
    PcsBridge.Kc3.limbPoly ey c d κ = tablePoly x := by
  unfold PcsBridge.Kc3.limbPoly
  rw [h0, h1, h2, h3, tablePoly_add', tablePoly_add', ← tablePoly_limbs x]
  have h2' : (2 : E[X]) = 0 := CharTwo.two_eq_zero
  have hc : C (ey ^ 3) = C ey + 1 := by rw [ey_cube, C_add, C_1]
  rw [hc]
  linear_combination (tablePoly sl * (1 + C ey)) * h2'

/-- **The quotient table's digit `d` of kind `κ`**, its four limbs on `1, y, y², y³`, is the slot's polynomial. -/
theorem limbPoly_tableOf (n : ℕ) (hn : n = 2 ^ 24) (hHat qHat : Array E) (b2 : E) (coins : Coins)
    (cT : (Fin 28 → Bool) → E) (hcT : ∀ b, cT b = ofK ((tableOf n hHat qHat b2 coins).getD (Completeness.idx b) 0))
    (d κ : Bool) :
    PcsBridge.Kc3.limbPoly (k := 24) ey cT d κ =
      tablePoly (fun b : Fin 24 → Bool => slotOf n hHat qHat b2 coins d κ (Completeness.idx b)) := by
  have hT : ∀ l₀ l₁, PcsBridge.Kc3.subT (k := 24) cT d l₀ l₁ κ = fun b =>
      ofK (if limbN l₀ l₁ < 3 then limbOf (slotOf n hHat qHat b2 coins d κ (Completeness.idx b)) (limbN l₀ l₁) +
        (if limbN l₀ l₁ < 2 then slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b) else 0)
      else slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b)) :=
    fun l₀ l₁ => funext fun b => by
      rw [PcsBridge.Kc3.subT, hcT, tableOf_getD n hn]
  have h0 : PcsBridge.Kc3.subT (k := 24) cT d false false κ =
      fun b => ofK ((slotOf n hHat qHat b2 coins d κ (Completeness.idx b)).limb 0) +
        ofK (slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b)) := by
    rw [hT]; funext b
    rw [if_pos (by decide), show limbN false false = 0 from rfl, if_pos (by decide), limbOf_lt _ 0 (by norm_num),
      Compose.Reduce.ofK_add]
    rfl
  have h1 : PcsBridge.Kc3.subT (k := 24) cT d true false κ =
      fun b => ofK ((slotOf n hHat qHat b2 coins d κ (Completeness.idx b)).limb 1) +
        ofK (slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b)) := by
    rw [hT]; funext b
    rw [if_pos (by decide), show limbN true false = 1 from rfl, if_pos (by decide), limbOf_lt _ 1 (by norm_num),
      Compose.Reduce.ofK_add]
    rfl
  have h2 : PcsBridge.Kc3.subT (k := 24) cT d false true κ =
      fun b => ofK ((slotOf n hHat qHat b2 coins d κ (Completeness.idx b)).limb 2) := by
    rw [hT]; funext b
    rw [if_pos (by decide), show limbN false true = 2 from rfl, if_neg (by decide), add_zero,
      limbOf_lt _ 2 (by norm_num)]
    rfl
  have h3 : PcsBridge.Kc3.subT (k := 24) cT d true true κ =
      fun b => ofK (slackOf coins (if κ then 1 else 0) (if d then 1 else 0) (Completeness.idx b)) := by
    rw [hT]; funext b; rw [if_neg (by decide)]
  exact limbPoly_eq _ _ _ d κ h0 h1 h2 h3

theorem slotOf_ff' (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) (i : ℕ) :
    slotOf n hHat qHat b2 coins false false i = qHat.getD i 0 := by simp only [slotOf, ite_true]
theorem slotOf_tf' (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) (i : ℕ) :
    slotOf n hHat qHat b2 coins true false i = (divX (qhOf n qHat)).getD i 0 := by
  simp only [slotOf, ite_true, Bool.true_eq_false, ite_false]
theorem slotOf_ft' (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) (i : ℕ) :
    slotOf n hHat qHat b2 coins false true i = (mulX hHat).getD i 0 := by
  simp only [slotOf, ite_true, Bool.true_eq_false, ite_false]
theorem slotOf_tt' (n : ℕ) (hHat qHat : Array E) (b2 : E) (coins : Coins) (i : ℕ) :
    slotOf n hHat qHat b2 coins true true i = b1Of coins b2 i := by
  simp only [slotOf, Bool.true_eq_false, ite_false]

section Slots

variable (n : ℕ) (hn : n = 2 ^ 24) (hHat qHat : Array E) (b2 : E) (coins : Coins) (cT : (Fin 28 → Bool) → E)
  (hcT : ∀ b, cT b = ofK ((tableOf n hHat qHat b2 coins).getD (Completeness.idx b) 0))
include hn hcT

theorem limbPoly_ff : PcsBridge.Kc3.limbPoly (k := 24) ey cT false false =
    tablePoly (fun b : Fin 24 → Bool => qHat.getD (Completeness.idx b) 0) := by
  rw [limbPoly_tableOf n hn hHat qHat b2 coins cT hcT false false]
  exact congrArg tablePoly (funext fun b => slotOf_ff' n hHat qHat b2 coins _)

theorem limbPoly_tf : PcsBridge.Kc3.limbPoly (k := 24) ey cT true false =
    tablePoly (fun b : Fin 24 → Bool => (divX (qhOf (2 ^ 24) qHat)).getD (Completeness.idx b) 0) := by
  rw [limbPoly_tableOf n hn hHat qHat b2 coins cT hcT true false, ← hn]
  exact congrArg tablePoly (funext fun b => slotOf_tf' n hHat qHat b2 coins _)

theorem limbPoly_ft : PcsBridge.Kc3.limbPoly (k := 24) ey cT false true =
    tablePoly (fun b : Fin 24 → Bool => (mulX hHat).getD (Completeness.idx b) 0) := by
  rw [limbPoly_tableOf n hn hHat qHat b2 coins cT hcT false true]
  exact congrArg tablePoly (funext fun b => slotOf_ft' n hHat qHat b2 coins _)

theorem limbPoly_tt : PcsBridge.Kc3.limbPoly (k := 24) ey cT true true =
    tablePoly (fun b : Fin 24 → Bool => b1Of coins b2 (Completeness.idx b)) := by
  rw [limbPoly_tableOf n hn hHat qHat b2 coins cT hcT true true]
  exact congrArg tablePoly (funext fun b => slotOf_tt' n hHat qHat b2 coins _)

end Slots

end E2ECompleteness.Pcs.H
