-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import QuotientSecurity.Cantor

/-!
# The quotient table from its three committed parts

The quotient table `T` has `m + 6` variables: a coefficient (`m`), then a chunk's digit (`d₀, d₁`), kind
(`k₀, k₁`) and limb (`e₀, e₁`), the last six coordinates in this order (`protocol::quotient_parts`). It is
committed as three subcubes: `H` (kind `0`, `d₁ = 0`: coordinates the coefficient, `d₀`, `e₀`, `e₁`), `Q` (kind
`1`: the coefficient, `d₀`, `d₁`, `e₀`, `e₁`) and `G` (kind `2`, `d₁ = 0`, limb `0`: the coefficient, `d₀`);
everything else of `T` is zero (`assemble`).

**`mle_assemble`**: `T(P) = w_H(P) H(P_H) + w_Q(P) Q(P_Q) + w_G(P) G(P_G)`, each part's point the free
coordinates of `P` and its weight the `eq` of the fixed ones: `w_H = (1 + d₁)(1 + k₀)(1 + k₁)`,
`w_Q = k₀ (1 + k₁)`, `w_G = (1 + d₁)(1 + k₀) k₁ (1 + e₀)(1 + e₁)`.
-/

namespace PcsBridge

open QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2] {m : ℕ}

/-- **The quotient table** of the three parts: `H` on kind `0` with `d₁ = 0`, `Q` on kind `1`, `G` on kind `2`
with `d₁ = 0` and limb `0`, zero elsewhere. -/
def assemble (cH : (Fin (m + 1 + 1 + 1) → Bool) → F) (cQ : (Fin (m + 1 + 1 + 1 + 1) → Bool) → F)
    (cG : (Fin (m + 1) → Bool) → F) : (Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F := fun b =>
  let e₁ := b (Fin.last _)
  let b₅ := Fin.init b
  let e₀ := b₅ (Fin.last _)
  let b₄ := Fin.init b₅
  let k₁ := b₄ (Fin.last _)
  let b₃ := Fin.init b₄
  let k₀ := b₃ (Fin.last _)
  let b₂ := Fin.init b₃
  let d₁ := b₂ (Fin.last _)
  let b₁ := Fin.init b₂
  let d₀ := b₁ (Fin.last _)
  let low := Fin.init b₁
  if !k₀ && !k₁ && !d₁ then cH (Fin.snoc (Fin.snoc (Fin.snoc low d₀) e₀) e₁)
  else if k₀ && !k₁ then cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) e₀) e₁)
  else if !k₀ && k₁ && !d₁ && !e₀ && !e₁ then cG (Fin.snoc low d₀)
  else 0

theorem mle_zero' (u : Fin m → F) : mle (fun _ : Fin m → Bool => (0 : F)) u = 0 := by
  simp [mle]

/-- **The quotient table's extension through its parts.** -/
theorem mle_assemble (cH : (Fin (m + 1 + 1 + 1) → Bool) → F)
    (cQ : (Fin (m + 1 + 1 + 1 + 1) → Bool) → F) (cG : (Fin (m + 1) → Bool) → F)
    (low : Fin m → F) (d₀ d₁ k₀ k₁ e₀ e₁ : F) :
    mle (assemble cH cQ cG)
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) k₀) k₁) e₀) e₁) =
      (1 + d₁) * (1 + k₀) * (1 + k₁) * mle cH (Fin.snoc (Fin.snoc (Fin.snoc low d₀) e₀) e₁) +
      k₀ * (1 + k₁) * mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) e₀) e₁) +
      (1 + d₁) * (1 + k₀) * k₁ * (1 + e₀) * (1 + e₁) * mle cG (Fin.snoc low d₀) := by
  simp only [mle_snoc]
  simp only [assemble, Fin.init_snoc, Fin.snoc_last, Bool.not_false, Bool.not_true, Bool.and_true,
    Bool.and_false, Bool.true_and, Bool.false_and, ite_true, ite_false, Bool.false_eq_true,
    mle_zero', if_true, if_false]
  ring

end PcsBridge
