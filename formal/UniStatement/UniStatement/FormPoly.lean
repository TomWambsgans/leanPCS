-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Moved from `formal/UniSound`'s `UniSound/Ids/Model.lean`
-- (`toK`, `formK`, `tupleK`) and `UniSound/Ids/LvRealize.lean` (the polynomial normal form), which import this module;
-- the declarations keep their names and namespaces.
module

public import UniStatement.TablesBase
public import Clean.Circuit.Expression

/-!
# A verifier form at a row, and polynomials in a normal form

`tupleK`: a tuple of the verifier's forms (`UniStatement.Form`) read at a row of `K` values, as a bus tuple of sixteen
coordinates (`formK`, its coefficients read in `K` by `toK`). `LvR.SP`: polynomials in the row's variables in a normal
form (`spNorm`: monomials sorted and merged, zero coefficients dropped), which keeps the value (`spEval_spNorm`), and
the readings of Clean's expressions (`exprSP`, `eval_exprSP`) and of forms (`formSP`, `formK_eq`) as such
polynomials; `tupleK_eq` reads `tupleK` through them. Instruction-set-independent: `UniSound` reads Lv42's tables
through them (`uni_tuples_eq`), `KeccakFlushes` the Keccak VM's `SHA3` table.
-/

@[expose] public section

namespace UniSound.Ids

open LeanVM.Parameters UniStatement

/-- An element's base limb (`K`'s part). -/
def toK (e : E) : K := e.limb 0

/-- A form at a row of `K` values (its coefficients read in `K`). -/
def formK (f : Form) (row : ℕ → K) : K :=
  (f.map fun mc ↦ match mc.1 with
    | [] => toK mc.2
    | [i] => toK mc.2 * row i
    | [i, j] => toK mc.2 * row i * row j
    | _ => 0).sum

/-- A tuple at a row, as a bus tuple of sixteen coordinates. -/
def tupleK (tuple : List Form) (row : ℕ → K) : Vector K 16 :=
  Vector.ofFn fun s ↦ formK (tuple.getD s.val []) row

namespace LvR

/-! ## Polynomials in a normal form -/

/-- A polynomial in the row's variables: monomials (lists of variables) with `K` coefficients. -/
abbrev SP := List (List ℕ × K)

/-- A monomial's value at a row. -/
def monoVal (r : ℕ → K) (m : List ℕ) : K := (m.map r).prod

/-- A polynomial's value at a row. -/
def spEval (r : ℕ → K) (p : SP) : K := (p.map fun mc ↦ mc.2 * monoVal r mc.1).sum

@[simp] theorem spEval_nil (r : ℕ → K) : spEval r [] = 0 := rfl

@[simp] theorem spEval_cons (r : ℕ → K) (a : List ℕ × K) (p : SP) :
    spEval r (a :: p) = a.2 * monoVal r a.1 + spEval r p := by
  simp [spEval]

theorem spEval_append (r : ℕ → K) (p q : SP) : spEval r (p ++ q) = spEval r p + spEval r q := by
  simp [spEval]

theorem monoVal_append (r : ℕ → K) (a b : List ℕ) : monoVal r (a ++ b) = monoVal r a * monoVal r b := by
  simp [monoVal]

/-- A monomial's variables, sorted (insertion sort: the kernel reduces it). -/
def sortMono (m : List ℕ) : List ℕ := m.insertionSort (· ≤ ·)

theorem monoVal_sortMono (r : ℕ → K) (m : List ℕ) : monoVal r (sortMono m) = monoVal r m :=
  ((List.perm_insertionSort _ m).map r).prod_eq

/-- Add `c · m` to a polynomial sorted by `monoLt`, merging a monomial it has. -/
def spIns (m : List ℕ) (c : K) : SP → SP
  | [] => [(m, c)]
  | (k, v) :: rest =>
    if k = m then (k, v + c) :: rest
    else if monoLt m k then (m, c) :: (k, v) :: rest
    else (k, v) :: spIns m c rest

theorem spEval_spIns (r : ℕ → K) (m : List ℕ) (c : K) (p : SP) :
    spEval r (spIns m c p) = c * monoVal r m + spEval r p := by
  induction p with
  | nil => simp [spIns]
  | cons a p ih =>
    obtain ⟨k, v⟩ := a
    simp only [spIns]
    split_ifs with h1 h2
    · subst h1
      simp only [spEval_cons]
      ring
    · simp only [spEval_cons]
    · simp only [spEval_cons, ih]
      ring

/-- **The normal form**: monomials sorted and merged, zero coefficients dropped. -/
def spNorm (p : SP) : SP :=
  (p.foldr (fun mc acc ↦ spIns (sortMono mc.1) mc.2 acc) []).filter fun mc ↦ decide (mc.2 ≠ 0)

theorem spEval_foldr (r : ℕ → K) (p : SP) :
    spEval r (p.foldr (fun mc acc ↦ spIns (sortMono mc.1) mc.2 acc) []) = spEval r p := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [List.foldr_cons, spEval_spIns, ih, monoVal_sortMono, spEval_cons]

theorem spEval_filter (r : ℕ → K) (p : SP) :
    spEval r (p.filter fun mc ↦ decide (mc.2 ≠ 0)) = spEval r p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, spEval_cons, h, zero_mul, zero_add]
    · rw [List.filter_cons_of_pos (by simp [h]), spEval_cons, spEval_cons, ih]

/-- **The normal form keeps the value.** -/
theorem spEval_spNorm (r : ℕ → K) (p : SP) : spEval r (spNorm p) = spEval r p := by
  rw [spNorm, spEval_filter, spEval_foldr]

/-- The product of two polynomials. -/
def spMul (p q : SP) : SP := p.flatMap fun a ↦ q.map fun b ↦ (a.1 ++ b.1, a.2 * b.2)

theorem spEval_map_mul (r : ℕ → K) (a : List ℕ × K) (q : SP) :
    spEval r (q.map fun b ↦ (a.1 ++ b.1, a.2 * b.2)) = a.2 * monoVal r a.1 * spEval r q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    rw [List.map_cons, spEval_cons, spEval_cons, ih, monoVal_append]
    ring

theorem spEval_spMul (r : ℕ → K) (p q : SP) : spEval r (spMul p q) = spEval r p * spEval r q := by
  induction p with
  | nil => simp [spMul]
  | cons a p ih =>
    rw [spMul, List.flatMap_cons, spEval_append, spEval_map_mul, ← spMul, ih, spEval_cons]
    ring

/-! ## Clean's expressions and the verifier's forms as polynomials -/

/-- A Clean expression on a row of `n` cells as a polynomial (a variable past the row is `0`, as Clean
reads a missing cell). -/
def exprSP (n : ℕ) : Expression K → SP
  | .var v => if v.index < n then [([v.index], 1)] else []
  | .const c => [([], c)]
  | .add x y => exprSP n x ++ exprSP n y
  | .mul x y => spMul (exprSP n x) (exprSP n y)

/-- **An expression's value on a row is its polynomial's.** -/
theorem eval_exprSP (n : ℕ) (R : ℕ → K) (data : ProverData K) (e : Expression K) :
    e.eval (Environment.fromArray (Array.ofFn fun i : Fin n ↦ R i.val) data) = spEval R (exprSP n e) := by
  induction e with
  | var v =>
    simp only [Expression.eval, exprSP]
    split_ifs with h
    · simp [h, monoVal]
    · simp [h]
  | const c => simp [Expression.eval, exprSP, monoVal]
  | add x y hx hy => simp only [Expression.eval, exprSP, spEval_append, hx, hy]
  | mul x y hx hy => simp only [Expression.eval, exprSP, spEval_spMul, hx, hy]

/-- A form as a polynomial: its coefficients read in `K` (`toK`), a monomial of more than two variables
`0` (as `formK` reads it). -/
def formSP (f : Form) : SP := f.map fun mc ↦ (mc.1, if mc.1.length ≤ 2 then toK mc.2 else 0)

/-- **A form's value on a row is its polynomial's.** -/
theorem formK_eq (f : Form) (R : ℕ → K) : formK f R = spEval R (formSP f) := by
  simp only [formK, formSP, spEval, List.map_map]
  congr 1
  refine List.map_congr_left fun mc _ ↦ ?_
  obtain ⟨m, c⟩ := mc
  match m with
  | [] => simp [monoVal]
  | [i] => simp [monoVal]
  | [i, j] => simp only [Function.comp_apply, monoVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil]; simp; ring
  | _ :: _ :: _ :: _ => simp

/-! ## Tuples -/

/-- No prover data (a flush's polynomials read none). -/
def noData : ProverData K := fun _ _ ↦ #[]

/-- Sixteen polynomials' values at a row. -/
def tupleOfSP (R : ℕ → K) (l : List SP) : Vector K 16 := Vector.ofFn fun s ↦ spEval R (l.getD s.val [])

/-- A tuple of forms as sixteen polynomials. -/
def tupSP (tup : List Form) : List SP := (List.range 16).map fun s ↦ formSP (tup.getD s [])

theorem getD_map_range (g : ℕ → SP) (s : ℕ) (hs : s < 16) :
    (((List.range 16).map g).map spNorm).getD s [] = spNorm (g s) := by
  rw [List.getD_eq_getElem _ _ (by simp [hs])]
  simp

/-- **`tupleK` is its polynomials' values.** -/
theorem tupleK_eq (tup : List Form) (R : ℕ → K) : tupleK tup R = tupleOfSP R ((tupSP tup).map spNorm) := by
  apply Vector.ext
  intro s hs
  simp only [tupleK, tupleOfSP, tupSP, Vector.getElem_ofFn]
  rw [getD_map_range _ s hs, spEval_spNorm, formK_eq]

end LvR

end UniSound.Ids

end
