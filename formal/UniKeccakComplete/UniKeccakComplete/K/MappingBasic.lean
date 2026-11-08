-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): `tupleOf`; `formal/UniStatement`'s `formK`, `tupleK` (the Keccak VM's tuples at a row).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/MappingBasic.lean`.
import UniKeccakComplete.K.Honest
import UniComplete.Domain
import UniKeccakSound.IdsReal.Realize
import UniKeccakSound.IdsReal.LaneSlots
import UniKeccakSound.IdsMain.Cvec
import UniKeccakSound.IdsMain.Reading
import UniKeccakSound.Fs.LayerK
import UniKeccak.Fits

/-!
# The mapping's toolkit (milestone 4): constants, forms, tuples

The honest trace (`honestTrace`) is the Keccak VM's stack placed in the univariate PIOP's order; its properties
(`TraceHonest`) are read off the Keccak VM's relation (`KvHonest`). This file holds what every part of that reading uses:

* **The constants** (`gen_eq`, `gpow_eq`, `sepMem_eq`, `sepBytecode_eq`, `ofBits_four`): `layout.rs`'s `E`-constants
  are `K`'s generator's powers, `GEN = ofK g`, `gpow i = (ofK g)^i` (`epow` is square and multiply,
  `epow_eq`), `SEP_MEM = ofK g`, `SEP_BYTECODE = (ofK g)^2`, `K.ofBits 4 = g^2` (the setup's slot `0`); Lv42's
  separators are `gpow 0, 1, 2` of `K` (`channelSep`).
* **Forms at a row** (`formE_*`, `tupleAt_eq`): a form's value is the sum of its terms (`formE_eq_sum`), so the
  `Form` builders of `layout.rs` (`addAt`, `addScaled`, `add`, `sum`, `term`, `col`, `prod`, `constant`) evaluate
  term by term, whatever order the map keeps; a tuple of at most sixteen forms is their values then zeros.
* **The Keccak VM's tuples in `E`** (`phi`, `phi_tupleOf`): a sixteen-slot `K`-tuple, limb by limb in `E`; injective
  (`phi_injective`), so it carries the Keccak VM's balance (a permutation of `K`-tuples) to the PIOP's (of
  `E`-lists).
* **A tuple of forms at a row of `K` values** (`formE_ofK`, `tupleAt_ofK`): where every coefficient is in `K` and
  every monomial has degree at most two (the tables' forms), the PIOP's tuple in `E` (`tupleAt`) is `phi` of
  `tupleK`, the `K`-tuple `UniKeccakSound` reads the Keccak VM's flushes as (`rowTuplesK_eq`).
-/

namespace UniKeccakComplete.Mapping

open UniComplete

open UniStatement LeanVM.Parameters

/-! ### The constants -/

theorem ofKZero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofKOne : ofK 1 = 1 := map_one (algebraMap K E)

theorem ofKPow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

/-- Square and multiply computes the power: `epowAux fuel base out n = out · base^n` while `n < 2^fuel`. -/
theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, h => by
    rw [epowAux]
    by_cases h0 : n = 0
    · subst h0
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0),
        epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega)]
      conv_rhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · simp [h2]
      · simp only [h2, ite_true, pow_one]
        ring

/-- **`E::pow` is the power.** -/
theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

/-- `GEN = E(2)` is `g` in `E`. -/
theorem gen_eq : UniStatement.gen = ofK LeanVM.Parameters.g := by decide +kernel

/-- **`gpow i = GEN^i`** is `(ofK g)^i`. -/
theorem gpow_eq (n : ℕ) : UniStatement.gpow n = ofK LeanVM.Parameters.g ^ n := by
  rw [UniStatement.gpow, epow_eq, gen_eq]

/-- `SEP_MEM = g`. -/
theorem sepMem_eq : sepMem = ofK LeanVM.Parameters.g := gen_eq

/-- `K.ofBits 4` is `g^2`. -/
theorem ofBits_four : K.ofBits 4 = LeanVM.Parameters.g ^ 2 := by decide +kernel

/-- `SEP_BYTECODE = g^2`. -/
theorem sepBytecode_eq : sepBytecode = ofK LeanVM.Parameters.g ^ 2 := by
  rw [← ofKPow]
  decide +kernel

/-- `SEP_STATE = 1`. -/
theorem sepState_eq : sepState = 1 := rfl

/-! ### Forms at a row -/

/-- A monomial's value at a row. -/
def monoE (mono : List ℕ) (col : ℕ → E) : E := mono.foldl (fun p j ↦ p * col j) 1

theorem foldl_add_shift {α : Type} (F : α → E) :
    ∀ (l : List α) (a : E), l.foldl (fun acc x ↦ acc + F x) a = a + (l.map F).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_shift F l, List.map_cons, List.sum_cons]
    ring

/-- **A form's value is the sum of its terms.** -/
theorem formE_eq_sum (f : Form) (col : ℕ → E) :
    formE f col = (f.map fun x ↦ x.2 * monoE x.1 col).sum := by
  show f.foldl (fun acc x ↦ acc + x.2 * monoE x.1 col) 0 = _
  rw [foldl_add_shift, zero_add]

theorem formE_nil (col : ℕ → E) : formE [] col = 0 := rfl

theorem formE_addAt (col : ℕ → E) (mono : List ℕ) (c : E) :
    ∀ f : Form, formE (f.addAt mono c) col = formE f col + c * monoE mono col
  | [] => by simp [Form.addAt, formE_eq_sum]
  | (k, v) :: rest => by
    rw [Form.addAt]
    split_ifs with h1
    · have hk : k = mono := by simpa using h1
      subst hk
      simp only [formE_eq_sum, List.map_cons, List.sum_cons]
      ring
    · simp only [formE_eq_sum, List.map_cons, List.sum_cons]
      ring
    · have ih := formE_addAt col mono c rest
      simp only [formE_eq_sum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem formE_addScaled (col : ℕ → E) (w : E) :
    ∀ (other f : Form), formE (f.addScaled other w) col = formE f col + w * formE other col
  | [], f => by simp [Form.addScaled, formE_nil]
  | (m, c) :: rest, f => by
    have ih := formE_addScaled col w rest (f.addAt m (w * c))
    simp only [Form.addScaled, List.foldl_cons] at ih ⊢
    rw [ih, formE_addAt]
    simp only [formE_eq_sum, List.map_cons, List.sum_cons]
    ring

theorem formE_add (col : ℕ → E) (f f' : Form) : formE (f.add f') col = formE f col + formE f' col := by
  rw [Form.add, formE_addScaled, one_mul]

theorem formE_term (col : ℕ → E) (mono : List ℕ) (c : E) :
    formE (Form.term mono c) col = c * monoE mono col := by
  simp [Form.term, formE_eq_sum]

theorem formE_constant (col : ℕ → E) (v : E) : formE (constant v) col = v := by
  simp [constant, formE_term, monoE]

theorem formE_col (col' : ℕ → E) (i e : ℕ) : formE (col i e) col' = ofK LeanVM.Parameters.g ^ e * col' i := by
  simp [UniStatement.col, formE_term, monoE, gpow_eq]

theorem formE_prod (col' : ℕ → E) (a b e : ℕ) :
    formE (prod a b e) col' = ofK LeanVM.Parameters.g ^ e * (col' (min a b) * col' (max a b)) := by
  simp [UniStatement.prod, formE_term, monoE, gpow_eq]

/-- A product of two columns in order. -/
theorem formE_prod_le (col' : ℕ → E) (a b e : ℕ) (h : a ≤ b) :
    formE (prod a b e) col' = ofK LeanVM.Parameters.g ^ e * (col' a * col' b) := by
  rw [formE_prod, min_eq_left h, max_eq_right h]

theorem formE_sum_go (col : ℕ → E) :
    ∀ (forms : List Form) (f : Form), formE (forms.foldl Form.add f) col =
      formE f col + (forms.map (formE · col)).sum
  | [], f => by simp
  | x :: l, f => by
    rw [List.foldl_cons, formE_sum_go col l, formE_add, List.map_cons, List.sum_cons]
    ring

theorem formE_sum (col : ℕ → E) (forms : List Form) :
    formE (Form.sum forms) col = (forms.map (formE · col)).sum := by
  rw [Form.sum, formE_sum_go, formE_nil, zero_add]

/-- **A tuple of at most sixteen forms**: their values, then zeros. -/
theorem tupleAt_eq (tuple : List Form) (col : ℕ → E) (h : tuple.length ≤ 16) :
    tupleAt tuple col = tuple.map (formE · col) ++ List.replicate (16 - tuple.length) 0 := by
  apply List.ext_getElem (by simp [tupleAt]; omega)
  intro n h1 h2
  simp only [tupleAt, List.length_map, List.length_range] at h1
  simp only [tupleAt, List.getElem_map, List.getElem_range]
  by_cases hn : n < tuple.length
  · rw [List.getElem_append_left (by simpa using hn)]
    simp [List.getElem?_eq_getElem hn]
  · rw [List.getElem_append_right (by simpa using hn)]
    simp [List.getElem?_eq_none (by omega : tuple.length ≤ n), formE_nil]

/-! ### The Keccak VM's tuples in `E` -/

/-- **A sixteen-slot `K`-tuple in `E`**, slot by slot. -/
def phi (v : Vector K 16) : List E := v.toList.map ofK

theorem phi_injective : Function.Injective phi := by
  intro a b h
  have h' : a.toList = b.toList := List.map_injective_iff.mpr ofK_injective h
  exact Vector.toList_inj.mp h'

open Lv42.Protocol.LeanIsa in
/-- A message's tuple in `E`: the separator, the message, then zeros. -/
theorem phi_tupleOf (σ : K) (m : Array K) (h : m.size ≤ 15) :
    phi (tupleOf σ m) = ofK σ :: m.toList.map ofK ++ List.replicate (15 - m.size) 0 := by
  apply List.ext_getElem (by simp [phi]; omega)
  intro n h1 h2
  simp only [phi, List.length_map, Vector.length_toList] at h1
  simp only [phi, List.getElem_map, Vector.getElem_toList, tupleOf, Vector.getElem_ofFn]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, List.cons_append,
      List.getElem_cons_succ]
    by_cases hn : n < m.size
    · rw [List.getElem_append_left (by simpa using hn)]
      simp [Array.getElem?_eq_getElem hn]
    · rw [List.getElem_append_right (by simpa using hn)]
      simp [Array.getElem?_eq_none (by omega : m.size ≤ n)]

/-! ### A tuple of forms at a row of `K` values -/

/-- A form whose coefficients are in `K` and whose monomials have degree at most two. -/
def FormOk (f : Form) : Prop := ∀ mc ∈ f, mc.1.length ≤ 2 ∧ ofK (UniSound.Ids.toK mc.2) = mc.2

/-- **A form at a row of `K` values is `formK` in `E`.** -/
theorem formE_ofK (f : Form) (R : ℕ → K) (hf : FormOk f) :
    formE f (fun c ↦ ofK (R c)) = ofK (UniSound.Ids.formK f R) := by
  rw [formE_eq_sum]
  induction f with
  | nil => simp [UniSound.Ids.formK]
  | cons mc f ih =>
    have ih' := ih fun m hm ↦ hf m (List.mem_cons_of_mem _ hm)
    obtain ⟨hlen, hK⟩ := hf mc List.mem_cons_self
    unfold UniSound.Ids.formK at ih' ⊢
    rw [List.map_cons, List.sum_cons, ih', List.map_cons, List.sum_cons, UniSound.Ids.ofK_add]
    congr 1
    rcases mc with ⟨m, cf⟩
    rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨k, m⟩⟩⟩
    · simp only [monoE, List.foldl_nil, mul_one]
      exact hK.symm
    · simp only [monoE, List.foldl_cons, List.foldl_nil, one_mul]
      rw [UniSound.Ids.ofK_mul, hK]
    · simp only [monoE, List.foldl_cons, List.foldl_nil, one_mul]
      rw [UniSound.Ids.ofK_mul, UniSound.Ids.ofK_mul, hK, mul_assoc]
    · simp at hlen

/-- **A tuple of forms at a row of `K` values is `phi` of `tupleK`.** -/
theorem tupleAt_ofK (tup : List Form) (R : ℕ → K) (h : ∀ f ∈ tup, FormOk f) :
    tupleAt tup (fun c ↦ ofK (R c)) = phi (UniSound.Ids.tupleK tup R) := by
  apply List.ext_getElem (by simp [tupleAt, phi])
  intro n h1 h2
  simp only [tupleAt, List.length_map, List.length_range] at h1
  simp only [tupleAt, phi, List.getElem_map, List.getElem_range, Vector.getElem_toList, UniSound.Ids.tupleK,
    Vector.getElem_ofFn]
  by_cases hn : n < tup.length
  · rw [List.getD_eq_getElem _ _ hn]
    exact formE_ofK _ R (h _ (List.getElem_mem hn))
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [formE_nil, UniSound.Ids.formK]

end UniKeccakComplete.Mapping
