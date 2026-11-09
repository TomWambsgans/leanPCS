-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Eval

/-!
# The identities' degrees (`DegBoundP`)

Every polynomial of `polysOf` is bounded from its construction, symbolically in the shape's numbers;
no polynomial is evaluated.

* **Columns** (`ndeg_colPoly`): a column's polynomial at a polynomial point has degree at most the sum
  of its point's coordinates' degrees over its limb's variables, which `StackLayout.new` sets to the
  column's (`c1_limbs`, `c2_limbs`, `setup_limbs`): at the digits `w_l` (degree `2^l`) a column of `v`
  variables has degree below `2^v`; a heap block's restriction `R_b` below `2^r`; `q_flock`'s slot at
  `y(X)` at most `h_B 2^(h_B − 1)` (`y_l = Σ_{m<h_B} a_{l,m} X^(2^m)`).
* **Products** (`ndeg_listProd`): a table's pull product at most `Σ_j deg(τ_j) 2^r`, `deg(τ_j)` its tuple's
  largest monomial (`fdeg`, the kernel reads the six tables' monomials, not their coefficients:
  `tables_pullDeg`, `tables_pushDeg`); `Z_act` below `2^(r+1)`; the lift `w_m / w_r` at most `2^m`.
* **Quotients** (`ndeg_quotP`, `chunks_sum_le`): `Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)` has degree at most
  `Σ_c 2^(e_c)`, and `chunks` covers `n` coefficients with `Σ_c 2^(e_c) ≤ 5n/4` (the greedy chunks,
  the third rounded up).
* **`degBound_of`**: the degrees' sum is at most `treeB + wB + Σ_b blockB b` at every shape whose
  heap is `HeapGood`; **`degBound_reference`**: at most `50,708,397 < 2^25.6` at the reference shape
  (the tree `2^24 + 2`, `Z_bad P_W` `5,636,097`, the six tables' leaves `22,265,774`, the memory's
  `4,718,590`, the bytecode's `1,179,646`, the unused block's `2^17`), by `norm_num`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial UniSound.Ids.Eval

/-! ## Degrees of sums and products -/

theorem ndeg_listSum (l : List (Polynomial E)) (B : ℕ) (h : ∀ p ∈ l, p.natDegree ≤ B) :
    l.sum.natDegree ≤ B := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact (natDegree_add_le _ _).trans (max_le (h p (List.mem_cons_self ..))
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)))

theorem ndeg_listProd : ∀ l : List (Polynomial E), l.prod.natDegree ≤ (l.map natDegree).sum
  | [] => by simp
  | p :: l => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact natDegree_mul_le.trans (Nat.add_le_add_left (ndeg_listProd l) _)

theorem ndeg_add {p q : Polynomial E} {B : ℕ} (hp : p.natDegree ≤ B) (hq : q.natDegree ≤ B) :
    (p + q).natDegree ≤ B :=
  (natDegree_add_le _ _).trans (max_le hp hq)

theorem ndeg_mul {p q : Polynomial E} {a b B : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (h : a + b ≤ B) : (p * q).natDegree ≤ B :=
  natDegree_mul_le.trans ((Nat.add_le_add hp hq).trans h)

theorem ndeg_C (a : E) (B : ℕ) : (C a).natDegree ≤ B := by simp

theorem ndeg_Cmul {a : E} {p : Polynomial E} {B : ℕ} (hp : p.natDegree ≤ B) : (C a * p).natDegree ≤ B :=
  (natDegree_C_mul_le _ _).trans hp

theorem list_sum_map_le {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..)) (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-! ## Columns at polynomial points -/

/-- **A column's polynomial**: at most the point's coordinates' degrees summed over each limb's
variables. -/
theorem ndeg_colPoly (L : StackLayout) (V : ℕ) (St : Stk) (col : Column) (pt : ℕ → Polynomial E) (B : ℕ)
    (h : ∀ b ∈ L.limbs col, ∑ l ∈ range b.2.1, (pt l).natDegree ≤ B) :
    (colPoly L V St col pt).natDegree ≤ B := by
  unfold colPoly
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul ((natDegree_mlP_le _ _ _).trans (h b hb))

theorem sum_pow_add_le (v s : ℕ) : ∑ l ∈ range v, 2 ^ (l + s) ≤ 2 ^ (v + s) := by
  have h := sum_two_pow_lt v
  have e : ∑ l ∈ range v, 2 ^ (l + s) = (∑ l ∈ range v, 2 ^ l) * 2 ^ s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ pow_add 2 l s
  rw [e, pow_add]
  exact Nat.mul_le_mul_right _ h.le

/-- Coordinates of degree at most `2^(l+s)`: the sum over `v` variables at most `2^(v+s)`. -/
theorem sum_deg_pow (pt : ℕ → Polynomial E) (v s : ℕ) (h : ∀ l < v, (pt l).natDegree ≤ 2 ^ (l + s)) :
    ∑ l ∈ range v, (pt l).natDegree ≤ 2 ^ (v + s) :=
  (Finset.sum_le_sum fun l hl ↦ h l (mem_range.mp hl)).trans (sum_pow_add_le v s)

/-- Coordinates of degree `2^l` below `r` and constant above: the sum at most `2^r`. -/
theorem sum_deg_below (pt : ℕ → Polynomial E) (v r : ℕ)
    (h : ∀ l < v, (pt l).natDegree ≤ if l < r then 2 ^ l else 0) :
    ∑ l ∈ range v, (pt l).natDegree ≤ 2 ^ r := by
  refine (Finset.sum_le_sum fun l hl ↦ h l (mem_range.mp hl)).trans ?_
  rw [← Finset.sum_filter]
  refine (Finset.sum_le_sum_of_subset fun l hl ↦ ?_).trans (sum_two_pow_lt r).le
  simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
  exact hl.2

theorem digit_le (l : ℕ) : (digitP l).natDegree ≤ 2 ^ (l + 0) := by
  rw [add_zero]; exact natDegree_digitP l

/-- A coordinate functional `y_l = Σ_m a_{l,m} X^(2^m)`. -/
theorem ndeg_yP (a : Array (Array K)) (l : ℕ) : (yP a l).natDegree ≤ 2 ^ (a.size - 1) := by
  unfold yP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hm
  exact ndeg_Cmul ((natDegree_X_pow_le _).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-! ## Lifts, `Z_act`, `Z_bad` -/

theorem range'_pow_sum (r : ℕ) : ∀ k, ((List.range' r k).map (2 ^ ·)).sum + 2 ^ r = 2 ^ (r + k)
  | 0 => by simp
  | k + 1 => by
    rw [List.range'_succ, List.map_cons, List.sum_cons]
    have := range'_pow_sum (r + 1) k
    rw [show r + (k + 1) = r + 1 + k by ring, ← this, pow_succ]
    ring

theorem digit_one_le (j : ℕ) : (digitP j + 1).natDegree ≤ 2 ^ j :=
  ndeg_add (natDegree_digitP j) (by simp)

/-- **The lift `w_m / w_r`**: at most `2^m`. -/
theorem ndeg_liftP (r m : ℕ) : (liftP r m).natDegree ≤ 2 ^ m := by
  unfold liftP
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map]
  refine (list_sum_map_le _ _ (2 ^ ·) fun j _ ↦ digit_one_le j).trans ?_
  by_cases hrm : r ≤ m
  · have h := range'_pow_sum r (m - r)
    have e : r + (m - r) = m := by omega
    rw [e] at h
    have := Nat.two_pow_pos r
    omega
  · rw [show m - r = 0 by omega]
    simp

theorem ndeg_zFold (F : ℕ → Polynomial E) (hF : ∀ b, (F b).natDegree ≤ 2 ^ b) :
    ∀ (l : List ℕ) (P : Polynomial E) (A : ℕ), P.natDegree ≤ A →
      (l.foldl (fun prod b ↦ prod * F b) P).natDegree ≤ A + (l.map (2 ^ ·)).sum
  | [], P, A, h => by simpa using h
  | b :: l, P, A, h => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    exact ndeg_zFold F hF l _ _ (ndeg_mul h (hF b) le_rfl)

/-- **`Z_act`**: below `2^(r+1)`. -/
theorem ndeg_zActP (bits : List E) (r : ℕ) : (zActP bits r).natDegree ≤ 2 ^ (r + 1) := by
  unfold zActP
  have hF : ∀ b, (1 + C (bits.getD b 0) * (digitP b + C (cosetOffset r b + 1))).natDegree ≤ 2 ^ b :=
    fun b ↦ ndeg_add (by simp) (ndeg_Cmul (ndeg_add (natDegree_digitP b) (ndeg_C _ _)))
  have h0 : (1 + C (bits.getD r 0) * (digitP r + 1)).natDegree ≤ 2 ^ r :=
    ndeg_add (by simp) (ndeg_Cmul (digit_one_le r))
  refine (ndeg_zFold _ hF (List.range r) _ _ h0).trans ?_
  have h := range'_pow_sum 0 r
  rw [zero_add, pow_zero] at h
  rw [List.range_eq_range', pow_succ]
  omega

/-- **`Z_bad = (y_0 + X)(y_0 + p_0)`**: at most `2 · 2^(h_B − 1)`. -/
theorem ndeg_zBad (S : Shape) (p0 : E) :
    (zBad S p0).natDegree ≤ 2 * 2 ^ (S.heights.getD opSha3 0 - 1) := by
  unfold zBad
  have hy := ndeg_yP (coordinateFunctionals (S.heights.getD opSha3 0)) 0
  rw [coordinateFunctionals_size] at hy
  have h1 : (1 : ℕ) ≤ 2 ^ (S.heights.getD opSha3 0 - 1) := Nat.one_le_two_pow
  exact ndeg_mul (ndeg_add hy (natDegree_X_le.trans h1)) (ndeg_add hy (ndeg_C _ _)) (by omega)

/-! ## Forms, tuples, fingerprint products -/

/-- A form's largest monomial. -/
def formMax (f : Form) : ℕ := (f.map fun mc ↦ mc.1.length).foldr max 0

/-- **A tuple's degree bound**: its largest monomial, at least `1` (the verifier's `tupleDegree` without
the zero-coefficient check). -/
def fdeg (tup : List Form) : ℕ := max 1 ((tup.map formMax).foldr max 0)

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem le_fdeg (tup : List Form) : ∀ f ∈ tup, ∀ mc ∈ f, mc.1.length ≤ fdeg tup := fun f hf mc hmc ↦
  (le_foldr_max (l := f.map fun mc ↦ mc.1.length) (List.mem_map.mpr ⟨mc, hmc, rfl⟩)).trans
    ((le_foldr_max (l := tup.map formMax) (List.mem_map.mpr ⟨f, hf, rfl⟩)).trans (le_max_right _ _))

theorem ndeg_formP (f : Form) (cols : ℕ → Polynomial E) (B k : ℕ) (hc : ∀ i, (cols i).natDegree ≤ B)
    (hk : ∀ mc ∈ f, mc.1.length ≤ k) : (formP f cols).natDegree ≤ k * B := by
  unfold formP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨⟨m, cf⟩, hm, rfl⟩ := List.mem_map.mp hp
  have hl := hk _ hm
  rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨_, _⟩⟩⟩
  · simp
  · simp only [List.length_cons, List.length_nil] at hl
    exact ndeg_Cmul ((hc i).trans (Nat.le_mul_of_pos_left B (by omega)))
  · simp only [List.length_cons, List.length_nil] at hl
    exact ndeg_mul (ndeg_Cmul (hc i)) (hc j) (by
      have := Nat.mul_le_mul_right B hl
      omega)
  · simp

theorem ndeg_tupleP (tuple : List Form) (weights : Array E) (cols : ℕ → Polynomial E) (B k : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) (hk : ∀ f ∈ tuple, ∀ mc ∈ f, mc.1.length ≤ k) :
    (tupleP tuple weights cols).natDegree ≤ k * B := by
  unfold tupleP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨⟨f, s⟩, hq, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul (ndeg_formP _ cols B k hc (hk _ (List.of_mem_zip hq).1))

/-- A table's pull tuples' degrees, summed. -/
def pullDeg (tab : Table) : ℕ := ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ fdeg fl.1).sum

/-- A table's push tuples' degrees, summed. -/
def pushDeg (tab : Table) : ℕ := ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ fdeg fl.2).sum

/-- **A table's pull product**: at most `pullDeg · B`, its columns of degree at most `B`. -/
theorem ndeg_pullP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) (B : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) : (pullP tab weights beta cols).natDegree ≤ pullDeg tab * B := by
  unfold pullP pullDeg
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map, ← List.sum_map_mul_right]
  exact list_sum_map_le _ _ _ fun fl _ ↦ ndeg_add (ndeg_C _ _) (ndeg_tupleP _ _ _ B _ hc (le_fdeg fl.1))

/-- **A table's push product.** -/
theorem ndeg_pushP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) (B : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) : (pushP tab weights beta cols).natDegree ≤ pushDeg tab * B := by
  unfold pushP pushDeg
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map, ← List.sum_map_mul_right]
  exact list_sum_map_le _ _ _ fun fl _ ↦ ndeg_add (ndeg_C _ _) (ndeg_tupleP _ _ _ B _ hc (le_fdeg fl.2))

/-- The verifier's leaf degrees are at most the tuples' monomials'. -/
theorem tableDegrees_le' (tab : Table) :
    (tableDegrees tab).1 ≤ 1 + pullDeg tab ∧ (tableDegrees tab).2 ≤ pushDeg tab := by
  rw [tableDegrees_eq]
  refine ⟨Nat.add_le_add_left (list_sum_map_le _ _ _ fun fl _ ↦
    tupleDegree_le _ _ (le_max_left _ _) (le_fdeg fl.1)) 1, ?_⟩
  rw [zero_add]
  exact list_sum_map_le _ _ _ fun fl _ ↦ tupleDegree_le _ _ (le_max_left _ _) (le_fdeg fl.2)

/-! ## The six tables, as the degrees read them (the kernel reads monomials, not coefficients) -/

/-- The tables' pull degrees. -/
def pullL : List ℕ := [8, 8, 4, 8, 8, 20]

/-- The tables' push degrees. -/
def pushL : List ℕ := [8, 8, 4, 8, 9, 20]

/-- The tables' opcodes and counters' numbers. -/
def ocL : List (ℕ × ℕ) := [(0, 4), (1, 4), (2, 2), (3, 4), (4, 4), (5, 10)]

/-! ## Quotients and their chunks -/

/-- `chunks`' potential: `4 Σ 2^e + β(k) · left`, `β = 5, 6, 8, 8, …` after `k` chunks. -/
def cβ : ℕ → ℕ
  | 0 => 5
  | 1 => 6
  | _ + 2 => 8

/-- The potential is at most `5 n`. -/
def ChunkPot (n : ℕ) (s : Array ℕ × ℕ) : Prop :=
  4 * (s.1.toList.map (2 ^ ·)).sum + cβ s.1.size * s.2 ≤ 5 * n

theorem chunkStep_pot (n : ℕ) (s : Array ℕ × ℕ) (x : ℕ) (h : ChunkPot n s) :
    ChunkPot n (chunkStep s x) := by
  unfold ChunkPot at *
  unfold chunkStep
  by_cases h0 : s.2 > 0
  · rw [ite_eq_left h0]
    have hne : s.2 ≠ 0 := by omega
    have hle := Nat.log2_self_le hne
    have hlt := Nat.lt_log2_self (n := s.2)
    rw [pow_succ] at hlt
    split_ifs with hs
    · simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, mul_zero, pow_succ]
      rw [hs.1, show cβ 2 = 8 from rfl] at h
      omega
    · simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Array.size_push]
      rcases Nat.lt_or_ge s.1.size 2 with hlt2 | hge
      · rcases Nat.lt_or_ge s.1.size 1 with hlt1 | hge1
        · have e0 : s.1.size = 0 := by omega
          rw [e0, show cβ 0 = 5 from rfl] at h
          rw [e0, show cβ (0 + 1) = 6 from rfl]
          omega
        · have e1 : s.1.size = 1 := by omega
          rw [e1, show cβ 1 = 6 from rfl] at h
          rw [e1, show cβ (1 + 1) = 8 from rfl]
          omega
      · obtain ⟨k, hk⟩ : ∃ k, s.1.size = k + 2 := ⟨s.1.size - 2, by omega⟩
        rw [hk, show cβ (k + 2) = 8 from rfl] at h
        rw [hk, show cβ (k + 2 + 1) = 8 from rfl]
        omega
  · rw [ite_eq_right h0]
    exact h

/-- **The chunks cover `n` coefficients with `Σ 2^e ≤ 5n/4`.** -/
theorem chunks_sum_le (n : ℕ) : 4 * ((chunks n).map (2 ^ ·)).sum ≤ 5 * n := by
  rw [chunks_eq]
  have key : ∀ (l : List ℕ) (s : Array ℕ × ℕ), ChunkPot n s → ChunkPot n (l.foldl chunkStep s) := by
    intro l
    induction l with
    | nil => intro s h; exact h
    | cons x l ih => intro s h; exact ih _ (chunkStep_pot n s x h)
  have := key (List.range' 0 4) (#[], n) (by simp [ChunkPot, cβ])
  unfold ChunkPot at this
  omega

/-- `5n/4`. -/
def chB (n : ℕ) : ℕ := 5 * n / 4

theorem chB_mono {m n : ℕ} (h : m ≤ n) : chB m ≤ chB n := Nat.div_le_div_right (by omega)

theorem chunks_le_chB (n : ℕ) : ((chunks n).map (2 ^ ·)).sum ≤ chB n := by
  have := chunks_sum_le n
  unfold chB
  omega

/-! ## The constraint quotient's degree -/

/-- A table's bound on the constraint quotient's degree: `max(2^r max(1, counts), r 2^r / 2)`. -/
def cdOf (S : Shape) (p : ℕ × ℕ) : ℕ :=
  max (2 ^ S.heights.getD p.1 0 * max 1 p.2) (S.heights.getD p.1 0 * (2 ^ S.heights.getD p.1 0 / 2))

/-- **The constraint quotient's degree bound.** -/
def cdB (S : Shape) : ℕ := max ((ocL.map (cdOf S)).foldr max 0) (2 ^ S.logMemory)

theorem cdStep_le (S : Shape) (B d : ℕ) (tab : Table) (hd : d ≤ B)
    (hB : cdOf S (tab.opcode, tab.countColumns.length) ≤ B) : cdStep S d tab ≤ B := by
  unfold cdStep cdOf at *
  dsimp only at *
  generalize S.heights.getD tab.opcode 0 = r at hB ⊢
  generalize tab.countColumns.length = cnt at hB ⊢
  generalize 2 ^ r = n at hB ⊢
  generalize hM : max 1 cnt = M at hB
  have hm : 1 ≤ M := hM ▸ le_max_left _ _
  have hm1 : n ≤ n * M := Nat.le_mul_of_pos_right _ hm
  have h2a : (n - 1) * (1 + cnt) ≤ n * (1 + cnt) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2b : n * (1 + cnt) = n + n * cnt := by ring
  have h2c : n * cnt ≤ n * M := Nat.mul_le_mul_left _ (hM ▸ le_max_right _ _)
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have hJ : n - 2 ≤ B := by omega
  have hC : (n - 1) * (1 + cnt) - n ≤ B := by omega
  have hBl : r * (n / 2) - n ≤ B := (Nat.sub_le _ _).trans hB2
  unfold UniStatement.degree
  split_ifs <;> simp only [max_le_iff] <;> omega

/-! ## The constraints' degrees -/

/-- A table's bound on its constraints' `W_i`: `2^r (1 + max(1, counts))`. -/
def wOf (S : Shape) (p : ℕ × ℕ) : ℕ := 2 ^ S.heights.getD p.1 0 * (1 + max 1 p.2)

/-- **The constraints' `W_i` bound**: the tables', `q_flock`'s slots', the public lines'. -/
def wMax (S : Shape) : ℕ :=
  max (2 ^ S.logMemory) (max (S.heights.getD opSha3 0 * 2 ^ (S.heights.getD opSha3 0 - 1))
    ((ocL.map (wOf S)).foldr max 0))

/-- **The constraint quotient's identity `Z_bad (Σ γ^i M_i W_i + Q_W w_{r_W})`.** -/
def wB (S : Shape) : ℕ :=
  2 * 2 ^ (S.heights.getD opSha3 0 - 1) +
    max (2 ^ S.constraintVars + wMax S) (chB (cdB S + 1) + 2 ^ S.constraintVars)

/-! ## The tree and the root -/

/-- **The tree's identity**: at most `2^(h+1) + 2`. -/
def treeB (S : Shape) : ℕ := 2 ^ (S.heap.h + 1) + 2

/-! ## The heap blocks' leaves -/

/-- **A table's leaf** `R (P w_r + Z²) + Q w_r Z + P' w_r + Z²`, at height `r`, pull and push degrees
`P`, `Q`. -/
def tabB (r P Q : ℕ) : ℕ :=
  max (2 ^ r + max (P * 2 ^ r + 2 ^ r) (2 ^ (r + 2)))
    (max (chB (UniStatement.degree (max (1 + P) Q * (2 ^ r - 1) + (2 ^ r - Shape.leastRows r)) (2 ^ r) + 1) +
        (2 ^ r + 2 ^ (r + 1)))
      (max (Q * 2 ^ r + 2 ^ r) (2 ^ (r + 2))))

/-- **The memory's or the bytecode's leaf** `R P + Q w_r + P'`, its tuples' column of `v` variables. -/
def memB (r v : ℕ) : ℕ := max (2 ^ r + 2 ^ v) (chB (UniStatement.degree (2 * (2 ^ r - 1)) (2 ^ r) + 1) + 2 ^ r)

/-- **A heap block's leaf identity's degree bound.** -/
def blockB (S : Shape) (b : Block) : ℕ :=
  match b.leaves with
  | .unused => 2 ^ b.r
  | .memory => memB b.r S.logMemory
  | .bytecode => memB b.r S.logBytecode
  | .table t => tabB b.r (pullL.getD t 0) (pushL.getD t 0)

/-! ## The identities' degrees -/

theorem treeB_reference : treeB reference = 2 ^ 24 + 2 := by
  rw [treeB, heap_reference.1]

/-- **The bound at the reference shape**, by `norm_num` on the closed sum (`reference` is rewritten
to its numbers first, so nothing reduces its heap). -/
theorem refBound :
    treeB reference + wB reference + ((heapBlocksRef.map Block.ofTuple).map (blockB reference)).sum ≤
      50708397 := by
  rw [treeB_reference, reference_eq]
  simp only [heapBlocksRef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.ofTuple,
    blockB, wB, wMax, cdB, cdOf, wOf, ocL, tabB, memB, chB, pullL, pushL, List.foldr_cons,
    List.foldr_nil, List.getD_cons_succ, List.getD_cons_zero, Shape.leastRows, UniStatement.degree,
    Shape.constraintVars, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, opSha3]
  norm_num [max_def]

end UniSound.Ids
