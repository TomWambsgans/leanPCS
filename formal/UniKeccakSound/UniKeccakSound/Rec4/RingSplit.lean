-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The ring map's bad challenges are `formal/FlockSound`'s
-- (`FlockSound.ringBad`, `card_ringBad_le`).
import FlockSound.Frobenius

/-!
# The ring map drawn in two queries (π1-rec4)

π1-rec4 draws the ring switch's six map challenges in two queries: `f_0 … f_3` with `t` (after `C2`'s commitment) and
`f_4, f_5` with `ρ` (after the values at `t`), `docs/leanvm/univariate/SPEC.md` §14.4. The ring switch's map is staged
(`a ↦ a + f_j a^(2^(2^j))`), so its relation is **not** of degree `1` in each `f_j` as a polynomial (a stage's
Frobenius power raises the earlier challenges); what holds is `FlockSound`'s stage-by-stage bound: given the
challenges before it, each `f_j` has at most one bad value (`FlockSound.ringBad`, `card_ringBad_le`; a family that
escapes every bad value keeps the ring switch's `π_0 ≠ 0`, `FlockSound.ring_escape`). π1-rec3 draws the six one by one;
π1-rec4 draws several from one query, uniform and independent, so the query's error is the sum of its challenges':

* `card_exists_bad_le`: `k` challenges drawn together, each with at most one bad value given the ones before it (a bad
  family depending only on the prefix), hit one with probability at most `k/|K|`;
* `card_first_block_le`, `card_second_block_le`: a family on `a + b` challenges split into a query of `a` and a later
  query of `b` (the first fixed): at most `a/|K|`, then `b/|K|`;
* `ringBad_prefix`: `ringBad`'s family depends only on the challenges before each;
* **`ringBad_split_first`**, **`ringBad_split_second`**: the ring map at any six shifts, split `4 + 2`: the `t`-query's
  four challenges hit a bad value with probability at most `4/|E|`, and for every first four, the `ρ`-query's two with
  probability at most `2/|E|`.
-/

namespace UniKeccakSound.Rec4

open Finset

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **`k` challenges drawn together**, each with at most one bad value given the ones before it: at most
`k |K|^(k−1)` of the `|K|^k` draws hit one. -/
theorem card_exists_bad_le (k : ℕ) (bad : Fin k → (Fin k → K) → Finset K)
    (hdep : ∀ j f f', (∀ i : Fin k, i < j → f i = f' i) → bad j f = bad j f')
    (hcard : ∀ j f, (bad j f).card ≤ 1) :
    (univ.filter fun f : Fin k → K ↦ ∃ j, f j ∈ bad j f).card ≤ k * Fintype.card K ^ (k - 1) := by
  have hsub : (univ.filter fun f : Fin k → K ↦ ∃ j, f j ∈ bad j f) ⊆
      univ.biUnion fun j ↦ univ.filter fun f : Fin k → K ↦ f j ∈ bad j f := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨j, hj⟩ := hf
    simp only [mem_biUnion, mem_univ, mem_filter, true_and]
    exact ⟨j, hj⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  have hj : ∀ j : Fin k, (univ.filter fun f : Fin k → K ↦ f j ∈ bad j f).card ≤ Fintype.card K ^ (k - 1) := by
    intro j
    have hinj : Set.InjOn (fun f : Fin k → K ↦ fun i : {i : Fin k // i ≠ j} ↦ f i.1)
        (univ.filter fun f : Fin k → K ↦ f j ∈ bad j f) := by
      intro f hf f' hf' heq
      have hf : f j ∈ bad j f := by simpa using hf
      have hf' : f' j ∈ bad j f' := by simpa using hf'
      have hoff : ∀ i, i ≠ j → f i = f' i := fun i hi ↦ congrFun heq ⟨i, hi⟩
      have hb : bad j f = bad j f' := hdep j f f' fun i hi ↦ hoff i (ne_of_lt hi)
      rw [hb] at hf
      have hfj : f j = f' j := Finset.card_le_one.mp (hcard j f') _ hf _ hf'
      funext i
      by_cases hi : i = j
      · rw [hi, hfj]
      · exact hoff i hi
    calc (univ.filter fun f : Fin k → K ↦ f j ∈ bad j f).card
        ≤ (univ : Finset ({i : Fin k // i ≠ j} → K)).card :=
          card_le_card_of_injOn _ (fun _ _ ↦ mem_univ _) hinj
      _ = Fintype.card K ^ (k - 1) := by
          rw [card_univ, Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_fin,
            Fintype.card_subtype_eq]
  calc ∑ j : Fin k, (univ.filter fun f : Fin k → K ↦ f j ∈ bad j f).card
      ≤ ∑ _j : Fin k, Fintype.card K ^ (k - 1) := sum_le_sum fun j _ ↦ hj j
    _ = k * Fintype.card K ^ (k - 1) := by simp

/-- **The first query of a split** (`a` challenges, the later `b` at any `h₀`): at most `a |K|^(a−1)` hit. -/
theorem card_first_block_le (a b : ℕ) (bad : Fin (a + b) → (Fin (a + b) → K) → Finset K)
    (hdep : ∀ j f f', (∀ i : Fin (a + b), i < j → f i = f' i) → bad j f = bad j f')
    (hcard : ∀ j f, (bad j f).card ≤ 1) (h₀ : Fin b → K) :
    (univ.filter fun g : Fin a → K ↦ ∃ j : Fin a, g j ∈ bad (Fin.castAdd b j) (Fin.append g h₀)).card ≤
      a * Fintype.card K ^ (a - 1) := by
  have := card_exists_bad_le a (fun j g ↦ bad (Fin.castAdd b j) (Fin.append g h₀)) (fun j g g' hgg ↦ ?_)
    (fun j g ↦ hcard _ _)
  · simpa [Fin.append_left] using this
  refine hdep _ _ _ fun i hi ↦ ?_
  have hia : i.val < a := by
    have : i.val < j.val := hi
    omega
  have hi' : i = Fin.castAdd b ⟨i.val, hia⟩ := Fin.ext rfl
  rw [hi', Fin.append_left, Fin.append_left]
  exact hgg _ hi

/-- **The second query of a split** (`b` challenges, the first `a` fixed at `g`): at most `b |K|^(b−1)` hit. -/
theorem card_second_block_le (a b : ℕ) (bad : Fin (a + b) → (Fin (a + b) → K) → Finset K)
    (hdep : ∀ j f f', (∀ i : Fin (a + b), i < j → f i = f' i) → bad j f = bad j f')
    (hcard : ∀ j f, (bad j f).card ≤ 1) (g : Fin a → K) :
    (univ.filter fun h : Fin b → K ↦ ∃ j : Fin b, h j ∈ bad (Fin.natAdd a j) (Fin.append g h)).card ≤
      b * Fintype.card K ^ (b - 1) := by
  have := card_exists_bad_le b (fun j h ↦ bad (Fin.natAdd a j) (Fin.append g h)) (fun j h h' hhh ↦ ?_)
    (fun j h ↦ hcard _ _)
  · simpa [Fin.append_right] using this
  refine hdep _ _ _ fun i hi ↦ ?_
  by_cases hia : i.val < a
  · have hi' : i = Fin.castAdd b ⟨i.val, hia⟩ := Fin.ext rfl
    rw [hi', Fin.append_left, Fin.append_left]
  · have hib : i.val - a < b := by omega
    have hi' : i = Fin.natAdd a ⟨i.val - a, hib⟩ := Fin.ext (by simp; omega)
    rw [hi', Fin.append_right, Fin.append_right]
    refine hhh _ ?_
    show i.val - a < j.val
    have : i.val < a + j.val := hi
    omega

section Ring

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F] {ι : Type*}

omit [CharP F 2] in
/-- **`ringBad`'s family depends only on the challenges before each.** -/
theorem ringBad_prefix (s : Finset ι) (w : ι → F) :
    ∀ (sh : List ℕ) (b : ι → F) (j : Fin sh.length) (f f' : Fin sh.length → F),
      (∀ i : Fin sh.length, i < j → f i = f' i) → FlockSound.ringBad s w sh b f j = FlockSound.ringBad s w sh b f' j
  | [], _, j, _, _, _ => j.elim0
  | M :: sh, b, j, f, f', h => by
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      show FlockSound.ringBad s w sh (fun i ↦ b i + f 0 * b i ^ 2 ^ M) (Fin.tail f) j =
        FlockSound.ringBad s w sh (fun i ↦ b i + f' 0 * b i ^ 2 ^ M) (Fin.tail f') j
      rw [h 0 (Fin.succ_pos j)]
      exact ringBad_prefix s w sh _ j _ _ fun i hi ↦ h i.succ (Fin.succ_lt_succ_iff.mpr hi)

/-- **The ring map's `t`-query** (π1-rec4: its first four challenges drawn with `t`), at six shifts: at most a
`4/|E|` fraction of the four hit a bad value, whatever the last two. -/
theorem ringBad_split_first (s : Finset ι) (w : ι → F) (sh : List ℕ) (hsh : sh.length = 4 + 2) (b : ι → F)
    (h₀ : Fin 2 → F) :
    (univ.filter fun g : Fin 4 → F ↦ ∃ j : Fin 4,
      g j ∈ FlockSound.ringBad s w sh b (fun i ↦ Fin.append g h₀ (Fin.cast hsh i)) (Fin.cast hsh.symm (Fin.castAdd 2 j))).card ≤
      4 * Fintype.card F ^ 3 := by
  have := card_first_block_le 4 2
    (fun j f ↦ FlockSound.ringBad s w sh b (fun i ↦ f (Fin.cast hsh i)) (Fin.cast hsh.symm j))
    (fun j f f' hff ↦ ringBad_prefix s w sh b _ _ _ fun i hi ↦ hff _ (by simpa [Fin.lt_def] using hi))
    (fun j f ↦ FlockSound.card_ringBad_le s w sh b _ _) h₀
  simpa using this

/-- **The ring map's `ρ`-query** (π1-rec4: its last two challenges drawn with `ρ`, the first four fixed): at most a
`2/|E|` fraction of the two hit a bad value. -/
theorem ringBad_split_second (s : Finset ι) (w : ι → F) (sh : List ℕ) (hsh : sh.length = 4 + 2) (b : ι → F)
    (g : Fin 4 → F) :
    (univ.filter fun h : Fin 2 → F ↦ ∃ j : Fin 2,
      h j ∈ FlockSound.ringBad s w sh b (fun i ↦ Fin.append g h (Fin.cast hsh i)) (Fin.cast hsh.symm (Fin.natAdd 4 j))).card ≤
      2 * Fintype.card F ^ 1 := by
  have := card_second_block_le 4 2
    (fun j f ↦ FlockSound.ringBad s w sh b (fun i ↦ f (Fin.cast hsh i)) (Fin.cast hsh.symm j))
    (fun j f f' hff ↦ ringBad_prefix s w sh b _ _ _ fun i hi ↦ hff _ (by simpa [Fin.lt_def] using hi))
    (fun j f ↦ FlockSound.card_ringBad_le s w sh b _ _) g
  simpa using this

end Ring

end UniKeccakSound.Rec4
