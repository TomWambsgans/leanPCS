-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Lemmas.Side
import RecStatement.Lemmas.Subspace

/-!
# The verifier's constants are the circuit's

`SpecOf S G B pairOf portOf pubOf` says that the arithmetic's constants `S` (`CoreSpec`) are `Spec::of` of
`RecPiop`'s circuit `G`, its points the Cantor basis `B` (`ω = Heap.omega B`):

* the shape: `m = logN`, `r = logW`, `m ≤ n`;
* **the recursion's constants** are the blocks' normalised ones (`NormConsts`, `c_s = Π_{j<s} e_j / e_s`);
* **the pairs** enumerate `G.pairs` (`pairOf`, a bijection from the indices), each with its block's rows' log `s` and
  `Ẑ_s(c_p)`;
* **the groups** partition the pairs' indices (`groups_perm`), a group's pairs of its role, its pull flag the
  pairs' (a pull-less pair is a port's), its formula theirs as a value on any cells (`group_formula`, at the powers of
  `γ` the verifier takes);
* **the ports' `Φ`**: its roles distinct (`phi_nodup`), its terms (flattened, `phiTerms`) enumerate distinct ports
  (`portOf`), each term's role and row its port's hole's (`G.port j % W`, `G.port j / W`), its value the port's
  public fingerprint `F_j` (`phi_value`); the ports in no term have zero public fingerprints (`zero_ports`: π1's zero
  checks and their padding).

This is the transcription's hypothesis: `Spec.of` computes these from the circuit's tables, as the Rust does; that
they are `RecPiop`'s circuit's is the composition's link (the circuit compiler's, `RecCircuit`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- The `Φ` terms, flattened: `(role, row, value)`. -/
def phiTerms (S : CoreSpec F) : List (ℕ × ℕ × LinF F) := S.phi.flatMap fun kt ↦ kt.2.map fun yl ↦ (kt.1, yl)

/-- The empty `Φ` term. -/
def noPhi : ℕ × ℕ × LinF F := (0, 0, ⟨[], none⟩)

/-- **The verifier's constants are `G`'s.** -/
structure SpecOf {n : ℕ} (S : CoreSpec F) (G : RecPiop.Circuit F) (B : QuotientSecurity.CantorBasis F n)
    (pairOf : ℕ → Block × ℕ) (portOf : ℕ → ℕ) (pubOf : List F → ℕ → List F) : Prop where
  logN : S.logN = G.logN
  logRow : S.logRow = G.logW
  hn : G.logN ≤ n
  omega : S.ω = Heap.omega B
  c : NormConsts (blockBasis (Heap.omega B) G.logW) S.c (G.logN - G.logW)
  pair_mem : ∀ i < S.pairs.length, pairOf i ∈ G.pairs
  pair_inj : ∀ i < S.pairs.length, ∀ j < S.pairs.length, pairOf i = pairOf j → i = j
  pair_surj : ∀ p ∈ G.pairs, ∃ i < S.pairs.length, pairOf i = p
  pair_s : ∀ i < S.pairs.length, (S.pairs.getD i (0, 0)).1 = (pairOf i).1.logRows
  pair_z : ∀ i < S.pairs.length, (S.pairs.getD i (0, 0)).2 =
    zHat S.c (pairOf i).1.logRows (Heap.omega B (G.pairBase (pairOf i)))
  groups_perm : (S.groups.flatMap (·.pairs)).Perm (List.range S.pairs.length)
  group_role : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, (pairOf i).2 = g.role
  group_pulls : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, g.pulls = !(G.regionRole (pairOf i).1 (pairOf i).2).isPort
  group_formula : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, ∀ (γ : F) (v : ℕ → F),
    g.formula.eval (powersList γ (S.maxGamma + 1)) (fun c ↦ v (c ^^^ g.role)) =
      (G.regionRole (pairOf i).1 (pairOf i).2).value γ (v 0) (fun c ↦ v ((pairOf i).2 ^^^ c))
  phi_nodup : (S.phi.map (·.1)).Nodup
  phi_port_lt : ∀ J < (phiTerms S).length, portOf J < G.nP
  phi_port_inj : ∀ J < (phiTerms S).length, ∀ J' < (phiTerms S).length, portOf J = portOf J' → J = J'
  phi_role : ∀ J < (phiTerms S).length, ((phiTerms S).getD J noPhi).1 = G.port (portOf J) % G.W
  phi_row : ∀ J < (phiTerms S).length, ((phiTerms S).getD J noPhi).2.1 = G.port (portOf J) / G.W
  phi_value : ∀ J < (phiTerms S).length, ∀ (pubs : List F) (γ : F),
    ((phiTerms S).getD J noPhi).2.2.eval (powersList γ (S.maxGamma + 1)) (fun c ↦ pubs.getD c 0) =
      G.pubFp γ (pubOf pubs) (portOf J)
  zero_ports : ∀ j < G.nP, (∀ J < (phiTerms S).length, portOf J ≠ j) → ∀ (pubs : List F) (γ : F),
    G.pubFp γ (pubOf pubs) j = 0

/-! ## The Cantor basis's points, bit by bit -/

theorem list_range_sum (f : ℕ → F) : ∀ N, ((List.range N).map f).sum = ∑ i ∈ range N, f i
  | 0 => rfl
  | N + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_range_sum f N, Finset.sum_range_succ]; simp

theorem omega_two_pow {n : ℕ} (B : QuotientSecurity.CantorBasis F n) (b : ℕ) :
    Heap.omega B (2 ^ b) = if b < n then B.β b else 0 := by
  unfold Heap.omega
  split_ifs with hb
  · rw [Finset.sum_eq_single b (fun k _ hk ↦ by simp [Ne.symm hk])
      (fun h ↦ absurd (Finset.mem_range.mpr hb) h)]
    simp [Nat.testBit_two_pow_self]
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    have : b ≠ k := fun h ↦ hb (h ▸ Finset.mem_range.mp hk)
    simp [this]

/-- **`ω_d` from `d`'s bits** below `2^28`: `Σ_{b<28} d_b ω(2^b)`. -/
theorem omega_bits {n : ℕ} (B : QuotientSecurity.CantorBasis F n) {d : ℕ} (hd : d < 2 ^ 28) :
    Heap.omega B d = ((List.range 28).map fun b ↦ if d.testBit b then Heap.omega B (2 ^ b) else 0).sum := by
  rw [list_range_sum]
  simp only [omega_two_pow]
  unfold Heap.omega
  rcases le_total n 28 with h | h
  · have e := Finset.sum_subset (Finset.range_subset_range.mpr h)
      (f := fun b ↦ if d.testBit b then (if b < n then B.β b else 0) else 0) (fun b _ hb' ↦ by
        have : ¬ b < n := fun h' ↦ hb' (Finset.mem_range.mpr h')
        simp [this])
    rw [← e]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    simp [Finset.mem_range.mp hb]
  · have e := Finset.sum_subset (Finset.range_subset_range.mpr h)
      (f := fun k ↦ if d.testBit k then B.β k else 0) (fun k _ hk' ↦ by
        have h28 : ¬ k < 28 := fun h' ↦ hk' (Finset.mem_range.mpr h')
        have : d.testBit k = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [this])
    rw [← e]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    have : b < n := lt_of_lt_of_le (Finset.mem_range.mp hb) h
    simp [this]

end RecStatement
