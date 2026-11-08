-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The round-by-round form is
-- `formal/Compose/Compose/ListChainK.lean`'s `Piop`.
import UniSound.Sumcheck

/-!
# The univariate PIOP, round by round

The main line's rounds as the chain sees them (`uniRounds`):

| round | message | challenges |
|---|---|---|
| `0` | `C1`'s root | `α ∈ E^4`, `β`, `γ` |
| `1 … nF` | Flock's rounds (`FlockSound.prog.rounds`) | Flock's |
| `nF + 1` | `C2`'s root | `t` |
| `nF + 2` | the `nV` values at `t` | `ρ`, `λ` |
| `nF + 3 …` | the batching sumcheck's `V` rounds, `c0, c2` each | its point, one each |

then the three stacks' values at the batch's point (the tail, which no challenge follows) and the
five openings.

**The states** (`uniPiop`, in the form of `Compose.Piop`: the state before a round's challenges
`pre`, after them `post`), for a statement `s` (the public input and the row counts) and the
candidates `c1`, `c2` of `C1`'s and `C2`'s roots (stacks, `Stk`):

* before round `0`: **leanVM 42422001's relation** holds of `c1`'s Lv42 stack (`Rel`);
* after round `0` and Flock's rounds: the **bus and constraint state** `MainOK s c1 (α, β, γ)` (some
  heap and quotients can still satisfy the identities), and **Flock's state** on `q_flock`
  (`FlockSound.S`) after the Flock rounds so far;
* before `t`: the **identities hold as polynomials** for `c2` (`polys`, all zero), Flock's claim on
  `q_flock` holds, its checks pass and its matrices' claims hold;
* after `t`: **some values make every relation true** at `t` (`diffs`, all zero), Flock's checks
  and matrices as before;
* after `ρ, λ`: the **batch's target is the sum** `Σ_u g(u)` (`ProdSum.T []`);
* after each sumcheck round: the claim is the partial sum (`SumState`);
* from `t` on, each of these **or `t` a root of the merge polynomial** (`zb`).

**The errors** (`uniErr`): round `0` the bus and the constraints' batching (`errMain`: `4N/|E|`
and the `γ` term, `mainSound`); Flock's rounds Flock's (`FlockSound.err`); `t` Schwartz–Zippel for
every identity and the merge polynomial (`(degSum + degBad) / |E|`, the sum of their degrees); `ρ, λ` the two combinations
(`(nRel − 1 + 2) / |E|`); each sumcheck round `2 / |E|`. `uniPiop_sound` proves each.

**The identity model** (`UniIds`): what the states are made of and the facts the rounds need,
the bridges between the verifier's relations and Lv42's relation. Its fields are the end
theorem's mathematical obligations; `UniSound.Bus` discharges `mainSound` from `Heap`'s bus.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-! ## Round-by-round soundness on a list of rounds -/

/-- **An opened transcript** (`Compose.Opened`): each round's candidate (if it has a root) and
values, and its challenges. -/
abbrev Op (M : Type) := Compose.Opened M E

/-- **A protocol's round-by-round soundness on its rounds** (`Compose.Piop`, with the rounds in
place of the chain's specification). -/
structure RbrPiop (rounds : List Compose.RoundSpec) (St M : Type) where
  pre : St → Op M → Option M × List E → Prop
  post : St → Op M → Option M × List E → List E → Prop
  pre_post : ∀ s p m c m', pre s (p ++ [(m, c)]) m' → post s p m c
  err : ℕ → ℝ≥0∞
  sound : ∀ (j : ℕ) (s : St) (p : Op M) (m : Option M × List E), j < rounds.length →
    p.length = j → Pr{let c ← Compose.draws E ((rounds.getD j ⟨false, 0, 0⟩).ns + 1)}[
      ¬ pre s p m ∧ post s p m c] ≤ err j

/-- **The protocol of a chain with these rounds** (`Compose.Piop`). -/
def RbrPiop.toPiop {St M : Type} (K : Compose.ChainSpec E St) {rounds : List Compose.RoundSpec}
    (R : RbrPiop rounds St M) (hK : K.rounds = rounds) : Compose.Piop K M where
  pre := R.pre
  post := R.post
  pre_post := R.pre_post
  err := R.err
  sound j s p m hj hp := by
    have h := R.sound j s p m (hK ▸ hj) hp
    simpa only [Compose.ChainSpec.spec, hK] using h

/-! ## The statement, the candidates -/

/-- **A statement**: the public input's 32 bytes and the proof's row counts. -/
abbrev USt := Vector UInt8 32 × List ℕ

/-- **A candidate**: a stack, word by word. -/
abbrev Stk := ℕ → K

/-! ## The rounds -/

/-- **The main line's rounds**: `C1` and `α, β, γ`; Flock's; `C2` and `t`; the `nV` values and
`ρ, λ`; the `V` rounds of the batching sumcheck. -/
def uniRounds (flockRounds : List Compose.RoundSpec) (nV V : ℕ) : List Compose.RoundSpec :=
  [⟨true, 0, 5⟩] ++ flockRounds ++ [⟨true, 0, 0⟩, ⟨false, nV, 1⟩] ++ List.replicate V ⟨false, 2, 0⟩

/-! ## The identity model -/

/-! ## Reading an opened transcript -/

/-- Round `j` of an opened transcript. -/
def rd {M : Type} (q : Op M) (j : ℕ) : (Option M × List E) × List E := q.getD j ((none, []), [])

/-- Flock's transcript in an opened one: rounds `1 … nF`, their values and challenges. -/
def fdOf {M : Type} (nF : ℕ) (q : Op M) : Done :=
  ((q.drop 1).take nF).map fun x => ((none, x.1.2), x.2)

/-- The batching sumcheck's rounds in an opened one: from round `nF + 3` on. -/
def brOf {M : Type} (nF : ℕ) (q : Op M) : List (List E × List E) :=
  (q.drop (nF + 3)).map fun x => (x.1.2, x.2)

section Read

variable {M : Type}

theorem rd_append_lt (q l : Op M) (j : ℕ) (h : j < q.length) : rd (q ++ l) j = rd q j := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_self (q : Op M) (x : (Option M × List E) × List E) : rd (q ++ [x]) q.length = x := by
  simp [rd, List.getD_eq_getElem?_getD]

theorem fdOf_append_le (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E) (h1 : 1 ≤ q.length)
    (h2 : q.length ≤ nF) : fdOf nF (q ++ [x]) = fdOf nF q ++ [((none, x.1.2), x.2)] := by
  unfold fdOf
  rw [List.drop_append_of_le_length h1, List.take_of_length_le (by simp; omega),
    List.take_of_length_le (by simp; omega)]
  simp

theorem fdOf_append_gt (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E)
    (h : nF + 1 ≤ q.length) : fdOf nF (q ++ [x]) = fdOf nF q := by
  unfold fdOf
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem fdOf_singleton (nF : ℕ) (x : (Option M × List E) × List E) : fdOf nF [x] = [] := by
  simp [fdOf]

theorem brOf_append (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E)
    (h : nF + 3 ≤ q.length) : brOf nF (q ++ [x]) = brOf nF q ++ [(x.1.2, x.2)] := by
  unfold brOf
  rw [List.drop_append_of_le_length h]
  simp

theorem brOf_of_length (nF : ℕ) (q : Op M) (h : q.length ≤ nF + 3) : brOf nF q = [] := by
  simp [brOf, List.drop_eq_nil_of_le h]

theorem length_fdOf (nF : ℕ) (q : Op M) (h : q.length ≤ nF + 1) :
    (fdOf nF q).length = q.length - 1 := by
  simp [fdOf]
  omega

theorem length_brOf (nF : ℕ) (q : Op M) : (brOf nF q).length = q.length - (nF + 3) := by
  simp [brOf]

end Read

/-! ## The rounds' specifications -/

section Rounds

variable (Fr : List Compose.RoundSpec) (nV V : ℕ)

theorem length_uniRounds : (uniRounds Fr nV V).length = Fr.length + 3 + V := by
  simp [uniRounds]
  omega

theorem uniRounds_zero : (uniRounds Fr nV V).getD 0 ⟨false, 0, 0⟩ = ⟨true, 0, 5⟩ := rfl

theorem uniRounds_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Fr.length) :
    (uniRounds Fr nV V).getD j ⟨false, 0, 0⟩ = Fr.getD (j - 1) ⟨false, 0, 0⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [uniRounds, List.getD_eq_getElem?_getD, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_left (by omega)]

theorem uniRounds_c2 : (uniRounds Fr nV V).getD (Fr.length + 1) ⟨false, 0, 0⟩ = ⟨true, 0, 0⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem uniRounds_vals :
    (uniRounds Fr nV V).getD (Fr.length + 2) ⟨false, 0, 0⟩ = ⟨false, nV, 1⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.append_assoc, List.append_assoc, List.singleton_append,
    show Fr.length + 2 = (Fr.length + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by omega), show Fr.length + 1 - Fr.length = 1 by omega]
  rfl

theorem uniRounds_batch (j : ℕ) (h1 : Fr.length + 3 ≤ j) (h2 : j < Fr.length + 3 + V) :
    (uniRounds Fr nV V).getD j ⟨false, 0, 0⟩ = ⟨false, 2, 0⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [List.getElem?_replicate]
  split_ifs with h
  · rfl
  · omega

end Rounds

/-! ## The states -/

end UniSound
