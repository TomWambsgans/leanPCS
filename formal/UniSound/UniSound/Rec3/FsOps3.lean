-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsOps.lean` (and `FsChain.lean`'s
-- tail) for π1-rec3's verifier (`formal/UniStatement`'s `verifyWithFs … .rec3 true`: three `PCS_OPEN` calls).
import UniSound.FsOps
import UniSound.Rec3.Fs3

/-!
# π1-rec3's three openings, its check, and the tail

`FsOps.lean`'s openings for π1-rec3 (`uniOps3`): `C1` (round `0`'s root) and `C2` (round `nF + 1`'s), opened by the
computable decoder (`uniTc`, unchanged), and the setup's stack `F` at the setup's root, each a `WhirShape.large`
of a plain layout at its layout word's variables. Flock's `A0`, `B0` are **not** opened (π1-rec3 walks the
lincheck's terminal: no matrices' claim), though the setup still commits them (three trees, unchanged).

* **The chain's statement and messages** are `FsChain.lean`'s (`uniSpec`, `uView`, `uDone`: generic in the
  rounds), at `rec3Rounds` (`uRounds3`); **the tail** (`uTail3`) is three scalars (the stacks' values at the
  batch's point; no `a`, `b`).
* **The check** (`uniCheck3`): the transcript completes the rounds, every value the chain program requires zero
  is, and its result is π1-rec3's shape (`WellFormed3`: one point claim per commitment, of its layout word's
  variables, and **no** matrices' claim, which `verifyWithFs … .rec3 true` rejects).
* **`good`** (`uniGood3`: a candidate satisfies its commitment's claims) and **`goodS`** (`uniGoodS3`: the setup's
  honest stack satisfies its claim; there is no `A0`, `B0` claim).
* **`root_rec3Rounds`**: the rounds with a root are `0` and `nF + 1`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

/-! ## The tail -/

/-- **π1-rec3's tail**: the three scalars after the rounds (the stacks' values at the batch's point). -/
def uTail3 (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 3).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTail3 (rounds : List RoundSpec) (π : UPf) : (uTail3 rounds π).length = 3 := by
  simp [uTail3]

/-! ## The rounds with a root -/

theorem root_rec3Rounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV np i : ℕ)
    (h : ((rec3Rounds fr nV np).getD i ⟨false, 0, 0⟩).root = true) : i = 0 ∨ i = fr.length + 1 := by
  rcases i with _ | k
  · exact Or.inl rfl
  · right
    have e : (rec3Rounds fr nV np).getD (k + 1) ⟨false, 0, 0⟩ =
        (fr ++ (([⟨true, 0, 0⟩, ⟨false, nV, 1⟩] : List RoundSpec) ++
          (List.replicate np (⟨false, 8, 0⟩ : RoundSpec) ++ ([⟨false, 2, 0⟩] : List RoundSpec)))).getD k
          ⟨false, 0, 0⟩ := by
      rw [rec3Rounds_eq]
      rfl
    rw [e] at h
    by_contra hk
    rcases Nat.lt_or_ge k fr.length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt] at h
      rw [hfr _ (List.getElem_mem hlt)] at h
      exact Bool.false_ne_true h
    · rw [List.getD_append_right _ _ _ _ hge] at h
      obtain ⟨j, hj⟩ : ∃ j, k - fr.length = j + 1 := ⟨k - fr.length - 1, by omega⟩
      rw [hj] at h
      simp only [List.cons_append, List.getD_cons_succ] at h
      rcases j with _ | j
      · simp at h
      · simp only [List.getD_cons_succ, List.nil_append] at h
        rw [List.getD_eq_getElem?_getD] at h
        rcases hj' : (List.replicate np (⟨false, 8, 0⟩ : RoundSpec) ++ ([⟨false, 2, 0⟩] : List RoundSpec))[j]? with
            _ | r
        · rw [hj'] at h
          simp at h
        · rw [hj', Option.getD_some] at h
          have hm := List.mem_of_getElem? hj'
          rw [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
          rcases hm with ⟨-, rfl⟩ | rfl <;> simp at h

/-! ## The verifier's openings -/

section Ops

variable (D : Deployment) {κ : ℕ} (nV np : ℕ)

/-- **The result is π1-rec3's shape**: one opening per commitment, in order, its point claims of its layout
word's variables, and no matrices' claim. -/
def WellFormed3 (r : Reduced) : Prop :=
  r.openings.map Prod.fst = commitments ∧
    (∀ c ∈ claimsOf r .c1, c.point.length = wv D 0) ∧
    (∀ c ∈ claimsOf r .c2, c.point.length = wv D 1) ∧
    (∀ c ∈ claimsOf r .setup, c.point.length = wv D 2) ∧
    r.matrices = none

end Ops

end UniSound

/-- info: 'UniSound.root_rec3Rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.root_rec3Rounds
