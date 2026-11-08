-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `formal/Lv42`'s `Arithmetization/Soundness/Walk.lean`
-- (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), at the Keccak VM's `run`.
module

public import KeccakVm.Isa

/-!
# The walk decomposition, for the Keccak VM

Lv42's `exists_run_of_perm` (specification Proposition 6.1) at `KeccakVm.run`: edges that are steps of the Keccak VM
away from the sentinel, balanced against a start `s` and the final registers, contain a run from `s` to the final
registers, each of whose steps is an edge. The proof is Lv42's, at the Keccak VM's `step` and `run`.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Semantics KeccakVm

/-- Away from the sentinel, a run takes a step. -/
theorem run_succ_of_ne {prog : KeccakVm.Program} {κ : ℕ} {L : MemImage κ} {r : Regs K}
    (h : r.pc ≠ prog.finalPc) (n : ℕ) :
    KeccakVm.run prog L (n + 1) r = KeccakVm.step prog L r >>= KeccakVm.run prog L n := by
  rw [KeccakVm.run, ite_eq_right h]

/-- **Specification Proposition 6.1, the walk decomposition**, for the Keccak VM. -/
theorem exists_run_of_perm {α : Type*} {prog : KeccakVm.Program} {κ : ℕ} {L : MemImage κ}
    (src dst : α → Regs K) (E : List α)
    (hE : ∀ e ∈ E, (src e).pc ≠ prog.finalPc ∧ KeccakVm.step prog L (src e) = some (dst e))
    (s : Regs K) (hbal : (s :: E.map dst).Perm (finalRegs prog :: E.map src)) :
    ∃ n, KeccakVm.run prog L n s = some (finalRegs prog) ∧
      ∀ k < n, ∃ e ∈ E, KeccakVm.run prog L k s = some (src e) ∧
        KeccakVm.run prog L (k + 1) s = some (dst e) := by
  induction hlen : E.length using Nat.strong_induction_on generalizing E s with
  | _ len ih =>
    by_cases hs : s = finalRegs prog
    · exact ⟨0, by rw [hs]; rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
    have hmem : s ∈ E.map src := by
      have := hbal.subset List.mem_cons_self
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hs
      · exact h
    obtain ⟨e, he, hse⟩ := List.mem_map.mp hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
    have hbal' : (dst e :: (l₁ ++ l₂).map dst).Perm (finalRegs prog :: (l₁ ++ l₂).map src) := by
      have h1 : (s :: (l₁ ++ e :: l₂).map dst).Perm (s :: dst e :: (l₁ ++ l₂).map dst) := by
        refine List.Perm.cons _ ?_
        rw [List.map_append, List.map_cons, List.map_append]
        exact List.perm_middle
      have h2 : (finalRegs prog :: (l₁ ++ e :: l₂).map src).Perm
          (s :: finalRegs prog :: (l₁ ++ l₂).map src) := by
        rw [List.map_append, List.map_cons, hse, List.map_append]
        exact (List.Perm.cons _ List.perm_middle).trans (List.Perm.swap _ _ _)
      exact (h1.symm.trans (hbal.trans h2)).cons_inv
    have hE' : ∀ e' ∈ l₁ ++ l₂,
        (src e').pc ≠ prog.finalPc ∧ KeccakVm.step prog L (src e') = some (dst e') :=
      fun e' he' ↦ hE e' (by
        rcases List.mem_append.mp he' with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    obtain ⟨n, hn, hsteps⟩ := ih (l₁ ++ l₂).length (by simp at hlen ⊢; omega) (l₁ ++ l₂) hE'
      (dst e) hbal' rfl
    obtain ⟨hpc, hstep⟩ := hE e he
    rw [hse] at hpc hstep
    have hrun : ∀ k, KeccakVm.run prog L (k + 1) s = KeccakVm.run prog L k (dst e) := fun k ↦ by
      rw [run_succ_of_ne hpc, hstep]; rfl
    refine ⟨n + 1, by rw [hrun]; exact hn, fun k hk ↦ ?_⟩
    rcases k with _ | k
    · exact ⟨e, he, by rw [hse]; rfl, by rw [hrun]; rfl⟩
    · obtain ⟨e', he', h1, h2⟩ := hsteps k (by omega)
      refine ⟨e', ?_, by rw [hrun]; exact h1, by rw [hrun]; exact h2⟩
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

end KeccakArith

end
