-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockPure
import RecGraphKeccak.Pi1.Flock
import RecGraphKeccak.Sim.TerminalE

/-!
# The structured terminal, simulated: the generic folds, the packing weights, the correlations

`RecGraph.Sim`'s pure-run judgment (`PH`, `Sim/FlockBase.lean`) for the program's parts against the pieces of
`UniKeccak.structuredTerminal` (`TerminalE`):

* `sumL_ph` (`S::sum` of a lazy map is `esum`), `buildS_ph` (`collect` and `from_fn` are `Array.ofFn`);
* `packS_ph`: `one`, `e_low` (`RecGraph.Sim.rowLowTail_ph`), `e_high`;
* `corrS_ph`: the correlations at the needed offsets, the memoised partial ones against `partialAtE`, the others `0`.

At the Keccak verifier's shape: a skip of 3 (`zSkip` drawn, `row_low` of 3 coordinates), so `lo = n_hi = 8`.
-/

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1 RecGraphKeccak.TerminalE

section Terminal

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)
local notation "PO" => PH.one (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

/-! ## The generic folds -/

theorem esum_take_succ {α : Type} (xs : List α) (F : α → E) (j : ℕ) (hj : j < xs.length) :
    esum ((xs.take (j + 1)).map F) = esum ((xs.take j).map F) + F xs[j] := by
  rw [take_succ_getElem _ _ hj, List.map_append]
  simp [esum, List.foldl_append]

/-- **`S::sum` of a lazy map** is `esum` of the map. -/
theorem sumL_ph {α : Type} {st : RecState} (hg : Good st) (xs : List α) (f : α → Prog Sym) (F : α → E)
    (hf : ∀ x ∈ xs, ∀ st', PStep st st' → PH (f x) st' (fun st'' v ↦ Rp' st'' v (F x))) :
    PH (sumL xs f) st (fun st' v ↦ Rp' st' v (esum (xs.map F))) := by
  unfold sumL
  dsimp only
  refine PH.bind' (PZ hg) fun st1 z hs1 hz ↦ ?_
  refine PH.bind' (PH.forIn_list xs z _ st1 (fun j st' acc ↦ PStep st st' ∧ Rp' st' acc (esum ((xs.take j).map F)))
    hs1.good ⟨hs1, by simpa [esum] using hz⟩ ?_) fun st2 acc _ ⟨hs2, hacc⟩ ↦ ?_
  · intro j hj st' acc hs' ⟨hst, hI⟩
    refine PH.bind' (hf xs[j] (List.getElem_mem hj) st' hst) fun st'' v hs'' hv ↦ ?_
    refine PH.bind' (PH.add hs''.good (hI.pgrow hs'.good hs'') hv) fun st3 a hs3 ha ↦
      PH.ret hs3.good ⟨a, rfl, hst.trans (hs''.trans hs3), ?_⟩
    rw [esum_take_succ _ _ _ hj]; exact ha
  · rw [List.take_length] at hacc
    exact PH.ret hs2.good hacc

/-- **`collect` / `from_fn`** is `Array.ofFn`. -/
theorem buildS_ph {st : RecState} (hg : Good st) (n : ℕ) (f : ℕ → Prog Sym) (F : ℕ → E)
    (hf : ∀ i < n, ∀ st', PStep st st' → PH (f i) st' (fun st'' v ↦ Rp' st'' v (F i))) :
    PH (buildS n f) st (fun st' a ↦ RpA' st' a (Array.ofFn (n := n) fun i ↦ F i.val)) := by
  unfold buildS
  dsimp only
  refine PH.bind' (PH.forIn_list (List.range n) #[] _ st
    (fun j st' (a : Array Sym) ↦ PStep st st' ∧ a.size = j ∧ ∀ i < j, Rp' st' (a.getD i 0) (F i))
    hg ⟨PStep.refl st hg, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩ ?_) fun st2 a _ ⟨hs2, ha, hv⟩ ↦ ?_
  · intro j hj st' a hs' ⟨hst, ha, hv⟩
    rw [List.length_range] at hj
    rw [List.getElem_range]
    refine PH.bind' (hf j hj st' hst) fun st'' x hs'' hx ↦
      PH.ret hs''.good ⟨a.push x, rfl, hst.trans hs'', by simp [ha], fun i hi ↦ ?_⟩
    rw [getD_pushB]
    by_cases h : i < a.size
    · rw [iteT h]; exact (hv i (by omega)).pgrow hs'.good hs''
    · have : i = a.size := by omega
      rw [iteF h, iteT this, this, ha]; exact hx
  · rw [List.length_range] at ha hv
    exact PH.ret hs2.good (RpA.ofFn ha fun i hi ↦ hv i hi)

/-- `eq_kernel`, its array. -/
theorem eqKernel_phA {st : RecState} (hg : Good st) {ps : List Sym} {xs : List E} (hp : RpL' st ps xs) :
    PH (RecGraph.Pi1.eqKernel ps) st (fun st' a ↦ RpA' st' a (UniStatement.eqKernel xs)) :=
  (eqKernel_ph hg hp).mono fun st' a _ h ↦ by
    have := h.toRpA
    simpa using this

/-! ## The packing weights -/

theorem eLowTail_eq : eLowTail = rowLowTail := rfl

/-- **`one`, `e_low`, `e_high`**, at a skip of 3 (`row_low` of 3 coordinates, the skip's point drawn). -/
theorem packS_ph {st : RecState} (hg : Good st) {z : Sym} {zE : E} (hz : Rp' st z zE) {rl : List Sym} {RL : List E}
    (hrl : RpL' st rl RL) (hlen : RL.length = 3) :
    PH (packS (some z) rl) st (fun st' P ↦ Rp' st' P.one 1 ∧ RpA' st' P.eLow (eLowE (some zE) RL) ∧
      RpA' st' P.eHigh (eHighE RL)) := by
  have hl := hrl.length
  unfold packS
  dsimp only
  phg (PO hg) as st1 o hs1 ho
  rw [hl]
  phg (lagrangeWeights_ph hg hz _) as st2 lag hs2 hlag
  rw [eLowTail_eq]
  phg (rowLowTail_ph hg hlag (List.forall₂_take _ hrl)) as st3 r hs3 hr
  obtain ⟨-, hr⟩ := hr
  phg (eqKernel_phA hg (List.forall₂_drop _ hrl)) as st4 eh hs4 heh
  refine PH.ret hg ⟨ho, ?_, ?_⟩
  · have := RpL.toRpA hr
    simpa [eLowE, lagE, kE, pE, hlen, Flock.packing] using this
  · simpa [eHighE, kE, pE, hlen, Flock.packing] using heh

/-! ## The correlations -/

theorem loE_3 {RL : List E} (hlen : RL.length = 3) : loE RL = 8 := by simp [loE, pE, kE, hlen]
theorem nHiE_3 {RL : List E} (hlen : RL.length = 3) : nHiE RL = 8 := by simp [nHiE, pE, kE, hlen]

theorem getD_ofFn {n : ℕ} (f : ℕ → E) {i : ℕ} (hi : i < n) : (Array.ofFn (n := n) fun j ↦ f j.val).getD i 0 = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **The partial correlations** at the low offset `ol`. -/
theorem partialS_ph {st : RecState} (hg : Good st) {eLow sA : Array Sym} {zS : Option E} {RL S : List E}
    (hlen : RL.length = 3) (hel : RpA' st eLow (eLowE zS RL)) (hels : (eLowE zS RL).size = 8)
    (hs : RpA' st sA S.toArray) (hS : S.length = 64) (ol : ℕ) :
    PH (partialS eLow sA 8 8 ol) st
      (fun st' q ↦ RpA' st' q (Array.ofFn (n := 8) fun m ↦ partialAtE zS RL S ol m.val)) := by
  unfold partialS
  refine buildS_ph hg 8 _ _ fun m _ st' hs' ↦ ?_
  have h := sumL_ph hs'.good (List.range 8)
    (fun zl ↦ RecGraph.Pi1.mul (eLow.getD zl 0) (sA.getD ((8 * m + zl + 64 - ol) % 64) 0))
    (fun zl ↦ (eLowE zS RL).getD zl 0 * S.toArray.getD ((8 * m + zl + 64 - ol) % 64) 0) fun zl hzl st'' hs'' ↦ by
      have hzl' : zl < 8 := List.mem_range.mp hzl
      exact PH.mul hs''.good ((hel.get (by omega)).pgrow hg (hs'.trans hs''))
        ((hs.get (by simp [hS]; omega)).pgrow hg (hs'.trans hs''))
  refine h.mono fun st'' v _ hv ↦ ?_
  simpa [partialAtE, UniKeccak.sumRange, loE_3 hlen, List.range_eq_range'] using hv

/-- **The correlations**: `corrE` (`0` off the needed offsets), the partial ones memoised. -/
theorem corrS_ph {st : RecState} (hg : Good st) {eLow eHigh sA : Array Sym} {zS : Option E} {RL S : List E}
    (hlen : RL.length = 3) (hel : RpA' st eLow (eLowE zS RL)) (hels : (eLowE zS RL).size = 8)
    (heh : RpA' st eHigh (eHighE RL)) (hehs : (eHighE RL).size = 8)
    (hs : RpA' st sA S.toArray) (hS : S.length = 64) :
    PH (corrS eLow eHigh sA 8 8) st (fun st' c ↦ RpA' st' c (corrE zS RL S)) := by
  unfold corrS
  dsimp only
  phg (PZ hg) as st1 z0 hs1 hz0
  obtain ⟨L, hL⟩ : ∃ L, L = (List.range 64).filter fun off ↦ UniKeccak.shiftOffsets.getD off false := ⟨_, rfl⟩
  rw [← hL]
  have hmemL : ∀ x ∈ L, x < 64 := by
    intro x hx; rw [hL, List.mem_filter, List.mem_range] at hx; exact hx.1
  refine PH.bind' (PH.forIn_list L (Array.replicate 8 none, Array.replicate 64 z0) _ st1
    (fun j st' (b : Array (Option (Array Sym)) × Array Sym) ↦
      PStep st1 st' ∧ b.1.size = 8 ∧
      (∀ ol q, b.1.getD ol none = some q → RpA' st' q (Array.ofFn (n := 8) fun m ↦ partialAtE zS RL S ol m.val)) ∧
      b.2.size = 64 ∧ ∀ off < 64, Rp' st' (b.2.getD off 0) (if off ∈ L.take j then corrAtE zS RL S off else 0))
    hg ⟨PStep.refl st1 hg, by simp, fun ol q h ↦ by by_cases hol : ol < 8 <;> simp [Array.getD_eq_getD_getElem?, hol] at h, by simp,
      fun off hoff ↦ by simpa [Array.getD_eq_getD_getElem?, hoff] using hz0⟩ ?_) ?_
  · intro j hj st' b hs' ⟨hst, hb1, hmemo, hb2, hcorr⟩
    have hoff : L[j] < 64 := hmemL _ (List.getElem_mem hj)
    -- the step after the partial correlations `q`, whichever way they came
    have cont : ∀ st'' (q : Array Sym), PStep st' st'' →
        RpA' st'' q (Array.ofFn (n := 8) fun m ↦ partialAtE zS RL S (L[j] % 8) m.val) →
        PH (do
          let __do_lift ← sumL (List.range 8) fun zh ↦
            RecGraph.Pi1.mul (eHigh.getD zh 0) (q.getD ((zh + 8 - L[j] / 8) % 8) 0)
          pure (ForInStep.yield (b.1.set! (L[j] % 8) (some q), b.2.set! L[j] __do_lift))) st''
          (fun st'' r ↦ ∃ b', r = .yield b' ∧ PStep st1 st'' ∧ b'.1.size = 8 ∧
            (∀ ol q, b'.1.getD ol none = some q →
              RpA' st'' q (Array.ofFn (n := 8) fun m ↦ partialAtE zS RL S ol m.val)) ∧
            b'.2.size = 64 ∧
            ∀ off < 64, Rp' st'' (b'.2.getD off 0) (if off ∈ L.take (j + 1) then corrAtE zS RL S off else 0)) := by
      intro st'' q hs'' hq
      have hsum := sumL_ph hs''.good (List.range 8)
        (fun zh ↦ RecGraph.Pi1.mul (eHigh.getD zh 0) (q.getD ((zh + 8 - L[j] / 8) % 8) 0))
        (fun zh ↦ (eHighE RL).getD zh 0 * partialAtE zS RL S (L[j] % 8) ((zh + 8 - L[j] / 8) % 8))
        fun zh hzh st3 hs3 ↦ by
          have hzh' : zh < 8 := List.mem_range.mp hzh
          have hq3 := (hq.pgrow hs''.good hs3).get (i := (zh + 8 - L[j] / 8) % 8) (by simp; omega)
          rw [getD_ofFn _ (by omega)] at hq3
          exact PH.mul hs3.good (((heh.pgrow hg hst).pgrow hs'.good hs'').pgrow hs''.good hs3 |>.get
            (by omega)) hq3
      refine PH.bind' hsum fun st3 v hs3 hv ↦ PH.ret hs3.good ⟨_, rfl, hst.trans (hs''.trans hs3), ?_, ?_, ?_, ?_⟩
      · simp [hb1]
      · intro ol q' hq'
        rw [getD_setB] at hq'
        by_cases h : L[j] % 8 = ol ∧ ol < b.1.size
        · rw [iteT h] at hq'
          cases hq'
          rw [← h.1]
          exact hq.pgrow hs''.good hs3
        · rw [iteF h] at hq'
          exact ((hmemo ol q' hq').pgrow hs'.good hs'').pgrow hs''.good hs3
      · simp [hb2]
      · intro off hoff'
        rw [getD_setB]
        have hmem : off ∈ L.take (j + 1) ↔ off ∈ L.take j ∨ off = L[j] := by
          rw [take_succ_getElem _ _ hj, List.mem_append, List.mem_singleton]
        by_cases h : L[j] = off ∧ off < b.2.size
        · rw [iteT h]
          have hin : off ∈ L.take (j + 1) := hmem.mpr (Or.inr h.1.symm)
          rw [iteT hin, ← h.1]
          simpa [corrAtE, UniKeccak.sumRange, nHiE_3 hlen, loE_3 hlen, List.range_eq_range'] using hv
        · rw [iteF h]
          have hne : off ≠ L[j] := fun he ↦ h ⟨he.symm, by omega⟩
          have hiff : off ∈ L.take (j + 1) ↔ off ∈ L.take j := by
            rw [hmem]; exact ⟨fun h' ↦ h'.resolve_right hne, Or.inl⟩
          rw [if_congr hiff rfl rfl]
          exact (((hcorr off hoff').pgrow hs'.good hs'').pgrow hs''.good hs3)
    split
    · rename_i q hq
      exact cont st' q (PStep.refl st' hs'.good) (hmemo _ q hq)
    · exact PH.bind' (partialS_ph hs'.good hlen (hel.pgrow hg hst) hels (hs.pgrow hg hst) hS _)
        fun st'' q hs'' hq ↦ cont st'' q hs'' hq
  · rintro st2 b hs2 ⟨_, _, _, hb2, hcorr⟩
    refine PH.ret hs2.good ⟨by simp [hb2, corrE], fun off hoff ↦ ?_⟩
    rw [hb2] at hoff
    have h := hcorr off hoff
    rw [List.take_length] at h
    have hiff : off ∈ L ↔ UniKeccak.shiftOffsets.getD off false = true := by
      rw [hL, List.mem_filter, List.mem_range]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hoff, h⟩⟩
    rw [if_congr hiff rfl rfl] at h
    simpa [corrE, Array.getD_eq_getD_getElem?, hoff] using h

end Terminal

end RecGraphKeccak.Sim
