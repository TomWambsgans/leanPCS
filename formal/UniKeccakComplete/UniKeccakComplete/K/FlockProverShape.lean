-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockProverShape.lean` (and `Rec3FlockShape.lean`'s
-- run of squares).
import UniKeccakComplete.K.FlockProverMle

/-!
# The honest prover's run: its output and its shapes

At a pure Keccak-256 (`Id`), the prover's run is a function of the writer it starts from. Here:

* `run_bind_id`, `run_pure_id`: a `WrM Id` program's run, bind by bind;
* **`flockProve_eq`**: the output is the front's point and the ring switch's end; **`frontW_eq`**: the front is
  `frontOf` of the zerocheck's output, `α` and the lincheck's output (each the run of its program at some writer);
  **`zerocheckW_eq`**: the zerocheck's output is the skip's start and the rounds';
* the loops' pure content, for every writer: `drawW_length` (either Fiat–Shamir shape), `zcRounds_chi_length`,
  `lcRounds_length`, `lcRounds_z` (the slices are the witness folded, high variable first, by the round
  challenges), `skipW_eq`;
* **`frontW_shape`**: at `log_n ≥ 17`, `k ≤ 6`: `row_low` has `6 − k` coordinates, `chi_in` and `chi_in'` `11`, the
  point `log_n − 6`; the 64 slices sent as they are; the skip's point present exactly when `k > 0`.

Decision: the programs are unfolded one bind at a time into existentials with equations (`…_eq`), never by
`simp` through a whole run (the substituted terms grow with every bind and the kernel's check of them recursed too
deep).
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol.KeccakHash

theorem run_bind_id {σ α β : Type} (x : StateT σ Id α) (f : α → StateT σ Id β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem run_pure_id {σ α : Type} (a : α) (s : σ) : (pure a : StateT σ Id α).run s = (a, s) := rfl

theorem lincheckRoundsK_eq : UniKeccak.lincheckRoundsK = 11 := rfl

/-- `squares c n` has `n` terms. -/
theorem squares_length : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by rw [squares, List.length_cons, squares_length (c * c) n]

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-! ## The programs, bind by bind -/

theorem samplesW_length : ∀ (n : ℕ) (w : Wr), ((samplesW H n).run w).1.length = n
  | 0, _ => rfl
  | n + 1, w => by
    simp only [samplesW, run_bind_id, run_pure_id, List.length_cons, samplesW_length n]

/-- **A draw has `count` terms**, either Fiat–Shamir shape, every writer. -/
theorem drawW_length (fs : FsShape) (n : ℕ) (w : Wr) : ((drawW H fs n).run w).1.length = n := by
  cases fs with
  | main => exact samplesW_length H n w
  | rec1 | rec2 | rec3 | rec4 =>
    unfold drawW
    by_cases hn : n = 0
    · subst hn; rfl
    · have hn' : (n = 0) = False := eq_false hn
      simp only [hn', ↓reduceIte, run_bind_id, run_pure_id, squares_length]

/-- **The prover's output** is the front's point and the ring switch's end. -/
theorem flockProve_eq (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) :
    ∃ (frs : Front × List E) (w1 : Wr), frs = ((frontW H logN v q).run w).1 ∧
      ((flockProve H logN v q).run w).1 = ⟨frs.1.point, ((ringEndW H frs.2).run w1).1⟩ := by
  refine ⟨_, ((frontW H logN v q).run w).2, rfl, ?_⟩
  simp only [flockProve, run_bind_id, run_pure_id]

/-- **The front** is `frontOf` of the zerocheck's output, `α` and the lincheck's output. -/
theorem frontW_eq (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) :
    ∃ (zc : Option E × List E × E × E × E) (alpha : E) (lc : LcOut),
      zc = ((zerocheckW H logN v.skip v.fs (witOf logN q)).run w).1 ∧
      (∃ w2, lc = ((lcRounds H UniKeccak.lincheckRoundsK (lcClaim zc alpha) (lcWeightsOf v.skip zc alpha)
        (lcWitnessOf v.skip q zc)).run w2).1) ∧
      ((frontW H logN v q).run w).1 = frontOf v zc alpha lc := by
  refine ⟨_, ((sampleW H).run ((zerocheckW H logN v.skip v.fs (witOf logN q)).run w).2).1, _, rfl,
    ⟨((sampleW H).run ((zerocheckW H logN v.skip v.fs (witOf logN q)).run w).2).2, rfl⟩, ?_⟩
  simp only [frontW, run_bind_id, run_pure_id]

/-- **The prover's front holds the slices it sent.** -/
theorem frontW_slices (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) :
    ((frontW H logN v q).run w).1.1.slices = some ((frontW H logN v q).run w).1.2 := by
  obtain ⟨zc, alpha, lc, _, _, hfr⟩ := frontW_eq H logN v q w
  rw [hfr]
  rfl

/-- **The zerocheck** is the skip's start and the rounds' output. -/
theorem zerocheckW_eq (logN k : ℕ) (fs : FsShape) (wit : Wit) (w : Wr) :
    ∃ (sampled : List E) (st : ZcStart) (zc : ZcOut), sampled.length = logN - k - nFixed ∧
      (∃ w1, st = ((skipW H k (fixedChallenges ++ sampled) wit).run w1).1) ∧
      (∃ w2, zc = ((zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c).run w2).1) ∧
      ((zerocheckW H logN k fs wit).run w).1 = (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb) := by
  refine ⟨_, _, _, drawW_length H fs _ w, ⟨((drawW H fs (logN - k - nFixed)).run w).2, rfl⟩,
    ⟨((skipW H k (fixedChallenges ++ ((drawW H fs (logN - k - nFixed)).run w).1) wit).run
      ((drawW H fs (logN - k - nFixed)).run w).2).2, rfl⟩, ?_⟩
  simp only [zerocheckW, run_bind_id, run_pure_id]

/-- **The skip's start**: with `k > 0` the tables at some point `z`, without the tables themselves. -/
theorem skipW_eq (k : ℕ) (r : List E) (wit : Wit) (w : Wr) :
    (0 < k → ∃ z, ((skipW H k r wit).run w).1 = startAt k (cosetValues k r wit) z wit) ∧
      (k = 0 → ((skipW H k r wit).run w).1 = startNone wit) := by
  refine ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
  · have hk' : (k > 0) = True := eq_true hk
    unfold skipW
    simp only [hk', ↓reduceIte]
    exact ⟨_, rfl⟩
  · subst hk
    rfl

/-! ## The loops -/

theorem zcRounds_chi_length : ∀ (r : List E) (claim : E) (a b c : Array E) (w : Wr),
    ((zcRounds H r claim a b c).run w).1.chi.length = r.length
  | [], _, _, _, _, _ => rfl
  | _ :: rest, claim, a, b, c, w => by
    simp only [zcRounds, run_bind_id, run_pure_id, List.length_cons, zcRounds_chi_length rest]

theorem lcRounds_length : ∀ (n : ℕ) (claim : E) (wt z : Array E) (w : Wr),
    ((lcRounds H n claim wt z).run w).1.challenges.length = n
  | 0, _, _, _, _ => rfl
  | n + 1, claim, wt, z, w => by
    simp only [lcRounds, run_bind_id, run_pure_id, List.length_cons, lcRounds_length n]

/-- **The lincheck's folded witness** is the witness folded, high variable first, by the round challenges (in round
order). -/
theorem lcRounds_z : ∀ (n : ℕ) (claim : E) (wt z : Array E) (w : Wr),
    ((lcRounds H n claim wt z).run w).1.z = ((lcRounds H n claim wt z).run w).1.challenges.foldl foldHigh z
  | 0, _, _, _, _ => rfl
  | n + 1, claim, wt, z, w => by
    simp only [lcRounds, run_bind_id, run_pure_id, List.foldl_cons]
    exact lcRounds_z n _ _ _ _

theorem foldHigh_size (v : Array E) (x : E) : (foldHigh v x).size = v.size / 2 := by
  simp [foldHigh]

theorem foldl_foldHigh_size : ∀ (xs : List E) (j : ℕ) (z : Array E), z.size = 2 ^ (xs.length + j) →
    (xs.foldl foldHigh z).size = 2 ^ j
  | [], j, z, h => by simpa using h
  | x :: xs, j, z, h => by
    rw [List.foldl_cons]
    refine foldl_foldHigh_size xs j _ ?_
    rw [foldHigh_size, h, List.length_cons, show xs.length + 1 + j = (xs.length + j) + 1 by ring, pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]

theorem fixedChallenges_length : fixedChallenges.length = nFixed := rfl

/-- **The zerocheck's shape**: its point has `log_n − k` coordinates (`log_n ≥ k + 7`), the skip's point is
present exactly when `k > 0`. -/
theorem zerocheckW_shape (logN k : ℕ) (fs : FsShape) (wit : Wit) (w : Wr) (hN : k + nFixed ≤ logN) :
    ((zerocheckW H logN k fs wit).run w).1.2.1.length = logN - k ∧
      (k = 0 → ((zerocheckW H logN k fs wit).run w).1.1 = none) ∧
      (0 < k → ((zerocheckW H logN k fs wit).run w).1.1.isSome) := by
  obtain ⟨sampled, st, zc, hlen, ⟨w1, hst⟩, ⟨w2, hzc⟩, heq⟩ := zerocheckW_eq H logN k fs wit w
  rw [heq]
  refine ⟨?_, fun hk ↦ ?_, fun hk ↦ ?_⟩
  · show zc.chi.length = _
    rw [hzc, zcRounds_chi_length, List.length_append, fixedChallenges_length, hlen]
    omega
  · show st.zSkip = none
    rw [hst, (skipW_eq H k _ wit w1).2 hk]
    rfl
  · show st.zSkip.isSome
    obtain ⟨z, hz⟩ := (skipW_eq H k _ wit w1).1 hk
    rw [hst, hz]
    rfl

/-- **The front's shape**, at `log_n ≥ 17`, `k ≤ 6`. -/
theorem frontOf_shape (v : UniKeccak.KeccakVariant) (zc : Option E × List E × E × E × E) (alpha : E) (lc : LcOut)
    (logN : ℕ) (hk : v.skip ≤ 6) (hN : 17 ≤ logN) (hchi : zc.2.1.length = logN - v.skip)
    (hlc : lc.challenges.length = 11) (hz : lc.z.size = 64) :
    (frontOf v zc alpha lc).1.rowLow.length = 6 - v.skip ∧
      (frontOf v zc alpha lc).1.chiIn.length = 11 ∧
      (frontOf v zc alpha lc).1.chiInPrime.length = 11 ∧
      (frontOf v zc alpha lc).2.length = 64 ∧
      (frontOf v zc alpha lc).1.slices = some (frontOf v zc alpha lc).2 ∧
      (frontOf v zc alpha lc).1.zSkip = zc.1 ∧
      (frontOf v zc alpha lc).1.point.length = logN - 6 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [frontOf, List.length_take, hchi]; unfold packing; omega
  · simp only [frontOf, List.length_take, List.length_drop, hchi, lincheckRoundsK_eq]
    unfold packing; omega
  · simp only [frontOf, List.length_reverse, hlc]
  · simp only [frontOf, Array.length_toList, hz]
  · simp only [frontOf, List.length_append, List.length_reverse, List.length_drop, hlc, hchi, lincheckRoundsK_eq]
    unfold packing; omega

/-- The lincheck's witness has `2^17` entries. -/
theorem lcWitnessOf_size (k : ℕ) (q : Array K) (zc : Option E × List E × E × E × E) :
    (lcWitnessOf k q zc).size = 2 ^ (11 + 6) := by
  simp [lcWitnessOf, lincheckWitness, keccakR1csLogSize]

/-- **The front's shape** of the run. -/
theorem frontW_shape (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) (hk : v.skip ≤ 6)
    (hN : 17 ≤ logN) :
    ((frontW H logN v q).run w).1.1.rowLow.length = 6 - v.skip ∧
      ((frontW H logN v q).run w).1.1.chiIn.length = 11 ∧
      ((frontW H logN v q).run w).1.1.chiInPrime.length = 11 ∧
      ((frontW H logN v q).run w).1.2.length = 64 ∧
      ((frontW H logN v q).run w).1.1.slices = some ((frontW H logN v q).run w).1.2 ∧
      (v.skip = 0 → ((frontW H logN v q).run w).1.1.zSkip = none) ∧
      (0 < v.skip → ((frontW H logN v q).run w).1.1.zSkip.isSome) ∧
      ((frontW H logN v q).run w).1.1.point.length = logN - 6 := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW_eq H logN v q w
  obtain ⟨hchi, hnone, hsome⟩ := zerocheckW_shape H logN v.skip v.fs (witOf logN q) w (by unfold nFixed; omega)
  rw [← hzc] at hchi hnone hsome
  have hlen : lc.challenges.length = 11 := by rw [hlc, lcRounds_length]; rfl
  have hsz : lc.z.size = 64 := by
    rw [hlc, lcRounds_z]
    refine foldl_foldHigh_size _ 6 _ ?_
    rw [lcRounds_length, lcWitnessOf_size]
    rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := frontOf_shape v zc alpha lc logN hk hN hchi hlen hsz
  rw [hfr]
  exact ⟨h1, h2, h3, h4, h5, fun h ↦ h6.trans (hnone h), fun h ↦ h6 ▸ hsome h, h7⟩

end UniKeccakComplete.FlockP
