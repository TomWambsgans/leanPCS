-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockProverMain.lean` (and the Flock facts of
-- `CoreBatch.lean`, `Rec3FlockRing.lean`, `Rec3FlockHonest.lean`, `Rec3End.lean`).
import UniKeccakComplete.K.FlockProverSync
import UniKeccakComplete.K.FlockProverRing
import UniKeccakComplete.K.FlockProverSum
import UniKeccakComplete.K.FlockProverSkip

/-!
# Flock's honest prover on the Keccak-f block: the headline theorems and their axioms

`UniKeccakComplete.FlockP.flockProve H : FlockProver m` (`FlockProver.lean`), at a pure Keccak-256 `H` (`Id`), every
writer (any challenges), on `q_flock`'s words `q`, for every variant (`keccakMain`, `keccakRec3`, any skip `k ≤ 6`,
either Fiat–Shamir shape):

* `flockSyncs` (`FlockProverSync.lean`, no hypotheses): `FlockSyncs H (flockProve (pure ∘ H)) log_n v q
  (flockZero H log_n v q)`, the value collected `flockZero` (the lincheck's terminal check on the honest front);
* **`flockZero_eq_zero`** (`k ≤ 6`, `log_n = 17 + κ`, `FlockHolds κ q`): that value is zero (`terminalHolds` with the
  univariate skip's completeness discharged, `Skip.skipComplete`); so **`flockSyncs_zero`**: `FlockSyncs … (fun _ ↦ 0)`;
* `flockRingHolds` (`FlockProverRing.lean`, no hypotheses): `FlockRingHolds`, tower order; `flockRingSum` the same
  unfolded;
* the shapes later layers read: `flock_point_length` (`log_n − 6` coordinates), `flock_ring` (a ring end of 6
  challenges), and on a trace `flock_point_length_trace` (`h_SHA3 + 11`), `flockSyncs_trace`.

`flockHolds_of_traceHonest`: an honest trace's `TraceHonest.flock` is `FlockHolds (tr.height 5) tr.qflock`.

The guards below fail the build if a theorem's axioms grow beyond Lean's three.
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

/-- **An honest trace's Flock relation** is `FlockHolds` of its `q_flock` (`qflockColumn tr = colOf …`, by
definition). -/
theorem flockHolds_of_traceHonest (tr : Trace) (h : TraceHonest tr) : FlockHolds (tr.height 5) tr.qflock := h.flock

/-! ## The terminal check -/

/-- **The lincheck's terminal check vanishes on the honest front**, unconditionally but for Flock's relation on
`q_flock`: the univariate skip's completeness holds at every `k ≤ 6` (`Skip.skipComplete`). -/
theorem terminalHolds_honest (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hF : FlockHolds κ q) :
    UniKeccak.structuredTerminal ((frontW H (17 + κ) v q).run w).1.1.zSkip
        ((frontW H (17 + κ) v q).run w).1.1.rowLow ((frontW H (17 + κ) v q).run w).1.1.chiIn
        ((frontW H (17 + κ) v q).run w).1.1.chiInPrime (((frontW H (17 + κ) v q).run w).1.1.slices.getD [])
        ((frontW H (17 + κ) v q).run w).1.1.alpha +
      ((frontW H (17 + κ) v q).run w).1.1.rLc = 0 :=
  terminalHolds H κ v q w hk hF fun _ ↦ Skip.skipComplete _ hk

/-- **The value the verifier collects on the honest front is zero**: `structuredTerminal … + r_lc = 0`, at
`log_n = 17 + κ`, any skip `k ≤ 6`, either Fiat–Shamir shape, every writer, given Flock's relation on `q_flock`. -/
theorem flockZero_eq_zero (H : List UInt8 → LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hF : FlockHolds κ q) : flockZero H (17 + κ) v q w = 0 :=
  terminalHolds_honest (Pure.pure ∘ H) κ v q w hk hF

/-- **`FlockSyncs` of the honest prover collecting zero**: at `log_n = 17 + κ`, any skip `k ≤ 6`, either Fiat–Shamir
shape, given Flock's relation on `q_flock`. -/
theorem flockSyncs_zero (H : List UInt8 → LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (hk : v.skip ≤ 6) (hF : FlockHolds κ q) :
    FlockSyncs H (flockProve (m := Id) (Pure.pure ∘ H)) (17 + κ) v q fun _ ↦ 0 := fun w ↦
  syncs_congr_zs (flockSyncs H (17 + κ) v q w) (by rw [flockZero_eq_zero H κ v q w hk hF])

theorem keccakMain_skip : UniKeccak.keccakMain.skip = 3 := rfl

theorem keccakRec3_skip : UniKeccak.keccakRec3.skip = 3 := rfl

/-- Flock's `log_n` on a trace, two spellings. -/
theorem logN_eq (tr : Trace) : keccakR1csLogSize + tr.shape.heights.getD opSha3 0 = 17 + tr.height 5 := rfl

/-- **The honest Flock step on an honest trace**, collecting zero, at the `log_n` the prover and the verifier use
(`keccakR1csLogSize + h_SHA3`), any variant of skip `≤ 6` (`keccakMain`, `keccakRec3`). -/
theorem flockSyncs_trace (H : List UInt8 → LeanVM.Protocol.Digest) (tr : Trace) (hon : TraceHonest tr)
    (v : UniKeccak.KeccakVariant) (hk : v.skip ≤ 6) :
    FlockSyncs H (flockProve (m := Id) (Pure.pure ∘ H)) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0)
      v tr.qflock (fun _ ↦ 0) := by
  rw [logN_eq]
  exact flockSyncs_zero H (tr.height 5) v tr.qflock hk (flockHolds_of_traceHonest tr hon)

/-! ## The ring switch and the shapes -/

/-- **Flock's ring identity, unfolded** (`flockRingHolds`'s content, in tower order): the prover ends with a ring
switch of six stages whose target is `Σ_u Φ(eq(point, u)) q_flock[u]`. -/
theorem flockRingSum (H : List UInt8 → Id LeanVM.Protocol.Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (w : Wr) :
    ∃ map target, ((flockProve H logN v q).run w).1.end_ = .ring map target ∧ map.length = 6 ∧
      ∑ u ∈ range (2 ^ ((flockProve H logN v q).run w).1.point.length),
        towerRingMap ((eqKernel ((flockProve H logN v q).run w).1.point).getD u 0) map * ofK (q.getD u 0) =
          target := by
  have hmap : ((samplesW H ringMapShifts.length).run ((frontW H logN v q).run w).2).1.length = 6 := by
    rw [samplesW_length]; rfl
  refine ⟨_, _, flockProve_ring H logN v q w, hmap, ?_⟩
  rw [flockProve_point]
  generalize ((samplesW H ringMapShifts.length).run ((frontW H logN v q).run w).2).1 = map at hmap ⊢
  show ∑ u ∈ range (2 ^ ((frontW H logN v q).run w).1.1.point.length),
      towerRingMap ((eqKernel ((frontW H logN v q).run w).1.1.point).getD u 0) map * ofK (q.getD u 0) =
    towerTarget ((frontW H logN v q).run w).1.2 map
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW_eq H logN v q w
  have hlen : lc.challenges.length = 11 := by rw [hlc, lcRounds_length]; rfl
  have hz : lc.z = lc.challenges.foldl foldHigh (lcWitnessOf v.skip q zc) := by rw [hlc, lcRounds_z]
  rw [hfr]
  show ∑ u ∈ range (2 ^ (lc.challenges.reverse ++
        (zc.2.1.drop (packing - v.skip)).drop UniKeccak.lincheckRoundsK).length),
      towerRingMap ((eqKernel (lc.challenges.reverse ++
        (zc.2.1.drop (packing - v.skip)).drop UniKeccak.lincheckRoundsK)).getD u 0) map * ofK (q.getD u 0) =
    towerTarget lc.z.toList map
  rw [hz]
  exact ringHolds_pure q _ lc.challenges map hlen hmap

/-- **The prover's point has `log_n − 6` coordinates** (`log_n ≥ 17`, `k ≤ 6`). -/
theorem flock_point_length (H : List UInt8 → LeanVM.Protocol.Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hN : 17 ≤ logN) :
    ((flockProve (m := Id) (Pure.pure ∘ H) logN v q).run w).1.point.length = logN - 6 := by
  rw [flockProve_point]
  exact (frontW_shape (Pure.pure ∘ H) logN v q w hk hN).2.2.2.2.2.2.2

/-- **The prover ends with a ring switch of six challenges.** -/
theorem flock_ring (H : List UInt8 → LeanVM.Protocol.Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K)
    (w : Wr) :
    ∃ map target, ((flockProve (m := Id) (Pure.pure ∘ H) logN v q).run w).1.end_ = .ring map target ∧
      map.length = 6 :=
  ⟨_, _, flockProve_ring (Pure.pure ∘ H) logN v q w, by rw [samplesW_length]; rfl⟩

/-- **On a trace, the point has `h_SHA3 + 11` coordinates** (`q_flock`'s `2^(11 + h_SHA3)` words). -/
theorem flock_point_length_trace (H : List UInt8 → LeanVM.Protocol.Digest) (tr : Trace) (v : UniKeccak.KeccakVariant)
    (hk : v.skip ≤ 6) (w : Wr) :
    ((flockProve (m := Id) (Pure.pure ∘ H) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) v
      tr.qflock).run w).1.point.length = tr.shape.heights.getD opSha3 0 + 11 := by
  rw [flock_point_length H (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) v _ w hk
    (by unfold keccakR1csLogSize; omega)]
  unfold keccakR1csLogSize
  omega

end UniKeccakComplete.FlockP

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.FlockP.flockSyncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockSyncs

/-- info: 'UniKeccakComplete.FlockP.flockZero_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockZero_eq_zero

/-- info: 'UniKeccakComplete.FlockP.flockSyncs_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockSyncs_zero

/-- info: 'UniKeccakComplete.FlockP.flockSyncs_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockSyncs_trace

/-- info: 'UniKeccakComplete.FlockP.flockRingHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockRingHolds

/-- info: 'UniKeccakComplete.FlockP.flockRingSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flockRingSum

/-- info: 'UniKeccakComplete.FlockP.flock_point_length_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.flock_point_length_trace

/-- info: 'UniKeccakComplete.FlockP.terminal_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.terminal_pure

/-- info: 'UniKeccakComplete.FlockP.Tower.towerTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.Tower.towerTarget_eq

/-- info: 'UniKeccakComplete.FlockP.Skip.skipComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.FlockP.Skip.skipComplete
