-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's verifier reads its honest prover's stream:
-- `Rec3SyncVerifier.lean`'s `reduce_steps3`, `runWithKH_syncs3`, `runWithKH_accepts3` for `reduceWithKH4 … keccakRec4
-- .point` (`Rec4VerifierH.lean`) and `Rec4Prover.lean`'s `proveStreamRec4With`, with the three wide draws.
import UniKeccakComplete.K.Rec4Flock
import UniKeccakComplete.K.Rec4Batch
import UniKeccakComplete.K.Rec4Split
import UniKeccakComplete.K.Rec3SyncVerifier

/-!
# π1-rec4's verifier reads back the honest prover's stream

At a pure Keccak-256 `H` and a pure rate `W` (`Id`), `reduceWithKH4 … keccakRec4 .point` run on the stream
`proveStreamRec4With` writes from the seed reads every message and draws the same challenges, in the verifier's order:
the counts, `C1`'s root and answer, **the bus draw** (`Steps.sampleWide`: one call of `W` on the same bytes, the same
challenges `wideXs`, the writer `wideWr`), Flock from `bus[3]` (`FlockP.flockSyncs4`, its value zero for an honest
`q_flock`), `C2`'s root and answer, **the point draw**, the values at `t` (π1-rec3's `tablesLoop_reads`,
`atTOf_values`), **the late draw**, the paired batch with `λ = late[1]` (`batchSyncs4_honest` under `BatchHolds` at the
prover's state `frontOf4`), `finish`.

* **`reduce_steps4`**: the joint steps, with the run's ends (the openings the prover's point claims, no matrices'
  claim, the roots its halves, the collected values the counts' checks and two zeros);
* **`runWithKH4_syncs4`**, **`runWithKH4_accepts4`**: the run returns `.ok R` at the end of the prover's stream and
  accepts.
-/

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniKeccakComplete.Prob (tInput)

-- The heavy definitions stay folded: the defeq checks between the prover's state (`frontOf4`) and the proof's
-- named values would otherwise unfold Flock's prover and the values at `t`.
attribute [local irreducible] flockProve4 atTOf c2DataOf c1Stack setupStackOf

/-! ## The wide draw -/

/-- **The wide draw's challenges** at the writer `w` and the rate function `W`. -/
def wideXs (W : List UInt8 → RateB) (count : ℕ) (w : Wr) : List E :=
  (List.range count).map (challengeAt (W (tInput w)).toList)

theorem extract_of_prefix (w : Wr) (D : Array UInt8) (hD : w.stream.toList <+: D.toList) :
    D.extract w.absorbed w.stream.size = w.stream.extract w.absorbed w.stream.size := by
  apply Array.toList_inj.mp
  obtain ⟨t, ht⟩ := hD
  rw [Array.toList_extract, Array.toList_extract, ← ht, List.extract_eq_take_drop, List.extract_eq_take_drop]
  by_cases hab : w.absorbed ≤ w.stream.toList.length
  · have hl : (List.drop w.absorbed w.stream.toList).length = w.stream.size - w.absorbed := by simp
    rw [List.drop_append_of_le_length hab, List.take_left' hl, List.take_of_length_le (le_of_eq hl)]
  · have h0 : w.stream.size - w.absorbed = 0 := by simp at hab; omega
    rw [h0, List.take_zero, List.take_zero]

/-- **The wide draw in step**: both at the end of the stream, the same rate on the same bytes, the same challenges,
the same writer and channel after it. -/
theorem Steps.sampleWide (W : List UInt8 → RateB) (count : ℕ) (w : Wr) :
    Steps (sampleWideH (m := Id) (Pure.pure ∘ W) count) (sampleWideW (m := Id) (Pure.pure ∘ W) count)
      w.stream.size w (wideXs W count w) (wideXs W count w) (wideWr w (W (tInput w)) count).stream.size
      (wideWr w (W (tInput w)) count) [] := by
  refine ⟨rfl, List.prefix_refl _, fun D Z hD ↦ ?_⟩
  have hex := extract_of_prefix w D hD
  have e : (sampleWideH (m := Id) (Pure.pure ∘ W) count).run.run (chanAt D w.stream.size w Z) =
      (.ok ((List.range count).map (challengeAt (W (digestBytes w.state ++
          (D.extract w.absorbed w.stream.size).toList)).toList)),
        ⟨D, w.stream.size, w.stream.size, digestOfRate (W (digestBytes w.state ++
          (D.extract w.absorbed w.stream.size).toList)),
          w.challenges ++ ((List.range count).map (challengeAt (W (digestBytes w.state ++
          (D.extract w.absorbed w.stream.size).toList)).toList)).toArray, Z⟩) := rfl
  rw [e, hex, show ([] : List E).toArray = #[] from rfl, Array.append_empty]
  rfl

/-! ## The prover's state when the batch starts -/

section Front

variable (H : List UInt8 → Digest) (W : List UInt8 → RateB) (commit : Commitment → ℕ → Array K → Id Committed)

/-- **π1-rec4's prover's run up to the late draw** (`proveStreamRec4With`'s steps 0–8, at `Id`), from the writer `w0`:
its state (Flock's output with its end at the map `pointDraw[1 …] ++ [late[2], late[3]]`), `λ = late[1]`, and the
writer when the batch's rounds start. -/
def frontOf4 (tr : Trace) (w0 : Wr) : FrontOut × E × Wr :=
  let shape := tr.shape
  let w1 := w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)
  let stack1 := c1Stack tr
  let committed1 : Committed := commit .c1 (c1LayoutK shape).vars stack1
  let w2 := (w1.append (rootWord committed1.halves)).append
    (scalarWire (pcsOod (c1LayoutK shape).vars stack1 (rootOf committed1.halves)))
  let bus := wideXs W 4 w2
  let w3 := wideWr w2 (W (tInput w2)) 4
  let alphas := squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let logN := keccakR1csLogSize + shape.heights.getD opSha3 0
  let fl := ((flockProve4 (m := Id) (Pure.pure ∘ H) logN keccakRec4 (bus.getD 3 0) tr.qflock).run w3).1
  let w4 := ((flockProve4 (m := Id) (Pure.pure ∘ H) logN keccakRec4 (bus.getD 3 0) tr.qflock).run w3).2
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((layoutsOfK shape).lookup .c2).getD default).vars c2.stack
  let w5 := (w4.append (rootWord committed2.halves)).append
    (scalarWire (pcsOod (((layoutsOfK shape).lookup .c2).getD default).vars c2.stack (rootOf committed2.halves)))
  let pointDraw := wideXs W 5 w5
  let w6 := wideWr w5 (W (tInput w5)) 5
  let t := pointDraw.getD 0 0
  let w7 := w6.append ((atTOf tr c2 alphas beta gamma t none).values.flatMap scalarWire)
  let late := wideXs W 4 w7
  let w8 := wideWr w7 (W (tInput w7)) 4
  let rho := late.getD 0 0
  let lambda := late.getD 1 0
  let map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0]
  let fo := flockOut4 fl map
  let a := atTOf tr c2 alphas beta gamma t (some fo)
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layoutsK shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, some fo, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, lambda, w8)

/-- **The honest batch's hypothesis at π1-rec4's prover's state**: `BatchHolds` of its combined claims. -/
def BatchHoldsAt4 (tr : Trace) (seed : Digest) : Prop :=
  BatchHolds (frontOf4 H W commit tr (Wr.start seed)).1.combined
    (frontOf4 H W commit tr (Wr.start seed)).1.stackLayouts
    (frontOf4 H W commit tr (Wr.start seed)).1.stackOf
    (frontOf4 H W commit tr (Wr.start seed)).1.atT.ringMap

/-- **The batch's hypothesis at π1-rec4's prover's state**: `BatchSyncs4` at its `λ`, combined claims, layouts,
stacks and ring map, the terminal `terminal`. -/
def BatchSyncsAt4 (tr : Trace) (seed : Digest) (terminal : Wr → E) : Prop :=
  BatchSyncs4 H (frontOf4 H W commit tr (Wr.start seed)).2.1 (frontOf4 H W commit tr (Wr.start seed)).1.combined
    (frontOf4 H W commit tr (Wr.start seed)).1.stackLayouts
    (frontOf4 H W commit tr (Wr.start seed)).1.stackOf
    (frontOf4 H W commit tr (Wr.start seed)).1.atT.ringMap terminal

/-- `BatchSyncsAt4` at the zero terminal from `BatchHoldsAt4`. -/
theorem batchSyncsAt4_of_holds (tr : Trace) (seed : Digest) (h : BatchHoldsAt4 H W commit tr seed) :
    BatchSyncsAt4 H W commit tr seed (fun _ ↦ 0) :=
  batchSyncs4_honest H _ _ _ _ _ h

/-- `BatchSyncsAt4` at `batchTerminal4`, always. -/
theorem batchSyncsAt4_any (tr : Trace) (seed : Digest) :
    BatchSyncsAt4 H W commit tr seed (fun w ↦ batchTerminal4 H (frontOf4 H W commit tr (Wr.start seed)).2.1
      (frontOf4 H W commit tr (Wr.start seed)).1.combined (frontOf4 H W commit tr (Wr.start seed)).1.stackLayouts
      (frontOf4 H W commit tr (Wr.start seed)).1.stackOf (frontOf4 H W commit tr (Wr.start seed)).1.atT.ringMap w) :=
  batchSyncs4 H _ _ _ _ _

end Front

/-! ## The joint steps -/

/-- `batchKH4`'s inputs, rewritten. -/
theorem batchKH4_congr (H : List UInt8 → Digest) (lambda : E) {c1 c2 : List (Commitment × Combined)}
    {l1 l2 : List (Commitment × StackLayout)} (r : Option (List E)) (hc : c1 = c2) (hl : l1 = l2) :
    batchKH4 (m := Id) (Pure.pure ∘ H) lambda c1 l1 r = batchKH4 (m := Id) (Pure.pure ∘ H) lambda c2 l2 r := by
  subst hc hl; rfl

set_option maxHeartbeats 4000000 in
/-- **π1-rec4's verifier on its honest prover's stream**: the joint steps from the seed, with the run's ends. -/
theorem reduce_steps4 (H : List UInt8 → Digest) (W : List UInt8 → RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (seed : Digest)
    (hvalid : tr.shape.validate true = true)
    (hlen : tr.rows.length = tr.shape.heights.length) (h32 : ∀ n ∈ tr.rows, n < 2 ^ 32)
    (hF : FlockP.FlockHolds (tr.height 5) tr.qflock)
    (terminal : Wr → E) (hbatch : BatchSyncsAt4 H W commit tr seed terminal) :
    StepsE (reduceWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) tr.shape (publicWordsOf tr.publicInput) keccakRec4
        .point)
      (proveStreamRec4With (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) commit tr) 0 (Wr.start seed)
      (fun R out posF wF zs ↦ posF = wF.stream.size ∧ out.stream = wF.stream ∧
        R.openings = out.claims.map pointOpening ∧ R.matrices = none ∧
        R.roots = (rootRead out.c1.2.halves, rootRead out.c2.2.halves) ∧
        R.oods = (pcsOod (c1LayoutK tr.shape).vars out.c1.1 (rootOf out.c1.2.halves),
          pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars out.c2.1
            (rootOf out.c2.2.halves)) ∧
        zs = countChecks tr.rows tr.shape.heights ++
          [0, terminal (frontOf4 H W commit tr (Wr.start seed)).2.2]) := by
  unfold reduceWithKH4 proveStreamRec4With midB4 tailT4
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  apply StepsE.pbind (rows_writes tr.rows _ (fun _ _ ↦ rfl) _)
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.pbind (sendScalar_writes _ _)
  apply StepsE.vread (P := [])
    (Q := rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves ++
      scalarWire (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr)
        (rootOf (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)))
    (countBits_reads hlen h32)
  · simp [Wr.start]
  apply StepsE.pos_start (pos0 := (tr.rows.flatMap fun n ↦ integerWire n 4).length) (by simp)
  apply StepsE.vread
    (Q := scalarWire (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr)
      (rootOf (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)))
    (nextRoot_reads (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)
  · simp [Wr.start]
  apply StepsE.pos_start (pos0 := ((tr.rows.flatMap fun n ↦ integerWire n 4) ++
    rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves).length) (by simp)
  apply StepsE.vread (Q := []) (nextScalar_reads (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr)
    (rootOf (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)))
  · simp [Wr.start]
  set w2 := (((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
    (rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)).append
      (scalarWire (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr)
        (rootOf (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves))) with hw2
  -- The bus draw.
  apply StepsE.bind_pos (h1 := Steps.sampleWide W 4 w2)
  case e => simp [hw2, Wr.start]
  set bus := wideXs W 4 w2 with hbus
  set w3 := wideWr w2 (W (tInput w2)) 4 with hw3
  -- Flock from `bus[3]`.
  have hflock := FlockP.syncs_congr_zs (FlockP.flockSyncs4 H (keccakR1csLogSize + tr.shape.heights.getD opSha3 0)
    keccakRec4 (bus.getD 3 0) tr.qflock w3)
    (by rw [FlockP.logN_eq, FlockP.flockZero4_eq_zero H (tr.height 5) keccakRec4 (bus.getD 3 0) tr.qflock w3
      (by decide) hF])
  apply StepsE.bind_pos (h1 := hflock.steps)
  case e => rfl
  set fl := ((flockProve4 (m := Id) (Pure.pure ∘ H) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4
    (bus.getD 3 0) tr.qflock).run w3).1 with hfl
  set w4 := ((flockProve4 (m := Id) (Pure.pure ∘ H) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4
    (bus.getD 3 0) tr.qflock).run w3).2 with hw4
  apply StepsE.plift
  set c2 := c2DataOf tr (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0) (bus.getD 2 0) with hc2
  set committed2 := commit .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack with hcm2
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.pbind (sendScalar_writes _ _)
  apply StepsE.pos_start (pos0 := w4.stream.toList.length) (by simp)
  apply StepsE.vread (P := w4.stream.toList)
    (Q := scalarWire (pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack
      (rootOf committed2.halves))) (nextRoot_reads committed2.halves)
  · simp
  apply StepsE.pos_start (pos0 := (w4.append (rootWord committed2.halves)).stream.size) (by simp)
  apply StepsE.vreadEnd (nextScalar_reads (pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars
    c2.stack (rootOf committed2.halves)))
  set w5 := (w4.append (rootWord committed2.halves)).append
    (scalarWire (pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack
      (rootOf committed2.halves))) with hw5
  -- The point draw.
  apply StepsE.bind_pos (h1 := Steps.sampleWide W 5 w5)
  case e => simp [hw5]
  set pointDraw := wideXs W 5 w5 with hpd
  set w6 := wideWr w5 (W (tInput w5)) 5 with hw6
  set alphas := squares (bus.getD 0 0) 4 with halphas
  set t := pointDraw.getD 0 0 with ht
  have hvals := atTOf_values tr c2 alphas (bus.getD 1 0) t (bus.getD 2 0) none
  apply StepsE.pbind (sendScalars_writes _ _)
  apply StepsE.vreadD (R := (tailAtT tr c2 alphas (bus.getD 1 0) t).flatMap scalarWire)
    (tablesLoop_reads tr (eqKernel alphas) (bus.getD 1 0) (wOf tr t) _ ?hb tablesKeccak (#[], #[]))
  case hb => intro _ _; rfl
  case hpos => simp [hw6, wideWr]
  case hd => rw [hvals]; simp [hw6, wideWr, List.flatMap_append]
  intro hd0
  unfold tailAtT at hd0
  apply StepsE.vscalarD hd0; intro hd1
  apply StepsE.vscalarD hd1; intro hd2
  apply StepsE.vscalarD hd2; intro hd3
  apply StepsE.vscalarD hd3; intro hd4
  apply StepsE.vscalarD hd4; intro hd5
  apply StepsE.vscalarD hd5; intro hd6
  apply StepsE.vscalarD hd6; intro _
  -- The late draw.
  set w7 := w6.append ((atTOf tr c2 alphas (bus.getD 1 0) (bus.getD 2 0) t none).values.flatMap scalarWire)
    with hw7
  apply StepsE.bind_pos (h1 := Steps.sampleWide W 4 w7)
  case e =>
    simp only [hw7]
    rw [hvals]
    simp [hw6, wideWr, tailAtT, List.flatMap_append]
    try omega
  set late := wideXs W 4 w7 with hlate
  set w8 := wideWr w7 (W (tInput w7)) 4 with hw8
  have hcond : (ClaimsMode.point == ClaimsMode.point) = true := rfl
  simp only [hcond, ↓reduceIte]
  set map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0] with hmap
  set a := atTOf tr c2 alphas (bus.getD 1 0) (bus.getD 2 0) t (some (flockOut4 fl map)) with ha
  have hring : a.ringMap = some map :=
    atTOf_ringMap tr c2 alphas (bus.getD 1 0) t (bus.getD 2 0) (flockOut4 fl map) rfl
  simp only [hring]
  have hB : BatchSyncs4 H (late.getD 1 0)
      (commitments.filterMap fun c ↦ (combine a.relations c (late.getD 0 0)).map (c, ·))
      (layoutsK tr.shape a.c2Columns) (stacksOf (c1Stack tr) c2.stack (setupStackOf tr)) (some map) terminal := by
    rw [← hring]
    exact hbatch
  apply StepsE.prog_eq (p' := batchProver4 (Pure.pure ∘ H) (late.getD 1 0)
    (commitments.filterMap fun c ↦ (combine a.relations c (late.getD 0 0)).map (c, ·))
    (layoutsK tr.shape a.c2Columns) (stacksOf (c1Stack tr) c2.stack (setupStackOf tr)) (some map) >>=
      fun cm ↦ (get : WrM Id Wr) >>= fun c ↦ Pure.pure ⟨c.stream, (c1Stack tr,
        commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)), (c2.stack, committed2), setupStackOf tr, cm,
        commitments.filterMap fun c ↦ (combine a.relations c (late.getD 0 0)).map (c, ·), c2.heapVals⟩)
  case e =>
    simp only [batchProver4, bind_assoc, pure_bind]
    rfl
  apply StepsE.bind_veq (h1 := (hB w8).steps)
  case e =>
    refine batchKH4_congr H _ _ ?_ ?_
    · refine congrArg (fun rels ↦ commitments.filterMap fun c ↦ (combine rels c (late.getD 0 0)).map (c, ·)) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only [flockOut4]
      rw [atTLoop_eq tr (eqKernel alphas) (bus.getD 1 0) (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, atTFold_snd]
      rfl
    · refine congrArg (layoutsK tr.shape) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only [flockOut4]
      rw [atTLoop_eq tr (eqKernel alphas) (bus.getD 1 0) (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, atTFold_snd]
      rfl
  apply StepsE.pget
  apply StepsE.pure
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [List.nil_append, List.append_nil, List.cons_append]
  try rfl

/-! ## The run on calldata -/

/-- **π1-rec4's honest prover's run** from the seed (`proveStreamRec4With` at `pure ∘ H`, `pure ∘ W`). -/
def proverRun4 (H : List UInt8 → Digest) (W : List UInt8 → RateB) (commit : Commitment → ℕ → Array K → Id Committed)
    (tr : Trace) (iv : List UInt8) : CoreOut × Wr :=
  (proveStreamRec4With (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) commit tr).run (Wr.start (seedAt H iv tr.publicInput))

theorem runWithKH4_eq (H : List UInt8 → Digest) (W : List UInt8 → RateB) (shape : UniStatement.Shape)
    (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant) (mode : ClaimsMode) :
    runWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) shape iv publicInput stream v mode =
      ⟨((reduceWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) shape (publicWordsOf publicInput) v mode >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).1,
        ((reduceWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) shape (publicWordsOf publicInput) v mode >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).2⟩ :=
  rfl

/-- **π1-rec4's verifier on the honest prover's stream**: the run returns `R` (its openings the prover's point
claims, no matrices' claim, its roots and answers the prover's), the channel at the end of the stream, having
collected the counts' checks and two zeros. -/
theorem runWithKH4_syncs4 (H : List UInt8 → Digest) (W : List UInt8 → RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows) (hF : FlockP.FlockHolds (tr.height 5) tr.qflock)
    (terminal : Wr → E) (hbatch : BatchSyncsAt4 H W commit tr (seedAt H iv tr.publicInput) terminal) :
    ∃ R : Reduced,
      runWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) tr.shape iv tr.publicInput
          (proverRun4 H W commit tr iv).1.stream keccakRec4 .point =
        ⟨.ok R, chanAt (proverRun4 H W commit tr iv).1.stream (proverRun4 H W commit tr iv).1.stream.size
          (proverRun4 H W commit tr iv).2 (countChecks tr.rows tr.shape.heights ++
            [0, terminal (frontOf4 H W commit tr (Wr.start (seedAt H iv tr.publicInput))).2.2]).toArray⟩ ∧
      R.openings = (proverRun4 H W commit tr iv).1.claims.map pointOpening ∧ R.matrices = none ∧
      R.roots = (rootRead (proverRun4 H W commit tr iv).1.c1.2.halves,
        rootRead (proverRun4 H W commit tr iv).1.c2.2.halves) ∧
      R.oods = (pcsOod (c1LayoutK tr.shape).vars (proverRun4 H W commit tr iv).1.c1.1
          (rootOf (proverRun4 H W commit tr iv).1.c1.2.halves),
        pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars (proverRun4 H W commit tr iv).1.c2.1
          (rootOf (proverRun4 H W commit tr iv).1.c2.2.halves)) := by
  have hlen : tr.rows.length = tr.shape.heights.length := by rw [hfit.1, hvalid.1]
  obtain ⟨R, out, posF, wF, zs, hs, hpos, hstr, hop, hmat, hroot, hood, hzs⟩ :=
    reduce_steps4 H W commit tr _ hvalid.2 hlen (rows_lt_32 hvalid.1 hvalid.2 hfit) hF terminal hbatch
  have hP : proverRun4 H W commit tr iv = (out, wF) := hs.1
  rw [hP]
  refine ⟨R, ?_, hop, hmat, hroot, hood⟩
  dsimp only
  rw [hstr, runWithKH4_eq, walk_finish hs hpos, hzs]

/-- **π1-rec4's verifier accepts** the honest prover's stream: no error, every collected value zero. -/
theorem runWithKH4_accepts4 (H : List UInt8 → Digest) (W : List UInt8 → RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows) (hF : FlockP.FlockHolds (tr.height 5) tr.qflock)
    (hbatch : BatchHoldsAt4 H W commit tr (seedAt H iv tr.publicInput)) :
    (runWithKH4 (m := Id) (Pure.pure ∘ H) (Pure.pure ∘ W) tr.shape iv tr.publicInput
      (proverRun4 H W commit tr iv).1.stream keccakRec4 .point).accepts = true := by
  obtain ⟨R, hrun, -⟩ := runWithKH4_syncs4 H W commit tr iv hvalid hfit hF _
    (batchSyncsAt4_of_holds H W commit tr _ hbatch)
  rw [hrun]
  simp only [Outcome.accepts, chanAt, Bool.true_and, Array.all_eq_true', beq_iff_eq]
  intro z hz
  rw [List.mem_toArray, List.mem_append, List.mem_cons, List.mem_singleton] at hz
  rcases hz with hz | rfl | rfl
  · exact countChecks_zero _ _ (rowsFit_zip hvalid.1 hvalid.2 hfit) z hz
  · rfl
  · rfl

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.reduce_steps4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.reduce_steps4

/-- info: 'UniKeccakComplete.Rec4.runWithKH4_accepts4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.runWithKH4_accepts4
