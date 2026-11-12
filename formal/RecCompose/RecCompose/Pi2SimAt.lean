-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's honest prover (`RecCompose.Pi2Prover`,
-- `crates/leanvm/rec/src/pi2/prover.rs`) cut at its challenges, as `Pi2ProbStaged` stages it; leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the run at pure
-- functions (`runAt`, `totalImpl`).
import RecCompose.Pi2SimMorph

/-!
# π2's staged run at pure functions

* **`stream_split`**: π2's prover's stream (`pi2ProveStreamWith`) is `pre2`, the three chained challenges, `mid2`,
  `t`, `post2`, in any lawful monad (`UniKeccakComplete.Prob.run_sampleW`; after a challenge the next one's input is the
  answer's `32` bytes, `tInput_absorbW`).
* **`tInput_pre2_length`**: on values matching the reads, `α`'s input has `32 + (public data) + 32 + 24` bytes (the
  state, the public data, `W`'s root word and out-of-domain answer); at the real circuit (π2v4: frame reads only, no
  public data in the stream) `88`, so `pi2Staged`'s `fixLen 88` keeps it (`fixLen_aAt`).
* **`runAt_staged`**, **`cAt_fst`**, **`stagedAt_good`**: at pure `(Ht, Ft)` the staged run is `stagedAt` at π1's
  prover's result; its verdict's first component is π1-rec4's graph's verdict, and on an honest witness (`Pi2Good`) the
  whole verdict is the experiment's (`expW2` at `Id`), its priors and challenges (`α, β, γ`, `t`, `ρ`) the honest
  prover's (`outOf`'s inputs).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (runAt)
open UniComplete (Wr WrM)
open Pi2S Pi2K Pi2P Pi2E Pi2G

/-! ## The stream, cut -/

theorem tInput_absorbW (w : Wr) (s : Digest) : UniKeccakComplete.Prob.tInput (absorbW w s) = digestBytes s := by
  simp [UniKeccakComplete.Prob.tInput, absorbW]

section Split

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

theorem run_sampleW' (w : Wr) :
    (UniComplete.sampleW H).run w = H (UniKeccakComplete.Prob.tInput w) >>= fun s ↦ pure (chalP s, absorbW w s) :=
  UniKeccakComplete.Prob.run_sampleW H w

/-- **The prover's stream, cut at its challenges.** -/
theorem stream_split (G : RecPiop.Circuit E) (S : CoreSpec E) (oodPt : ℕ → Digest → m (List E))
    (reads : List Read) (setupStack : Array K) (input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (w0 : Wr) :
    (pi2ProveStreamWith H G S oodPt reads setupStack input values w).run w0 =
      (pre2 H G oodPt reads values w).run w0 >>= fun p ↦
      H (UniKeccakComplete.Prob.tInput p.2) >>= fun s₁ ↦ H (digestBytes s₁) >>= fun s₂ ↦ H (digestBytes s₂) >>= fun s₃ ↦
      (mid2 H G S oodPt (publicScalarsOf input values) w (chalP s₁) (chalP s₂) (chalP s₃)).run
        (absorbW (absorbW (absorbW p.2 s₁) s₂) s₃) >>= fun q ↦
      H (UniKeccakComplete.Prob.tInput q.2) >>= fun st ↦
      (post2 H G setupStack input values w p.1.1 p.1.2.1 q.1.1 q.1.2.1 (chalP s₁) (chalP s₂) (chalP s₃)
        (chalP st) p.1.2.2 q.1.2.2).run (absorbW q.2 st) := by
  simp only [pi2ProveStreamWith, pre2, mid2, post2, StateT.run_bind, StateT.run_pure, StateT.run_lift,
    run_sampleW', bind_assoc, pure_bind, tInput_absorbW]

end Split

/-! ## `α`'s input -/

theorem tInput_start_append (seed : Digest) (B : List UInt8) :
    UniKeccakComplete.Prob.tInput ((Wr.start seed).append B) = digestBytes seed ++ B := by
  simp [UniKeccakComplete.Prob.tInput, Wr.start, UniComplete.Wr.append]

/-- **`pre2`'s writer**: the start's, the public data, `W`'s root word and its out-of-domain answer appended. -/
theorem pre2_writer (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → Id (List E)) (reads : List Read)
    (values : List PublicValue) (w : ℕ → K)
    (Hk : List UInt8 → Digest) (w0 : Wr) : ∃ (h : E × E) (o : E),
    (Id.run ((pre2 (m := Id) (Pure.pure ∘ Hk) G oodPt reads values w).run w0)).2 =
      w0.append (publicWire (reads.zip values) ++ UniStatement.rootWord h ++ UniComplete.scalarWire o) := by
  have hw := sendPublic_writes (reads.zip values) w0
  unfold UniKeccakComplete.Writes at hw
  refine ⟨UniStatement.rootHalves (Id.run (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (stackVars G.logN).1
    (padStack (stackVars G.logN).1 fun i ↦ (wTableB G w).getD i 0))).root,
    pi2OodAt (padStack (stackVars G.logN).1 fun i ↦ (wTableB G w).getD i 0)
      (oodPt (stackVars G.logN).1 (Id.run (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk)
        (stackVars G.logN).1 (padStack (stackVars G.logN).1 fun i ↦ (wTableB G w).getD i 0))).root), ?_⟩
  unfold pre2
  rw [UniKeccakComplete.wr_run_bind, hw, UniKeccakComplete.wr_run_bind, UniKeccakComplete.wr_run_bind,
    UniKeccakComplete.wr_run_bind]
  rw [List.append_assoc, ← UniComplete.Wr.append_append w0 (publicWire (reads.zip values)),
    ← UniComplete.Wr.append_append (w0.append (publicWire (reads.zip values)))]
  rfl

theorem tInput_pre2_length (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → Id (List E)) (reads : List Read)
    (values : List PublicValue) (w : ℕ → K)
    (Hk : List UInt8 → Digest) (seed : Digest) (frameAt : ℕ → List UInt8)
    (hm : List.Forall₂ (ReadMatch frameAt) reads values) :
    (UniKeccakComplete.Prob.tInput (Id.run ((pre2 (m := Id) (Pure.pure ∘ Hk) G oodPt reads values w).run
      (Wr.start seed))).2).length = 32 + (reads.map Read.bytes).sum + 32 + 24 := by
  obtain ⟨h, o, hw⟩ := pre2_writer G oodPt reads values w Hk (Wr.start seed)
  rw [hw, tInput_start_append]
  simp only [List.length_append, publicWire_length frameAt reads values hm, UniKeccakComplete.Prob.rootWord_length,
    E2ECompleteness.length_digestBytes, UniKeccakComplete.length_scalarWire]
  all_goals omega

/-! ## The staged run at pure functions -/

section At

variable (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment) (C : Pi2Circuits D)
  (Fa : Pi2Facts D C) (input : Vector UInt8 32)

/-- Stage A at `Id`, π1's prover's result `o`. -/
noncomputable def aAt (o : Option UniKeccak.KeccakProof) : StA :=
  Id.run (stageA (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure o) input)

/-- Stage B at `Id`. -/
def bAt (a : StA) (s₁ s₂ s₃ : Digest) : StB := Id.run (stageB (m := Id) (Pure.pure ∘ Ht) D C input a s₁ s₂ s₃)

/-- Stage C at `Id`. -/
noncomputable def cAt (b : StB) (st : Digest) : (Bool × Bool) × ((RecSetupRoots × E) × E) :=
  Id.run (stageC (m := Id) (Pure.pure ∘ Ht) Ft D C input b st)

/-- The prior of the triple, from stage A's output. -/
noncomputable def prOf (a : StA) : Pr2 := (a.roots, a.vw.2, Fa.pubOf a.roots (publicScalarsOf input.toList a.vw.1))

/-- **The staged run at `Id`**, π1's prover's result `o`. -/
noncomputable def stagedAt (o : Option UniKeccak.KeccakProof) : Z2 :=
  let a := aAt Ht Ft D C Fa input o
  let s₁ := Ht (fixLen 88 (UniKeccakComplete.Prob.tInput a.wr))
  let s₂ := Ht (digestBytes s₁)
  let s₃ := Ht (digestBytes s₂)
  let b := bAt Ht D C input a s₁ s₂ s₃
  let st := Ht (UniKeccakComplete.Prob.tInput b.wr)
  let c := cAt Ht Ft D C input b st
  ((c.1, ((prOf D C Fa input b.a, b.α, b.β, b.γ), chalP st), c.2), (prOf D C Fa input a, chalP s₁, chalP s₂, chalP s₃))

/-- **The staged run at pure `(Ht, Ft)`** is `stagedAt` at π1's prover's result. -/
theorem runAt_staged (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) :
    runAt Ht Ft (pi2Staged D C Fa P1k input).run = stagedAt Ht Ft D C Fa input (runAt Ht Ft P1k) := by
  unfold runAt
  simp only [Pi2Staged.run, staged3, Pi2Staged.tail, pi2Staged, simulateQ_bind, simulateQ_pure, simulateQ_queryH,
    sim_stageA, sim_stageB, sim_stageC]
  rfl

/-- **π1's prover returning none**: the verdict `(false, false)`. -/
theorem cAt_none (s₁ s₂ s₃ st : Digest) :
    (cAt Ht Ft D C input (bAt Ht D C input (aAt Ht Ft D C Fa input none) s₁ s₂ s₃) st).1 = (false, false) := rfl

/-- **Stage C's first component is π1-rec4's graph's verdict.** -/
theorem cAt_fst (b : StB) (st : Digest) (p1 : UniKeccak.KeccakProof) (hp : b.a.p1 = some p1) :
    (cAt Ht Ft D C input b st).1.1 = b.a.a1 := by
  have h : Holds (stageC (m := Id) (Pure.pure ∘ Ht) Ft D C input b st) fun z ↦ z.1.1 = b.a.a1 := by
    unfold stageC
    rw [hp]
    refine holds_bind (holds_true _) fun x _ ↦ ?_
    rcases x with ⟨out, w⟩
    exact holds_bind (holds_restC _ _ D C input b p1 out) fun v hv ↦ holds_pure hv
  have h' := holds_id h
  exact h'

/-! ### π1's prover returning a proof -/

variable (p1 : UniKeccak.KeccakProof)

/-- The seed at the setup's roots (the frame words of the witness's values last). -/
noncomputable abbrev seedAt : Digest :=
  Ht (RecStatement.name ++ ivOf D Ht (rootsH D Ht Ft) ++ input.toList ++ frameWordsOf (vwH D C Fa Ht Ft input p1).1)

/-- `pre2`'s run at `Id`. -/
noncomputable abbrev preAt : (Array K × LeanVM.Prover.Tree × List E) × Wr :=
  Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) (C.G (rootsH D Ht Ft)) (WhirBridge.Pcs.oodPointM (Pure.pure ∘ Ht))
    (D.circuitAt (rootsH D Ht Ft).pi1).circuit.reads (vwH D C Fa Ht Ft input p1).1 (vwH D C Fa Ht Ft input p1).2).run
    (Wr.start (seedAt Ht Ft D C Fa input p1)))

theorem aAt_p1 : (aAt Ht Ft D C Fa input (some p1)).p1 = some p1 := rfl
theorem aAt_a1 : (aAt Ht Ft D C Fa input (some p1)).a1 =
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) := rfl
theorem aAt_roots : (aAt Ht Ft D C Fa input (some p1)).roots = rootsH D Ht Ft := rfl
theorem aAt_vw : (aAt Ht Ft D C Fa input (some p1)).vw = vwH D C Fa Ht Ft input p1 := rfl
theorem aAt_wr : (aAt Ht Ft D C Fa input (some p1)).wr = (preAt Ht Ft D C Fa input p1).2 := rfl

/-- **On an honest witness `α`'s input has `88` bytes** (at the real deployment): `fixLen` keeps it. -/
theorem fixLen_aAt (hD : D.Real)
    (hgood : Pi2Good D C.G Fa.pubOf (rootsH D Ht Ft) input p1.stream (claimsH D Ht Ft input p1)
      (vwH D C Fa Ht Ft input p1)) :
    fixLen 88 (UniKeccakComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr) =
      UniKeccakComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr := by
  unfold fixLen
  split_ifs with h
  · rfl
  · exfalso
    apply h
    rw [aAt_wr, tInput_pre2_length _ _ _ _ _ _ _ _ hgood.1]
    unfold RecDeployment.circuitAt
    rw [hD.1 _]
    decide

/-- The honest prover's output at the setup's roots (`outOf`). -/
noncomputable abbrev outAt : Pi2Out :=
  outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) (pi2Z Ht) input (vwH D C Fa Ht Ft input p1).1
    (vwH D C Fa Ht Ft input p1).2

/-- The staged run's chained answers and stage B, on π1's proof `p1` (`fixLen` dropped). -/
noncomputable abbrev s1At : Digest := Ht (UniKeccakComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr)
noncomputable abbrev s2At : Digest := Ht (digestBytes (s1At Ht Ft D C Fa input p1))
noncomputable abbrev s3At : Digest := Ht (digestBytes (s2At Ht Ft D C Fa input p1))
noncomputable abbrev bAtP : StB := bAt Ht D C input (aAt Ht Ft D C Fa input (some p1)) (s1At Ht Ft D C Fa input p1)
  (s2At Ht Ft D C Fa input p1) (s3At Ht Ft D C Fa input p1)
noncomputable abbrev stAt : Digest := Ht (UniKeccakComplete.Prob.tInput (bAtP Ht Ft D C Fa input p1).wr)

/-- `post2`'s run in stage C, on π1's proof `p1`. -/
noncomputable abbrev post2At : Pi2Out × Wr :=
  Id.run ((post2 (m := Id) (Pure.pure ∘ Ht) (C.G (bAtP Ht Ft D C Fa input p1).a.roots)
      (D.circuitAt (bAtP Ht Ft D C Fa input p1).a.roots.pi1).setupStack input.toList
      (bAtP Ht Ft D C Fa input p1).a.vw.1 (bAtP Ht Ft D C Fa input p1).a.vw.2 (bAtP Ht Ft D C Fa input p1).a.wS
      (bAtP Ht Ft D C Fa input p1).a.wT (bAtP Ht Ft D C Fa input p1).qS (bAtP Ht Ft D C Fa input p1).qT
      (bAtP Ht Ft D C Fa input p1).α (bAtP Ht Ft D C Fa input p1).β (bAtP Ht Ft D C Fa input p1).γ
      (chalP (stAt Ht Ft D C Fa input p1)) (bAtP Ht Ft D C Fa input p1).a.wP (bAtP Ht Ft D C Fa input p1).qP).run
      (absorbW (bAtP Ht Ft D C Fa input p1).wr (stAt Ht Ft D C Fa input p1)))

/-- **The staged run's `post2` is the honest prover's output.** -/
theorem post2_eq_outAt : (post2At Ht Ft D C Fa input p1).1 = outAt Ht Ft D C Fa input p1 := by
  unfold post2At outAt outOf proverOut
  rw [← oodPointM_id_eq, stream_split]
  rfl

theorem idRun_pair {α β : Type} (a : α) (b : β) : Id.run ((a, b) : Id (α × β)) = (a, b) := rfl

theorem bAtP_p1 : (bAtP Ht Ft D C Fa input p1).a.p1 = some p1 := rfl

/-- **Stage C on π1's proof `p1`**: `post2`'s output, then `restC` on it. -/
theorem cAt_eq :
    cAt Ht Ft D C input (bAtP Ht Ft D C Fa input p1) (stAt Ht Ft D C Fa input p1) =
      (Id.run (restC (m := Id) (Pure.pure ∘ Ht) Ft D C input (bAtP Ht Ft D C Fa input p1) p1
          (post2At Ht Ft D C Fa input p1).1),
        (((bAtP Ht Ft D C Fa input p1).a.roots, chalP (stAt Ht Ft D C Fa input p1)),
          (post2At Ht Ft D C Fa input p1).1.inputs.ρ)) := rfl

/-- **Stage C on the honest witness is the experiment's verdict.** -/
theorem cAt_good :
    (cAt Ht Ft D C input (bAtP Ht Ft D C Fa input p1) (stAt Ht Ft D C Fa input p1)).1 =
      Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) := by
  rw [expW2_some, pi2ProverWith_run]
  simp only
  rw [pi2ProveWith_run]
  simp only
  rw [cAt_eq, post2_eq_outAt]
  unfold restC
  have e1 : (bAtP Ht Ft D C Fa input p1).a.roots = (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots :=
    rfl
  have e2 : (bAtP Ht Ft D C Fa input p1).a.setupTree = (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).pi2 :=
    rfl
  have e3 : (bAtP Ht Ft D C Fa input p1).a.trees = Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D) := rfl
  have e4 : (bAtP Ht Ft D C Fa input p1).a.claims =
      pi1ClaimsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1.stream := rfl
  have e5 : (bAtP Ht Ft D C Fa input p1).a.a1 = Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1) := rfl
  simp only [e1, e2, e3, e4, e5]
  simp only [Id.run_bind]
  generalize PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel _ _ _ _ _
    ((Spec.of _).core.run _).fold = rW
  generalize PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel _ _ _ _ _
    (outAt Ht Ft D C Fa input p1).inputs.ξ = rS
  generalize PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel _ _ _ _ _
    ((Spec.of _).core.run _).quotientValue = rQ1
  generalize PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel _ _ _ _ _
    ((Spec.of _).core.run _).pushesValue = rQ2
  rcases rW with _ | x <;> rcases rS with _ | y <;> rcases rQ1 with _ | z1 <;> rcases rQ2 with _ | z2 <;> rfl

/-- **The staged run on π1's proof `p1` with an honest witness**: its verdict the experiment's, its priors and challenges
(`α, β, γ`, `t`, `ρ`) the honest prover's. -/
theorem stagedAt_good (hD : D.Real)
    (hgood : Pi2Good D C.G Fa.pubOf (rootsH D Ht Ft) input p1.stream (claimsH D Ht Ft input p1)
      (vwH D C Fa Ht Ft input p1)) :
    (stagedAt Ht Ft D C Fa input (some p1)).1.1 =
        Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) ∧
    (stagedAt Ht Ft D C Fa input (some p1)).2 =
      (((rootsH D Ht Ft), (vwH D C Fa Ht Ft input p1).2,
          Fa.pubOf (rootsH D Ht Ft) (publicScalarsOf input.toList (vwH D C Fa Ht Ft input p1).1)),
        (outAt Ht Ft D C Fa input p1).inputs.α, (outAt Ht Ft D C Fa input p1).inputs.β,
        (outAt Ht Ft D C Fa input p1).inputs.γ) ∧
    (stagedAt Ht Ft D C Fa input (some p1)).1.2.1.2 = (outAt Ht Ft D C Fa input p1).inputs.t ∧
    (stagedAt Ht Ft D C Fa input (some p1)).1.2.1.1 = (stagedAt Ht Ft D C Fa input (some p1)).2 ∧
    (stagedAt Ht Ft D C Fa input (some p1)).1.2.2 =
      ((rootsH D Ht Ft, (outAt Ht Ft D C Fa input p1).inputs.t), (outAt Ht Ft D C Fa input p1).inputs.ρ) := by
  have hl := fixLen_aAt Ht Ft D C Fa input p1 hD hgood
  have hout := post2_eq_outAt Ht Ft D C Fa input p1
  unfold stagedAt
  simp only [hl]
  refine ⟨cAt_good Ht Ft D C Fa input p1, ?_, ?_, rfl, ?_⟩
  · rw [← hout]
    rfl
  · rw [← hout]
    rfl
  · rw [cAt_eq, ← hout]
    rfl

end At

end RecCompose.Pi2Sim
