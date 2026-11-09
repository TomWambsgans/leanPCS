-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/CoreRun.lean`.
import UniKeccakComplete.K.ProverRun
import UniKeccakComplete.K.FlockProverMain
import UniKeccakComplete.K.ProbHyp
import UniKeccakComplete.K.SyncVerifier

/-!
# The honest prover's run, read off for the verifier (Keccak VM, main line)

What the end composition (`Core.lean`) reads off the honest prover's stream (`proveStreamWith` at `Id`), beyond
`ProverRun.StreamFacts`:

* **`streamValues`** (a `StreamValues`): every point claim's value is its stack's multilinear extension at its point
  (`stackEval`, what WHIR's honest opening `pcsOpen_honest_k` needs), and `C2`'s stack is the prover's `c2DataOf`
  at some challenges. The Keccak verifier has no matrices' claim (no `A0`, `B0` openings), so nothing is said of
  Flock's matrices' point;
* **the prover's challenges are the staged ones** (`front_challenges`): at the prover's seed (`proverSeed`, the
  deployment's `A0`, `B0` constants in the IV), the state when the batching sumcheck starts (`frontOf`,
  `SyncVerifier.lean`) has the bus challenges `Prob.proverChallenges` and Flock's point and `t` of
  `Prob.proverTChallenge`, the values the bad events (`BadFp`, `BadT`) are stated at. Through `frontFrom`
  (`frontOf` from `γ` on, `frontOf_eq` by `rfl`) and the five samples from the stream's prefix (`samples_prefix`).
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Core

open UniComplete

open ProverRun

/-! ## The values of the claims -/

/-- **The claims' values** in the stream's output `out`: each point claim's value is its stack's extension at its
point; `C2`'s stack is the prover's at some challenges. -/
structure StreamValues (tr : Trace) (out : CoreOut) : Prop where
  values : ∀ x ∈ out.claims, x.2.2 = stackEval (stacksOf out.c1.1 out.c2.1 out.setup x.1) x.2.1
  c2stack : ∃ alphas beta gamma, out.c2.1 = (c2DataOf tr (eqKernel alphas) beta gamma).stack

set_option maxHeartbeats 1000000 in
theorem streamValues (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    StreamValues tr ((proveStreamWith (m := Id) H commit flock tr).run w0).1 := by
  unfold proveStreamWith
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  refine peel_map fun fo s5 _ ↦ ?_
  dsimp only
  refine peel_lift ?_
  refine peel fun _ s6 _ ↦ ?_
  refine peel fun t s7 _ ↦ ?_
  refine peel fun _ s8 _ ↦ ?_
  refine peel fun rho s9 _ ↦ ?_
  refine peel fun lambda s10 _ ↦ ?_
  refine peel fun r s11 _ ↦ ?_
  refine peel fun _ s12 _ ↦ ?_
  refine peel_get ?_
  refine peel_pure ?_
  refine ⟨?_, ⟨alphas, beta, gamma, rfl⟩⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
  cases c <;> rfl

/-! ## The prover's challenges -/

section Front

variable (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)

/-- **`frontOf` from `γ` on**: given `C1`'s commitment, the bus challenges and the writer after them. -/
def frontFrom (tr : Trace) (committed1 : Committed) (alphas : List E) (beta : E) (w4 : Wr) : FrontOut × Wr :=
  let shape := tr.shape
  let stack1 := c1Stack tr
  let gamma := (Wr.sampled H w4).1
  let w5 := (Wr.sampled H w4).2
  let logN := keccakR1csLogSize + shape.heights.getD opSha3 0
  let flockOut : Option FlockOut := some ((flock logN keccakMain tr.qflock).run w5).1
  let w6 := ((flock logN keccakMain tr.qflock).run w5).2
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((layoutsOfK shape).lookup .c2).getD default).vars c2.stack
  let w7 := w6.append (rootWord committed2.halves)
  let t := (Wr.sampled H w7).1
  let w8 := (Wr.sampled H w7).2
  let a := atTOf tr c2 alphas beta gamma t flockOut
  let w9 := w8.append (a.values.flatMap scalarWire)
  let rho := (Wr.sampled H w9).1
  let w10 := (Wr.sampled H w9).2
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layoutsK shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, flockOut, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, w10)

/-- **`frontOf` is `frontFrom`** after the stream's prefix and the five bus challenges. -/
theorem frontOf_eq (tr : Trace) (w0 : Wr) :
    frontOf H commit flock tr w0 =
      frontFrom H commit flock tr (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr))
        ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves))).1
        (Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves))).2).1
        (Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves))).2).2 := rfl

end Front

/-- A sample at a writer that has absorbed its stream hashes the state alone. -/
theorem sampled_absorbed (H : List UInt8 → Digest) (s : Array UInt8) (st : Digest) (ch : Array E) :
    Wr.sampled H ⟨s, s.size, st, ch⟩ =
      (Prob.chal (H (digestBytes st)), ⟨s, s.size, H (digestBytes st), ch.push (Prob.chal (H (digestBytes st)))⟩) := by
  simp [Wr.sampled, Prob.chal]

/-- The first sample from the stream's prefix. -/
theorem sampled_start (H : List UInt8 → Digest) (s : Array UInt8) (st : Digest) :
    Wr.sampled H ⟨s, 0, st, #[]⟩ =
      (Prob.chal (H (digestBytes st ++ (s.extract 0 s.size).toList)),
        ⟨s, s.size, H (digestBytes st ++ (s.extract 0 s.size).toList),
          #[Prob.chal (H (digestBytes st ++ (s.extract 0 s.size).toList))]⟩) := rfl

/-- **The five bus challenges from the stream's prefix**: `s₁ = H(seed ‖ prefix)`, `s_{k+1} = H(s_k)`; the writer
after them is `Prob.writerAfter`. -/
theorem samples_prefix (H : List UInt8 → Digest) (rows : List ℕ) (c1 : LeanVM.Prover.Tree) (seed : Digest)
    (s₁ s₂ s₃ s₄ s₅ : Digest)
    (h₁ : s₁ = H (digestBytes seed ++
      ((Prob.prefixStream rows c1).extract 0 (Prob.prefixStream rows c1).size).toList))
    (h₂ : s₂ = H (digestBytes s₁)) (h₃ : s₃ = H (digestBytes s₂)) (h₄ : s₄ = H (digestBytes s₃))
    (h₅ : s₅ = H (digestBytes s₄)) :
    ((samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).1 =
        [Prob.chal s₁, Prob.chal s₂, Prob.chal s₃, Prob.chal s₄] ∧
      Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2 =
        (Prob.chal s₅, Prob.writerAfter rows c1 s₁ s₂ s₃ s₄ s₅) := by
  subst h₁ h₂ h₃ h₄ h₅
  have h4 : (samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ =
      ([(Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).1,
        (Wr.sampled H (Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).1,
        (Wr.sampled H (Wr.sampled H (Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).1,
        (Wr.sampled H (Wr.sampled H (Wr.sampled H (Wr.sampled H
          ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).2).1],
        (Wr.sampled H (Wr.sampled H (Wr.sampled H (Wr.sampled H
          ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).2).2) := rfl
  rw [h4]
  refine ⟨?_, ?_⟩ <;> (simp only [sampled_start, sampled_absorbed]; try rfl)

/-- **The prover's challenges are the staged ones**: at the prover's seed, the state when the batching sumcheck
starts has the bus challenges `proverChallenges`, Flock's point and `t` of `proverTChallenge`. -/
theorem front_challenges (H : List UInt8 → Digest) (flock : FlockProver Id) (D : KDeployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (frontOf H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.alphas =
        (Prob.proverChallenges H D input rows q).1 ∧
      (frontOf H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.beta =
        (Prob.proverChallenges H D input rows q).2 ∧
      (frontOf H (commitReal (m := Id) H) flock (honestTrace D input rows q)
          (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.flockOut.map
          (·.point) = some (Prob.proverTChallenge H flock D input rows q).1 ∧
      (frontOf H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.t =
        (Prob.proverTChallenge H flock D input rows q).2 := by
  have hw2 : ((Wr.start (proverSeed H D.programIv (honestTrace D input rows q))).append
        ((honestTrace D input rows q).rows.flatMap fun n ↦ integerWire n 4)).append
      (rootWord (commitReal (m := Id) H .c1 (c1LayoutK (honestTrace D input rows q).shape).vars
        (c1Stack (honestTrace D input rows q))).halves) =
      ⟨Prob.prefixStream rows (E2ECompleteness.commitWithH (m := Id) H
          (c1LayoutK (honestTrace D input rows q).shape).vars (c1Stack (honestTrace D input rows q))), 0,
        proverSeed H D.programIv (honestTrace D input rows q), #[]⟩ := rfl
  obtain ⟨hα, hβ⟩ := samples_prefix H rows (E2ECompleteness.commitWithH (m := Id) H
      (c1LayoutK (honestTrace D input rows q).shape).vars (c1Stack (honestTrace D input rows q)))
    (proverSeed H D.programIv (honestTrace D input rows q)) _ _ _ _ _ rfl rfl rfl rfl rfl
  rw [frontOf_eq, hw2, hα, hβ]
  exact ⟨rfl, rfl, rfl, rfl⟩

end UniKeccakComplete.Core

/-- info: 'UniKeccakComplete.Core.streamValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Core.streamValues

/-- info: 'UniKeccakComplete.Core.front_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Core.front_challenges
