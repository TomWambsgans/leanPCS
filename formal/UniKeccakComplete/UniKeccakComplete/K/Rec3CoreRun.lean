-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The port of `ProverRun.lean` (`StreamFacts`,
-- `streamRun_facts`, `proveWith_eq_some`, `proveWith_eq_none`), `CoreRun.lean` (`StreamValues`, `streamValues`) and
-- `Core.lean` (`fails_only_at_opening`, `coreFailsOnlyAtPow`) to π1-rec3's prover (`Rec3Prover.lean`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Rec3CoreRun.lean`.
import UniKeccakComplete.K.Rec3Hyp
import UniKeccakComplete.K.CoreRun
import UniKeccakComplete.K.Mapping

/-!
# π1-rec3's honest prover's run at a pure hash (`proveRec3With` in `Id`)

`proveRec3With` (`Rec3Prover.lean`) at `m = Id`, a pure Keccak-256 `H` and permutation `F`, cut into the main line's
pieces (`ProverRun.lean`):

* **the pieces**: the setup's tree `setupTreeOf`, the Keccak contract's IV at `keccakRec3`, the seed `proverSeed3`, the
  stream's run `streamRun3` (`(proveStreamRec3With …).run (Wr.start seed)`), then the **three** openings, each the
  main line's `ProverRun.claimProof` (one commitment's claim found by `find?`, opened by `ProverRun.openingFor` on its
  stack, tree and layout word: π1-rec3's `openOne` is the main line's, by `rfl`);
* **`proveRec3With_eq`**: `proveRec3With` is those three, bound in `Option`; **`proveRec3With_eq_some`**: it returns `some π` exactly when each returns `some`, `π` the stream and
  those proofs (the form `Core.accepts_of_trace` reads `proveWith_eq_some` in); **`proveRec3With_eq_none`**: if it
  returns `none`, a commitment has no claim or one of the three `proveOpeningWithH` calls returned `none`;
* **the paired batch's point** (`batchRounds3_point`): a pair round appends `pairPoint z`'s two coordinates
  (`pairRound3_point`), the last plain round (with `vars` odd) one (`plainRound3_point`): `vars` coordinates in all;
* **the stream's facts** (`streamRun3_facts`, a `StreamFacts3`): every commitment has a claim (`claims_fst`, by the
  main line's `ProverRun.combined_fst` and `ProverRun.atTOf_cover`: `atTOf` and `combine` are shared code), `C1`'s
  and the setup's stacks and `C2`'s tree are the committed ones, every claim's point has its stack's variables (at
  most the batch's, under `ProverRun.C2ColumnsHonest tr`); the Keccak prover makes no matrices' claim;
* **the claims' values** (`streamValues3`, a `StreamValues3`): every claim's value is its stack's multilinear
  extension at its point (`stackEval`, what WHIR's honest opening needs), and `C2`'s stack is `c2DataOf`'s at some
  challenges (`c2stack`);
* **`coreFailsOnlyAtPow3`**: `CoreFailsOnlyAtPow3 D flock` (`Rec3Hyp.lean`), for every Flock prover: if the prover
  returns `none`, one of its three WHIR openings did (`fails_only_at_opening3`; every commitment has a claim).

Proved, as the main line's, by peeling the `StateT` program's binds one at a time (`ProverRun.peel`, …), each bound
value a variable: no term grows.

Decisions (recorded):
* The main line's `claimProof` / `openingFor` are reused as the three openings (not copied): π1-rec3's `openOne` at a
  given commitment is `openingFor`'s case, by `rfl`, so `Core.accepts_of_trace`'s use of `claimProof_eq_some` carries
  over unchanged.
* `StreamFacts3` is the main line's `ProverRun.StreamFacts` (the Keccak `CoreOut` has no matrices' claim).
* `coreFailsOnlyAtPow3` does not use the bad events (`¬ BadFp`, `¬ BadT`), nor the witness's honesty.
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Rec3

open UniComplete

open ProverRun

/-! ## The paired batch's point -/

theorem foldAt_point (st : BatchState) (x : E) : (foldAt st x).point = st.point ++ [x] := rfl

/-- **A pair round appends two coordinates** (`pairPoint z`'s). -/
theorem pairRound3_point (H : List UInt8 → Id Digest) (lambda : E) (nq : ℕ) (st : BatchState) (w : Wr) :
    ((pairRound3 (m := Id) H lambda nq st).run w).1.point.length = st.point.length + 2 := by
  unfold pairRound3
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure, foldAt_point, List.length_append,
    List.length_singleton]

/-- **The last plain round appends one coordinate.** -/
theorem plainRound3_point (H : List UInt8 → Id Digest) (lambda : E) (nh : ℕ) (st : BatchState) (w : Wr) :
    ((plainRound3 (m := Id) H lambda nh st).run w).1.point.length = st.point.length + 1 := by
  unfold plainRound3
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure, foldAt_point, List.length_append,
    List.length_singleton]

theorem forIn_pairRound3_point (H : List UInt8 → Id Digest) (lambda : E) (vars : ℕ) :
    ∀ (L : List ℕ) (st : BatchState) (w : Wr),
      (StateT.run (forIn L st fun j st ↦ do
        let st ← pairRound3 (m := Id) H lambda (2 ^ (vars - 2 * j - 2)) st
        pure (ForInStep.yield st)) w).1.point.length = st.point.length + 2 * L.length
  | [], st, w => rfl
  | j :: L, st, w => by
    rw [List.forIn_cons]
    simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
    rw [forIn_pairRound3_point H lambda vars L, pairRound3_point, List.length_cons]
    omega

/-- **The paired batch's point has `vars` coordinates**: `vars / 2` pair rounds of two, with `vars` odd a plain round
of one. -/
theorem batchRounds3_point (H : List UInt8 → Id Digest) (lambda : E) (vars : ℕ) (st : BatchState) (w : Wr) :
    ((batchRounds3 (m := Id) H lambda vars st).run w).1.length = st.point.length + vars := by
  unfold batchRounds3
  simp only [StateT.run_bind, idBind]
  split
  · rename_i hodd
    simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
    rw [plainRound3_point, forIn_pairRound3_point, List.length_range]
    omega
  · rename_i heven
    simp only [StateT.run_pure, idPure]
    rw [forIn_pairRound3_point, List.length_range]
    omega

/-! ## The stream's run -/

/-- **What the openings read off π1-rec3's stream's output** `out`: a claim on each of `C1`, `C2`, the setup, in
order; `C1`'s and the setup's stacks and `C2`'s tree the committed ones; each claim's point of its stack's variables
(at most the batch's); no matrices' claim. -/
structure StreamFacts3 (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (out : CoreOut) : Prop where
  claims_fst : out.claims.map (·.1) = [.c1, .c2, .setup]
  c1 : out.c1 = (c1Stack tr, commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr))
  c2 : out.c2.2 = commit .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars out.c2.1
  setup : out.setup = setupStackOf tr
  points : C2ColumnsHonest tr → ∀ x ∈ out.claims, x.2.1.length =
    min (layoutIn (layoutsK tr.shape (Shape.c2ColumnsK tr.shape)) x.1).vars
      (((layoutsK tr.shape (Shape.c2ColumnsK tr.shape)).map (·.2.vars)).foldl max 0)

set_option maxHeartbeats 1000000 in
/-- **π1-rec3's stream's facts**, at every hash, commitment, Flock prover, trace and writer. -/
theorem streamRun3_facts (H : List UInt8 → Id Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    StreamFacts3 commit tr ((proveStreamRec3With (m := Id) H commit flock tr).run w0).1 := by
  unfold proveStreamRec3With
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun _ s1' _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  refine peel_map fun fo s5 _ ↦ ?_
  try dsimp only
  refine peel_lift ?_
  refine peel fun _ s6 _ ↦ ?_
  refine peel fun _ s6' _ ↦ ?_
  refine peel fun t s7 _ ↦ ?_
  refine peel fun _ s8 _ ↦ ?_
  refine peel fun rho s9 _ ↦ ?_
  refine peel fun lambda s10 _ ↦ ?_
  refine peel fun r s11 hr ↦ ?_
  refine peel fun _ s12 _ ↦ ?_
  refine peel_get ?_
  refine peel_pure ?_
  have hl := congrArg (fun p ↦ p.1.length) hr
  simp only [batchRounds3_point, List.length_nil, Nat.zero_add] at hl
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · simp only [List.map_map, Function.comp_def]
    exact combined_fst _ _ (atTOf_cover _ _ _ _ _ _ _)
  · intro hC2 x hx
    unfold C2ColumnsHonest at hC2
    simp only [List.mem_map] at hx
    obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
    rw [List.length_take, ← hl, hC2]

/-- **The claims' values** in π1-rec3's stream's output `out`: each claim's value is its stack's extension at its
point; `C2`'s stack is `c2DataOf`'s at some challenges. -/
structure StreamValues3 (tr : Trace) (out : CoreOut) : Prop where
  values : ∀ x ∈ out.claims, x.2.2 = stackEval (stacksOf out.c1.1 out.c2.1 out.setup x.1) x.2.1
  c2stack : ∃ alphas beta gamma, out.c2.1 = (c2DataOf tr (eqKernel alphas) beta gamma).stack

set_option maxHeartbeats 1000000 in
/-- **π1-rec3's claims' values**, at every hash, commitment, Flock prover, trace and writer. -/
theorem streamValues3 (H : List UInt8 → Id Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    StreamValues3 tr ((proveStreamRec3With (m := Id) H commit flock tr).run w0).1 := by
  unfold proveStreamRec3With
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun _ s1' _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  refine peel_map fun fo s5 _ ↦ ?_
  try dsimp only
  refine peel_lift ?_
  refine peel fun _ s6 _ ↦ ?_
  refine peel fun _ s6' _ ↦ ?_
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

/-- **Every commitment has a claim** in π1-rec3's stream's output, for every trace and challenge. -/
theorem claims_complete3 (H : List UInt8 → Id Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    ((proveStreamRec3With (m := Id) H commit flock tr).run w0).1.claims.map (·.1) = [.c1, .c2, .setup] :=
  (streamRun3_facts H commit flock tr w0).claims_fst

/-! ## The prover's result -/

section Pieces

variable (H : List UInt8 → Digest) (F : KeccakState → KeccakState)

/-- **π1-rec3's seed** at a pure hash: `seedOf` of the Keccak contract's IV at `keccakRec3` on the setup's root and
the deployment's `A0`, `B0` constants. -/
def proverSeed3 (programIv : List UInt8) (tr : Trace) : Digest :=
  seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape keccakRec3 programIv
    (setupRootsOf tr (setupTreeOf (m := Id) H tr))) tr.publicInput

/-- **π1-rec3's stream's run** from its seed: output and writer. -/
def streamRun3 (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) : CoreOut × Wr :=
  (proveStreamRec3With (m := Id) H (commitReal (m := Id) H) flock tr).run
    (Wr.start (proverSeed3 H programIv tr))

/-- **`proveRec3With` at `Id`**: the three claims' openings (the main line's `claimProof`), bound in `Option`. -/
theorem proveRec3With_eq (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) :
    proveRec3With (m := Id) H F fuel flock programIv tr =
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .c1).bind fun p1 ↦
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .c2).bind fun p2 ↦
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .setup).bind fun p3 ↦
      some ⟨(streamRun3 H flock programIv tr).1.stream, p1, p2, p3⟩ := by
  simp only [proveRec3With, idBind, idPure, streamRun3, proverSeed3]
  generalize (StateT.run (proveStreamRec3With (m := Id) H (commitReal (m := Id) H) flock tr)
    (Wr.start (seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape keccakRec3 programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) tr.publicInput))).1 = out
  generalize setupTreeOf (m := Id) H tr = tree
  unfold claimProof
  split <;> split <;> split <;> (try simp only [openingFor, *]) <;> rfl

/-- **`proveRec3With` returns a proof** exactly when each of `C1`, `C2`, the setup has a claim and the three openings
(`claimProof`: the stack, tree and layout of the commitment, the point claim) all return one; the proof is the
stream and those openings. -/
theorem proveRec3With_eq_some (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (π : KeccakProof) :
    proveRec3With (m := Id) H F fuel flock programIv tr = some π ↔
      ∃ p1 p2 p3,
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .c1 = some p1 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .c2 = some p2 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun3 H flock programIv tr).1
          tr.shape .setup = some p3 ∧
        π = ⟨(streamRun3 H flock programIv tr).1.stream, p1, p2, p3⟩ := by
  rw [proveRec3With_eq, Option.bind_eq_some_iff]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨p1, h1, p2, h2, p3, h3, rfl⟩
    exact ⟨p1, p2, p3, h1, h2, h3, rfl⟩
  · rintro ⟨p1, p2, p3, h1, h2, h3, rfl⟩
    exact ⟨p1, h1, p2, h2, p3, h3, rfl⟩

/-- **When `proveRec3With` fails**: a commitment has no claim, or one of the three openings returned `none` (each
named with its layout, tree, stack and point claim). -/
theorem proveRec3With_eq_none (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (h : proveRec3With (m := Id) H F fuel flock programIv tr = none) :
    let tree := setupTreeOf (m := Id) H tr
    let out := (streamRun3 H flock programIv tr).1
    let words := tr.shape
    (∃ c ∈ [Commitment.c1, .c2, .setup], out.claims.find? (·.1 == c) = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c1) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c1) out.c1.2.tree out.c1.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c2) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c2) out.c2.2.tree out.c2.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .setup) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .setup) tree out.setup pt v = none) := by
  intro tree out words
  rw [proveRec3With_eq] at h
  change ((claimProof H F fuel tree out words .c1).bind fun p1 ↦ (claimProof H F fuel tree out words .c2).bind
    fun p2 ↦ (claimProof H F fuel tree out words .setup).bind fun p3 ↦
    some (⟨out.stream, p1, p2, p3⟩ : KeccakProof)) = none at h
  rcases h1 : claimProof H F fuel tree out words .c1 with _ | p1
  · rcases (claimProof_eq_none H F fuel tree out words .c1).mp h1 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.c1, by simp, h⟩
    · exact Or.inr (Or.inl ⟨c', pt, v, hf, ho⟩)
  rcases h2 : claimProof H F fuel tree out words .c2 with _ | p2
  · rcases (claimProof_eq_none H F fuel tree out words .c2).mp h2 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.c2, by simp, h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨c', pt, v, hf, ho⟩))
  rcases h3 : claimProof H F fuel tree out words .setup with _ | p3
  · rcases (claimProof_eq_none H F fuel tree out words .setup).mp h3 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.setup, by simp, h⟩
    · exact Or.inr (Or.inr (Or.inr ⟨c', pt, v, hf, ho⟩))
  rw [h1, h2, h3] at h
  exact absurd h (by simp)

end Pieces

/-! ## The prover fails only at an opening -/

/-- **`proveRec3With` fails only at an opening**: if it returns `none`, one of the three WHIR openings returned
`none` (every commitment has a claim, `claims_fst`). -/
theorem fails_only_at_opening3 (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) (hon : TraceHonest tr)
    (hnone : proveRec3With (m := Id) H F fuel flock programIv tr = none) :
    ∃ (n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E), pt.length = n ∧
      pcsProveH (m := Id) H F fuel n tree stack pt v = none := by
  have hf : StreamFacts3 (commitReal (m := Id) H) tr (streamRun3 H flock programIv tr).1 :=
    streamRun3_facts H (commitReal (m := Id) H) _ tr _
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  have hlen : ∀ {c c' : Commitment} {pt : List E} {v : E},
      (streamRun3 H flock programIv tr).1.claims.find? (·.1 == c) = some (c', pt, v) →
        pt.length = stackVarsK tr.shape c := by
    intro c c' pt v hfind
    have hc : c' = c := by simpa using List.find?_some hfind
    subst hc
    rw [hf.points hC2 _ (List.mem_of_find?_eq_some hfind)]
    exact min_layoutIn_eq _ _
  rcases proveRec3With_eq_none H F _ _ _ _ hnone with hmiss | ⟨_, pt, v, hfd, h⟩ | ⟨_, pt, v, hfd, h⟩ |
      ⟨_, pt, v, hfd, h⟩
  · exfalso
    obtain ⟨c, hc, hn⟩ := hmiss
    have hc' : c ∈ (streamRun3 H flock programIv tr).1.claims.map (·.1) := by
      rw [hf.claims_fst]; exact hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    exact absurd (by simp : (x.1 == x.1) = true) (List.find?_eq_none.mp hn x hx)
  all_goals exact ⟨_, _, _, pt, v, hlen hfd, h⟩

/-- **π1-rec3's honest prover fails only at an opening** (`CoreFailsOnlyAtPow3`), every shape and every Flock
prover; the bad events are not used. -/
theorem coreFailsOnlyAtPow3 (D : KDeployment) (flock : FlockProverH) : CoreFailsOnlyAtPow3 D flock :=
  fun input rows q hfit hrel H F _ _ hnone ↦ fails_only_at_opening3 H F _ _ _ _
    (Mapping.honestTrace_honest D input rows q hfit hrel) hnone

end UniKeccakComplete.Rec3

/-- info: 'UniKeccakComplete.Rec3.batchRounds3_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.batchRounds3_point

/-- info: 'UniKeccakComplete.Rec3.streamRun3_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.streamRun3_facts

/-- info: 'UniKeccakComplete.Rec3.streamValues3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.streamValues3

/-- info: 'UniKeccakComplete.Rec3.claims_complete3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.claims_complete3

/-- info: 'UniKeccakComplete.Rec3.proveRec3With_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.proveRec3With_eq_some

/-- info: 'UniKeccakComplete.Rec3.proveRec3With_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.proveRec3With_eq_none

/-- info: 'UniKeccakComplete.Rec3.coreFailsOnlyAtPow3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.coreFailsOnlyAtPow3
