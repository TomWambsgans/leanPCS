-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's honest prover's run at a pure hash and rate:
-- `Rec3CoreRun.lean`'s `streamRun3_facts`, `streamValues3`, `proveRec3With_eq_some`, `proveRec3With_eq_none`,
-- `fails_only_at_opening3`, `coreFailsOnlyAtPow3` for `Rec4Prover.lean`'s `proveRec4With`.
import UniKeccakComplete.K.Rec3CoreRun
import UniKeccakComplete.K.Rec4Grind

/-!
# π1-rec4's honest prover's run at a pure Keccak-256 and rate (`proveRec4With` in `Id`)

* **the stream's facts** (`streamRun4_facts`: π1-rec3's `StreamFacts3`) and **the claims' values**
  (`streamValues4`: `StreamValues3`), for every hash, rate, commitment, trace and writer: π1-rec4's stream ends as
  π1-rec3's (the same combined claims' code, the same paired batch), only its draws differ;
* **`proveRec4With_eq_some`**, **`proveRec4With_eq_none`**: the three openings, the main line's `claimProof`;
* **`coreFailsOnlyAtPow4`**: `CoreFailsOnlyAtPow4 D` (`Rec4Grind.lean`): if the prover returns `none`, one of its
  three WHIR openings did. The bad events are not used.

Proved, as π1-rec3's, by peeling the `StateT` program's binds one at a time (`ProverRun.peel`).
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

open ProverRun

/-! ## The stream's run -/

set_option maxHeartbeats 1000000 in
/-- **π1-rec4's stream's facts**, at every hash, rate, commitment, trace and writer. -/
theorem streamRun4_facts (H : List UInt8 → Id Digest) (W : List UInt8 → Id RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (w0 : Wr) :
    StreamFacts3 commit tr ((proveStreamRec4With (m := Id) H W commit tr).run w0).1 := by
  unfold proveStreamRec4With midB4 tailT4
  simp only [bind_assoc, pure_bind]
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun _ s1' _ ↦ ?_
  refine peel fun bus s2 _ ↦ ?_
  refine peel fun fl s3 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s4 _ ↦ ?_
  refine peel fun _ s4' _ ↦ ?_
  refine peel fun pointDraw s5 _ ↦ ?_
  refine peel fun _ s6 _ ↦ ?_
  refine peel fun late s7 _ ↦ ?_
  refine peel fun r s8 hr ↦ ?_
  refine peel fun _ s9 _ ↦ ?_
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

set_option maxHeartbeats 1000000 in
/-- **π1-rec4's claims' values**, at every hash, rate, commitment, trace and writer. -/
theorem streamValues4 (H : List UInt8 → Id Digest) (W : List UInt8 → Id RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (w0 : Wr) :
    StreamValues3 tr ((proveStreamRec4With (m := Id) H W commit tr).run w0).1 := by
  unfold proveStreamRec4With midB4 tailT4
  simp only [bind_assoc, pure_bind]
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun _ s1' _ ↦ ?_
  refine peel fun bus s2 _ ↦ ?_
  refine peel fun fl s3 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s4 _ ↦ ?_
  refine peel fun _ s4' _ ↦ ?_
  refine peel fun pointDraw s5 _ ↦ ?_
  refine peel fun _ s6 _ ↦ ?_
  refine peel fun late s7 _ ↦ ?_
  refine peel fun r s8 _ ↦ ?_
  refine peel fun _ s9 _ ↦ ?_
  refine peel_get ?_
  refine peel_pure ?_
  refine ⟨?_, ⟨_, _, _, rfl⟩⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
  cases c <;> rfl

/-! ## The prover's result -/

section Pieces

variable (H : List UInt8 → Digest) (W : List UInt8 → RateB) (F : KeccakState → KeccakState)

/-- **π1-rec4's seed** at a pure hash: `seedOf` of the Keccak contract's IV at `keccakRec4`. -/
def proverSeed4 (programIv : List UInt8) (tr : Trace) : Digest :=
  seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape keccakRec4 programIv
    (setupRootsOf tr (setupTreeOf (m := Id) H tr))) tr.publicInput

/-- **π1-rec4's stream's run** from its seed: output and writer. -/
def streamRun4 (programIv : List UInt8) (tr : Trace) : CoreOut × Wr :=
  (proveStreamRec4With (m := Id) H W (commitReal (m := Id) H) tr).run (Wr.start (proverSeed4 H programIv tr))

/-- **The three openings at `Id`** (`openingsTail3`), bound in `Option` (the main line's `claimProof`). -/
theorem openingsTail3_eq (fuel : ℕ) (tr : Trace) (tree : LeanVM.Prover.Tree) (out : CoreOut) :
    openingsTail3 (m := Id) H F fuel tr tree out =
      (claimProof H F fuel tree out tr.shape .c1).bind fun p1 ↦
      (claimProof H F fuel tree out tr.shape .c2).bind fun p2 ↦
      (claimProof H F fuel tree out tr.shape .setup).bind fun p3 ↦
      some ⟨out.stream, p1, p2, p3⟩ := by
  unfold openingsTail3 claimProof
  split <;> split <;> split <;> (try simp only [openingFor, *]) <;> rfl

/-- **`proveRec4With` at `Id`**: the three claims' openings on its stream's output. -/
theorem proveRec4With_eq (fuel : ℕ) (programIv : List UInt8) (tr : Trace) :
    proveRec4With (m := Id) H W F fuel programIv tr =
      openingsTail3 (m := Id) H F fuel tr (setupTreeOf (m := Id) H tr) (streamRun4 H W programIv tr).1 := by
  simp only [proveRec4With, idBind, streamRun4, proverSeed4]

/-- **`proveRec4With` returns a proof** exactly when each of the three openings returns one. -/
theorem proveRec4With_eq_some (fuel : ℕ) (programIv : List UInt8) (tr : Trace) (π : KeccakProof) :
    proveRec4With (m := Id) H W F fuel programIv tr = some π ↔
      ∃ p1 p2 p3,
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun4 H W programIv tr).1 tr.shape .c1 = some p1 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun4 H W programIv tr).1 tr.shape .c2 = some p2 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun4 H W programIv tr).1 tr.shape .setup =
          some p3 ∧
        π = ⟨(streamRun4 H W programIv tr).1.stream, p1, p2, p3⟩ := by
  rw [proveRec4With_eq, openingsTail3_eq, Option.bind_eq_some_iff]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨p1, h1, p2, h2, p3, h3, rfl⟩
    exact ⟨p1, p2, p3, h1, h2, h3, rfl⟩
  · rintro ⟨p1, p2, p3, h1, h2, h3, rfl⟩
    exact ⟨p1, h1, p2, h2, p3, h3, rfl⟩

/-- **When `proveRec4With` fails**: a commitment has no claim, or one of the three openings returned `none`. -/
theorem proveRec4With_eq_none (fuel : ℕ) (programIv : List UInt8) (tr : Trace)
    (h : proveRec4With (m := Id) H W F fuel programIv tr = none) :
    let tree := setupTreeOf (m := Id) H tr
    let out := (streamRun4 H W programIv tr).1
    let words := tr.shape
    (∃ c ∈ [Commitment.c1, .c2, .setup], out.claims.find? (·.1 == c) = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c1) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c1) out.c1.2.tree out.c1.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c2) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c2) out.c2.2.tree out.c2.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .setup) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .setup) tree out.setup pt v = none) := by
  intro tree out words
  rw [proveRec4With_eq, openingsTail3_eq] at h
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

/-- **`proveRec4With` fails only at an opening**: if it returns `none`, one of the three WHIR openings returned
`none` (every commitment has a claim). -/
theorem fails_only_at_opening4 (H : List UInt8 → Digest) (W : List UInt8 → RateB) (F : KeccakState → KeccakState)
    (fuel : ℕ) (programIv : List UInt8) (tr : Trace) (hon : TraceHonest tr)
    (hnone : proveRec4With (m := Id) H W F fuel programIv tr = none) :
    ∃ (n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E), pt.length = n ∧
      pcsProveH (m := Id) H F fuel n tree stack pt v = none := by
  have hf : StreamFacts3 (commitReal (m := Id) H) tr (streamRun4 H W programIv tr).1 :=
    streamRun4_facts H W (commitReal (m := Id) H) tr _
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  have hlen : ∀ {c c' : Commitment} {pt : List E} {v : E},
      (streamRun4 H W programIv tr).1.claims.find? (·.1 == c) = some (c', pt, v) →
        pt.length = stackVarsK tr.shape c := by
    intro c c' pt v hfind
    have hc : c' = c := by simpa using List.find?_some hfind
    subst hc
    rw [hf.points hC2 _ (List.mem_of_find?_eq_some hfind)]
    exact min_layoutIn_eq _ _
  rcases proveRec4With_eq_none H W F _ _ _ hnone with hmiss | ⟨_, pt, v, hfd, h⟩ | ⟨_, pt, v, hfd, h⟩ |
      ⟨_, pt, v, hfd, h⟩
  · exfalso
    obtain ⟨c, hc, hn⟩ := hmiss
    have hc' : c ∈ (streamRun4 H W programIv tr).1.claims.map (·.1) := by
      rw [hf.claims_fst]; exact hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    exact absurd (by simp : (x.1 == x.1) = true) (List.find?_eq_none.mp hn x hx)
  all_goals exact ⟨_, _, _, pt, v, hlen hfd, h⟩

/-- **π1-rec4's honest prover fails only at an opening** (`CoreFailsOnlyAtPow4`), every shape; the bad events are
not used. -/
theorem coreFailsOnlyAtPow4 (D : KDeployment) : CoreFailsOnlyAtPow4 D :=
  fun input rows q hfit hrel W F _ _ hnone ↦ fails_only_at_opening4 (hOf W) W F _ _ _
    (Mapping.honestTrace_honest D input rows q hfit hrel) hnone

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.streamRun4_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.streamRun4_facts

/-- info: 'UniKeccakComplete.Rec4.streamValues4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.streamValues4

/-- info: 'UniKeccakComplete.Rec4.proveRec4With_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.proveRec4With_eq_some

/-- info: 'UniKeccakComplete.Rec4.coreFailsOnlyAtPow4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.coreFailsOnlyAtPow4
