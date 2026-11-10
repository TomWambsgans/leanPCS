-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/ProverRun.lean`.
import UniKeccakComplete.K.Prover
import UniComplete.Whir
import UniKeccakComplete.K.Reference
import UniKeccakComplete.K.AlgHCols
import UniKeccakSound.Fs.Whir23

/-!
# The honest prover's run at a pure hash (`proveWith` in `Id`), Keccak VM

`proveWith` (Prover.lean) at `m = Id`, a pure Keccak-256 `H : List UInt8 → Digest` and permutation `F` (as
`E2ECompleteness.ProverOpening` and `Whir.lean` state their lemmas), cut into named pieces:

* **the pieces**: the setup's tree `setupTreeOf`, the IV `contractIvOf` (at `keccakMain`, the deployment's `A0`, `B0`
  constants `a0`, `b0`), the seed `proverSeed`, the stream's run `streamRun` (`(proveStreamWith …).run (Wr.start
  seed)`: output and writer), then the three openings `claimProof` (one commitment's: its claim found by `find?`,
  `openingFor` its stack, tree and layout word);
* **`proveWith_eq`**: `proveWith` is those three, bound in `Option`; **`proveWith_eq_some`**: it returns `some π`
  exactly when each returns `some`, `π` the stream and those proofs; **`proveWith_eq_none`**: if it returns `none`,
  a commitment has no claim or one of the three `proveOpeningWithH` calls (named with its layout, tree, stack and
  claim) returned `none`;
* **the stream's run** (`streamRun_facts`, a `StreamFacts`): every commitment has a claim (`claims_complete`:
  `combine` is `some` on each, as `atTOf` states a relation on each, `atTOf_cover`), `C1`'s and the setup's stacks
  and `C2`'s tree are the committed ones, every claim's point has its stack's variables (at most the batch's
  rounds, `batchRounds_point`). Proved by peeling the `StateT` program's binds one at a time (`peel`, …), each bound
  value a variable: no term grows. The Keccak verifier has no matrices' claim;
* **`prover_none_pow`**: at the reference shape (`keccakRefShape`), if `proveWith` returns `none`, one of the three
  openings reached WHIR's `17`-bit proof of work at a sponge where every nonce below `fuel` fails
  (`pcsOpen_fails_only_at_pow_k`, each opening at `27, 26, 23` variables, `reference_wordVars`; the setup's `2^23`
  words are admissible by `UniKeccakSound.admissible_k`), for an honest trace (`TraceHonest`). The trace's honesty
  gives `C2ColumnsHonest tr` (`c2ColumnsHonest_of_traceHonest`).
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.ProverRun

open UniComplete

open UniKeccakSound (keccakRefShape)

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem idPure {α : Type} (a : α) : (pure a : Id α) = a := rfl
theorem idMap {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl

/-! ### WHIR at `2^23 ..= 2^28` words -/

/-- **An honest opening fails only at its proof of work** (`pcsOpen_fails_only_at_pow`), at `2^23 ..= 2^28` words:
the setup's `2^23` admissible too (`UniKeccakSound.admissible_k`). -/
theorem pcsOpen_fails_only_at_pow_k (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    {vars : ℕ} (h1 : 23 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (claims : List PcsQuotient.Claim)
    (hlen : ∀ c ∈ claims, c.point.length = vars)
    (h : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram vars PcsQuotient.logInvRate
        (PcsQuotient.stackClaims (plainLayout vars) claims)).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n)
        (Compile.powStep F sp (Compile.nonceOf n)).1 = false :=
  E2ECompleteness.exists_failed_pow_opening H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (UniKeccakSound.admissible_k h1 h2) stack claims hlen h

/-- **WHIR's honest opening is accepted** (`pcsOpen_honest`), at `2^23 ..= 2^28` words. -/
theorem pcsOpen_honest_k (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ}
    (h1 : 23 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E)
    (hpt : pt.length = vars) {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack [⟨pt, stackEval stack pt⟩] = some π) :
    E2ECompleteness.openingWithH (m := Id) H F (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack).root [⟨pt, stackEval stack pt⟩] π = true :=
  E2ECompleteness.openingWithH_proveOpeningWithH H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (UniKeccakSound.admissible_k h1 h2) stack _ (List.cons_ne_nil _ _)
    (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hpt)
    (plain_holds (by omega) (by omega) stack hs pt hpt) (plain_multilinear vars _) hπ

variable (H : List UInt8 → Digest) (F : KeccakState → KeccakState)

/-- The prover's seed (`proveWith`'s): the Keccak contract's IV at `keccakMain` over the setup's root and the
deployment's `A0`, `B0` constants, then the public input. -/
def proverSeed (programIv : List UInt8) (tr : Trace) : Digest :=
  seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape keccakMain programIv
    (setupRootsOf tr (setupTreeOf (m := Id) H tr))) tr.publicInput

def streamRun (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) : CoreOut × Wr :=
  (proveStreamWith (m := Id) H (commitReal (m := Id) H) flock tr).run
    (Wr.start (proverSeed H programIv tr))

def openingFor (fuel : ℕ) (tree : LeanVM.Prover.Tree) (out : CoreOut) (shape : UniStatement.Shape) :
    Commitment → List E → E → Option Compile.Proof
  | .c1, pt, v => pcsProveH (m := Id) H F fuel (stackVarsK shape .c1) out.c1.2.tree out.c1.1 pt v
  | .c2, pt, v => pcsProveH (m := Id) H F fuel (stackVarsK shape .c2) out.c2.2.tree out.c2.1 pt v
  | .setup, pt, v => pcsProveH (m := Id) H F fuel (stackVarsK shape .setup) tree out.setup pt v

def claimProof (fuel : ℕ) (tree : LeanVM.Prover.Tree) (out : CoreOut) (shape : UniStatement.Shape)
    (c : Commitment) : Option Compile.Proof :=
  match out.claims.find? (·.1 == c) with
  | some (_, pt, v) => openingFor H F fuel tree out shape c pt v
  | none => none

/-- **`proveWith` at `Id`**: the three claims' openings, bound in `Option`. -/
theorem proveWith_eq (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8)
    (tr : Trace) :
    proveWith (m := Id) H F fuel flock programIv tr =
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .c1).bind fun p1 ↦
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .c2).bind fun p2 ↦
      (claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .setup).bind fun p3 ↦
      some ⟨(streamRun H flock programIv tr).1.stream, p1, p2, p3⟩ := by
  simp only [proveWith, idBind, idPure, streamRun, proverSeed]
  generalize (StateT.run (proveStreamWith (m := Id) H (commitReal (m := Id) H) flock tr)
    (Wr.start (seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape keccakMain programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) tr.publicInput))).1 = out
  generalize setupTreeOf (m := Id) H tr = tree
  unfold claimProof
  split <;> split <;> split <;> (try simp only [openingFor, *]) <;> rfl


/-! ### `combine` and the relations at `t` -/

theorem combine_isSome (relations : List Relation) (c : Commitment) (rho : E)
    (h : ∃ r ∈ relations, r.commitment = c) : (combine relations c rho).isSome := by
  obtain ⟨r, hr, hc⟩ := h
  unfold combine
  have : (relations.filter (·.commitment == c)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [hc]⟩⟩
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A `for` loop in `Id` whose every step yields keeps an invariant. -/
theorem forIn_invariant {α β : Type} (L : List α) (init : β) (F : α → β → Id (ForInStep β)) (P : β → Prop)
    (hinit : P init) (hF : ∀ a b, P b → ∃ b', F a b = pure (.yield b') ∧ P b') : P (forIn L init F) := by
  induction L generalizing init with
  | nil => exact hinit
  | cons a L ih =>
    obtain ⟨b', hb', hP⟩ := hF a init hinit
    rw [List.forIn_cons, hb']
    exact ih b' hP

theorem heapRelations_heap (shape : UniStatement.Shape) (active : List E) (parts : List TablePart)
    (weights : Array E) (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (constraintChunks : List ℕ) :
    Relation.equal .heap (w.take shape.heap.h) heapValue ∈ (heapRelations shape active parts weights beta heapValue
      constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks).1 := by
  unfold heapRelations
  simp only [Id.run, idBind, idPure]
  rw [Array.toList_push]
  apply List.mem_append_left
  refine forIn_invariant _ _ _
    (fun s : Array Relation × Array (Column × ℕ × Bool) ↦
      Relation.equal .heap (w.take shape.heap.h) heapValue ∈ s.1.toList) ?_ fun a b hb ↦ ?_
  · simp only [Array.toList_push]
    simp
  rcases a with ⟨⟨l, r, pos⟩, idx⟩
  cases l <;> exact ⟨_, rfl, by simp [hb]⟩

/-- The digits `atTOf` reads at `t`. -/
abbrev wAt (tr : Trace) (t : E) : List E := digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2)

set_option maxHeartbeats 1000000 in
/-- **`C1` has a relation at `t`**: the memory's final counts'. -/
theorem atTOf_mem_c1 (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal (.memory 3) ((wAt tr t).take tr.shape.logMemory)
      (evalB ((bCoefficients tr.shape.logMemory (tr.memory.getD 3 #[])).map ofK) tr.shape.logMemory (wAt tr t)) ∈
        (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_⟩
  · simp
  · cases end_ <;> simp

set_option maxHeartbeats 1000000 in
/-- **The setup has a relation at `t`**: the addresses'. -/
theorem atTOf_mem_setup (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal .address ((wAt tr t).take tr.shape.logMemory)
      (evalB ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).map ofK) tr.shape.logMemory
        (wAt tr t)) ∈ (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_⟩
  · simp
  · cases end_ <;> simp

set_option maxHeartbeats 1000000 in
/-- **`C2` has a relation at `t`**: the heap's value. -/
theorem atTOf_mem_c2 (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal .heap ((wAt tr t).take tr.shape.heap.h) (evalB c2.heapB tr.shape.heap.h (wAt tr t)) ∈
      (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_⟩
  · simp [heapRelations_heap]
  · cases end_ <;> simp [heapRelations_heap]

/-- **Every commitment has a relation at `t`.** -/
theorem atTOf_cover (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut)
    (c : Commitment) : ∃ r ∈ (atTOf tr c2 alphas beta gamma t fo).relations, r.commitment = c := by
  cases c
  · exact ⟨_, atTOf_mem_c1 tr c2 alphas beta gamma t fo, rfl⟩
  · exact ⟨_, atTOf_mem_c2 tr c2 alphas beta gamma t fo, rfl⟩
  · exact ⟨_, atTOf_mem_setup tr c2 alphas beta gamma t fo, rfl⟩


/-! ### The batching sumcheck's point -/

theorem batchRound_point (H : List UInt8 → Digest) (lambda : E) (j : ℕ) (st : BatchState) (w : Wr) :
    ((batchRound (m := Id) H lambda j st).run w).1.point.length = st.point.length + 1 := by
  unfold batchRound
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
  simp

theorem forIn_batchRound_point (H : List UInt8 → Digest) (lambda : E) :
    ∀ (L : List ℕ) (st : BatchState) (w : Wr),
      (StateT.run (forIn L st fun j st ↦ do
        let st ← batchRound (m := Id) H lambda j st
        pure (ForInStep.yield st)) w).1.point.length = st.point.length + L.length
  | [], st, w => rfl
  | j :: L, st, w => by
    rw [List.forIn_cons]
    simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
    rw [forIn_batchRound_point H lambda L, batchRound_point, List.length_cons]
    omega

/-- **The batching sumcheck's point has one coordinate a round.** -/
theorem batchRounds_point (H : List UInt8 → Digest) (lambda : E) (vars : ℕ) (st : BatchState) (w : Wr) :
    ((batchRounds (m := Id) H lambda vars st).run w).1.length = st.point.length + vars := by
  unfold batchRounds
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
  rw [forIn_batchRound_point, List.length_range]


/-! ### The stream's run -/

theorem combined_fst (rels : List Relation) (rho : E) (h : ∀ c, ∃ r ∈ rels, r.commitment = c) :
    (commitments.filterMap fun c ↦ (combine rels c rho).map (c, ·)).map (·.1) = [.c1, .c2, .setup] := by
  obtain ⟨x1, h1⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c1 rho (h .c1))
  obtain ⟨x2, h2⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c2 rho (h .c2))
  obtain ⟨x3, h3⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .setup rho (h .setup))
  simp [commitments, h1, h2, h3]

/-- **`C2`'s columns are the shape's**: the prover's `atTOf` lists `C2`'s columns as `Shape.c2ColumnsK` does, for
every challenge. -/
def C2ColumnsHonest (tr : Trace) : Prop :=
  ∀ c2 alphas beta gamma t fo, (atTOf tr c2 alphas beta gamma t fo).c2Columns = Shape.c2ColumnsK tr.shape

set_option maxHeartbeats 1000000 in
/-- **`C2`'s columns do not depend on Flock's output** (they are listed before its relation). -/
theorem atTOf_c2Columns_fo (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    (atTOf tr c2 alphas beta gamma t fo).c2Columns = (atTOf tr c2 alphas beta gamma t none).c2Columns := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_⟩
  · rfl
  · cases end_ <;> rfl

/-- **An honest trace's `C2` columns are the shape's**, for every challenge and Flock output. -/
theorem c2ColumnsHonest_of_traceHonest {tr : Trace} (hon : TraceHonest tr) : C2ColumnsHonest tr :=
  fun c2 alphas beta gamma t fo ↦
    (atTOf_c2Columns_fo tr c2 alphas beta gamma t fo).trans (AlgH.atTOf_c2Columns_eq hon c2 alphas beta gamma t)

/-- **What the openings read off the stream's output** `out`. -/
structure StreamFacts (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (out : CoreOut) : Prop where
  claims_fst : out.claims.map (·.1) = [.c1, .c2, .setup]
  c1 : out.c1 = (c1Stack tr, commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr))
  c2 : out.c2.2 = commit .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars out.c2.1
  setup : out.setup = setupStackOf tr
  points : C2ColumnsHonest tr → ∀ x ∈ out.claims, x.2.1.length =
    min (layoutIn (layoutsK tr.shape (Shape.c2ColumnsK tr.shape)) x.1).vars
      (((layoutsK tr.shape (Shape.c2ColumnsK tr.shape)).map (·.2.vars)).foldl max 0)

/-- At the shape's own `C2` columns, a commitment's layout has its PCS claim's variables (`stackVarsK`), at most the
batch's rounds. -/
theorem min_layoutIn_eq (s : UniStatement.Shape) (c : Commitment) :
    min (layoutIn (layoutsK s (Shape.c2ColumnsK s)) c).vars
      (((layoutsK s (Shape.c2ColumnsK s)).map (·.2.vars)).foldl max 0) = stackVarsK s c := by
  have e : layoutsK s (Shape.c2ColumnsK s) = layoutsOfK s := rfl
  rw [e]
  unfold stackVarsK
  rw [layoutsOf_eq]
  have e1 : (Commitment.c2 == Commitment.c1) = false := by decide
  have e2 : (Commitment.setup == Commitment.c1) = false := by decide
  have e3 : (Commitment.setup == Commitment.c2) = false := by decide
  cases c <;> simp [layoutIn, List.lookup, e1, e2, e3]

/-- **A claim's point has its PCS claim's variables**, for `C2`'s columns the shape's. -/
theorem claim_length {commit : Commitment → ℕ → Array K → Id Committed} {tr : Trace} {out : CoreOut}
    (hf : StreamFacts commit tr out) (hC2 : C2ColumnsHonest tr) {c c' : Commitment} {pt : List E} {v : E}
    (hfind : out.claims.find? (·.1 == c) = some (c', pt, v)) : pt.length = stackVarsK tr.shape c := by
  have hc : c' = c := by simpa using List.find?_some hfind
  subst hc
  rw [hf.points hC2 _ (List.mem_of_find?_eq_some hfind)]
  exact min_layoutIn_eq _ _

/-! #### Peeling a `StateT` program's binds -/

theorem peel {σ α β : Type} {x : StateT σ Id α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : ∀ a s', x.run s = (a, s') → P ((f a).run s').1) : P ((x >>= f).run s).1 := h _ _ rfl

theorem peel_lift {σ α β : Type} {x : Id α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f x).run s).1) : P ((StateT.lift x >>= f).run s).1 := h

theorem peel_map {σ α β γ : Type} {g : γ → α} {x : StateT σ Id γ} {f : α → StateT σ Id β} {P : β → Prop}
    {s : σ} (h : ∀ a s', x.run s = (a, s') → P ((f (g a)).run s').1) : P (((g <$> x) >>= f).run s).1 :=
  h _ _ rfl

theorem peel_get {σ β : Type} {f : σ → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f s).run s).1) : P ((get >>= f).run s).1 := h

theorem peel_pure_bind {σ α β : Type} {a : α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f a).run s).1) : P ((pure a >>= f).run s).1 := h

theorem peel_pure {σ β : Type} {a : β} {P : β → Prop} {s : σ} (h : P a) : P ((pure a : StateT σ Id β).run s).1 := h

set_option maxHeartbeats 1000000 in
theorem streamRun_facts (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    StreamFacts commit tr ((proveStreamWith (m := Id) H commit flock tr).run w0).1 := by
  unfold proveStreamWith
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun _ s1' _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  refine peel_map fun fo s5 _ ↦ ?_
  dsimp only
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
  simp only [batchRounds_point, List.length_nil, Nat.zero_add] at hl
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · simp only [List.map_map, Function.comp_def]
    exact combined_fst _ _ (atTOf_cover _ _ _ _ _ _ _)
  · intro hC2 x hx
    unfold C2ColumnsHonest at hC2
    simp only [List.mem_map] at hx
    obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
    rw [List.length_take, ← hl, hC2]


/-! ### The prover's result -/

/-- **Every commitment has a claim** in the stream's output, for every trace and challenge. -/
theorem claims_complete (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (w0 : Wr) :
    ((proveStreamWith (m := Id) H commit flock tr).run w0).1.claims.map (·.1) = [.c1, .c2, .setup] :=
  (streamRun_facts H commit flock tr w0).claims_fst

theorem claimProof_eq_some (fuel : ℕ) (tree : LeanVM.Prover.Tree) (out : CoreOut) (words : UniStatement.Shape)
    (c : Commitment) (p : Compile.Proof) :
    claimProof H F fuel tree out words c = some p ↔
      ∃ c' pt v, out.claims.find? (·.1 == c) = some (c', pt, v) ∧ openingFor H F fuel tree out words c pt v = some p := by
  unfold claimProof
  split
  · rename_i c' pt v heq
    simp [heq]
  · rename_i heq
    simp [heq]

theorem claimProof_eq_none (fuel : ℕ) (tree : LeanVM.Prover.Tree) (out : CoreOut) (words : UniStatement.Shape)
    (c : Commitment) :
    claimProof H F fuel tree out words c = none ↔
      out.claims.find? (·.1 == c) = none ∨
        ∃ c' pt v, out.claims.find? (·.1 == c) = some (c', pt, v) ∧ openingFor H F fuel tree out words c pt v = none := by
  unfold claimProof
  split
  · rename_i c' pt v heq
    simp [heq]
  · rename_i heq
    simp [heq]

/-- **`proveWith` returns a proof** exactly when each of `C1`, `C2`, the setup has a claim and the three openings
(`claimProof`: the stack, tree and layout of the commitment, the point claim) all return one; the proof is the
stream and those openings. -/
theorem proveWith_eq_some (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8)
    (tr : Trace) (π : KeccakProof) :
    proveWith (m := Id) H F fuel flock programIv tr = some π ↔
      ∃ p1 p2 p3,
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .c1 = some p1 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .c2 = some p2 ∧
        claimProof H F fuel (setupTreeOf (m := Id) H tr) (streamRun H flock programIv tr).1
          tr.shape .setup = some p3 ∧
        π = ⟨(streamRun H flock programIv tr).1.stream, p1, p2, p3⟩ := by
  rw [proveWith_eq, Option.bind_eq_some_iff]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨p1, h1, p2, h2, p3, h3, rfl⟩
    exact ⟨p1, p2, p3, h1, h2, h3, rfl⟩
  · rintro ⟨p1, p2, p3, h1, h2, h3, rfl⟩
    exact ⟨p1, h1, p2, h2, p3, h3, rfl⟩

/-- **When `proveWith` fails**: a commitment has no claim, or one of the three openings returned `none` (each named
with its layout, tree, stack and point claim). -/
theorem proveWith_eq_none (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8)
    (tr : Trace) (h : proveWith (m := Id) H F fuel flock programIv tr = none) :
    let tree := setupTreeOf (m := Id) H tr
    let out := (streamRun H flock programIv tr).1
    let words := tr.shape
    (∃ c ∈ [Commitment.c1, .c2, .setup], out.claims.find? (·.1 == c) = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c1) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c1) out.c1.2.tree out.c1.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c2) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .c2) out.c2.2.tree out.c2.1 pt v = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .setup) = some (c', pt, v) ∧
      pcsProveH (m := Id) H F fuel (stackVarsK words .setup) tree out.setup pt v = none) := by
  intro tree out words
  rw [proveWith_eq] at h
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


/-! ### At the reference shape -/

theorem ref_c1Layout : (c1LayoutK keccakRefShape).vars = 27 := reference_c1Vars

theorem ref_setupLayout : (setupLayout keccakRefShape).vars = 23 := reference_setupVars

theorem ref_c2Layout : (((layoutsOfK keccakRefShape).lookup .c2).getD default).vars = 26 := by
  rw [layoutsOf_eq]
  exact reference_c2Vars

theorem ref_layoutIn_c1 : (layoutIn (layoutsK keccakRefShape (Shape.c2ColumnsK keccakRefShape)) .c1).vars = 27 :=
  reference_c1Vars

theorem ref_layoutIn_c2 : (layoutIn (layoutsK keccakRefShape (Shape.c2ColumnsK keccakRefShape)) .c2).vars = 26 :=
  reference_c2Vars

theorem ref_layoutIn_setup :
    (layoutIn (layoutsK keccakRefShape (Shape.c2ColumnsK keccakRefShape)) .setup).vars = 23 :=
  reference_setupVars

theorem ref_rounds : ((layoutsK keccakRefShape (Shape.c2ColumnsK keccakRefShape)).map (·.2.vars)).foldl max 0 = 27 := by
  show ((layoutsOfK keccakRefShape).map (·.2.vars)).foldl max 0 = 27
  rw [reference_vars]
  rfl

theorem setupTree_eq (tr : Trace) :
    setupTreeOf (m := Id) H tr =
      E2ECompleteness.commitWithH (m := Id) H (setupLayout tr.shape).vars (setupStackOf tr) := rfl

/-- **The honest prover fails only at a proof of work**, at the reference shape, for an honest trace: if
`proveWith` returns `none`, one of the three PCS openings (at `23 ≤ vars ≤ 27` variables) reached WHIR's `17`-bit
proof of work at a sponge where every nonce below `fuel` fails. -/
theorem prover_none_pow (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (hshape : tr.shape = keccakRefShape) (hon : TraceHonest tr)
    (h : proveWith (m := Id) H F fuel flock programIv tr = none) :
    ∃ (vars : ℕ) (sc : List LeanVM.Protocol.Verifier.StackClaim) (hist : List Ev) (k : Prog Bool) (sp : Sponge), 23 ≤ vars ∧ vars ≤ 27 ∧
      (Whir.Complete.openingProgram vars PcsQuotient.logInvRate sc).after hist =
        some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n) (Compile.powStep F sp (Compile.nonceOf n)).1 =
        false := by
  have hf : StreamFacts (commitReal (m := Id) H) tr (streamRun H flock programIv tr).1 :=
    streamRun_facts H (commitReal (m := Id) H) flock tr _
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  have hpts := hf.points hC2
  rw [hshape] at hpts
  -- A claim found for `c` is `c`'s, with a point of its stack's variables.
  have hpt : ∀ c c' pt v, (streamRun H flock programIv tr).1.claims.find? (·.1 == c) =
      some (c', pt, v) → c' = c ∧
        pt.length = min (layoutIn (layoutsK keccakRefShape (Shape.c2ColumnsK keccakRefShape)) c).vars 27 := by
    intro c c' pt v hfind
    have hc : c' = c := by simpa using List.find?_some hfind
    subst hc
    have := hpts _ (List.mem_of_find?_eq_some hfind)
    rw [ref_rounds] at this
    exact ⟨rfl, this⟩
  rcases proveWith_eq_none H F fuel flock programIv tr h with
    hmiss | ⟨c', pt, v, hfind, hopen⟩ | ⟨c', pt, v, hfind, hopen⟩ | ⟨c', pt, v, hfind, hopen⟩
  · -- Every commitment has a claim.
    obtain ⟨c, hc, hnone⟩ := hmiss
    have hc' : c ∈ (streamRun H flock programIv tr).1.claims.map (·.1) := by
      rw [hf.claims_fst]
      exact hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    exact absurd (by simp : (x.1 == x.1) = true) (List.find?_eq_none.mp hnone x hx)
  · -- `C1`.
    obtain ⟨-, hlen⟩ := hpt .c1 c' pt v hfind
    rw [ref_layoutIn_c1, Nat.min_self] at hlen
    simp only [hf.c1, commitReal, idBind, idPure, hshape, reference_stackVars_c1] at hopen
    rw [ref_c1Layout] at hopen
    obtain ⟨sc, hist, k, sp, h1, h2⟩ := pcsProveH_fails_only_at_pow H F fuel (n := 27) (by norm_num)
      (by norm_num) _ pt hlen v hopen
    exact ⟨27, sc, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- `C2`.
    obtain ⟨-, hlen⟩ := hpt .c2 c' pt v hfind
    rw [ref_layoutIn_c2, show min 26 27 = 26 from rfl] at hlen
    simp only [hf.c2, commitReal, idBind, idPure, hshape, reference_stackVars_c2] at hopen
    rw [ref_c2Layout] at hopen
    obtain ⟨sc, hist, k, sp, h1, h2⟩ := pcsProveH_fails_only_at_pow H F fuel (n := 26) (by norm_num)
      (by norm_num) _ pt hlen v hopen
    exact ⟨26, sc, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- The setup.
    obtain ⟨-, hlen⟩ := hpt .setup c' pt v hfind
    rw [ref_layoutIn_setup, show min 23 27 = 23 from rfl] at hlen
    rw [hf.setup, setupTree_eq, hshape, reference_stackVars_setup, ref_setupLayout] at hopen
    obtain ⟨sc, hist, k, sp, h1, h2⟩ := pcsProveH_fails_only_at_pow H F fuel (n := 23) (by norm_num)
      (by norm_num) (setupStackOf tr) pt hlen v hopen
    exact ⟨23, sc, hist, k, sp, by norm_num, by norm_num, h1, h2⟩

end UniKeccakComplete.ProverRun

/-- info: 'UniKeccakComplete.ProverRun.proveWith_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.proveWith_eq_some

/-- info: 'UniKeccakComplete.ProverRun.proveWith_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.proveWith_eq_none

/-- info: 'UniKeccakComplete.ProverRun.claims_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.claims_complete

/-- info: 'UniKeccakComplete.ProverRun.streamRun_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.streamRun_facts

/-- info: 'UniKeccakComplete.ProverRun.c2ColumnsHonest_of_traceHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.c2ColumnsHonest_of_traceHonest

/-- info: 'UniKeccakComplete.ProverRun.pcsOpen_honest_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.pcsOpen_honest_k

/-- info: 'UniKeccakComplete.ProverRun.prover_none_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.ProverRun.prover_none_pow
