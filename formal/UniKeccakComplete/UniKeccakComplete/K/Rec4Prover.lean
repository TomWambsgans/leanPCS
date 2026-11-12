-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `crates/leanvm/univariate/src/prover/prove.rs`
-- at `KECCAK_REC4` (the draws through `crates/leanvm/statement/src/transcript.rs`'s `Draws`: `bus_challenges`,
-- `point_challenge`, `late_challenges`; `KeccakWriter::sample_wide`) and the zerocheck with its first coordinate given
-- (`crates/vendor/flock-42422001`, `EqPoint::Squares` with the caller's challenge); the verifier it writes for is
-- `formal/UniKeccak/UniKeccak/Verifier4.lean`'s `reduceWithK4 … keccakRec4 .point`. Built on π1-rec3's prover
-- (`Rec3Prover.lean`) and its commutation (`Rec3ProverSim.lean`).
import UniKeccakComplete.K.Rec3ProverSim
import UniKeccakComplete.K.Rec3Split
import UniKeccakComplete.K.Rec4VerifierH

/-!
# π1-rec4's honest prover

π1-rec3's prover (`Rec3Prover.lean`) with π1-rec4's draws, in the verifier's order (`reduceWithK4 … keccakRec4
.point`); the stream is π1-rec3's byte for byte:

1. after `C1`'s commitment **one wide draw** (`sampleWideW W 4`, the prover's `sampleWide`): `c` (`α = squares c 4`),
   `β`, `γ`, Flock's zerocheck's first coordinate `c'`;
2. **Flock** on the Keccak-f block (`flockProve4`): π1-rec3's zerocheck with its coordinates after the seven fixed
   ones `squares c' …` given (`zerocheckW4`), `α`, the lincheck's 11 rounds, the 64 slices; **no ring map** here;
3. `C2`, then **one wide draw** (`sampleWideW W 5`): `t` and the ring map's `f_0 … f_3`;
4. the values at `t` (`atTOf … none`: they do not depend on Flock's end, `atTOf_values`);
5. **one wide draw** (`sampleWideW W 4`): `ρ`, the batch's `λ`, `f_4`, `f_5`; Flock's end the ring switch at the
   map `f_0 … f_5` (`towerTarget` of the slices); the relations and the combined claims (`atTOf … (some out)`);
6. π1-rec3's paired batch (`Rec3.batchRounds3`) with that `λ`; the stacks' values;
7. the IV at `keccakRec4`, three PCS claims' openings (`pcsProveH`, as π1-rec3's).

`uniProverRec4With H W F D` is generic in the monad, Keccak-256 `H` and its rate `W`; **`uniProverRec4RP D`** is it over
the random permutation (`keccak256With π`, `rateWith π`, `π`). It commutes with every monad morphism that commutes
with the opening (`app_uniProverRec4With`).
-/

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

open UniStatement UniStatement.Flock UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
  LeanVM.Protocol.KeccakHash

/-! ## The wide draw and Flock -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

/-- **`KeccakWriter::sample_wide`**: one call of `W` on the state and the bytes written since the last challenge; the
challenges `challengeAt` of its bytes, the new state its digest (the verifier's `sampleWideH`). -/
def sampleWideW (count : ℕ) : WrM m (List E) := do
  let c ← get
  let input := digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList
  let r ← (StateT.lift (W input) : WrM m RateB)
  let xs := (List.range count).map (challengeAt r.toList)
  set { c with absorbed := c.stream.size, state := digestOfRate r, challenges := c.challenges ++ xs.toArray }
  return xs

/-- **The zerocheck at π1-rec4** (`zerocheckFirst`'s order): the coordinates after the seven fixed ones `squares c …`
of the caller's `c`; with a skip, the coset values and `z`; the rounds; `v_a`, `v_b`. -/
def zerocheckW4 (logN k : ℕ) (c : E) (wit : FlockP.Wit) : WrM m (Option E × List E × E × E × E) := do
  let sampled := squares c (logN - k - nFixed)
  let st ← FlockP.skipW H k (fixedChallenges ++ sampled) wit
  let zc ← FlockP.zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c
  sendScalar zc.va
  sendScalar zc.vb
  return (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb)

/-- **Flock's front at π1-rec4** (`frontK4`'s order): the zerocheck from `c`, `α`, the lincheck's 11 rounds, the 64
slices. -/
def frontW4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) : WrM m (Front × List E) := do
  let zc ← zerocheckW4 H logN v.skip c (FlockP.witOf logN q)
  let alpha ← sampleW H
  let lc ← FlockP.lcRounds H lincheckRoundsK (FlockP.lcClaim zc alpha) (FlockP.lcWeightsOf v.skip zc alpha)
    (FlockP.lcWitnessOf v.skip q zc)
  sendScalars lc.z.toList
  return FlockP.frontOf v zc alpha lc

/-- **Flock's honest prover at π1-rec4** (`verifyWalkedK4`'s order): the front; `q_flock`'s point and the slices (the
ring switch's map is drawn later). -/
def flockProve4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) : WrM m (List E × List E) := do
  let frs ← frontW4 H logN v c q
  return (frs.1.point, frs.2)

end With

/-- **Flock's end at π1-rec4**: the ring switch at the map, its target in tower order. -/
def flockOut4 (fl : List E × List E) (map : List E) : FlockOut := ⟨fl.1, .ring map (towerTarget fl.2 map)⟩

/-! ## The stream and the proof -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

/-- The bus draw's challenges at a rate. -/
def busOf (r : RateB) : List E := (List.range 4).map (challengeAt r.toList)

/-- The point draw's challenges at a rate. -/
def pointOf (r : RateB) : List E := (List.range 5).map (challengeAt r.toList)

/-- **The stream from Flock to `C2`'s root** (steps 2–3): Flock's prover from the bus draw (`c = bus[0]`,
`α = squares c 4`, `β = bus[1]`, `γ = bus[2]`, Flock's first coordinate `bus[3]`), `C2`'s commitment, its root and
out-of-domain answer. -/
def midB4 (commit : Commitment → ℕ → Array K → m Committed) (tr : Trace) (bus : List E) :
    WrM m ((List E × List E) × Committed) := do
  let alphas := squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let logN := keccakR1csLogSize + tr.shape.heights.getD opSha3 0
  let fl ← flockProve4 H logN keccakRec4 (bus.getD 3 0) tr.qflock
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  sendScalar (pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack (rootOf committed2.halves))
  return (fl, committed2)

/-- **The stream from the point draw on** (steps 4–9): the values at `t = pointDraw[0]`; the late draw (`ρ`, `λ`,
`f_4`, `f_5`); Flock's end at the map `pointDraw[1 …] ++ [f_4, f_5]`; the combined claims; the paired batch with `λ`;
the stacks' values. -/
def tailT4 (tr : Trace) (committed1 : Committed) (bus : List E) (fl : List E × List E) (committed2 : Committed)
    (pointDraw : List E) : WrM m CoreOut := do
  let shape := tr.shape
  let stack1 := c1Stack tr
  let alphas := squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let t := pointDraw.getD 0 0
  sendScalars (atTOf tr c2 alphas beta gamma t none).values
  let late ← sampleWideW W 4
  let rho := late.getD 0 0
  let lambda := late.getD 1 0
  let map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0]
  let a := atTOf tr c2 alphas beta gamma t (some (flockOut4 fl map))
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layoutsK shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, combined, c2.heapVals⟩

/-- **π1-rec4's stream** on the Keccak VM (`prove`, steps 0–9 at `KECCAK_REC4`), from the seed: the row counts,
`C1`, the bus draw, `midB4`, the point draw, `tailT4`. -/
def proveStreamRec4With (commit : Commitment → ℕ → Array K → m Committed) (tr : Trace) : WrM m CoreOut := do
  for rows in tr.rows do
    sendInteger rows 4
  let committed1 ← (StateT.lift (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)) : WrM m Committed)
  sendRoot committed1.halves
  sendScalar (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr) (rootOf committed1.halves))
  let bus ← sampleWideW W 4
  let x ← midB4 H commit tr bus
  let pointDraw ← sampleWideW W 5
  tailT4 H W tr committed1 bus x.1 x.2 pointDraw

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
  (F : KeccakState → m KeccakState)

/-- **π1-rec4's honest prover** over `H`, `W`, `F`: the setup's tree, the Keccak contract's IV at `keccakRec4`, the
seed, the stream, then the three PCS claims' openings (`C1`, `C2`, the setup, `pcsProveH`); `none` if a proof of
work fails. -/
def proveRec4With (fuel : ℕ) (programIv : List UInt8) (tr : Trace) : m (Option KeccakProof) := do
  let tree ← setupTreeOf H tr
  let iv ← contractIvOf H tr.shape keccakRec4 programIv (setupRootsOf tr tree)
  let seed ← seedOf H iv tr.publicInput
  let (out, _) ← (proveStreamRec4With H W (commitReal H) tr).run (Wr.start seed)
  openingsTail3 H F fuel tr tree out

/-- **π1-rec4's honest prover on a witness**: `proveRec4With` on the placed trace (`honestTrace`), `nonceFuel` nonces
a proof of work. -/
def uniProverRec4With (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    m (Option KeccakProof) :=
  proveRec4With H W F PcsQuotient.nonceFuel D.programIv (honestTrace D input rows q)

end With

/-- **π1-rec4's honest prover in the random-permutation model**: `uniProverRec4With` over `π`, Keccak-256 the sponge
over `π`, its rate the sponge's rate (`rateWith`). -/
def uniProverRec4RP (D : KDeployment) : KProver D :=
  uniProverRec4With (keccak256With Common.queryPermutation) (rateWith Common.queryPermutation)
    Common.queryPermutation D

/-! ## The prover commutes with every monad morphism -/

section Morph

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n) (H : List UInt8 → m Digest)
  (W : List UInt8 → m RateB)

theorem wr_sampleWideW (count : ℕ) : φ.wr (sampleWideW W count) = sampleWideW (fun x ↦ φ.app (W x)) count := by
  simp only [sampleWideW, Morph.wr_bind, Morph.wr_get, Morph.wr_lift, Morph.wr_set, Morph.wr_pure]

theorem wr_zerocheckW4 (logN k : ℕ) (c : E) (wit : FlockP.Wit) :
    φ.wr (zerocheckW4 H logN k c wit) = zerocheckW4 (fun x ↦ φ.app (H x)) logN k c wit := by
  simp only [zerocheckW4, Morph.wr_bind, FlockP.wr_skipW, FlockP.wr_zcRounds, Morph.wr_sendScalar, Morph.wr_pure]

theorem wr_flockProve4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) :
    φ.wr (flockProve4 H logN v c q) = flockProve4 (fun x ↦ φ.app (H x)) logN v c q := by
  simp only [flockProve4, frontW4, Morph.wr_bind, wr_zerocheckW4, Morph.wr_sampleW, FlockP.wr_lcRounds,
    Morph.wr_sendScalars, Morph.wr_pure]

theorem wr_midB4 (commit : Commitment → ℕ → Array K → m Committed)
    (commit' : Commitment → ℕ → Array K → n Committed) (hcommit : ∀ c v s, φ.app (commit c v s) = commit' c v s)
    (tr : Trace) (bus : List E) :
    φ.wr (midB4 H commit tr bus) = midB4 (fun x ↦ φ.app (H x)) commit' tr bus := by
  simp only [midB4, Morph.wr_bind, Morph.wr_pure, Morph.wr_lift, hcommit, Morph.wr_sendRoot, Morph.wr_sendScalar,
    wr_flockProve4]

theorem wr_tailT4 (tr : Trace) (committed1 : Committed) (bus : List E) (fl : List E × List E)
    (committed2 : Committed) (pointDraw : List E) :
    φ.wr (tailT4 H W tr committed1 bus fl committed2 pointDraw) =
      tailT4 (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) tr committed1 bus fl committed2 pointDraw := by
  simp only [tailT4, Morph.wr_bind, Morph.wr_pure, Morph.wr_sendScalars, wr_sampleWideW, wr_batchRounds3,
    Morph.wr_get]

/-- **π1-rec4's stream commutes with a morphism** that commutes with the commitment. -/
theorem wr_proveStreamRec4With (commit : Commitment → ℕ → Array K → m Committed)
    (commit' : Commitment → ℕ → Array K → n Committed) (hcommit : ∀ c v s, φ.app (commit c v s) = commit' c v s)
    (tr : Trace) :
    φ.wr (proveStreamRec4With H W commit tr) =
      proveStreamRec4With (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) commit' tr := by
  simp only [proveStreamRec4With, midB4, tailT4, Morph.wr_bind, Morph.wr_forIn_list, Morph.wr_sendInteger,
    Morph.wr_pure, Morph.wr_lift, hcommit, Morph.wr_sendRoot, Morph.wr_sendScalar, wr_sampleWideW, wr_flockProve4,
    Morph.wr_sendScalars, wr_batchRounds3, Morph.wr_get]

end Morph

section Top

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (W : List UInt8 → m RateB) (F : KeccakState → m KeccakState)

omit [LawfulMonad m] [LawfulMonad n] in
/-- The three openings commute with a morphism that commutes with the opening. -/
theorem app_openingsTail3
    (hopen : ∀ (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
      φ.app (pcsProveH H F fuel n tree stack pt v) =
        pcsProveH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel n tree stack pt v)
    (fuel : ℕ) (tr : Trace) (tree : LeanVM.Prover.Tree) (out : CoreOut) :
    φ.app (openingsTail3 H F fuel tr tree out) =
      openingsTail3 (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel tr tree out := by
  unfold openingsTail3
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    simp only [φ.app_bind, φ.app_pure, hopen]

/-- **π1-rec4's honest prover commutes with a monad morphism** that commutes with the opening. -/
theorem app_proveRec4With
    (hopen : ∀ (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
      φ.app (pcsProveH H F fuel n tree stack pt v) =
        pcsProveH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel n tree stack pt v)
    (fuel : ℕ) (programIv : List UInt8) (tr : Trace) :
    φ.app (proveRec4With H W F fuel programIv tr) =
      proveRec4With (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (fun s ↦ φ.app (F s)) fuel programIv tr := by
  have hs : ∀ seed, φ.app ((proveStreamRec4With H W (commitReal H) tr).run (Wr.start seed)) =
      (proveStreamRec4With (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (commitReal fun x ↦ φ.app (H x)) tr).run
        (Wr.start seed) := fun seed ↦ by
    rw [← Morph.wr_run, wr_proveStreamRec4With φ H W _ _ (Morph.app_commitReal φ H)]
  simp only [proveRec4With, φ.app_bind, Morph.app_setupTreeOf, Morph.app_contractIvOf, Morph.app_seedOf, hs]
  refine bind_congr fun tree ↦ bind_congr fun iv ↦ bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  exact app_openingsTail3 φ H F hopen fuel tr tree x.1

/-- **π1-rec4's deployed honest prover commutes with a monad morphism** that commutes with the opening. -/
theorem app_uniProverRec4With
    (hopen : ∀ (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
      φ.app (pcsProveH H F fuel n tree stack pt v) =
        pcsProveH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel n tree stack pt v)
    (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    φ.app (uniProverRec4With H W F D input rows q) =
      uniProverRec4With (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (fun s ↦ φ.app (F s)) D input rows q :=
  app_proveRec4With φ H W F hopen _ _ _

end Top

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.app_uniProverRec4With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.app_uniProverRec4With
