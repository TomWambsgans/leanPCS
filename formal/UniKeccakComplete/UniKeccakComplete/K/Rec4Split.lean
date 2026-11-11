-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's prover (`Rec4Prover.lean`) cut at its two first
-- wide draws, as `Rec3Split.lean` cuts π1-rec3's: the tails are its text, copied; and its experiment staged in the
-- five-digest reading (`Rec4Staged.lean`'s `KStaged4`), as `Rec3ProbExp.lean`'s `stagedU3`.
import UniKeccakComplete.K.Rec4Prob

/-!
# π1-rec4's honest prover, cut at the bus draw and the point draw

π1-rec4's prover (`uniProverRec4With`, any lawful monad) is the prefix up to `C1`'s root (`proverA4`: the setup's
tree, **π1-rec4's IV**, the seed, `C1`'s commitment), **the bus draw** (`W` on `firstInput rows a`, `112` bytes), the
stream from Flock to `C2`'s root (`midB4`, on the writer after the draw, `writerAfter4`), **the point draw** (`W` on
`tInput`, the writer's state and the bytes since), and the rest (`proverD4`: `tailT4`, the values at `t`, the late
draw, the batch, then the openings): **`uniProverRec4With_split`**.

In the five-digest reading (`H = hash5`, `W = rate5`) the experiment is a staged run (**`stagedU4`**,
**`expW4_eq_staged4`**): `A` the setup and `proverA4`, `B` `midB4`, `C` `proverD4` and the verdict. Stage `A` hashes
`GoodL5` inputs only (**`hashA_stagedU4`**: the trees' `512`- and `64`-byte inputs, the IV's preimage, the seed's,
and their tails).
-/

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniKeccakComplete.Prob (chal ProverA firstInput prefixStream tInput run_forIn_send run_sendRoot run_sendScalar
  extract_size_toList oodOf countBytes)

/-! ## The stream, cut -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

/-- **The writer after a wide draw** of `count` challenges at the rate `r`. -/
def wideWr (w : Wr) (r : RateB) (count : ℕ) : Wr :=
  let xs := (List.range count).map (challengeAt r.toList)
  { w with absorbed := w.stream.size, state := digestOfRate r, challenges := w.challenges ++ xs.toArray }

/-- **The stream, cut at the two draws.** -/
theorem proveStreamRec4With_split (commit : Commitment → ℕ → Array K → m Committed) (tr : Trace) :
    proveStreamRec4With H W commit tr = (do
      for rows in tr.rows do
        sendInteger rows 4
      let committed1 ← (StateT.lift (commit .c1 (c1LayoutK tr.shape).vars (c1Stack tr)) : WrM m Committed)
      sendRoot committed1.halves
      sendScalar (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr) (rootOf committed1.halves))
      let bus ← sampleWideW W 4
      let x ← midB4 H commit tr bus
      let pointDraw ← sampleWideW W 5
      tailT4 H W tr committed1 bus x.1 x.2 pointDraw) := rfl

omit [Monad m] in
theorem run_sampleWideW [Monad m] [LawfulMonad m] (count : ℕ) (w : Wr) :
    (sampleWideW W count).run w =
      W (tInput w) >>= fun r ↦ pure ((List.range count).map (challengeAt r.toList), wideWr w r count) := by
  simp [sampleWideW, tInput, wideWr]

end With

/-- **The writer after π1-rec4's bus draw**: the prefix absorbed, the state the draw's digest, its four challenges. -/
def writerAfter4 (rows : List ℕ) (c1 : LeanVM.Prover.Tree) (ood : E) (r : RateB) : Wr :=
  ⟨prefixStream rows c1 ood, (prefixStream rows c1 ood).size, digestOfRate r, (busOf r).toArray⟩

section Run

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

/-- **The stream, run from the seed**: `C1`'s commitment, the bus draw, `midB4`, the point draw, the tail. -/
theorem run_proveStreamRec4With (tr : Trace) (seed : Digest) :
    (proveStreamRec4With H W (commitReal H) tr).run (Wr.start seed) = (do
      let c1 ← E2ECompleteness.commitWithH H (c1LayoutK tr.shape).vars (c1Stack tr)
      let r₁ ← W (digestBytes seed ++
        ((prefixStream tr.rows c1 (oodOf tr c1)).extract 0 (prefixStream tr.rows c1 (oodOf tr c1)).size).toList)
      let x ← (midB4 H (commitReal H) tr (busOf r₁)).run (writerAfter4 tr.rows c1 (oodOf tr c1) r₁)
      let r₂ ← W (tInput x.2)
      (tailT4 H W tr ⟨c1, rootHalves c1.root⟩ (busOf r₁) x.1.1 x.1.2 (pointOf r₂)).run (wideWr x.2 r₂ 5)) := by
  rw [proveStreamRec4With_split, StateT.run_bind, run_forIn_send]
  · simp only [pure_bind, StateT.run_bind, StateT.run_lift, commitReal, bind_assoc, run_sendRoot, run_sendScalar,
      run_sampleWideW, tInput, Wr.start]
    refine bind_congr fun c1 ↦ ?_
    refine bind_congr fun r₁ ↦ ?_
    have hw : ∀ st : Array UInt8, wideWr ⟨st, 0, seed, #[]⟩ r₁ 4 = ⟨st, st.size, digestOfRate r₁, (busOf r₁).toArray⟩ :=
      fun st ↦ by simp [wideWr, busOf]
    rw [hw]
    rfl
  · intro r u w
    simp [sendInteger, sendBytes]

end Run

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
  (F : KeccakState → m KeccakState)

/-- **π1-rec4's prover before the bus draw**: the setup's tree, π1-rec4's IV, the seed, `C1`'s tree. -/
def proverA4 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : m ProverA := do
  let tr := honestTrace D input rows q
  let tree ← setupTreeOf H tr
  let iv ← contractIvOf H tr.shape keccakRec4 D.programIv (setupRootsOf tr tree)
  let seed ← seedOf H iv tr.publicInput
  let c1 ← E2ECompleteness.commitWithH H (c1LayoutK tr.shape).vars (c1Stack tr)
  return ⟨tree, iv, seed, c1, oodOf tr c1⟩

/-- **π1-rec4's prover after the point draw**: the stream's tail on the writer after it, the openings. -/
def proverD4 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA)
    (r₁ : RateB) (x : ((List E × List E) × Committed) × Wr) (r₂ : RateB) : m (Option KeccakProof) := do
  let tr := honestTrace D input rows q
  let (out, _) ← (tailT4 H W tr ⟨a.c1, rootHalves a.c1.root⟩ (busOf r₁) x.1.1 x.1.2 (pointOf r₂)).run
    (wideWr x.2 r₂ 5)
  openingsTail3 H F PcsQuotient.nonceFuel tr a.tree out

/-- **π1-rec4's honest prover, cut at the two draws**, in any lawful monad. -/
theorem uniProverRec4With_split [LawfulMonad m] (D : KDeployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    uniProverRec4With H W F D input rows q = (do
      let a ← proverA4 H D input rows q
      let r₁ ← W (firstInput rows a)
      let x ← (midB4 H (commitReal H) (honestTrace D input rows q) (busOf r₁)).run
        (writerAfter4 rows a.c1 a.ood r₁)
      let r₂ ← W (tInput x.2)
      proverD4 H W F D input rows q a r₁ x r₂) := by
  simp only [uniProverRec4With, proveRec4With, run_proveStreamRec4With, proverA4, proverD4, bind_assoc, pure_bind]
  rfl

end With

/-! ## The staged experiment -/

open OracleComp OracleSpec
open UniKeccakComplete.Prob (GoodL)

variable (D : KDeployment)

/-- **What the run carries to the point draw**: the setup's tree, the prover before the bus draw, the bus draw's
rate, and the stream from Flock to `C2`'s root (`midB4`'s output, the writer). -/
structure MidU4 where
  tree : LeanVM.Prover.Tree
  a : ProverA
  r₁ : RateB
  mw : ((List E × List E) × Committed) × Wr

/-- **π1-rec4's experiment's stages** in the five-digest reading. -/
def stagedU4 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : KStaged4 where
  α := LeanVM.Prover.Tree × ProverA
  β := MidU4
  inp x := firstInput rows x.2
  A := do
    let tree ← setupTreeKWithH hash5 callKeccakF1600 D
    let a ← proverA4 hash5 D input rows q
    return (tree, a)
  B x r₁ := do
    let mw ← (midB4 hash5 (commitReal hash5) (honestTrace D input rows q) (busOf r₁)).run
      (writerAfter4 rows x.2.c1 x.2.ood r₁)
    return ⟨x.1, x.2, r₁, mw⟩
  tin b := tInput b.mw.2
  pr b := b.mw.1.1.1
  C b r₂ := do
    let o ← proverD4 hash5 rate5 callKeccakF1600 D input rows q b.a b.r₁ b.mw r₂
    verdictW4 hash5 rate5 callKeccakF1600 D b.tree input o

/-- **The five-digest experiment is the staged run's verdict.** -/
theorem expW4_eq_staged4 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    expW4 hash5 rate5 callKeccakF1600 D input rows q = (fun z ↦ z.1.1) <$> (stagedU4 D input rows q).run := by
  simp only [expW4, uniProverRec4With_split, KStaged4.run, stagedU4, map_bind, map_pure, bind_assoc, pure_bind,
    bind_pure]

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.expW4_eq_staged4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.expW4_eq_staged4
