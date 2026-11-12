-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProverCost.lean` and
-- `VerifierHCost.lean` (the writer's and the channel's calculi `WC`, `CC`, reused), through a reading of π1-rec4's
-- calls by leanerVM's two (`sigma3`); uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): the block cost `hashBlocks`, the weight calculus.
import UniKeccakComplete.K.Rec4ProbK
import UniKeccakComplete.K.Rec3ProverCost

/-!
# The block count of π1-rec4's experiment (`ExpCost4`)

**`expCost4_reference`**: at the reference shape and a program IV of at most `2^16` bytes, π1-rec4's experiment over
its calls (`expW4 hashW callRate callFW`) makes at most `2^48` block calls (`hashBlocksW`: a hash, rate or digest, of
`n` bytes `⌊n / 136⌋ + 1`, a permutation call one).

**The reading.** The experiment over π1-rec4's calls is its three-call form read by `nu3` (`Rec4Exp.lean`), whose
block count is the three-call form's (`qcW_of_qc3`). The three-call form is bounded through leanerVM's two calls: a
rate call read as a digest query and a permutation call (`rateSigma`: the rate's first 32 bytes the digest, the rest
the permutation's answer's rate, `rateMix`, onto every rate, `rateMix_surj`) costs one block more than the rate call,
and every rate is reached, so the three-call form's block count is at most the reading's (`qc3_of_sigma3`), which is
the experiment at `H = callKeccak256`, `W = rateSigma` (`simulateQ_sigma3_exp3`): π1-rec3's calculi apply, the Keccak-256
calls being leanerVM's.

* **The prover** (`costP_proveRec4With`): the setup's tree, the IV, the seed, the stream (`wc_proveStreamRec4With`: the
  trees, two blocks a wide draw, Flock's `42` at the reference, the batch's, beyond its bytes), three openings: at
  most `2^47` blocks at the reference (`proverBlocks4_reference`), its stream at most `6952 + 3696` bytes.
* **The verifier** (`cost_verifierWith4H`): the IV, the seed, the walk (`cc_reduceWithKH4`: three blocks a wide draw,
  two a challenge, the rounds paid by their reads; `walkCost4 = 13`), three per stream byte, three openings.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## The rate read through leanerVM's two calls -/

/-- The zero state. -/
def zeroSt : KeccakState := Vector.replicate 25 0

/-- **A rate from a digest and a state**: the digest's 32 bytes, then the state's rate's bytes `32 … 135`. -/
def rateMix (d : Digest) (st : KeccakState) : RateB :=
  Vector.ofFn fun i : Fin 136 ↦ if h : i.val < 32 then (Digest.toRpm d)[i.val] else (rateOfState st)[i.val]

theorem rateOfState_symm (y : UniKeccakSound.Rec4.RState) : rateOfState (stateEquivR.symm y) = y.1.1 := by
  unfold rateOfState
  rw [Equiv.apply_symm_apply]

/-- **Every rate is a mix.** -/
theorem rateMix_surj (r : RateB) : ∃ d st, rateMix d st = r := by
  obtain ⟨y, hy⟩ : ∃ y : UniKeccakSound.Rec4.RState, y.1.1 = r := ⟨((r, Vector.replicate 0 0), Vector.replicate 64 0), rfl⟩
  generalize hv : (Vector.ofFn fun i : Fin 32 ↦ r[i.val]) = v
  refine ⟨Digest.ofRpm v, stateEquivR.symm y, ?_⟩
  apply Vector.ext
  intro i hi
  rw [rateMix, Vector.getElem_ofFn]
  by_cases h : i < 32
  · simp only [h, ↓reduceDIte]
    rw [digestToRpm_ofRpm, ← hv, Vector.getElem_ofFn]
  · simp only [h, ↓reduceDIte]
    rw [rateOfState_symm, hy]

/-- **A rate call read through leanerVM's two calls**: a digest query, a permutation call on the zero state. -/
def rateSigma (x : Bytes) : OracleComp KeccakCalls RateB := do
  let d ← callKeccak256 x
  let st ← callKeccakF1600 zeroSt
  pure (rateMix d st)

/-- **Three calls read through leanerVM's two.** -/
def sigma3 : QueryImpl KeccakCalls3 (OracleComp KeccakCalls)
  | .inl x => callKeccak256 x
  | .inr (.inl x) => rateSigma x
  | .inr (.inr s) => callKeccakF1600 s

/-- The block cost of the three calls. -/
def cost3 : KeccakCalls3.Domain → ℕ
  | .inl x => x.length / 136 + 1
  | .inr (.inl x) => x.length / 136 + 1
  | .inr (.inr _) => 1

/-- **The three calls' block count is at most their reading's.** -/
theorem qc3_of_sigma3 {α : Type} {X : OracleComp KeccakCalls3 α} {N : ℕ}
    (h : Common.QueryCostAtMost (simulateQ sigma3 X) hashBlocks N) : Common.QueryCostAtMost X cost3 N := by
  induction X using OracleComp.inductionOn generalizing N with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind] at h
    rw [Common.isWeightBound_query_bind_iff]
    rcases t with x | x | s
    · have h' : Common.QueryCostAtMost (callKeccak256 x >>= fun u ↦ simulateQ sigma3 (k u)) hashBlocks N := h
      rw [callKeccak256, Common.isWeightBound_query_bind_iff] at h'
      exact ⟨h'.1, fun u ↦ ih u (h'.2 u)⟩
    · have h' : Common.QueryCostAtMost (rateSigma x >>= fun u ↦ simulateQ sigma3 (k u)) hashBlocks N := h
      simp only [rateSigma, bind_assoc, pure_bind] at h'
      rw [callKeccak256, Common.isWeightBound_query_bind_iff] at h'
      refine ⟨h'.1, fun r ↦ ?_⟩
      obtain ⟨d, st, rfl⟩ := rateMix_surj r
      have h2 := h'.2 d
      rw [callKeccakF1600, Common.isWeightBound_query_bind_iff] at h2
      have e1 : hashBlocks (Sum.inr zeroSt) = 1 := rfl
      have e2 : cost3 (Sum.inr (Sum.inl x)) = hashBlocks (Sum.inl x) := rfl
      exact (ih _ (h2.2 st)).mono (by omega)
    · have h' : Common.QueryCostAtMost (callKeccakF1600 s >>= fun u ↦ simulateQ sigma3 (k u)) hashBlocks N := h
      rw [callKeccakF1600, Common.isWeightBound_query_bind_iff] at h'
      exact ⟨h'.1, fun u ↦ ih u (h'.2 u)⟩

/-- **π1-rec4's calls' block count is the three calls'.** -/
theorem qcW_of_qc3 {α : Type} {X : OracleComp KeccakCalls3 α} {N : ℕ} (h : Common.QueryCostAtMost X cost3 N) :
    Common.QueryCostAtMost (simulateQ nu3 X) hashBlocksW N := by
  refine isWeightBound_simulateQ' nu3 cost3 hashBlocksW (fun t ↦ ?_) h
  rcases t with x | x | s
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query (spec := KeccakCallsW) hashBlocksW (.inl x))
  · exact Common.isWeightBound_query (spec := KeccakCallsW) hashBlocksW (.inl x)
  · exact Common.isWeightBound_query (spec := KeccakCallsW) hashBlocksW (.inr s)

/-- **The three-call experiment read through leanerVM's two calls** is the experiment at `H = callKeccak256`,
`W = rateSigma`. -/
theorem simulateQ_sigma3_exp3 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ sigma3 (expW4 call3H call3W call3F D input rows q) =
      expW4 callKeccak256 rateSigma callKeccakF1600 D input rows q := by
  rw [simulateQ_exp3]
  have hH : (fun x ↦ simulateQ sigma3 (call3H x)) = callKeccak256 := by
    funext x; unfold call3H; rw [simulateQ_spec_query]; rfl
  have hW : (fun x ↦ simulateQ sigma3 (call3W x)) = rateSigma := by
    funext x; unfold call3W; rw [simulateQ_spec_query]; rfl
  have hF : (fun s ↦ simulateQ sigma3 (call3F s)) = callKeccakF1600 := by
    funext s; unfold call3F; rw [simulateQ_spec_query]; rfl
  rw [hH, hW, hF]

/-- **`ExpCost4` from the experiment at `H = callKeccak256`, `W = rateSigma`.** -/
theorem expCost4_of (D : KDeployment) {N : ℕ}
    (h : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
      Common.QueryCostAtMost (expW4 callKeccak256 rateSigma callKeccakF1600 D input rows q) hashBlocks N) :
    ExpCost4 D N := by
  intro input rows q hfit hrel
  rw [← simulateQ_nu3_exp3]
  refine qcW_of_qc3 (qc3_of_sigma3 ?_)
  rw [simulateQ_sigma3_exp3]
  exact h input rows q hfit hrel

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.expCost4_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.expCost4_of
