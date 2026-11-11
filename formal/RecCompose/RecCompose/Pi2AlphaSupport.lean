-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's staged run's facts on every outcome of its run
-- against the lazy oracles, from `Pi2SimAt`'s facts at pure functions (`aAt`, `pre2_writer`) through
-- `Pi2AlphaChain.runAt_read`; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls, their lazy random oracles, `simulateQ`.
import RecCompose.Pi2AlphaChain
import RecCompose.Pi2SimAt

/-!
# `α`'s input on every outcome (π2v4)

On every outcome of stage A against the lazy oracles (`Pi2AlphaChain.runAt_read`: the outcome is the pure run at its
cache's answers):

* **`publicWire_data`**: the real circuit's reads are frame reads only (π2v4), so no public value is written to the
  stream;
* **`gAcc_length`**: stage A's outcome with `GAccA` (π1's prover returned a proof the graph accepted) has `α`'s input
  of `88` bytes (the seed's `32`, `W`'s root word, its out-of-domain answer), so `fixLen 88` keeps it.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (ro runAt Cache)
open UniComplete (Wr WrM)
open Pi2S Pi2K Pi2P Pi2E Pi2G

theorem publicBytes_frame (p : ℕ) (v : PublicValue) : publicBytes (.frame p, v) = [] := by
  cases v <;> rfl

/-- **The real circuit writes no public value** (its reads are the frame's three payloads). -/
theorem publicWire_data (values : List PublicValue) : Pi2S.publicWire (Data.reads.zip values) = [] := by
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp [Pi2S.publicWire, Data.reads, publicBytes_frame]

variable {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)

theorem runAt_stageA (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) :
    runAt Ht Ft (stageA callKeccak256 callKeccakF1600 D C Fa P1k input) =
      aAt Ht Ft D C Fa input (runAt Ht Ft P1k) := by
  unfold runAt aAt
  rw [sim_stageA]
  rfl

/-- **Stage A with `GAccA` has `α`'s input of `88` bytes**, on every outcome. -/
theorem gAcc_length (hD : D.Real) (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) {c : Cache}
    {p : StA × Cache}
    (hp : p ∈ support ((simulateQ ro (stageA callKeccak256 callKeccakF1600 D C Fa P1k input)).run c))
    (hG : GAccA p.1) : (UniKeccakComplete.Prob.tInput p.1.wr).length = 88 := by
  have e := Pi2C.runAt_read hp
  rw [runAt_stageA] at e
  rw [← e] at hG ⊢
  generalize Pi2C.readH p.2 = Ht at hG ⊢
  generalize Pi2C.readF p.2 = Ft at hG ⊢
  generalize runAt Ht Ft P1k = o at hG ⊢
  rcases o with _ | p1
  · have h0 : (aAt Ht Ft D C Fa input none).p1 = none := rfl
    exact absurd hG.1 (by rw [h0]; simp)
  · rw [aAt_wr]
    obtain ⟨hh, ho, hw⟩ := pre2_writer (C.G (rootsH D Ht Ft)) (WhirBridge.Pcs.oodPointM (Pure.pure ∘ Ht))
      (D.circuitAt (rootsH D Ht Ft).pi1).circuit.reads (vwH D C Fa Ht Ft input p1).1 (vwH D C Fa Ht Ft input p1).2 Ht
      (Wr.start (seedAt Ht Ft D C Fa input p1))
    have hr : (D.circuitAt (rootsH D Ht Ft).pi1).circuit.reads = Data.reads := by
      rw [RecDeployment.circuitAt, hD.1]
      rfl
    rw [hw, tInput_start_append, hr, publicWire_data]
    simp [E2ECompleteness.length_digestBytes, UniKeccakComplete.length_scalarWire]

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.gAcc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.gAcc_length
