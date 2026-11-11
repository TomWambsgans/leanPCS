-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. Byte lemmas from leanerVM `mumbai` (6175f1a0, MIT OR Apache-2.0: `common/Common/Lanes.lean`,
-- `lean_vm/LeanVM/Protocol/KeccakHash.lean`).
import ZK.PcsNF
import LeanVM.Protocol.KeccakHash

/-!
# The Fiat–Shamir inputs are injective in their fresh values

The permutation's input of a one-block message determines the message (`blockIn_pad_inj`), of a longer one its
first block (`blockIn_take_inj`), of a later block the previous answer (`blockIn_state_inj`). The out-of-domain
input determines the root and the coordinate (`oodInput_inj`), a chain's message each scalar (`scalarBytes_inj`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

theorem lane_blockIn (st : KeccakState) (b : List UInt8) (i : ℕ) (hi : i < 25) :
    Keccak.lane (blockIn st b) i = if i < 17 then Keccak.lane st i ^^^ leLane b i else Keccak.lane st i := by
  rw [LeanVM.Rpm.lane_eq_getElem _ _ hi, blockIn, Vector.getElem_ofFn]

theorem blockIn_state_inj {st st' : KeccakState} {b : List UInt8} (h : blockIn st b = blockIn st' b) : st = st' := by
  apply Vector.ext
  intro i hi
  have := congrArg (fun v ↦ Keccak.lane v i) h
  simp only [lane_blockIn _ _ _ hi] at this
  rw [← LeanVM.Rpm.lane_eq_getElem _ _ hi, ← LeanVM.Rpm.lane_eq_getElem _ _ hi]
  split_ifs at this
  · simpa using this
  · exact this

theorem blockIn_zero_bytes {b b' : List UInt8} (h : blockIn zeroSt b = blockIn zeroSt b') (k : ℕ) (hk : k < 136) :
    b.getD k 0 = b'.getD k 0 := by
  have hi : k / 8 < 17 := by omega
  have := congrArg (fun v ↦ Keccak.lane v (k / 8)) h
  simp only [lane_blockIn _ _ _ (by omega : k / 8 < 25), hi, ite_true] at this
  have hz : Keccak.lane zeroSt (k / 8) = 0 := by
    rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega)]; simp
  rw [hz, UInt64.zero_xor, UInt64.zero_xor] at this
  have hb := congrArg (fun w ↦ (wordBytes w).getD (k % 8) 0) this
  simp only [LeanVM.Rpm.wordBytes_leLane] at hb
  have e : 8 * (k / 8) + k % 8 = k := by omega
  simpa [List.getD_eq_getElem?_getD, Nat.mod_lt _ (by omega : 8 > 0), e] using hb

theorem padBlock_getD (m : List UInt8) (k : ℕ) (hk : k < m.length) (hm : m.length < 136) :
    (padBlock m).getD k 0 = m.getD k 0 := by
  have h1 : ¬ (136 - 1 = k) := by omega
  have h2 : ¬ (m.length = k) := by omega
  simp only [padBlock, rate, List.getD_eq_getElem?_getD, List.getElem?_modify, h1, h2, ite_false,
    List.getElem?_append_left hk]
  cases m[k]? <;> rfl

theorem list_ext_getD {m m' : List UInt8} (hl : m.length = m'.length) (h : ∀ k < m.length, m.getD k 0 = m'.getD k 0) :
    m = m' := by
  refine List.ext_getElem hl fun k h1 h2 ↦ ?_
  have := h k h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

/-- **A one-block message is determined by its input.** -/
theorem blockIn_pad_inj {m m' : List UInt8} (hl : m.length = m'.length) (hm : m.length < 136)
    (h : blockIn zeroSt (padBlock m) = blockIn zeroSt (padBlock m')) : m = m' :=
  list_ext_getD hl fun k hk ↦ by
    rw [← padBlock_getD m k hk hm, ← padBlock_getD m' k (hl ▸ hk) (hl ▸ hm),
      blockIn_zero_bytes h k (by omega)]

/-- **A longer message's first block is determined by its input.** -/
theorem blockIn_take_inj {d d' : List UInt8} (hd : 136 ≤ d.length) (hd' : 136 ≤ d'.length)
    (h : blockIn zeroSt (d.take rate) = blockIn zeroSt (d'.take rate)) : d.take 136 = d'.take 136 :=
  list_ext_getD (by simp [List.length_take]; omega) fun k hk ↦ by
    have := blockIn_zero_bytes h k (by simp at hk; omega)
    simpa [rate] using this

theorem oodInput_inj {n : ℕ} {r r' : Digest} {j j' : ℕ} (h : oodInput n r j = oodInput n r' j') :
    r = r' ∧ j.toUInt8 = j'.toUInt8 := by
  unfold oodInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [digestBytes_len])
  obtain ⟨-, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨digestBytes_injective h3, by simpa using h2⟩

theorem beBytes_inj {a b : UInt64} (h : beBytes a = beBytes b) : a = b :=
  wordBytes_injective (List.reverse_injective h)

theorem scalarBytes_inj {x x' : E} (h : scalarBytes x = scalarBytes x') : x = x' := by
  unfold scalarBytes at h
  have hb : ∀ w : UInt64, (beBytes w).length = 8 := fun w ↦ by simp [beBytes, LeanVM.Rpm.wordBytes_len]
  obtain ⟨h1, h0⟩ := List.append_inj h (by simp [hb])
  obtain ⟨h2, h1⟩ := List.append_inj h1 (by simp [hb])
  obtain ⟨-, h2⟩ := List.append_inj h2 (by simp)
  have l0 := congrArg K.ofLane (beBytes_inj h0)
  have l1 := congrArg K.ofLane (beBytes_inj h1)
  have l2 := congrArg K.ofLane (beBytes_inj h2)
  simp only [K.ofLane_lane] at l0 l1 l2
  rw [← ofLimbs_limb x, ← ofLimbs_limb x', l0, l1, l2]

end PcsQuotient.EndToEnd
