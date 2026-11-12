-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsBadOod

/-!
# The cost of the challenge phase

**`phase_bound`**: the challenge phase's `58` tracked queries cost at most `58 · δq L`, `L = 5 · 2^19 + 90` the
edges any of them can see (the circuit's commitment's `5 · 2^19 + 24`, the chain's seed's `2`, the phase's own
`58`): each input is injective in a value drawn just before it (a root, a revealed scalar drawn last, the previous
answer).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A : Type}

/-- The edges a tracked query of the phase can see. -/
def phaseL : ℕ := 5 * 2 ^ 19 + 90

theorem uniformReveal_indep (q : Reveal) : StateIndep (uniformReveal (A := A) q) eDist := indep_coinE _ edge_coin

theorem chainMsg_length (c : Chain) : (chainMsg c).length = 32 + 32 * c.pending.length := chainMsg_len c

theorem flatMap_sc_length (l : List E) : (l.flatMap scalarBytes).length = 32 * l.length := by
  simp [List.length_flatMap, scalarBytes_len, Nat.mul_comm]

theorem inj_last (d : Digest) (pre : List E) (h : 32 + 32 * (pre.length + 1) < 136) :
    Function.Injective fun x ↦ blockIn zeroSt (padBlock (chainMsg ⟨d, pre ++ [x]⟩)) := fun x x' hx ↦ by
  have := blockIn_pad_inj (by simp [chainMsg_length]) (by rw [chainMsg_length]; simpa using h) hx
  simp only [chainMsg, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc] at this
  exact scalarBytes_inj (List.append_cancel_left this)

theorem inj_mid (d : Digest) (pre post : List E) (h : 32 + 32 * (pre.length + 1) ≤ 136)
    (h2 : 136 ≤ 32 + 32 * (pre.length + 1 + post.length)) :
    Function.Injective fun x ↦ blockIn zeroSt ((chainMsg ⟨d, pre ++ x :: post⟩).take rate) := fun x x' hx ↦ by
  have hlen : ∀ y : E, 136 ≤ (chainMsg ⟨d, pre ++ y :: post⟩).length := fun y ↦ by
    rw [chainMsg_length]; simp; omega
  have := blockIn_take_inj (hlen x) (hlen x') hx
  have hpre : (digestBytes d ++ pre.flatMap scalarBytes).length = 32 + 32 * pre.length := by
    rw [List.length_append, digestBytes_len, flatMap_sc_length]
  simp only [chainMsg, List.flatMap_append, List.flatMap_cons, ← List.append_assoc] at this
  have e : ∀ y : E, (digestBytes d ++ pre.flatMap scalarBytes ++ scalarBytes y ++ post.flatMap scalarBytes).take 136 =
      (digestBytes d ++ pre.flatMap scalarBytes) ++
        (scalarBytes y ++ post.flatMap scalarBytes).take (136 - (32 + 32 * pre.length)) := fun y ↦ by
    rw [List.append_assoc _ (scalarBytes y), List.take_append, List.take_of_length_le (by omega), hpre]
  rw [e x, e x'] at this
  have h3 := congrArg (List.take 32) (List.append_cancel_left this)
  simp only [List.take_take] at h3
  rw [min_eq_left (by omega : 32 ≤ 136 - (32 + 32 * pre.length)), List.take_left' (scalarBytes_len x),
    List.take_left' (scalarBytes_len x')] at h3
  exact scalarBytes_inj h3

theorem inj_digest : Function.Injective fun d : Digest ↦ blockIn zeroSt (padBlock (chainMsg ⟨d, []⟩)) := fun d d' h ↦ by
  have := blockIn_pad_inj (by simp [chainMsg_length]) (by rw [chainMsg_length]; simp) h
  simp only [chainMsg, List.flatMap_nil, List.append_nil] at this
  exact digestBytes_injective this

theorem inj_alpha (d rW : Digest) : Function.Injective fun oW ↦
    blockIn zeroSt (padBlock (chainMsg (({ state := d, pending := [] } : Chain).absorbCommitment
      (CommitmentScalars.of { root := rW, ood := oW })))) := by
  intro x x' h
  apply inj_last d [(rootHalves rW).1, (rootHalves rW).2] (by norm_num)
  simpa [Chain.absorbCommitment, Chain.absorb, CommitmentScalars.of] using h

/-- `ρ`'s first block is injective in `X`, the value drawn last (after `C` and `V + Y`). -/
theorem inj_rho (d : Digest) (v1 v2 nx : E) : Function.Injective fun v0 ↦
    blockIn zeroSt (List.take rate (chainMsg ((#v[v0, v1, v2].toList.foldl Chain.absorb
      ({ state := d, pending := [] } : Chain)).absorb nx))) := by
  intro x x' h
  apply inj_mid d [] [v1, v2, nx] (by norm_num) (by norm_num)
  simpa [Chain.absorb] using h

theorem prEvent_eDist_inj (F : E → KeccakState) (hF : Function.Injective F) (z : KeccakState) :
    Pr{let u ← eDist}[F u = z] ≤ pmax := prEvent_inj_le _ _ hF _ (fun e ↦ (prEvent_eDist e).le) z

theorem prEvent_state_inj (b : List UInt8) (z : KeccakState) : Pr{let y ← uState}[blockIn y b = z] ≤ pmax :=
  prEvent_uState_inj _ (fun _ _ h ↦ blockIn_state_inj h) z

theorem protocolName_length : protocolName.length = 16 := by
  have h : "pcs-quotient-kc3".toUTF8.size = 16 := by
    simp only [String.toUTF8, String.size_toByteArray]
    decide
  simp only [protocolName, ByteArray.toList]
  rw [loop_length _ _ 0 [] rfl, h]
  rfl

theorem label_length (index : Commitment) (stmt : Statement) : (label index stmt).length = 136 := by
  unfold label
  simp only [List.length_append, Vector.length_toList, elementBytes, beBytes, List.length_reverse,
    LeanVM.Rpm.wordBytes_len, digestBytes_len]
  rw [protocolName_length]

theorem phase_bound (stmt : Statement) (s : Edges × A) (hs : s.1.length = 0) :
    badB (phaseF (A := A) (membership logRows) stmt) s ≤ 58 * δq phaseL := by
  simp only [phaseF, membership_logRows, cellVars_logRows, squeezeF_bind]
  simp (disch := simp [chainMsg_length, Chain.absorbCommitment, Chain.absorb, rate]) only
    [keccakF_bind_one, keccakF_bind_two]
  refine badB_step_le _ _ _ _ fun p1 hp1 ↦ ?_
  have h1 := addsS_setup _ s p1 hp1
  rw [hs] at h1
  refine (badB_oodBlock phaseL 24 (by norm_num) _ p1.2 (by unfold phaseL; omega) (34 * δq phaseL)
    fun rW zW s2 hs2 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  refine badB_step_le _ _ _ _ fun p3 hp3 ↦ ?_
  have h3 := addsS_keccak_le (A := A) (label p1.1.2 stmt) 2 (by rw [label_length]; rfl) s2 p3 hp3
  -- `α, β, μ`: `W`'s out-of-domain answer drawn last, then each challenge's answer.
  rw [badB_r]
  refine (badB_ent phaseL _ eDist rDraw_indep _
    (fun z ↦ prEvent_inj_le _ _ (inj_alpha p3.1 rW) _ (fun e ↦ (prEvent_eDist e).le) z) _ p3.2
    (by unfold phaseL; omega) (33 * δq phaseL) fun oW ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ (fun y ↦ blockIn zeroSt (padBlock (chainMsg ⟨digestOf y, []⟩)))
    (fun z ↦ prEvent_uState_digest _ inj_digest z) _ p3.2 (by unfold phaseL; omega) (32 * δq phaseL)
    fun y ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ (fun y ↦ blockIn zeroSt (padBlock (chainMsg ⟨digestOf y, []⟩)))
    (fun z ↦ prEvent_uState_digest _ inj_digest z) _ (_ :: p3.2.1, p3.2.2) (by simp; unfold phaseL; omega)
    (31 * δq phaseL) fun y1 ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ (_ :: _ :: p3.2.1, p3.2.2) _ fun y2 ↦ ?_
  -- `T`'s out-of-domain point.
  refine (badB_oodBlock phaseL (24 + 4) (by norm_num) _ _ (by simp; unfold phaseL; omega) (3 * δq phaseL)
    fun rT zT s5 hs5 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  -- `t`: `T`'s out-of-domain answer drawn last, then its one block's answer.
  rw [badB_r]
  refine (badB_ent phaseL _ eDist rDraw_indep _
    (fun z ↦ prEvent_inj_le _ _ (inj_alpha _ rT) _ (fun e ↦ (prEvent_eDist e).le) z) _ s5
    (by simp at hs5 ⊢; unfold phaseL; omega) (2 * δq phaseL) fun oT ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ s5 _ fun yt ↦ ?_
  rw [badB_r]
  refine badB_step_le _ _ _ _ fun p10 hp10 ↦ ?_
  have h10 := addsS_indep rDraw_indep _ p10 hp10
  rw [badB_r]
  refine badB_step_le _ _ _ _ fun p11 hp11 ↦ ?_
  have h11 := addsS_indep rDraw_indep _ p11 hp11
  -- `ρ`: `X` drawn last, then the first block's answer.
  rw [badB_r]
  refine (badB_ent phaseL _ eDist rDraw_indep _ (prEvent_eDist_inj _ (inj_rho _ _ _ _)) _ p11.2
    (by simp at hs5 h10 h11 ⊢; unfold phaseL; omega) (1 * δq phaseL) fun v0 ↦ ?_).trans
    (le_of_eq (by ring))
  refine (badB_chain phaseL _ _ (prEvent_state_inj _) _ p11.2
    (by simp at hs5 h10 h11 ⊢; unfold phaseL; omega) 0 fun yρ ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ (_ :: p11.2.1, p11.2.2) _ fun yρ' ↦ ?_
  exact le_of_eq (by rw [badB])

end PcsQuotient.EndToEnd
