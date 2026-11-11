-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsBadOod

/-!
# The cost of the challenge phase

**`badB_phaseF`**: the challenge phase's `113` tracked queries cost at most `113 · δq L`, `L = 5 · 2^19 + 140` the
edges any of them can see (the circuit's commitment's, the chain's seed's, the phase's own): each input is
injective in a value drawn just before it (a root, a revealed scalar drawn last, the previous answer).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A : Type}

/-- The edges a tracked query of the phase can see. -/
def phaseL : ℕ := 5 * 2 ^ 19 + 140

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

theorem inj_t (d rH rQ rG : Digest) (oQ oG : E) : Function.Injective fun oH ↦
    blockIn zeroSt (List.take rate (chainMsg (((({ state := d, pending := [] } : Chain).absorbCommitment
      (CommitmentScalars.of { root := rH, ood := oH })).absorbCommitment
        (CommitmentScalars.of { root := rQ, ood := oQ })).absorbCommitment
          (CommitmentScalars.of { root := rG, ood := oG })))) := by
  intro x x' h
  apply inj_mid d [(rootHalves rH).1, (rootHalves rH).2]
    [(rootHalves rQ).1, (rootHalves rQ).2, oQ, (rootHalves rG).1, (rootHalves rG).2, oG] (by norm_num) (by norm_num)
  simpa [Chain.absorbCommitment, Chain.absorb, CommitmentScalars.of] using h

theorem inj_rho (d : Digest) (a1 a2 a3 nx : E) : Function.Injective fun a0 ↦
    blockIn zeroSt (List.take rate (chainMsg ((#v[a0, a1, a2, a3].toList.foldl Chain.absorb
      ({ state := d, pending := [] } : Chain)).absorb nx))) := by
  intro x x' h
  apply inj_mid d [] [a1, a2, a3, nx] (by norm_num) (by norm_num)
  simpa [Chain.absorb] using h

theorem prEvent_eDist_inj (F : E → KeccakState) (hF : Function.Injective F) (z : KeccakState) :
    Pr{let u ← eDist}[F u = z] ≤ pmax := prEvent_inj_le _ _ hF _ (fun e ↦ (prEvent_eDist e).le) z

theorem prEvent_state_inj (b : List UInt8) (z : KeccakState) : Pr{let y ← uState}[blockIn y b = z] ≤ pmax :=
  prEvent_uState_inj _ (fun _ _ h ↦ blockIn_state_inj h) z

theorem kc1_length : ("pcs-quotient-kc1".toUTF8.toList).length = 16 := by
  have h : "pcs-quotient-kc1".toUTF8.size = 16 := by
    simp only [String.toUTF8, String.size_toByteArray]
    decide
  simp only [ByteArray.toList]
  rw [loop_length _ _ 0 [] rfl, h]
  rfl

theorem label_length (index : Commitment) (stmt : Statement) : (label index stmt).length = 136 := by
  unfold label
  simp only [List.length_append, Vector.length_toList, elementBytes, beBytes, List.length_reverse,
    LeanVM.Rpm.wordBytes_len, digestBytes_len]
  rw [kc1_length]

theorem phase_bound (stmt : Statement) (s : Edges × A) (hs : s.1.length = 0) :
    badB (phaseF (A := A) (membership logRows) stmt) s ≤ 113 * δq phaseL := by
  simp only [phaseF, membership_logRows, cellVars_logRows, squeezeF_bind]
  simp (disch := simp [chainMsg_length, Chain.absorbCommitment, Chain.absorb, rate]) only
    [keccakF_bind_one, keccakF_bind_two, keccakF_bind_three]
  refine badB_step_le _ _ _ _ fun p1 hp1 ↦ ?_
  have h1 := addsS_setup _ s p1 hp1
  rw [hs] at h1
  refine (badB_oodBlock phaseL (24 + 1) (by norm_num) _ p1.2 (by unfold phaseL; omega) (88 * δq phaseL)
    fun rW zW s2 hs2 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  refine badB_step_le _ _ _ _ fun p3 hp3 ↦ ?_
  have h3 := addsS_keccak_le (A := A) (label p1.1.2 stmt) 2 (by rw [label_length]; rfl) s2 p3 hp3
  -- `α, β, γ`: `W`'s out-of-domain answer drawn last, then each challenge's answer.
  refine (badB_ent phaseL _ eDist (uniformReveal_indep _) _
    (fun z ↦ prEvent_inj_le _ _ (inj_alpha p3.1 rW) _ (fun e ↦ (prEvent_eDist e).le) z) _ p3.2
    (by unfold phaseL; omega) (87 * δq phaseL) fun oW ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ (fun y ↦ blockIn zeroSt (padBlock (chainMsg ⟨digestOf y, []⟩)))
    (fun z ↦ prEvent_uState_digest _ inj_digest z) _ p3.2 (by unfold phaseL; omega) (86 * δq phaseL)
    fun y ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ (fun y ↦ blockIn zeroSt (padBlock (chainMsg ⟨digestOf y, []⟩)))
    (fun z ↦ prEvent_uState_digest _ inj_digest z) _ (_ :: p3.2.1, p3.2.2) (by simp; unfold phaseL; omega)
    (85 * δq phaseL) fun y1 ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ (_ :: _ :: p3.2.1, p3.2.2) _ fun y2 ↦ ?_
  -- The parts' out-of-domain points.
  refine (badB_oodBlock phaseL (24 + 3) (by norm_num) _ _ (by simp; unfold phaseL; omega) (58 * δq phaseL)
    fun rH zH s5 hs5 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  refine (badB_oodBlock phaseL (24 + 4) (by norm_num) _ _ (by simp at hs5 ⊢; unfold phaseL; omega) (30 * δq phaseL)
    fun rQ zQ s6 hs6 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  refine (badB_oodBlock phaseL (24 + 1) (by norm_num) _ _ (by simp at hs5 hs6 ⊢; unfold phaseL; omega)
    (5 * δq phaseL) fun rG zG s7 hs7 ↦ ?_).trans (le_of_eq (by push_cast; ring))
  refine badB_step_le _ _ _ _ fun p8 hp8 ↦ ?_
  have h8 := addsS_indep (uniformReveal_indep _) s7 p8 hp8
  refine badB_step_le _ _ _ _ fun p9 hp9 ↦ ?_
  have h9 := addsS_indep (uniformReveal_indep _) p8.2 p9 hp9
  -- `t`: `H`'s out-of-domain answer drawn last, then each block's answer.
  refine (badB_ent phaseL _ eDist (uniformReveal_indep _) _ (prEvent_eDist_inj _ (inj_t _ _ _ _ _ _)) _ p9.2
    (by simp at hs5 hs6 hs7 ⊢; unfold phaseL; omega) (4 * δq phaseL) fun oH ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ _ (prEvent_state_inj _) _ p9.2 (by simp at hs5 hs6 hs7 ⊢; unfold phaseL; omega)
    (3 * δq phaseL) fun yt ↦ ?_).trans (le_of_eq (by ring))
  refine (badB_chain phaseL _ _ (prEvent_state_inj _) _ (_ :: p9.2.1, p9.2.2)
    (by simp at hs5 hs6 hs7 ⊢; unfold phaseL; omega) (2 * δq phaseL) fun yt' ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ (_ :: _ :: p9.2.1, p9.2.2) _ fun yt'' ↦ ?_
  refine badB_step_le _ _ _ _ fun p10 hp10 ↦ ?_
  have h10 := addsS_indep (uniformReveal_indep _) _ p10 hp10
  refine badB_step_le _ _ _ _ fun p11 hp11 ↦ ?_
  have h11 := addsS_indep (uniformReveal_indep _) _ p11 hp11
  refine badB_step_le _ _ _ _ fun p12 hp12 ↦ ?_
  have h12 := addsS_indep (uniformReveal_indep _) _ p12 hp12
  -- `ρ`: `a_0` drawn last, then the first block's answer.
  refine (badB_ent phaseL _ eDist (uniformReveal_indep _) _ (prEvent_eDist_inj _ (inj_rho _ _ _ _ _)) _ p12.2
    (by simp at hs5 hs6 hs7 h8 h9 h10 h11 h12 ⊢; unfold phaseL; omega) (1 * δq phaseL) fun a0 ↦ ?_).trans
    (le_of_eq (by ring))
  refine (badB_chain phaseL _ _ (prEvent_state_inj _) _ p12.2
    (by simp at hs5 hs6 hs7 h8 h9 h10 h11 h12 ⊢; unfold phaseL; omega) 0 fun yρ ↦ ?_).trans (le_of_eq (by ring))
  refine badB_last _ _ (_ :: p12.2.1, p12.2.2) _ fun yρ' ↦ ?_
  refine badB_step_le _ _ _ _ fun p13 _ ↦ ?_
  refine badB_step_le _ _ _ _ fun p14 _ ↦ ?_
  exact le_of_eq (by rw [badB])

end PcsQuotient.EndToEnd
