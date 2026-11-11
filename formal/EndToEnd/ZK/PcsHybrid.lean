-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the hybrid prover (`PcsQuotient.proveWithPcs` with the ideal PCS) is the challenge phase with the
-- prover's answers, then the openings.
import ZK.PcsReplay
import ZK.PcsRoot

/-!
# The hybrid prover is the challenge phase with the prover's answers

**`hybrid_run_eq`**: the honest prover with the ideal PCS (`proveWithPcs sim.perm sim.idealPcs`, the hybrid
experiment's) is, run from any state, the Statement's challenge phase with the revealed scalars the prover's
(`detReveal`: `revealAnswer` of its coins), then `finishOpenings`. The prover recomputes the reduction's chain
twice (its two `reduceWith` calls); in the lazily sampled permutation the recomputed challenges are the ones it
drew (`Replay`), the roots read back are its own (`rootOfHalves_rootHalves`), and whether the reduction rejects
does not depend on `Q`'s and `G`'s values (`claimsAt_isSome`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- The prover's answers to the reveal queries. -/
def detReveal {A : Type} (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (q : Reveal) :
    StateT (Edges × A) ProbComp E := pure (revealAnswer circuit stmt cells₀ coins q)

theorem run_bind_congr {σ β α : Type} {m m' : StateT σ ProbComp β} (hm : m = m')
    {k k' : β → StateT σ ProbComp α} {s : σ}
    (h : ∀ p ∈ support (m.run s), (k p.1).run p.2 = (k' p.1).run p.2) :
    (m >>= k).run s = (m' >>= k').run s := by
  subst hm
  rw [StateT.run_bind, StateT.run_bind]
  exact bind_congr_of_forall_mem_support _ h

theorem readCommitment_of (c : Chain) (com : Commitment) :
    readCommitment c (CommitmentScalars.of com) =
      some (com, c.absorbCommitment (CommitmentScalars.of com)) := by
  simp only [readCommitment, CommitmentScalars.of, rootOfHalves_rootHalves, Option.map_some]
  rfl

/-- **The reduction replayed**: from a state where its chain's seed and first four challenges are recorded,
the reduction's verifier draws `ρ` and gives the claims. -/
theorem reduceWith_replay {A γ' : Type} {s : Edges × A} {lr : ℕ} (hS : Supported lr) {index : Commitment}
    {stmt : Statement} {wCom hCom qCom gCom : Commitment} {values : Vector E 4} {next qv gv : E}
    {c0 c1 c2 c3 c4 : Chain} {α β γ t : E}
    (h0 : (Chain.startWith edgePerm (label index stmt)).run s = pure (c0, s))
    (h1 : (Chain.squeezeWith edgePerm (c0.absorbCommitment (CommitmentScalars.of wCom))).run s =
      pure ((α, c1), s))
    (h2 : (Chain.squeezeWith edgePerm c1).run s = pure ((β, c2), s))
    (h3 : (Chain.squeezeWith edgePerm c2).run s = pure ((γ, c3), s))
    (h4 : (Chain.squeezeWith edgePerm (((c3.absorbCommitment (CommitmentScalars.of hCom)).absorbCommitment
      (CommitmentScalars.of qCom)).absorbCommitment (CommitmentScalars.of gCom))).run s = pure ((t, c4), s))
    (f : Option Reduced → StateT (Edges × A) ProbComp γ') :
    (reduceWith edgePerm lr index stmt ⟨CommitmentScalars.of wCom, CommitmentScalars.of hCom,
        CommitmentScalars.of qCom, CommitmentScalars.of gCom, values, next, qv, gv⟩ >>= f).run s =
      (Chain.squeezeWith edgePerm ((values.toList.foldl Chain.absorb c4).absorb next) >>= fun x ↦
        f ((claimsAt lr stmt α β γ t x.1 values next qv gv).map fun cl ↦ ⟨⟨wCom, hCom, qCom, gCom⟩, cl⟩)).run s := by
  simp only [reduceWith, hS, not_true_eq_false, ite_false, bind_assoc]
  rw [StateT.run_bind, h0, pure_bind]
  simp only [readCommitment_of, bind_assoc]
  rw [StateT.run_bind, h1, pure_bind]
  rw [StateT.run_bind, h2, pure_bind]
  rw [StateT.run_bind, h3, pure_bind]
  rw [StateT.run_bind, h4, pure_bind]
  simp only [pure_bind]

theorem claimsAt_eq_none_iff (lr : ℕ) (stmt : Statement) (α β γ t ρ : E) (a : Vector E 4) (next qv gv : E) :
    claimsAt lr stmt α β γ t ρ a next qv gv = none ↔ claimsAt lr stmt α β γ t ρ a next 0 0 = none := by
  simp only [claimsAt]
  split_ifs <;> simp

theorem vec4_eta (v : Vector E 4) :
    (#v[v[(0 : Fin 4)], v[(1 : Fin 4)], v[(2 : Fin 4)], v[(3 : Fin 4)]] : Vector E 4) = v := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem supported_logRows : Supported logRows := by
  unfold Supported minLogRows maxLogRows logRows
  omega

theorem rowValues_snd (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (t : E) :
    (rowValues circuit cells₀ coins t).2 = wiringValue circuit t := rfl

section

variable (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins)

theorem revealAnswer_oodW (z : List E) :
    revealAnswer circuit stmt cells₀ coins (.oodW z) = tableEval (witnessTable circuit cells₀ coins) z := rfl

theorem revealAnswer_oodH (α β γ : E) (z : List E) :
    revealAnswer circuit stmt cells₀ coins (.oodH α β γ z) =
      tableEval (quotientTables circuit cells₀ coins α β γ).1 z := rfl

theorem revealAnswer_oodQ (α β γ : E) (z : List E) :
    revealAnswer circuit stmt cells₀ coins (.oodQ α β γ z) =
      tableEval (quotientTables circuit cells₀ coins α β γ).2.1 z := rfl

theorem revealAnswer_oodG (α β γ : E) (z : List E) :
    revealAnswer circuit stmt cells₀ coins (.oodG α β γ z) =
      tableEval (quotientTables circuit cells₀ coins α β γ).2.2 z := rfl

theorem revealAnswer_value (j : Fin 4) (t : E) :
    revealAnswer circuit stmt cells₀ coins (.value j t) = (rowValues circuit cells₀ coins t).1[j] := rfl

theorem revealAnswer_qValue (α β γ t ρ : E) :
    revealAnswer circuit stmt cells₀ coins (.qValue α β γ t ρ) =
      ((claimsAt circuit.logRows stmt α β γ t ρ (rowValues circuit cells₀ coins t).1 (wiringValue circuit t) 0
        0).map fun cl ↦ tableEval (quotientTables circuit cells₀ coins α β γ).2.1 cl.q.point).getD 0 := rfl

theorem revealAnswer_gValue (α β γ t ρ : E) :
    revealAnswer circuit stmt cells₀ coins (.gValue α β γ t ρ) =
      ((claimsAt circuit.logRows stmt α β γ t ρ (rowValues circuit cells₀ coins t).1 (wiringValue circuit t) 0
        0).map fun cl ↦ tableEval (quotientTables circuit cells₀ coins α β γ).2.2 cl.g.point).getD 0 := rfl

end

/-- **The hybrid prover is the challenge phase with the prover's answers, then the openings**, for any circuit
of a supported size (the membership circuit's is `logRows`). -/
theorem hybrid_run_eq (sim : PcsSimulator) (circuit : Circuit) (hS : Supported circuit.logRows)
    (stmt : Statement) (cells₀ : Array K) (coins : Coins) (s : sim.S) :
    (proveWithPcs sim.perm sim.idealPcs nonceFuel circuit stmt cells₀ coins).run s =
      (do let (_, out) ← challengePhase circuit stmt (detReveal circuit stmt cells₀ coins)
          finishOpenings sim circuit out).run s := by
  simp only [proveWithPcs, challengePhase, PcsSimulator.idealPcs, PcsSimulator.perm, PcsSimulator.oracle,
    detReveal, bind_assoc, pure_bind, revealAnswer_oodW, revealAnswer_oodH, revealAnswer_oodQ,
    revealAnswer_oodG, revealAnswer_value, revealAnswer_qValue, revealAnswer_gValue, rowValues_snd]
  refine run_bind_congr rfl fun p1 h1 ↦ ?_
  refine run_bind_congr rfl fun p2 h2 ↦ ?_
  refine run_bind_congr rfl fun p3 h3 ↦ ?_
  refine run_bind_congr rfl fun p4 h4 ↦ ?_
  refine run_bind_congr rfl fun p5 h5 ↦ ?_
  refine run_bind_congr rfl fun p6 h6 ↦ ?_
  refine run_bind_congr rfl fun p7 h7 ↦ ?_
  refine run_bind_congr rfl fun p8 h8 ↦ ?_
  refine run_bind_congr rfl fun p9 h9 ↦ ?_
  refine run_bind_congr rfl fun p10 h10 ↦ ?_
  refine run_bind_congr rfl fun p11 h11 ↦ ?_
  refine run_bind_congr rfl fun p12 h12 ↦ ?_
  refine run_bind_congr rfl fun p13 h13 ↦ ?_
  refine run_bind_congr rfl fun p14 h14 ↦ ?_
  have e5 := squeezeWith_mono _ _ p5 h5
  have e6 := squeezeWith_mono _ _ p6 h6
  have e7 := squeezeWith_mono _ _ p7 h7
  have e8 := mono_sampleDigest _ p8 h8
  have e9 := oodPointWith_mono _ _ _ p9 h9
  have e10 := mono_sampleDigest _ p10 h10
  have e11 := oodPointWith_mono _ _ _ p11 h11
  have e12 := mono_sampleDigest _ p12 h12
  have e13 := oodPointWith_mono _ _ _ p13 h13
  have e14 := squeezeWith_mono _ _ p14 h14
  have r0 := startWith_replay _ _ p4 h4 p14.2
    (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans e14)))))))))
  have r1 := squeezeWith_replay _ _ p5 h5 p14.2
    (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans e14))))))))
  have r2 := squeezeWith_replay _ _ p6 h6 p14.2
    (e7.trans (e8.trans (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans e14)))))))
  have r3 := squeezeWith_replay _ _ p7 h7 p14.2
    (e8.trans (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans e14))))))
  have r4 := squeezeWith_replay _ _ p14 h14 p14.2 (Ext.refl _)
  rw [reduceWith_replay hS r0 r1 r2 r3 r4]
  simp only [vec4_eta]
  refine run_bind_congr rfl fun p15 h15 ↦ ?_
  have e15 := squeezeWith_mono _ _ p15 h15
  rcases hc : claimsAt circuit.logRows stmt p5.1.1 p6.1.1 p7.1.1 p14.1.1 p15.1.1
    (rowValues circuit cells₀ coins p14.1.1).1 (wiringValue circuit p14.1.1) 0 0 with _ | cl0
  · simp only [hc, Option.map_none, Option.getD_none, finishOpenings]
  · simp only [Option.map_some, Option.getD_some]
    have r0' := startWith_replay _ _ p4 h4 p15.2 (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans
      (e11.trans (e12.trans (e13.trans (e14.trans e15))))))))))
    have r1' := squeezeWith_replay _ _ p5 h5 p15.2 (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans
      (e11.trans (e12.trans (e13.trans (e14.trans e15)))))))))
    have r2' := squeezeWith_replay _ _ p6 h6 p15.2 (e7.trans (e8.trans (e9.trans (e10.trans
      (e11.trans (e12.trans (e13.trans (e14.trans e15))))))))
    have r3' := squeezeWith_replay _ _ p7 h7 p15.2 (e8.trans (e9.trans (e10.trans
      (e11.trans (e12.trans (e13.trans (e14.trans e15)))))))
    have r4' := squeezeWith_replay _ _ p14 h14 p15.2 e15
    have r5 := squeezeWith_replay _ _ p15 h15 p15.2 (Ext.refl _)
    rw [reduceWith_replay hS r0' r1' r2' r3' r4', StateT.run_bind, r5, pure_bind]
    rcases hc2 : claimsAt circuit.logRows stmt p5.1.1 p6.1.1 p7.1.1 p14.1.1 p15.1.1
      (rowValues circuit cells₀ coins p14.1.1).1 (wiringValue circuit p14.1.1)
      (tableEval (quotientTables circuit cells₀ coins p5.1.1 p6.1.1 p7.1.1).2.1 cl0.q.point)
      (tableEval (quotientTables circuit cells₀ coins p5.1.1 p6.1.1 p7.1.1).2.2 cl0.g.point) with _ | cl
    · rw [claimsAt_eq_none_iff, hc] at hc2
      exact absurd hc2 (by simp)
    · simp only [Option.map_some, finishOpenings, PcsSimulator.perm]
      rfl

end PcsQuotient.EndToEnd
