-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: zero knowledge of the membership proof with the EIP's PCS claims, assuming a zero-knowledge PCS
-- (`docs/membership/HIDING.md`), in leanerVM's programmable random-permutation model (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import ZK.PcsHybrid
import ZK.PcsCoins

/-!
# Zero knowledge, assuming a zero-knowledge PCS

**`zeroKnowledge_pcs`**: `PcsZeroKnowledge sim εpcs → RevealedUniform εr → FiatShamirUniform εfs →
ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs)`, the three hypotheses those of
`formal/Statement/PcsQuotient/Zk.lean`.

1. Real ≈ hybrid: `PcsZeroKnowledge` (the PCS idealized in the prover's use of it), within `εpcs Q`.
2. The hybrid is the mixture over the prover's coins of the full program (`fullProg`: the challenge phase, its
   ten reveals answered by `revealAnswer` of the coins, then the openings and the distinguisher;
   `hybrid_eq`, from `hybrid_run_eq`); the ideal experiment of `zkSimulator` is the full program with uniform
   answers (`ideal_eq`).
3. Hybrid ≈ ideal (`RProg.trace_le`): within the probability, in the ideal run, that the log of reveals is not
   good. A log whose queries are `revealQueries c` is good where the revealed scalars are uniform at `c`
   (`good_of_uniformAt`), and the log's queries are those of the challenges the phase returns (`log_phaseProg`).
   So the bad probability is that of `¬ UniformAt` at the simulator's challenges: at most
   `Pr[¬ UniformAt at uniform challenges] + εfs ≤ εr + εfs` (`FiatShamirUniform`, `RevealedUniform`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open RProg

/-- **The full program**: the challenge phase, then the openings and the distinguisher on the proof. -/
noncomputable def fullProg (sim : PcsSimulator) (stmt : Statement) (D : Distinguisher) :
    RProg sim.S Reveal E Bool :=
  (phaseProg (membership logRows) stmt).bind fun x ↦
    .step (finishOpenings sim (membership logRows) x.2 >>= fun proof ↦ simulateQ sim.oracle (D proof)) .ret

theorem interp_fullProg (sim : PcsSimulator) (stmt : Statement) (D : Distinguisher)
    (rv : Reveal → StateT sim.S ProbComp E) :
    interp rv (fullProg sim stmt D) =
      (do let (_, out) ← challengePhase (membership logRows) stmt rv; finishOpenings sim (membership logRows) out) >>=
        fun proof ↦ simulateQ sim.oracle (D proof) := by
  rw [fullProg, interp_bind, interp_phaseProg, bind_assoc]
  simp only [interp, bind_pure]

theorem detReveal_eq_liftAns {A : Type} (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) :
    (detReveal (A := A) circuit stmt cells₀ coins) =
      liftAns (fun q ↦ pure (revealAnswer circuit stmt cells₀ coins q)) := by
  funext q
  rfl

theorem uniformReveal_eq_liftAns {A : Type} :
    (uniformReveal : Reveal → StateT (Edges × A) ProbComp E) = liftAns (fun _ ↦ eDist) := by
  funext q
  funext s
  exact indep_coinE _ edge_coin s

/-- **The hybrid experiment is the mixture over the coins** of the full program with the prover's answers. -/
theorem hybrid_eq (sim : PcsSimulator) (stmt : Statement) (w : Secret) (D : Distinguisher) :
    hybridExperiment sim stmt w D =
      (fun o ↦ o.1) <$> (coinsDist >>= fun c ↦
        semL (fun q ↦ pure (revealAnswer (membership logRows) stmt ((membership logRows).cells (membershipInputs w))
          c q)) (fullProg sim stmt D) sim.s₀ []) := by
  have hrest : ∀ c, (do
        let proof ← proveWithPcs sim.perm sim.idealPcs nonceFuel (membership logRows) stmt
          ((membership logRows).cells (membershipInputs w)) c
        simulateQ sim.oracle (D proof) : StateT sim.S ProbComp Bool).run sim.s₀ =
      (interp (detReveal (membership logRows) stmt ((membership logRows).cells (membershipInputs w)) c)
        (fullProg sim stmt D)).run sim.s₀ := by
    intro c
    rw [interp_fullProg, StateT.run_bind, StateT.run_bind, hybrid_run_eq sim _ supported_logRows]
  show Prod.fst <$> (simulateQ sim.oracle sampleCoins >>= fun c ↦ (do
        let proof ← proveWithPcs sim.perm sim.idealPcs nonceFuel (membership logRows) stmt
          ((membership logRows).cells (membershipInputs w)) c
        simulateQ sim.oracle (D proof) : StateT sim.S ProbComp Bool)).run sim.s₀ = _
  rw [StateT.run_bind, indep_sampleCoins sim.oracle (fun n ↦ edge_coin n), bind_map_left, map_bind, map_bind]
  refine congrArg _ (funext fun c ↦ ?_)
  rw [hrest]
  rw [detReveal_eq_liftAns, interp_liftAns_run _ _ _ [], Functor.map_map]

/-- **The ideal experiment of `zkSimulator`** is the full program with uniform answers. -/
theorem ideal_eq (sim : PcsSimulator) (stmt : Statement) (D : Distinguisher) :
    idealExperimentWith sim.s₀ (zkSimulator sim) sim.oracle stmt D =
      (fun o ↦ o.1) <$> semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ [] := by
  have h : (zkSimulator sim stmt >>= fun proof ↦ simulateQ sim.oracle (D proof)) =
      interp uniformReveal (fullProg sim stmt D) := by
    rw [interp_fullProg]
    rfl
  show Prod.fst <$> (zkSimulator sim stmt >>= fun proof ↦ simulateQ sim.oracle (D proof)).run sim.s₀ = _
  rw [h, uniformReveal_eq_liftAns, interp_liftAns_run _ _ _ [], Functor.map_map]

/-! ### Good logs -/

theorem forall_agree_iff {Q R : Type} (g : Q → R) (L : List (Q × R)) :
    (∀ x ∈ L, g x.1 = x.2) ↔ (L.map Prod.fst).map g = L.map Prod.snd := by
  induction L with
  | nil => simp
  | cons x L ih => simp

/-- **A log of the challenges' queries is good where the revealed scalars are uniform.** -/
theorem good_of_uniformAt (stmt : Statement) (cells₀ : Array K) (c : Challenges) (L : List (Reveal × E))
    (hL : L.map Prod.fst = revealQueries c) (hU : UniformAt stmt cells₀ c) :
    Good (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) L := by
  classical
  have hlen : (L.map Prod.snd).length = 10 := by
    rw [List.length_map, ← List.length_map (f := Prod.fst), hL]
    rfl
  have hw : weight (fun _ ↦ eDist) L 0 = ((L.map Prod.snd).map fun r ↦ Pr{let y ← eDist}[y = r]).prod := by
    simp [weight, List.map_map, Function.comp_def]
  refine ⟨?_, ?_⟩
  · have hagree : ∀ x, agrees (fun q ↦ revealAnswer (membership logRows) stmt cells₀ x q) L 0 =
        if revealed stmt cells₀ x c = L.map Prod.snd then 1 else 0 := by
      intro x
      simp only [agrees, List.drop_zero, revealed, ← hL]
      exact if_congr (forall_agree_iff _ L) rfl rfl
    simp only [hagree, mul_ite, mul_one, mul_zero]
    rw [← prEvent_eq_tsum_ite coinsDist (fun x ↦ revealed stmt cells₀ x c = L.map Prod.snd),
      ← prEvent_map coinsDist (fun x ↦ revealed stmt cells₀ x c) (· = L.map Prod.snd),
      ← runWithRandomPermutation_sampleCoins_map, hU, prEvent_coinEs _ hlen, hw]
  · rw [hw]
    refine List.prod_ne_zero fun h ↦ ?_
    obtain ⟨r, -, hr⟩ := List.mem_map.1 h
    exact prEvent_eDist_ne_zero r hr

/-! ### The bad logs -/

theorem semL_step_ret {σ Q R α : Type} (ν : Q → ProbComp R) (m : StateT σ ProbComp α) (s : σ)
    (L : List (Q × R)) :
    semL ν (.step m .ret) s L = m.run s >>= fun p ↦ pure (p.1, p.2, L) := rfl

theorem prEvent_keep {α σ β : Type} (m : ProbComp (α × σ)) (L : β) (P : β → Prop) [Decidable (P L)] :
    Pr{let y ← (m >>= fun p ↦ pure (p.1, p.2, L))}[P y.2.2] = if P L then 1 else 0 := by
  rw [show (m >>= fun p ↦ pure (p.1, p.2, L)) = (fun p ↦ (p.1, p.2, L)) <$> m by
    rw [map_eq_bind_pure_comp]; rfl, prEvent_map]
  split_ifs with h
  · exact (prEvent_eq_one_iff _ _).2 fun _ _ ↦ h
  · exact (prEvent_eq_zero_iff _ _).2 fun _ _ ↦ h

/-- **The bad logs** of the ideal run: at most the probability that the revealed scalars are not uniform at the
simulator's challenges. -/
theorem bad_le (sim : PcsSimulator) (stmt : Statement) (D : Distinguisher) (cells₀ : Array K) :
    Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[¬ Good (fun _ ↦ eDist) coinsDist
        (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) y.2.2] ≤
      Pr{let x ← (challengePhase (A := sim.Aux) (membership logRows) stmt uniformReveal).run' sim.s₀}[
        ¬ UniformAt stmt cells₀ x.1] := by
  classical
  set G : List (Reveal × E) → Prop :=
    Good (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q)
  -- The openings and the distinguisher keep the log.
  have hkeep : Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[¬ G y.2.2] =
      Pr{let o ← semL (fun _ ↦ eDist) (phaseProg (membership logRows) stmt) sim.s₀ []}[¬ G o.2.2] :=
    prEvent_semL_bind_step _ _ (fun x : Challenges × PhaseOut ↦ finishOpenings sim (membership logRows) x.2 >>= fun proof ↦
      simulateQ sim.oracle (D proof)) _ _ fun L ↦ ¬ G L
  rw [hkeep]
  -- A good log where the revealed scalars are uniform at the returned challenges.
  refine (prEvent_mono_of_support _ _ (fun o ↦ ¬ UniformAt stmt cells₀ o.1.1) fun o ho hbad hU ↦
    hbad (good_of_uniformAt stmt cells₀ o.1.1 o.2.2 (log_phaseProg _ stmt _ sim.s₀ o ho) hU)).trans_eq ?_
  rw [← interp_phaseProg, uniformReveal_eq_liftAns]
  show _ = Pr{let x ← (Prod.fst <$>
    (interp (liftAns fun _ ↦ eDist) (phaseProg (membership logRows) stmt)).run sim.s₀)}[¬ UniformAt stmt cells₀ x.1]
  rw [interp_liftAns_run _ _ _ [], Functor.map_map, prEvent_map]

/-! ### The end theorem -/

/-- **Zero knowledge of the membership proof, assuming a zero-knowledge PCS**: for every PCS simulator `sim`
whose ideal PCS the real one is within `εpcs` of (`PcsZeroKnowledge`), if the revealed scalars are uniform at all
but `εr` of the challenges (`RevealedUniform`) and the simulator's challenges are within `εfs` of uniform
(`FiatShamirUniform`), the simulator `zkSimulator sim` (no witness read) is within `εpcs Q + εr + εfs` of the
honest prover for every distinguisher of `Q` calls of `π`, `π⁻¹`. -/
theorem zeroKnowledge_pcs (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (εr εfs : ℝ≥0∞)
    (hpcs : PcsZeroKnowledge sim εpcs) (hrev : RevealedUniform εr) (hfs : FiatShamirUniform εfs) :
    ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs) := by
  intro stmt w hrel D Q hQ
  obtain ⟨h1, h2⟩ := hpcs stmt w hrel D Q hQ
  set cells₀ := (membership logRows).cells (membershipInputs w)
  -- The hybrid and the ideal experiment, within the bad logs.
  obtain ⟨t1, t2⟩ := trace_le (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q)
    (fullProg sim stmt D) sim.s₀ (fun o ↦ o.1 = true)
  have hbad : Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[¬ Good (fun _ ↦ eDist) coinsDist
      (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) y.2.2] ≤ εr + εfs := by
    refine (bad_le sim stmt D cells₀).trans ?_
    refine (hfs sim.Aux sim.aux₀ stmt (fun c ↦ ¬ UniformAt stmt cells₀ c)).trans ?_
    exact add_le_add_left (hrev stmt w hrel) εfs
  have hhyb : Pr{let b ← hybridExperiment sim stmt w D}[b = true] =
      Pr{let y ← (coinsDist >>= fun c ↦ semL (fun q ↦ pure (revealAnswer (membership logRows) stmt cells₀ c q))
        (fullProg sim stmt D) sim.s₀ [])}[y.1 = true] := by
    rw [hybrid_eq, prEvent_map]
  have hid : Pr{let b ← idealExperimentWith sim.s₀ (zkSimulator sim) sim.oracle stmt D}[b = true] =
      Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[y.1 = true] := by
    rw [ideal_eq, prEvent_map]
  rw [← hhyb, ← hid] at t1 t2
  generalize Pr{let b ← realExperiment stmt w D}[b = true] = pr at h1 h2 ⊢
  generalize Pr{let b ← hybridExperiment sim stmt w D}[b = true] = ph at h1 h2 t1 t2 ⊢
  generalize Pr{let b ← idealExperimentWith sim.s₀ (zkSimulator sim) sim.oracle stmt D}[b = true] = pi at t1 t2 ⊢
  generalize Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[¬ Good (fun _ ↦ eDist) coinsDist
      (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) y.2.2] = pb at t1 t2 hbad
  have t1' : ph ≤ pi + (εr + εfs) := t1.trans (by gcongr)
  have t2' : pi ≤ ph + (εr + εfs) := t2.trans (by gcongr)
  refine ⟨?_, ?_⟩
  · calc pr ≤ ph + εpcs Q := h1
      _ ≤ pi + (εr + εfs) + εpcs Q := by gcongr
      _ = pi + (εpcs Q + εr + εfs) := by ring
  · calc pi ≤ ph + (εr + εfs) := t2'
      _ ≤ pr + εpcs Q + (εr + εfs) := by gcongr
      _ = pr + (εpcs Q + εr + εfs) := by ring

end PcsQuotient.EndToEnd
