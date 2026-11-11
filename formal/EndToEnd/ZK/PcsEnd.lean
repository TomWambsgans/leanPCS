-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: zero knowledge of the membership proof with the EIP's PCS claims, assuming a zero-knowledge PCS
-- (`docs/membership/PROTOCOL.md`, "Zero knowledge"), in leanerVM's programmable random-permutation model (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import ZK.PcsHybrid
import ZK.PcsCoins

/-!
# Zero knowledge, assuming a zero-knowledge PCS

**`zeroKnowledge_pcs`**: `PcsZeroKnowledge sim εpcs → RevealedUniform εr δr → FiatShamirUniform εfs →
ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + δr + εfs)`, the three hypotheses those
of `formal/Statement/PcsQuotient/Zk.lean`.

1. Real ≈ hybrid: `PcsZeroKnowledge` (the PCS idealized in the prover's use of it), within `εpcs Q`.
2. The hybrid is the mixture over the prover's coins of the full program (`fullProg`: the challenge phase, its
   five reveals answered by `revealAnswer` of the coins, then the openings and the distinguisher; `hybrid_eq`, from
   `hybrid_run_eq`); the ideal experiment of `zkSimulator` is the full program with uniform answers (`ideal_eq`).
3. Hybrid ≈ ideal (`RProg.trace_le_approx`): within the ideal run's expected shortfall, at each outcome how much the
   revealed scalars' mass under the prover's coins falls short of their uniform mass, relative to it. On a log of
   the challenges `c` with answers `a` that is `gap c a` (`shortfall_eq`, from `log_phaseProg`); its expectation over
   the simulator's challenge phase is at most its expectation over independent uniform challenges and scalars plus
   `εfs` (`FiatShamirUniform`), which is the expected statistical distance of the revealed scalars from uniform
   (`tsum_uMass_gap`): at most `δr` at the challenges where `UniformWithin` holds, `1` elsewhere, so at most
   `εr + δr` (`RevealedUniform`).
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

/-! ### The masses of a log -/

theorem forall_agree_iff {Q R : Type} (g : Q → R) (L : List (Q × R)) :
    (∀ x ∈ L, g x.1 = x.2) ↔ (L.map Prod.fst).map g = L.map Prod.snd := by
  induction L with
  | nil => simp
  | cons x L ih => simp

/-- The uniform mass of five scalars. -/
noncomputable def uMass (a : List E) : ℝ≥0∞ := Pr{let x ← runWithRandomPermutation (coinEs 5)}[x = a]

/-- The mass of five scalars as the revealed scalars at the challenges `c`, with uniform randomness. -/
noncomputable def rMass (stmt : Statement) (cells₀ : Array K) (c : Challenges) (a : List E) : ℝ≥0∞ :=
  Pr{let x ← runWithRandomPermutation (do return revealed stmt cells₀ (← sampleCoins) c)}[x = a]

/-- **The `ν`-mass of a log of the challenges' queries** is the uniform mass of its answers. -/
theorem weight_eq (c : Challenges) (L : List (Reveal × E)) (hL : L.map Prod.fst = revealQueries c) :
    weight (fun _ ↦ eDist) L 0 = uMass (L.map Prod.snd) := by
  have hlen : (L.map Prod.snd).length = 5 := by
    rw [List.length_map, ← List.length_map (f := Prod.fst), hL]
    rfl
  rw [uMass, prEvent_coinEs _ hlen]
  simp [weight, List.map_map, Function.comp_def]

theorem weight_ne_zero (L : List (Reveal × E)) : weight (fun _ ↦ eDist) L 0 ≠ 0 := by
  refine List.prod_ne_zero fun h ↦ ?_
  obtain ⟨r, -, hr⟩ := List.mem_map.1 h
  exact prEvent_eDist_ne_zero r.2 hr

/-- **The mixture's mass of a log of the challenges' queries** is the revealed scalars' mass of its answers. -/
theorem mixMass_eq (stmt : Statement) (cells₀ : Array K) (c : Challenges) (L : List (Reveal × E))
    (hL : L.map Prod.fst = revealQueries c) :
    mixMass coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) L =
      rMass stmt cells₀ c (L.map Prod.snd) := by
  classical
  have hagree : ∀ x, agrees (fun q ↦ revealAnswer (membership logRows) stmt cells₀ x q) L 0 =
      if revealed stmt cells₀ x c = L.map Prod.snd then 1 else 0 := by
    intro x
    simp only [agrees, List.drop_zero, revealed, ← hL]
    exact if_congr (forall_agree_iff _ L) rfl rfl
  simp only [mixMass, hagree, mul_ite, mul_one, mul_zero]
  rw [← prEvent_eq_tsum_ite coinsDist (fun x ↦ revealed stmt cells₀ x c = L.map Prod.snd),
    ← prEvent_map coinsDist (fun x ↦ revealed stmt cells₀ x c) (· = L.map Prod.snd),
    ← runWithRandomPermutation_sampleCoins_map, rMass]

/-- **The gap at challenges and scalars**: how much the revealed scalars' mass falls short of the uniform mass,
relative to it (truncated at zero). -/
noncomputable def gap (stmt : Statement) (cells₀ : Array K) (c : Challenges) (a : List E) : ℝ≥0∞ :=
  1 - rMass stmt cells₀ c a / uMass a

theorem gap_le_one (stmt : Statement) (cells₀ : Array K) (c : Challenges) (a : List E) :
    gap stmt cells₀ c a ≤ 1 := tsub_le_self

/-- **The expected gap at uniform scalars is the statistical distance.** -/
theorem tsum_uMass_gap (stmt : Statement) (cells₀ : Array K) (c : Challenges) :
    ∑' a, uMass a * gap stmt cells₀ c a = ∑' a, (uMass a - rMass stmt cells₀ c a) := by
  refine tsum_congr fun a ↦ ?_
  by_cases hu : uMass a = 0
  · rw [hu, zero_mul, zero_tsub]
  · have hut : uMass a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
    rw [gap, ENNReal.mul_sub (fun _ _ ↦ hut), mul_one, ENNReal.mul_div_cancel hu hut]

theorem tsum_uMass_sub_le_one (stmt : Statement) (cells₀ : Array K) (c : Challenges) :
    ∑' a, (uMass a - rMass stmt cells₀ c a) ≤ 1 :=
  (ENNReal.tsum_le_tsum fun _ ↦ tsub_le_self).trans (tsum_prEvent_eq_one _).le

/-! ### The expected shortfall -/

theorem tsum_semL_step_ret {σ Q R α γ : Type} (ν : Q → ProbComp R) (P : RProg σ Q R α)
    (m : α → StateT σ ProbComp γ) (s : σ) (L : List (Q × R)) (φ : List (Q × R) → ℝ≥0∞) :
    ∑' y, Pr{let y' ← semL ν (P.bind fun a ↦ .step (m a) .ret) s L}[y' = y] * φ y.2.2 =
      ∑' o, Pr{let o' ← semL ν P s L}[o' = o] * φ o.2.2 := by
  classical
  rw [semL_bind, tsum_prEvent_bind_mul]
  refine tsum_congr fun o ↦ ?_
  congr 1
  simp only [semL]
  rw [tsum_prEvent_bind_mul]
  calc ∑' p, Pr{let y ← (m o.1).run o.2.1}[y = p] *
        ∑' y, Pr{let y' ← (pure (p.1, p.2, o.2.2) : ProbComp _)}[y' = y] * φ y.2.2
      = ∑' p, Pr{let y ← (m o.1).run o.2.1}[y = p] * φ o.2.2 := by
        refine tsum_congr fun p ↦ ?_
        congr 1
        simp only [RProg.prEvent_pure_eq]
        rw [tsum_eq_single (p.1, p.2, o.2.2) fun b hb ↦ by rw [ite_eq_right (Ne.symm hb), zero_mul]]
        simp
    _ = φ o.2.2 := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- **The ideal run's expected shortfall** is the simulator's challenge phase's expected gap, at its challenges
and revealed scalars. -/
theorem shortfall_eq (sim : PcsSimulator) (stmt : Statement) (D : Distinguisher) (cells₀ : Array K) :
    ∑' o, Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[y = o] *
        shortfall (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) o.2.2 =
      ∑' x, Pr{let y ← (challengePhase (A := sim.Aux) (membership logRows) stmt uniformReveal).run' sim.s₀}[y = x] *
        gap stmt cells₀ x.1 (answersOf x.2) := by
  classical
  rw [fullProg, tsum_semL_step_ret]
  -- On the phase's support, the shortfall of the log is the gap at the output's challenges and scalars.
  have hpt : ∀ o, Pr{let y ← semL (fun _ ↦ eDist) (phaseProg (membership logRows) stmt) sim.s₀ []}[y = o] *
      shortfall (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) o.2.2 =
      Pr{let y ← semL (fun _ ↦ eDist) (phaseProg (membership logRows) stmt) sim.s₀ []}[y = o] *
        gap stmt cells₀ o.1.1 (answersOf o.1.2) := by
    intro o
    by_cases ho : o ∈ support (semL (fun _ ↦ eDist) (phaseProg (membership logRows) stmt) sim.s₀ [])
    · obtain ⟨h1, h2⟩ := log_phaseProg _ stmt _ sim.s₀ o ho
      rw [shortfall, mixMass_eq stmt cells₀ _ _ h1, weight_eq _ _ h1, h2, gap]
    · rw [prEvent_eq_zero_of_not_mem_support _ ho, zero_mul, zero_mul]
  rw [tsum_congr hpt]
  rw [← interp_phaseProg, uniformReveal_eq_liftAns]
  show _ = ∑' x, Pr{let y ← (Prod.fst <$>
    (interp (liftAns fun _ ↦ eDist) (phaseProg (membership logRows) stmt)).run sim.s₀)}[y = x] *
      gap stmt cells₀ x.1 (answersOf x.2)
  rw [interp_liftAns_run _ _ _ [], Functor.map_map, tsum_map]

/-! ### The end theorem -/

/-- **Zero knowledge of the membership proof, assuming a zero-knowledge PCS**: for every PCS simulator `sim`
whose ideal PCS the real one is within `εpcs` of (`PcsZeroKnowledge`), if the revealed scalars are within `δr` of
uniform at all but `εr` of the challenges (`RevealedUniform`) and the simulator's challenges and scalars are
within `εfs` of uniform (`FiatShamirUniform`), the simulator `zkSimulator sim` (no witness read) is within
`εpcs Q + εr + δr + εfs` of the honest prover for every distinguisher of `Q` calls of `π`, `π⁻¹`. -/
theorem zeroKnowledge_pcs (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (εr δr εfs : ℝ≥0∞)
    (hpcs : PcsZeroKnowledge sim εpcs) (hrev : RevealedUniform εr δr) (hfs : FiatShamirUniform εfs) :
    ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + δr + εfs) := by
  classical
  intro stmt w hrel D Q hQ
  obtain ⟨h1, h2⟩ := hpcs stmt w hrel D Q hQ
  set cells₀ := (membership logRows).cells (membershipInputs w)
  -- The hybrid and the ideal experiment, within the expected shortfall.
  obtain ⟨t1, t2⟩ := trace_le_approx (fun _ ↦ eDist) coinsDist
    (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) (fullProg sim stmt D) sim.s₀ weight_ne_zero
    (fun o ↦ o.1 = true)
  have hgap : ∑' o, Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[y = o] *
      shortfall (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) o.2.2 ≤
        εr + δr + εfs := by
    rw [shortfall_eq]
    refine (hfs sim.Aux sim.aux₀ stmt (gap stmt cells₀) (gap_le_one stmt cells₀)).trans (add_le_add ?_ le_rfl)
    -- At independent uniform challenges and scalars: the expected statistical distance.
    have hc : ∀ c, ∑' a, Pr{let y ← sampleChallenges}[y = c] * uMass a * gap stmt cells₀ c a ≤
        Pr{let y ← sampleChallenges}[y = c] * ((if UniformWithin stmt cells₀ c δr then 0 else 1) + δr) := by
      intro c
      simp only [mul_assoc]
      rw [ENNReal.tsum_mul_left, tsum_uMass_gap]
      gcongr
      split_ifs with hu
      · exact hu.trans le_add_self
      · exact (tsum_uMass_sub_le_one stmt cells₀ c).trans le_self_add
    calc ∑' c, ∑' a, Pr{let y ← sampleChallenges}[y = c] * uMass a * gap stmt cells₀ c a
        ≤ ∑' c, Pr{let y ← sampleChallenges}[y = c] * ((if UniformWithin stmt cells₀ c δr then 0 else 1) + δr) :=
          ENNReal.tsum_le_tsum hc
      _ = Pr{let c ← sampleChallenges}[¬ UniformWithin stmt cells₀ c δr] + δr := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]
          congr 1
          rw [prEvent_eq_tsum_ite]
          exact tsum_congr fun c ↦ by split_ifs <;> simp_all
      _ ≤ εr + δr := add_le_add (hrev stmt w hrel) le_rfl
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
  generalize ∑' o, Pr{let y ← semL (fun _ ↦ eDist) (fullProg sim stmt D) sim.s₀ []}[y = o] *
      shortfall (fun _ ↦ eDist) coinsDist (fun x q ↦ revealAnswer (membership logRows) stmt cells₀ x q) o.2.2 = pb
    at t1 t2 hgap
  have t1' : ph ≤ pi + (εr + δr + εfs) := t1.trans (by gcongr)
  have t2' : pi ≤ ph + (εr + δr + εfs) := t2.trans (by gcongr)
  refine ⟨?_, ?_⟩
  · calc pr ≤ ph + εpcs Q := h1
      _ ≤ pi + (εr + δr + εfs) + εpcs Q := by gcongr
      _ = pi + (εpcs Q + εr + δr + εfs) := by ring
  · calc pi ≤ ph + (εr + δr + εfs) := t2'
      _ ≤ pr + εpcs Q + (εr + δr + εfs) := by gcongr
      _ = pr + (εpcs Q + εr + δr + εfs) := by ring

end PcsQuotient.EndToEnd
