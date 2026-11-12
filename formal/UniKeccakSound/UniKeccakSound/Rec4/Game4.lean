-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Fs/GameK3.lean`'s `fsLayer128K3_of_gameV` (and
-- `Fs/ProofK3.lean`'s `uniNumbersK3_of`, `Compose/Coupling.lean`'s `prEvent_run'_loggedKC`) for π1-rec4's verifier
-- in the rate model.
import UniKeccakSound.Rec4.Bridge4

/-!
# π1-rec4's Fiat–Shamir layer, from the coupling

**`fsLayer128K4_of_gameV`**: `FsLayer128K4 F D κ nV np C` from the coupling **`UniGameLeVK4`**, the numbers
(`UniNumbersK4`) and the IV (`UniIvK`), as `Fs/GameK3.lean`'s `fsLayer128K3_of_gameV`, in the rate model:

1. the coupling bounds the Keccak experiment's break by the random-permutation game whose verifier reads
   Keccak-256's rate (`rpmGameSR`, with `uVerIvK4`);
2. `rpm_le_kcSR` moves it to the rate model's random oracles (`kcGameSR`), at `(QSπ + Q + QVπ)² / 2^508`; the
   verifier keeps the duplex discipline (`duplexVmR_uVerIvK4`) and makes at most `2^80 + 8` calls of `π`
   (`cost_uVerIvK4`: the IV's at most eight, the composed verifier's `2^80`, `uniNumbersK4_of`);
3. the IV moves into the adversary (`ivAdvR`, `expLGR_ivAdvR`): the rate-model game with the IV in the verifier is,
   up to writing the IV in the proof and appending its entry to the log, the first component of `expLGR`'s run
   (its outer log dropped: `prEvent_run'_loggedKCR`), whose adversary computes the IV last;
4. `knowledgeSoundness_listChainW_closed128R` bounds that run's break, the seed's first 32 bytes `name ‖ iv[0:16]`
   with `iv` an answer the adversary asked at every table of tails (`hlab_uni4R`, from the two-oracle
   `hlab_uniK4` through `instR_liftR`), the openings once (`hU_uni4`), the chain's errors `9952² · e`
   (`maxErrK_uni4`); `le_uniBound128` closes the arithmetic.

**`fsLayer128K4_of_gameV'`**: the same with the numbers from the rounds' sizes (`(uSpec4 κ nV np).nQ ≤ 2^10`, every
round at most `2^30` scalars).
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak LeanVM.Semantics
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## The IV's input -/

theorem length_variantBytesK_rec4 : (variantBytesK keccakRec4).length = 11 := by
  decide +kernel

theorem length_ivInputK4 (D : KDeployment) (roots : SetupRootsK) :
    (ivInputK4 D roots).length = D.programIv.length + 91 := by
  simp only [ivInputK4, List.length_append, length_ivTag, length_digestBytes, length_shapeBytes,
    length_elementBytes24, length_variantBytesK_rec4]
  omega

/-! ## The composed verifier's discipline and calls of `π` -/

theorem duplexVmR_runMW : ∀ (y : List UInt8) (es : List (List UInt8)) (h : List KeccakState),
    DuplexVmR (ChainSpecW.runMW Compose.hashR y es) h
  | y, [], h => by
    simp only [ChainSpecW.runMW]
    exact duplexVmR_hashR_bind y _ h fun _ => trivial
  | y, e :: es, h => by
    simp only [ChainSpecW.runMW]
    refine duplexVmR_hashR_bind y _ h fun u => ?_
    exact DuplexVmR.bind (duplexVmR_runMW _ es h) fun _ => trivial

theorem duplexVmR_chain {St : Type} (W : ChainSpecW E St) (s : St) (ms : List (RMsg E)) :
    DuplexVmR (W.chain Compose.hashR s ms) [] := by
  unfold ChainSpecW.chain
  rw [map_eq_bind_pure_comp]
  exact DuplexVmR.bind (duplexVmR_runMW _ _ _) fun _ => trivial

theorem allQ_runMWR : ∀ (y : List UInt8) (es : List (List UInt8)), y.length ≤ 2 ^ 39 + 9 →
    (∀ e ∈ es, 32 + e.length ≤ 2 ^ 39 + 9) →
      AllQueriesSatisfy (ChainSpecW.runMW Compose.hashR y es) fun t => hashBlocksR t ≤ 2 ^ 32
  | y, [], hy, _ => by
    simp only [ChainSpecW.runMW, Compose.hashR, callKeccak256R, bind_assoc, pure_bind]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨LeanVM.Rpm.hashBlocks_le_of_short (t := .inl y) hy, fun _ => trivial⟩
  | y, e :: es, hy, he => by
    simp only [ChainSpecW.runMW, Compose.hashR, callKeccak256R, bind_assoc, pure_bind]
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨LeanVM.Rpm.hashBlocks_le_of_short (t := .inl y) hy, fun u => ?_⟩
    refine allQueriesSatisfy_bind (allQ_runMWR _ es ?_ fun e' he' => he e' (List.mem_cons_of_mem _ he'))
      fun _ => trivial
    rw [length_stepIn]
    exact he e List.mem_cons_self

theorem length_uniEncW (p : ℕ) (m : RMsg E) : (uniEncW p m).length ≤ 32 + 24 * m.2.length := by
  rcases m with ⟨_ | r, l⟩ <;> simp [uniEncW] <;> omega

/-- The bytes a step absorbs: at most `24 + 32 + 24 B` for messages of at most `B` scalars. -/
theorem length_mem_absorbsW4 (κ nV np : ℕ) (s : FSt) (B : ℕ) : ∀ (i : ℕ) (rs : List RoundSpec)
    (ms : List (RMsg E)), (∀ m ∈ ms, m.2.length ≤ B) →
      ∀ e ∈ absorbsW ((uSpec4 κ nV np).encAt s) i rs ms, e.length ≤ 24 + 32 + 24 * B
  | _, [], _, _, e, he => by simp [absorbsW] at he
  | i, r :: rs, ms, hm, e, he => by
    simp only [absorbsW, List.mem_cons] at he
    rcases he with rfl | he
    · have hB : (ms.headD (none, [])).2.length ≤ B := by
        rcases ms with _ | ⟨m, ms⟩
        · simp
        · exact hm m List.mem_cons_self
      have h2 : 24 * (ms.headD (none, [])).2.length ≤ 24 * B := Nat.mul_le_mul_left 24 hB
      unfold ChainSpecW.encAt
      split_ifs with hi
      · subst hi
        have h1 := length_uniEncW (pv4 κ 0) (ms.headD (none, []))
        have he : ((uSpec4 κ nV np).enc 0 (ms.headD (none, []))).length =
            (uniEncW (pv4 κ 0) (ms.headD (none, []))).length := rfl
        rw [List.length_append]
        have hp : ((uSpec4 κ nV np).pre s).length = 24 := by
          show s.2.2.toList.length = 24
          simp
        omega
      · have h1 := length_uniEncW (pv4 κ i) (ms.headD (none, []))
        have he : ((uSpec4 κ nV np).enc i (ms.headD (none, []))).length =
            (uniEncW (pv4 κ i) (ms.headD (none, []))).length := rfl
        omega
    · exact length_mem_absorbsW4 κ nV np s B (i + 1) rs ms.tail
        (fun m hm' => hm m (List.mem_of_mem_tail hm')) e he

section Numbers

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)

/-- **π1-rec4's numbers**: the chain's queries below `2^10`, the composed verifier's calls of `π` (rate model)
below `2^80`. -/
structure UniNumbersK4 : Prop where
  chain : (uSpec4 κ nV np).nQ ≤ 2 ^ 10
  verifier : ∀ π, Common.QueryCostAtMost (verWR (uSpec4 κ nV np) (uView4 κ nV np) (uOps4 D κ nV np C hs) π)
    hashBlocksR (2 ^ 80)

/-- **The numbers from the rounds' sizes**: at most `2^10` chain queries, every round at most `2^30` scalars. -/
theorem uniNumbersK4_of (hnQ : (uSpec4 κ nV np).nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ rec4Rounds κ nV np, r.nv ≤ 2 ^ 30) : UniNumbersK4 D κ nV np C hs := by
  refine ⟨hnQ, fun π => ?_⟩
  have hmsg : ∀ m ∈ (uView4 κ nV np π).2, m.2.length ≤ 2 ^ 30 := by
    intro m hm
    have hfit : FitsAll (rec4Rounds κ nV np) (uView4 κ nV np π).2 := fitsAll_uViewW _ _ π
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have hl := hfit.length_eq
    have := fitsAll_getD hfit i (by omega)
    have hi' : i < (rec4Rounds κ nV np).length := by omega
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this.2, List.getD_eq_getElem _ _ hi']
    exact hnv _ (List.getElem_mem hi')
  have hch : Common.QueryCostAtMost ((uSpec4 κ nV np).chain Compose.hashR (uView4 κ nV np π).1 (uView4 κ nV np π).2)
      hashBlocksR ((uSpec4 κ nV np).nQ * 2 ^ 32) := by
    unfold ChainSpecW.chain
    refine Common.isWeightBound_map _ (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocksR (2 ^ 32) ?_ ?_)
    · have h := isTotalQueryBound_runMWR ((uSpec4 κ nV np).label (uView4 κ nV np π).1)
        ((uSpec4 κ nV np).absorbsS (uView4 κ nV np π).1 (uSpec4 κ nV np).K.rounds (uView4 κ nV np π).2)
      rw [ChainSpecW.absorbsS, length_absorbsW] at h
      exact h
    · refine allQ_runMWR _ _ ?_ ?_
      · show (uniLabel _).length ≤ _
        simp [uniLabel, name_length]
      · intro e he
        have := length_mem_absorbsW4 κ nV np _ (2 ^ 30) 0 _ _ hmsg e he
        omega
  have hops : ∀ ch, Common.QueryCostAtMost (gopsRun (uView4 κ nV np) (uOps4 D κ nV np C hs) π ch)
      LeanVM.Rpm.hashBlocks ((3 * 10122) * 2 ^ 32) := fun ch =>
    LeanVM.Rpm.isWeightBound_of_isTotalQueryBound LeanVM.Rpm.hashBlocks (2 ^ 32)
      ((isTotalQueryBound_gopsRun _ _ _ _).mono (sumQO_le4 D κ nV np C hs))
      ((allQ_gopsRunK _ _ _ _ fun o ho r π' ch' => by
        simp only [uOps4, uniOps4, List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> exact allQ_pcsOpenC _ _ _ _ _ _).mono
        fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)
  unfold verWR
  refine (hch.bind fun ch => (cost_liftR (hops ch)).bind fun b =>
    Common.isWeightBound_pure (ch, b) hashBlocksR 0).mono ?_
  have h1 : (uSpec4 κ nV np).nQ * 2 ^ 32 ≤ 2 ^ 10 * 2 ^ 32 := Nat.mul_le_mul_right _ hnQ
  calc (uSpec4 κ nV np).nQ * 2 ^ 32 + (3 * 10122 * 2 ^ 32 + 0)
      ≤ 2 ^ 10 * 2 ^ 32 + (3 * 10122 * 2 ^ 32 + 0) := Nat.add_le_add_right h1 _
    _ ≤ 2 ^ 80 := by norm_num

theorem duplexVmR_uVerIvK4 (π : UPf) : DuplexVmR (uVerIvK4 D κ nV np C hs π) [] := by
  unfold uVerIvK4 ivKCK4
  refine DuplexVmR.bind (duplexVmR_liftR ?_) fun iv => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_hash256 _).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    refine DuplexVmR.bind ?_ fun _ => trivial
    unfold verWR
    exact DuplexVmR.bind (duplexVmR_chain _ _ _) fun ch =>
      DuplexVmR.bind (duplexVmR_liftR (duplexVm_gopsRun _ _ _ _)) fun _ => trivial

theorem cost_uVerIvK4 (hN : UniNumbersK4 D κ nV np C hs) (hI : UniIvK D) (π : UPf) :
    Common.QueryCostAtMost (uVerIvK4 D κ nV np C hs π) hashBlocksR (2 ^ 80 + 8) := by
  unfold uVerIvK4
  have hb : (ivInputK4 D (skOf D π.roots)).length / 136 + 1 ≤ 8 := by
    rw [length_ivInputK4]
    have := hI.le
    omega
  have h1 : Common.QueryCostAtMost (simulateQ liftR (ivKCK4 D π)) hashBlocksR 8 := by
    refine cost_liftR ?_
    have h := cost_hash256_bind (ivInputK4 D (skOf D π.roots)) pure 8 hb fun _ => trivial
    rw [bind_pure] at h
    exact h
  refine (h1.bind fun iv => Common.isWeightBound_map _ (hN.verifier (setIv iv π))).mono ?_
  rw [Nat.add_comm]

end Numbers

/-! ## The IV moved into the adversary, in the rate model -/

/-- The two-oracle adversary with the IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdvK4 (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (s : Bytes32) :
    OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKCK4 D (uFixK D s π)

/-- **The rate-model adversary with the IV**: `A₀`, then the IV (Keccak-256's digest, lifted) of the proof the
setup fixes. -/
def ivAdvR (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCallsR UPf) (s : Bytes32) :
    OracleComp KeccakCallsR UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> simulateQ liftR (ivKCK4 D (uFixK D s π))

theorem isTotalQueryBound_ivAdvR (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCallsR UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32) :
    IsTotalQueryBound (ivAdvR D A₀ s) (n + 1) := by
  unfold ivAdvR
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  refine UniKeccakSound.Rec4.isTotalQueryBound_liftR _ 1 ?_
  simp only [ivKCK4, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

/-- **The split of the rate-model adversary with the IV** is the two-oracle one of the split adversary. -/
theorem instR_ivAdvR (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCallsR UPf) (τ : List UInt8 → TailP) :
    (fun s => simulateQ (instR τ) (ivAdvR D A₀ s)) = ivAdvK4 D (fun s => simulateQ (instR τ) (A₀ s)) := by
  funext s
  simp only [ivAdvR, ivAdvK4, simulateQ_bind, simulateQ_map, instR_liftR]

theorem logImplKCR_bind {α β : Type} (oa : OracleComp KeccakCallsR α)
    (f : α → OracleComp KeccakCallsR β) (l : Transcript) :
    (simulateQ logImplKCR (oa >>= f)).run l =
      (simulateQ logImplKCR oa).run l >>= fun p => (simulateQ logImplKCR (f p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

theorem liftR_hash256 (x : List UInt8) :
    simulateQ liftR (hash256 x) = (fun u : Digest × TailP => toB u.1) <$> callKeccak256R x := by
  rw [hash256, callKeccak256, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, liftR, callKeccak256R, bind_map_left]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The IV's call, logged**: its entry is the input and the digest. -/
theorem logged_liftR_hash256 (x : List UInt8) (l : Transcript) :
    (simulateQ logImplKCR (simulateQ liftR (hash256 x))).run l =
      (fun d => (d, l ++ [(x, d)])) <$> simulateQ liftR (hash256 x) := by
  rw [liftR_hash256, simulateQ_map, StateT.run_map, callKeccak256R, simulateQ_spec_query]
  show (fun p : (Digest × TailP) × Transcript => (toB p.1.1, p.2)) <$>
      ((fun u => (u, l ++ (inlEntryR ⟨.inl x, u⟩).toList)) <$> _) = _
  rw [Functor.map_map, Functor.map_map]
  rfl

/-- **Logging changes no event of the run**: an event of the logged run's result is the unlogged run's. -/
theorem prEvent_run'_loggedKCR {α : Type} (v : OracleComp KeccakCallsR α) (tr : Transcript)
    (c : KeccakCallsR.QueryCache) (E : α → Prop) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKCR v).run tr)).run' c}[E z.1] =
      Pr{let z ← (simulateQ randomOracle v).run' c}[E z] := by
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  refine (prEvent_map _ (fun z : (α × Transcript) × KeccakCallsR.QueryCache => (z.1.1, z.2))
    (fun w => E w.1)).symm.trans ?_
  rw [map_run_loggedKCR]

theorem run'_simulateQ_mapR {α β : Type} (Y : OracleComp KeccakCallsR α) (f : α → β)
    (c : KeccakCallsR.QueryCache) :
    (simulateQ randomOracle (f <$> Y)).run' c = f <$> (simulateQ randomOracle Y).run' c := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    Functor.map_map]

section Move

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)

/-- **The IV moved into the adversary** (rate model): the run before `expLGR`'s outer log, whose adversary computes
the IV last, is the game with the IV in the verifier, up to writing the IV in the proof and appending its entry to
the log. -/
theorem preWideR_ivAdvR (A₀ : Bytes32 → OracleComp KeccakCallsR UPf) :
    (preWideR (uSpec4 κ nV np) (uView4 κ nV np) (withSetupGR (uSetupK D hs) (uFixK D) (ivAdvR D A₀)) >>=
        fun x => opsOut x <$> simulateQ liftR (gopsRun (uView4 κ nV np) (uOps4 D κ nV np C hs) x.1 x.2.1)) =
      (fun w => (ivOut w.1, w.2 ++ [(ivInputK4 D (skOf D w.1.1.roots), w.1.2.1)])) <$>
        kcGameSR (uSetupK D hs) (uFixK D) A₀ (uVerIvK4 D κ nV np C hs) := by
  have hw : withSetupGR (uSetupK D hs) (uFixK D) (ivAdvR D A₀) =
      withSetupGR (uSetupK D hs) (uFixK D) A₀ >>= fun π =>
        (fun iv => setIv iv π) <$> simulateQ liftR (ivKCK4 D π) := by
    simp only [withSetupGR, ivAdvR, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [preWideR, kcGameSR, hw]
  simp only [loggedKCR]
  rw [logImplKCR_bind]
  simp only [bind_assoc, map_bind]
  refine bind_congr fun p => ?_
  rw [simulateQ_map, StateT.run_map, ivKCK4, logged_liftR_hash256]
  simp only [uVerIvK4, ivKCK4, verWR, bind_map_left, map_bind, bind_assoc, pure_bind, map_pure,
    Functor.map_map]
  refine bind_congr fun d => ?_
  refine bind_congr fun ch => ?_
  simp only [ivOut, map_eq_bind_pure_comp]
  rfl

end Move

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem eval_ivKCK4 (D : KDeployment) (π : UPf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (ivKCK4 D π) = viewT T (ivInputK4 D (skOf D π.roots)) := by
  simp only [ivKCK4, hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_ivKCK4 (D : KDeployment) (π : UPf) (T : KTable) :
    (tableQueryLog (ivKCK4 D π) T).map Sigma.fst = [Sum.inl (ivInputK4 D (skOf D π.roots))] := by
  simp only [ivKCK4, hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last query** (`ivAdvK4`:
the Keccak contract's IV at `keccakRec4` of the proof the setup fixes). -/
theorem hlab_uniK4 (D : KDeployment) (κ nV np : ℕ) (hs : UniShapesK D)
    (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK4 D A₀)) T).map
        Sigma.fst ∧
      ((uSpec4 κ nV np).label (uView4 κ nV np (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK4 D A₀)))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (uSetupK D hs) (uFixK D) (ivAdvK4 D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (uSetupK D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  refine ⟨ivInputK4 D (skOf D (uFixK D s π).roots), ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [ivAdvK4, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_ivKCK4]
    exact List.mem_singleton_self _
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (ivAdvK4 D A₀ s) =
        setIv (viewT T (ivInputK4 D (skOf D (uFixK D s π).roots))) π := by
      simp only [ivAdvK4, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_ivKCK4]
      rfl
    rw [hev, name_length]
    show (uniLabel (uView4 κ nV np (uFixK D s (setIv _ π))).1).take 32 = _
    rw [uniLabel_take32]
    rfl

/-- **The seed's pair at every table of tails** (`knowledgeSoundness_listChainW_closed128R`'s `hlab`): the split
rate-model adversary with the IV is the two-oracle one (`instR_ivAdvR`). -/
theorem hlab_uni4R (D : KDeployment) (κ nV np : ℕ) (hs : UniShapesK D)
    (A₀ : Bytes32 → OracleComp KeccakCallsR UPf) (τ : List UInt8 → TailP) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetupK D hs) (uFixK D)
        (fun s => simulateQ (instR τ) (ivAdvR D A₀ s))) T).map Sigma.fst ∧
      ((uSpec4 κ nV np).label (uView4 κ nV np (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetupK D hs) (uFixK D) (fun s => simulateQ (instR τ) (ivAdvR D A₀ s))))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  rw [instR_ivAdvR]
  exact hlab_uniK4 D κ nV np hs _ T

/-! ## The Fiat–Shamir layer -/

section Layer

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)

/-- `UniBreaksRel4` reads the transcript through its answers only. -/
theorem uniBreaksRel4_congr {F : KeccakVm.KeccakFlockSpec} (z : UPf × (List (List E) × List Bool))
    (tr tr' : Transcript) (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : UniBreaksRel4 D κ nV np C hs F (z, tr)) :
    UniBreaksRel4 D κ nV np C hs F (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-- **π1-rec4's Fiat–Shamir layer at `≥ 128` bits from the coupling with the IV in the verifier**: `FsLayer128K4`
from the coupling `UniGameLeVK4`, the numbers (`UniNumbersK4`) and the IV (`UniIvK`), through `rpm_le_kcSR` and
`knowledgeSoundness_listChainW_closed128R` (the openings once, `hU_uni4`; the chain's errors, `maxErrK_uni4`). -/
theorem fsLayer128K4_of_gameV {F : KeccakVm.KeccakFlockSpec} (hN : UniNumbersK4 D κ nV np C hs) (hI : UniIvK D)
    (hG : UniGameLeVK4 D κ nV np C hs F) : FsLayer128K4 F D κ nV np C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcSR (uSetupK D hs) (hOnly_setupK1 hs _) (setupQSK D)
    (setupQSK D * 2 ^ 32) (isTotalQueryBound_setupK1 hs _) (cost_setupK1 hs _) (uFixK D) (uAdvK D A) Q
    (cost_uAdvK D A Q hQ) (uVerIvK4 D κ nV np C hs) (duplexVmR_uVerIvK4 D κ nV np C hs) (2 ^ 80 + 8)
    (cost_uVerIvK4 D κ nV np C hs hN hI)
    (fun z tr => UniBreaksRel4 D κ nV np C hs F (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRel4_congr D κ nV np C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainW_closed128R (uSpec4 κ nV np)
    (liftPiop (uSpec4 κ nV np).K R rfl) (uView4 κ nV np) (uOps4 D κ nV np C hs)
    (fun i => uniTcK hs i) (uniCheck4 D κ nV np C) (uniGood4 D κ nV np C) (uniGoodS4 D κ nV np C)
    (uSetupK D hs) (uFixK D) (ivAdvR D A₀) (setupQSK D) (setupQSK D + Q + 1)
    (isTotalQueryBound_setupK1 hs _) (isTotalQueryBound_ivAdvR D A₀ _ hA₀) (hok_uni4 D κ nV np C hs)
    (hcov_uni4 D κ nV np C hs) (hS_uni4 D κ nV np C hs) (fun π _ _ => fitsAll_uViewW _ _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni4 D κ nV np C R hFin π ch cs hc hl hg hn hgS)
    name name_length (hlab_uni4R D κ nV np hs A₀) _ (hU_uni4 D κ nV np C hs)
  have hkc : Pr{let z ← (simulateQ randomOracle
        (kcGameSR (uSetupK D hs) (uFixK D) A₀ (uVerIvK4 D κ nV np C hs))).run' ∅}[
        UniBreaksRel4 D κ nV np C hs F (ivOut z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expLGR (uView4 κ nV np)
          (preWideR (uSpec4 κ nV np) (uView4 κ nV np) (withSetupGR (uSetupK D hs) (uFixK D) (ivAdvR D A₀)))
          (uOps4 D κ nV np C hs))).run' ∅}[
        BreaksOK (uSpec4 κ nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpec4 κ nV np).K R rfl)
          (uView4 κ nV np) (uniCheck4 D κ nV np C)
          (fun bs => ∀ k < (uOps4 D κ nV np C hs).length, bs.getD k false = true) z.1] := by
    rw [expLGR, prEvent_run'_loggedKCR, preWideR_ivAdvR, run'_simulateQ_mapR, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    have hb := breaksOK_of_rel4 D κ nV np C hs R hpre _ hw
    have hlen : (ivInputK4 D (skOf D w.1.1.roots)).length = D.programIv.length + 91 := length_ivInputK4 _ _
    have h64 : (ivInputK4 D (skOf D w.1.1.roots)).length ≠ 64 := by rw [hlen]; omega
    have hl : (ivInputK4 D (skOf D w.1.1.roots)).length ≠ (uniTcK hs 0).leafLen := by
      rw [hlen, leafLen_uniTcK_zero]
      have := hI.ne
      omega
    have he := extractorK_append (uniTcK hs) (uView4 κ nV np) (ivOut w.1) w.2
      (ivInputK4 D (skOf D w.1.1.roots), w.1.2.1) h64 hl
    refine ⟨hb.1, hb.2.1, fun c hc => hb.2.2 c ?_⟩
    rw [← he]
    exact hc
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS : setupQSK D ≤ 3 * 2 ^ 24 := (setupQSK_le D hs).trans (by norm_num)
  have hn := hN.chain
  have hq : ((uOps4 D κ nV np C hs).map fun o => o.QO).sum ≤ 5 * 10122 :=
    (sumQO_le4 D κ nV np C hs).trans (by norm_num)
  exact le_uniBound128 e Q (setupQSK D) (uSpec4 κ nV np).nQ _ (uSpec4 κ nV np).nRf 10122 hS hn hq
    (show (6 : ℕ) ≤ 6 from le_rfl) le_rfl _ _ _ (le_of_eq rfl) le_rfl (maxErrK_uni4 D κ nV np hs R e herr)

/-- `fsLayer128K4_of_gameV` with the numbers from the rounds' sizes (`uniNumbersK4_of`). -/
theorem fsLayer128K4_of_gameV' {F : KeccakVm.KeccakFlockSpec} (hnQ : (uSpec4 κ nV np).nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ rec4Rounds κ nV np, r.nv ≤ 2 ^ 30) (hI : UniIvK D) (hG : UniGameLeVK4 D κ nV np C hs F) :
    FsLayer128K4 F D κ nV np C :=
  fsLayer128K4_of_gameV D κ nV np C hs (uniNumbersK4_of D κ nV np C hs hnQ hnv) hI hG

end Layer

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.preWideR_ivAdvR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.preWideR_ivAdvR

/-- info: 'UniKeccakSound.Rec4.uniNumbersK4_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniNumbersK4_of

/-- info: 'UniKeccakSound.Rec4.fsLayer128K4_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.fsLayer128K4_of_gameV

/-- info: 'UniKeccakSound.Rec4.fsLayer128K4_of_gameV'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.fsLayer128K4_of_gameV'
