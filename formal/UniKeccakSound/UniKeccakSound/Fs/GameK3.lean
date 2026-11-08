-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/GameK.lean` at π1-rec3's
-- shape (`keccakRec3`: the contract's IV binds the variant), as `UniSound/Rec3/FsGame128_3.lean`.
import UniKeccakSound.Fs.ProofK3
import UniKeccakSound.Fs.GameK

/-!
# The Keccak verifier's Fiat–Shamir layer at π1-rec3's shape, from the coupling

**`fsLayer128K3_of_gameV`**: `FsLayer128K3 F D F3 nV np C` from the coupling **`UniGameLeVK3`** and the numbers, as
`GameK.lean`'s `fsLayer128K_of_gameV`: the contract's IV at `keccakRec3` (`ivInputK3`: the variant's bytes
`"keccak-vm" ‖ 3 ‖ 3`, so the same `D.programIv.length + 291` bytes and the same `UniIvK`), computed by the verifier
(`uVerIvK3`) and moved into the two-oracle adversary (`expU_ivAdvK3`); the openings once at `kShapes`, the seed's
pair (`hlab_uniK3`), the chain (`maxErrK_uniK3`): the bound `uniBound128 e`. The adversary (`uAdvK`), the setup's
roots (`uFixK`) and `UniIvK` are the main line's.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK

/-! ## The Keccak contract's IV -/

/-- **The Keccak contract IV's input** (`contractIvKWith` at `keccakRec3`): the tag, the program's IV, the three
roots, the shape's bytes, the five Keccak layout words and the variant's bytes. -/
def ivInputK3 (D : KDeployment) (roots : SetupRoots) : List UInt8 :=
  ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWordsK D.shape).flatten ++ variantBytesK keccakRec3

theorem contractIvKWith_eq3 {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (D : KDeployment) (roots : SetupRoots) :
    contractIvKWith F D.shape keccakRec3 D.programIv roots =
      digestBytes <$> keccak256With F (ivInputK3 D roots) := by
  rw [map_eq_bind_pure_comp]
  rfl

theorem length_variantBytesK_rec3 : (variantBytesK keccakRec3).length = 11 := by
  decide +kernel

theorem length_ivInputK3 (D : KDeployment) (roots : SetupRoots) :
    (ivInputK3 D roots).length = D.programIv.length + 291 := by
  simp only [ivInputK3, List.length_append, length_ivTag, length_digestBytes, length_shapeBytes,
    length_layoutWordsK_flatten, length_variantBytesK_rec3]
  omega

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKCK3 (D : KDeployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInputK3 D π.roots)

/-- **The Keccak experiment's IV is the composed one**, Keccak-256 over `π`. -/
theorem ivWithK_eq3 (D : KDeployment) (roots : SetupRoots) :
    D.ivWith Common.queryPermutation keccakRec3 roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK3 D roots)) := by
  rw [KDeployment.ivWith, contractIvKWith_eq3, hash256, callKeccak256, simulateQ_bind,
    simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

section Verifier

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- **The composed verifier with the IV**: the Keccak contract's IV, then the chain and the three openings on the
proof carrying it. -/
noncomputable def uVerIvK3 (π : UPf) :
    OracleComp KeccakCalls (Bytes32 × (List (List E) × List Bool)) :=
  ivKCK3 D π >>= fun iv => (fun v => (iv, v)) <$>
    verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
      (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) (setIv iv π)

/-- **The coupling** (`fsLayer128K3_of_gameV` takes it): the Keccak experiment's break is at most as likely as the
composed random-permutation game's, of the setup's tree, the adversary (`uAdvK`) and the composed verifier with the
Keccak contract's IV (`uVerIvK3`), the event read on the proof with its IV (`ivOut`), the setup's log and the
Keccak-256 evaluations of the adversary's permutation transcript. -/
def UniGameLeVK3 : Prop :=
  ∀ A : KAdversary,
    Pr{let z ← keccakSoundnessExperiment D keccakRec3 A}[KBreaksKnowledgeSoundness F D (uniExtractorK F D) z] ≤
      Pr{let z ← Common.runWithRandomPermutation
          (rpmGameS (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK3 D F3 nV np C hs))}[
        UniBreaksRelK3 D F3 nV np C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

theorem duplexVm_uVerIvK3 (π : UPf) : LeanVM.Rpm.DuplexVm (uVerIvK3 D F3 nV np C hs π) [] := by
  unfold uVerIvK3 ivKCK3
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun iv => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_hash256 _).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_verU _ _ _ (fun π ch => duplexVm_opsRun _ _ π ch) _)
      fun _ => trivial

theorem cost_uVerIvK3 (hN : UniNumbersK3 D F3 nV np C hs) (hI : UniIvK D) (π : UPf) :
    Common.QueryCostAtMost (uVerIvK3 D F3 nV np C hs π) LeanVM.Rpm.hashBlocks (2 ^ 80 + 8) := by
  unfold uVerIvK3 ivKCK3
  have hb : (ivInputK3 D π.roots).length / 136 + 1 ≤ 8 := by
    rw [length_ivInputK3]
    have := hI.le
    omega
  refine cost_hash256_bind _ _ _ (hb.trans (by norm_num)) fun u => ?_
  refine (Common.isWeightBound_map _ (hN.verifier _)).mono ?_
  generalize (2 : ℕ) ^ 80 = a
  omega

end Verifier

/-! ## The IV moved into the adversary, in the two-oracle game -/

/-- The two-oracle adversary with the IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdvK3 (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (s : Bytes32) :
    OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKCK3 D (uFixK D s π)

theorem isTotalQueryBound_ivAdvK3 (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32) :
    IsTotalQueryBound (ivAdvK3 D A₀ s) (n + 1) := by
  unfold ivAdvK3
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  simp only [ivKCK3, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

section Move

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- **The IV moved into the adversary**: the two-oracle game with the IV in the verifier is, up to writing the IV
in the proof and appending its entry to the log, the experiment whose adversary computes the IV last. -/
theorem expU_ivAdvK3 (A₀ : Bytes32 → OracleComp KeccakCalls UPf) :
    expU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np)) (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀))
        (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) =
      (fun w => (ivOut w.1, w.2 ++ [(ivInputK3 D w.1.1.roots, w.1.2.1)])) <$>
        kcGameS (uSetupK D hs) (uFixK D) A₀ (uVerIvK3 D F3 nV np C hs) := by
  have hw : withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀) =
      withSetupG (uSetupK D hs) (uFixK D) A₀ >>= fun π => (fun iv => setIv iv π) <$> ivKCK3 D π := by
    simp only [withSetupG, ivAdvK3, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [expU, kcGameS, hw, loggedKC, logImplKC_bind]
  simp only [uVerIvK3, ivKCK3, hash256, bind_assoc, pure_bind, map_bind, map_pure,
    bind_map_left, ivOut]
  rfl

end Move

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem eval_ivKCK3 (D : KDeployment) (π : UPf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (ivKCK3 D π) = viewT T (ivInputK3 D π.roots) := by
  simp only [ivKCK3, hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_ivKCK3 (D : KDeployment) (π : UPf) (T : KTable) :
    (tableQueryLog (ivKCK3 D π) T).map Sigma.fst = [Sum.inl (ivInputK3 D π.roots)] := by
  simp only [ivKCK3, hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last query** (`ivAdvK3`:
the Keccak contract's IV of the proof the setup fixes). -/
theorem hlab_uniK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (hs : UniShapesK D) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀)) T).map
        Sigma.fst ∧
      ((uSpecK3 F3 nV np).label (uView (uRoundsK3 F3 nV np) (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀)))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (uSetupK D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  refine ⟨ivInputK3 D (uFixK D s π).roots, ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [ivAdvK3, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_ivKCK3]
    exact List.mem_singleton_self _
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (ivAdvK3 D A₀ s) =
        setIv (viewT T (ivInputK3 D (uFixK D s π).roots)) π := by
      simp only [ivAdvK3, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_ivKCK3]
      rfl
    rw [hev, name_length]
    show (uniLabel (uView (uRoundsK3 F3 nV np) (uFixK D s (setIv _ π))).1).take 32 = _
    rw [uniLabel_take32]
    rfl

/-! ## The Fiat–Shamir layer -/

section Layer

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- `UniBreaksRelK3` reads the transcript through its answers only. -/
theorem uniBreaksRelK3_congr (z : UPf × (List (List E) × List Bool)) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : UniBreaksRelK3 D F3 nV np C hs (z, tr)) :
    UniBreaksRelK3 D F3 nV np C hs (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-- **The three openings' shapes are among `kShapes`**: each a plain layout of `2^v` words, `23 ≤ v ≤ 28`, at rate
`1/2`. -/
theorem hops_uniK3 : ∀ o ∈ uOpsK3 D F3 nV np C hs, ∃ s ∈ kShapes, s.L = o.S.L ∧ s.R = o.S.R := by
  intro o ho
  simp only [uOpsK3, uniOpsK3, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact kShapes_plainK _ (hs.lo 0 (by decide)) (hs.hi 0 (by decide))
  · exact kShapes_plainK _ (hs.lo 1 (by decide)) (hs.hi 1 (by decide))
  · exact kShapes_plainK _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide))

/-- **The Keccak verifier's Fiat–Shamir layer at `≥ 128` bits from the coupling with the IV in the verifier**:
`FsLayer128K3` from the coupling `UniGameLeVK3`, the numbers (`UniNumbersK3`) and the IV (`UniIvK`), through
`knowledgeSoundness_listChainU_closed128` and its three terms bounded (`prEvent_doomF_le` at `kShapes`,
`prEvent_pairTr_expL_le`, `maxErrK_uniK3`). -/
theorem fsLayer128K3_of_gameV (hN : UniNumbersK3 D F3 nV np C hs) (hI : UniIvK D)
    (hG : UniGameLeVK3 D F3 nV np C hs) : FsLayer128K3 F D F3 nV np C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetupK D hs) (hOnly_setupK1 hs _) (setupQSK D)
    (setupQSK D * 2 ^ 32) (isTotalQueryBound_setupK1 hs _) (cost_setupK1 hs _) (uFixK D) (uAdvK D A) Q
    (cost_uAdvK D A Q hQ) (uVerIvK3 D F3 nV np C hs) (duplexVm_uVerIvK3 D F3 nV np C hs) (2 ^ 80 + 8)
    (cost_uVerIvK3 D F3 nV np C hs hN hI)
    (fun z tr => UniBreaksRelK3 D F3 nV np C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRelK3_congr D F3 nV np C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128 (uSpecK3 F3 nV np)
    (liftPiop (uSpecK3 F3 nV np).K R rfl) (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)
    (fun i => uniTcK hs i) (uniCheckK3 D F3 nV np C) (uniGoodK3 D F3 nV np C) (uniGoodSK3 D F3 nV np C)
    (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀) (setupQSK D) (setupQSK D + Q + 1)
    (isTotalQueryBound_setupK1 hs _) (isTotalQueryBound_ivAdvK3 D A₀ _ hA₀) (hok_uniK3 D F3 nV np C hs)
    (hcov_uniK3 D F3 nV np C hs) (hS_uniK3 D F3 nV np C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uniK3 D F3 nV np C R hFin π ch cs hc hl hg hn hgS)
    name (hlab_uniK3 D F3 nV np hs A₀)
  have hkc : Pr{let z ← (simulateQ randomOracle
        (kcGameS (uSetupK D hs) (uFixK D) A₀ (uVerIvK3 D F3 nV np C hs))).run' ∅}[
        UniBreaksRelK3 D F3 nV np C hs (ivOut z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
          (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀))
          (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)))).run' ∅}[
        BreaksOK (uSpecK3 F3 nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK3 F3 nV np).K R rfl)
          (uView (uRoundsK3 F3 nV np)) (uniCheckK3 D F3 nV np C)
          (fun bs => ∀ k < (uOpsK3 D F3 nV np C hs).length, bs.getD k false = true) z] := by
    rw [expU_ivAdvK3, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    have hb := breaksOK_of_relK3 D F3 nV np C hs R hpre _ hw
    have hlen : (ivInputK3 D w.1.1.roots).length = D.programIv.length + 291 := length_ivInputK3 _ _
    have h64 : (ivInputK3 D w.1.1.roots).length ≠ 64 := by rw [hlen]; omega
    have hl : (ivInputK3 D w.1.1.roots).length ≠ (uniTcK hs 0).leafLen := by
      rw [hlen, leafLen_uniTcK_zero]
      have := hI.ne
      omega
    have he := extractorK_append (uniTcK hs) (uView (uRoundsK3 F3 nV np)) (ivOut w.1) w.2
      (ivInputK3 D w.1.1.roots, w.1.2.1) h64 hl
    refine ⟨hb.1, hb.2.1, fun c hc => hb.2.2 c ?_⟩
    rw [← he]
    exact hc
  -- The run before the openings, and its queries.
  set X := preU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
    (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK3 D A₀)) with hXdef
  have hX : IsTotalQueryBound X (setupQSK D + (setupQSK D + Q + 1) + (uSpecK3 F3 nV np).K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _
      (isTotalQueryBound_setupK1 hs _) (isTotalQueryBound_ivAdvK3 D A₀ _ hA₀))
  -- The openings, once.
  have hdoom := prEvent_doomF_le εExact kShapes kShapes_nodup (uView (uRoundsK3 F3 nV np))
    (uOpsK3 D F3 nV np C hs) (hops_uniK3 D F3 nV np C hs) X _ hX 10122 kShapes_QO_le
  -- The seed's pair.
  have hpair := prEvent_pairTr_expL_le (uView (uRoundsK3 F3 nV np)) X (uOpsK3 D F3 nV np C hs) _ hX
    name name_length
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS : setupQSK D ≤ 3 * 2 ^ 24 := (setupQSK_le D hs).trans (by norm_num)
  have hn := hN.chain
  have hq : ((uOpsK3 D F3 nV np C hs).map fun o => o.S.QO).sum ≤ 5 * 10122 :=
    (sumQO_leK3 D F3 nV np C hs).trans (by norm_num)
  exact le_uniBound128 e Q (setupQSK D) (uSpecK3 F3 nV np).K.nQ _ (uSpecK3 F3 nV np).nRf 10122 hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) le_rfl _ _ _ hdoom hpair (maxErrK_uniK3 D F3 nV np hs R e herr)

/-- `fsLayer128K3_of_gameV` with the numbers from the rounds' sizes (`uniNumbersK3_of`). -/
theorem fsLayer128K3_of_gameV' (hnQ : (uSpecK3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK3 F3 nV np, r.nv ≤ 2 ^ 30) (hI : UniIvK D) (hG : UniGameLeVK3 D F3 nV np C hs) :
    FsLayer128K3 F D F3 nV np C :=
  fsLayer128K3_of_gameV D F3 nV np C hs (uniNumbersK3_of D F3 nV np C hs hnQ hnv) hI hG

end Layer

end UniKeccakSound

/-- info: 'UniKeccakSound.hlab_uniK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hlab_uniK3

/-- info: 'UniKeccakSound.fsLayer128K3_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K3_of_gameV
