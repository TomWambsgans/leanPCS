-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The route is `UniSound/FsGame.lean`'s
-- `fsLayer_of_gameV`, `UniSound/Fs128.lean`'s `hlab_uni` and `UniSound/FsGame128.lean`'s `fsLayer128_of_gameV`,
-- through `Compose`'s `rpm_le_kcS`, `knowledgeSoundness_listChainU_closed128`, `prEvent_doomF_le` and
-- `prEvent_pairTr_expL_le`, for the Keccak verifier (one setup tree, three openings, the Keccak contract's IV).
import UniKeccakSound.Fs.ProofK
import Compose.ListChainUDoom128
import Compose.FirstDoom
import Compose.SeedPair

/-!
# The Keccak verifier's Fiat–Shamir layer at `≥ 128` bits, from the coupling

**`fsLayer128K_of_gameV`**: `FsLayer128K F D Fl nV V C` from one named hypothesis, the coupling **`UniGameLeVK`**
(the Keccak experiment is dominated by `Compose.rpmGameS` of the setup's one tree, the adversary, and the composed
verifier computing the Keccak contract's IV, then the chain over the univariate encoding and the three openings;
proved from bridge facts in `CoupleK.lean`), and the deployment's numbers (`UniShapesK`, `UniNumbersK`, `UniIvK`):

* **the contract's IV** (`ivInputK`: `contractIvKWith`'s input, `ivTag`, the program's IV, the three roots, the
  shape's bytes, the five Keccak layout words and the variant's bytes, `D.programIv.length + 291` bytes): computed
  by the verifier (`uVerIvK`) as in the Keccak experiment, then moved into the two-oracle adversary
  (`expU_ivAdvK`); its log entry has neither a Merkle node's `64` bytes nor a leaf's `512` (`UniIvK`), so `C1`'s
  extractor reads the same word (`UniSound.extractorK_append`);
* **the openings once** (`prEvent_doomF_le` at `kShapes`, the plain layouts of `2^23 ..= 2^28` words at `εExact`,
  `Whir23.lean`: the setup's stack has `2^23` words at every Keccak shape), **the seed's pair**
  (`prEvent_pairTr_expL_le`, the label's first 32 bytes `name ‖ iv[0:16]` with `iv` the IV query's answer:
  `hlab_uniK`), **the chain** (`maxErrK ≤ 9952² e`): the bound `uniBound128 e` (`UniSound.le_uniBound128`, with
  one setup tree of `≤ 2^24` calls and three openings of `≤ 10122` queries in place of three and five).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK

/-! ## The Keccak contract's IV -/

/-- **The Keccak contract IV's input** (`contractIvKWith` at `keccakMain`): the tag, the program's IV, the three
roots, the shape's bytes, the five Keccak layout words and the variant's bytes. -/
def ivInputK (D : KDeployment) (roots : SetupRoots) : List UInt8 :=
  ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWordsK D.shape).flatten ++ variantBytesK keccakMain

theorem contractIvKWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (D : KDeployment) (roots : SetupRoots) :
    contractIvKWith F D.shape keccakMain D.programIv roots =
      digestBytes <$> keccak256With F (ivInputK D roots) := by
  rw [map_eq_bind_pure_comp]
  rfl

theorem length_layoutWordsK_flatten (s : UniStatement.Shape) : (layoutWordsK s).flatten.length = 160 := by
  unfold layoutWordsK
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, length_layoutWord,
    List.length_nil]

theorem length_variantBytesK_main : (variantBytesK keccakMain).length = 11 := by
  decide +kernel

theorem length_ivInputK (D : KDeployment) (roots : SetupRoots) :
    (ivInputK D roots).length = D.programIv.length + 291 := by
  simp only [ivInputK, List.length_append, length_ivTag, length_digestBytes, length_shapeBytes,
    length_layoutWordsK_flatten, length_variantBytesK_main]
  omega

/-- **The Keccak deployment's IV is short and of no Merkle length**: the program's IV not `221` bytes (the IV's
input then `512`, a leaf's), and at most `796` (the IV at most eight calls of `π`). The reference program IV
(`UniStatement.programIv`) has `32` bytes. -/
structure UniIvK (D : KDeployment) : Prop where
  ne : D.programIv.length ≠ 221
  le : D.programIv.length ≤ 796

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKCK (D : KDeployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInputK D π.roots)

/-- **The Keccak experiment's IV is the composed one**, Keccak-256 over `π`. -/
theorem ivWithK_eq (D : KDeployment) (roots : SetupRoots) :
    D.ivWith Common.queryPermutation keccakMain roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK D roots)) := by
  rw [KDeployment.ivWith, contractIvKWith_eq, hash256, callKeccak256, simulateQ_bind,
    simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

theorem uFixK_setIv (D : KDeployment) (s : Bytes32) (iv : Vector UInt8 32) (π : UPf) :
    uFixK D s (setIv iv π) = setIv iv (uFixK D s π) := rfl

/-- **The adversary of the composed game**: the Keccak adversary given the setup's roots (`rootsK`), its statement
and proof as a `UPf` (`upOf`; the IV and the roots the verifier and `uFixK` set). -/
def uAdvK (D : KDeployment) (A : KAdversary) (s : Bytes32) :
    OracleComp Common.RandomPermutationOracles UPf :=
  (fun z : Vector UInt8 32 × KeccakProof =>
    (⟨z.1, upOf z.2, Vector.replicate 32 0, rootsK D s⟩ : UPf)) <$> A (rootsK D s)

theorem cost_uAdvK (D : KDeployment) (A : KAdversary) (Q : ℕ)
    (hQ : ∀ roots, Common.QueryCostAtMost (A roots) Common.permutationCallCost Q) (s : Bytes32) :
    Common.QueryCostAtMost (uAdvK D A s) Common.permutationCallCost Q :=
  Common.isWeightBound_map _ (hQ _)

section Verifier

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- **The composed verifier with the IV**: the Keccak contract's IV, then the chain and the three openings on the
proof carrying it. -/
noncomputable def uVerIvK (π : UPf) :
    OracleComp KeccakCalls (Bytes32 × (List (List E) × List Bool)) :=
  ivKCK D π >>= fun iv => (fun v => (iv, v)) <$>
    verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
      (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) (setIv iv π)

/-- **The coupling** (`fsLayer128K_of_gameV` takes it): the Keccak experiment's break is at most as likely as the
composed random-permutation game's, of the setup's tree, the adversary (`uAdvK`) and the composed verifier with the
Keccak contract's IV (`uVerIvK`), the event read on the proof with its IV (`ivOut`), the setup's log and the
Keccak-256 evaluations of the adversary's permutation transcript. -/
def UniGameLeVK : Prop :=
  ∀ A : KAdversary,
    Pr{let z ← keccakSoundnessExperiment D keccakMain A}[KBreaksKnowledgeSoundness F D (uniExtractorK F D) z] ≤
      Pr{let z ← Common.runWithRandomPermutation
          (rpmGameS (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK D Fl nV V C hs))}[
        UniBreaksRelK D Fl nV V C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

theorem duplexVm_uVerIvK (π : UPf) : LeanVM.Rpm.DuplexVm (uVerIvK D Fl nV V C hs π) [] := by
  unfold uVerIvK ivKCK
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun iv => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_hash256 _).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_verU _ _ _ (fun π ch => duplexVm_opsRun _ _ π ch) _)
      fun _ => trivial

theorem cost_uVerIvK (hN : UniNumbersK D Fl nV V C hs) (hI : UniIvK D) (π : UPf) :
    Common.QueryCostAtMost (uVerIvK D Fl nV V C hs π) LeanVM.Rpm.hashBlocks (2 ^ 80 + 8) := by
  unfold uVerIvK ivKCK
  have hb : (ivInputK D π.roots).length / 136 + 1 ≤ 8 := by
    rw [length_ivInputK]
    have := hI.le
    omega
  refine cost_hash256_bind _ _ _ (hb.trans (by norm_num)) fun u => ?_
  refine (Common.isWeightBound_map _ (hN.verifier _)).mono ?_
  generalize (2 : ℕ) ^ 80 = a
  omega

end Verifier

/-! ## The IV moved into the adversary, in the two-oracle game -/

/-- The two-oracle adversary with the IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdvK (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (s : Bytes32) :
    OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKCK D (uFixK D s π)

theorem isTotalQueryBound_ivAdvK (D : KDeployment) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32) :
    IsTotalQueryBound (ivAdvK D A₀ s) (n + 1) := by
  unfold ivAdvK
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  simp only [ivKCK, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

section Move

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- **The IV moved into the adversary**: the two-oracle game with the IV in the verifier is, up to writing the IV
in the proof and appending its entry to the log, the experiment whose adversary computes the IV last. -/
theorem expU_ivAdvK (A₀ : Bytes32 → OracleComp KeccakCalls UPf) :
    expU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V)) (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀))
        (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) =
      (fun w => (ivOut w.1, w.2 ++ [(ivInputK D w.1.1.roots, w.1.2.1)])) <$>
        kcGameS (uSetupK D hs) (uFixK D) A₀ (uVerIvK D Fl nV V C hs) := by
  have hw : withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀) =
      withSetupG (uSetupK D hs) (uFixK D) A₀ >>= fun π => (fun iv => setIv iv π) <$> ivKCK D π := by
    simp only [withSetupG, ivAdvK, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [expU, kcGameS, hw, loggedKC, logImplKC_bind]
  simp only [uVerIvK, ivKCK, hash256, bind_assoc, pure_bind, map_bind, map_pure,
    bind_map_left, ivOut]
  rfl

end Move

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem eval_ivKCK (D : KDeployment) (π : UPf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (ivKCK D π) = viewT T (ivInputK D π.roots) := by
  simp only [ivKCK, hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_ivKCK (D : KDeployment) (π : UPf) (T : KTable) :
    (tableQueryLog (ivKCK D π) T).map Sigma.fst = [Sum.inl (ivInputK D π.roots)] := by
  simp only [ivKCK, hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last query** (`ivAdvK`:
the Keccak contract's IV of the proof the setup fixes). -/
theorem hlab_uniK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (hs : UniShapesK D) (A₀ : Bytes32 → OracleComp KeccakCalls UPf) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀)) T).map
        Sigma.fst ∧
      ((uSpecK Fl nV V).label (uView (uRoundsK Fl nV V) (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀)))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (uSetupK D hs) (uFixK D) (ivAdvK D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (uSetupK D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  refine ⟨ivInputK D (uFixK D s π).roots, ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [ivAdvK, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_ivKCK]
    exact List.mem_singleton_self _
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (ivAdvK D A₀ s) =
        setIv (viewT T (ivInputK D (uFixK D s π).roots)) π := by
      simp only [ivAdvK, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_ivKCK]
      rfl
    rw [hev, name_length]
    show (uniLabel (uView (uRoundsK Fl nV V) (uFixK D s (setIv _ π))).1).take 32 = _
    rw [uniLabel_take32]
    rfl

/-! ## The Fiat–Shamir layer -/

section Layer

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- `UniBreaksRelK` reads the transcript through its answers only. -/
theorem uniBreaksRelK_congr (z : UPf × (List (List E) × List Bool)) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : UniBreaksRelK D Fl nV V C hs (z, tr)) :
    UniBreaksRelK D Fl nV V C hs (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

theorem leafLen_uniTcK_zero : (uniTcK hs 0).leafLen = 512 := by
  unfold uniTcK
  rw [ite_eq_left rfl]
  rfl

/-- **The three openings' shapes are among `kShapes`**: each a plain layout of `2^v` words, `23 ≤ v ≤ 28`, at rate
`1/2`. -/
theorem hops_uniK : ∀ o ∈ uOpsK D Fl nV V C hs, ∃ s ∈ kShapes, s.L = o.S.L ∧ s.R = o.S.R := by
  intro o ho
  simp only [uOpsK, uniOpsK, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact kShapes_plainK _ (hs.lo 0 (by decide)) (hs.hi 0 (by decide))
  · exact kShapes_plainK _ (hs.lo 1 (by decide)) (hs.hi 1 (by decide))
  · exact kShapes_plainK _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide))

/-- **The Keccak verifier's Fiat–Shamir layer at `≥ 128` bits from the coupling with the IV in the verifier**:
`FsLayer128K` from the coupling `UniGameLeVK`, the numbers (`UniNumbersK`) and the IV (`UniIvK`), through
`knowledgeSoundness_listChainU_closed128` and its three terms bounded (`prEvent_doomF_le` at `kShapes`,
`prEvent_pairTr_expL_le`, `maxErrK_uniK`). -/
theorem fsLayer128K_of_gameV (hN : UniNumbersK D Fl nV V C hs) (hI : UniIvK D)
    (hG : UniGameLeVK D Fl nV V C hs) : FsLayer128K F D Fl nV V C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetupK D hs) (hOnly_setupK1 hs _) (setupQSK D)
    (setupQSK D * 2 ^ 32) (isTotalQueryBound_setupK1 hs _) (cost_setupK1 hs _) (uFixK D) (uAdvK D A) Q
    (cost_uAdvK D A Q hQ) (uVerIvK D Fl nV V C hs) (duplexVm_uVerIvK D Fl nV V C hs) (2 ^ 80 + 8)
    (cost_uVerIvK D Fl nV V C hs hN hI)
    (fun z tr => UniBreaksRelK D Fl nV V C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRelK_congr D Fl nV V C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128 (uSpecK Fl nV V)
    (liftPiop (uSpecK Fl nV V).K R rfl) (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)
    (fun i => uniTcK hs i) (uniCheckK D Fl nV V C) (uniGoodK D Fl nV V C) (uniGoodSK D Fl nV V C)
    (uSetupK D hs) (uFixK D) (ivAdvK D A₀) (setupQSK D) (setupQSK D + Q + 1)
    (isTotalQueryBound_setupK1 hs _) (isTotalQueryBound_ivAdvK D A₀ _ hA₀) (hok_uniK D Fl nV V C hs)
    (hcov_uniK D Fl nV V C hs) (hS_uniK D Fl nV V C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uniK D Fl nV V C R hFin π ch cs hc hl hg hn hgS)
    name (hlab_uniK D Fl nV V hs A₀)
  have hkc : Pr{let z ← (simulateQ randomOracle
        (kcGameS (uSetupK D hs) (uFixK D) A₀ (uVerIvK D Fl nV V C hs))).run' ∅}[
        UniBreaksRelK D Fl nV V C hs (ivOut z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
          (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀))
          (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)))).run' ∅}[
        BreaksOK (uSpecK Fl nV V).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK Fl nV V).K R rfl)
          (uView (uRoundsK Fl nV V)) (uniCheckK D Fl nV V C)
          (fun bs => ∀ k < (uOpsK D Fl nV V C hs).length, bs.getD k false = true) z] := by
    rw [expU_ivAdvK, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    have hb := breaksOK_of_relK D Fl nV V C hs R hpre _ hw
    have hlen : (ivInputK D w.1.1.roots).length = D.programIv.length + 291 := length_ivInputK _ _
    have h64 : (ivInputK D w.1.1.roots).length ≠ 64 := by rw [hlen]; omega
    have hl : (ivInputK D w.1.1.roots).length ≠ (uniTcK hs 0).leafLen := by
      rw [hlen, leafLen_uniTcK_zero]
      have := hI.ne
      omega
    have he := extractorK_append (uniTcK hs) (uView (uRoundsK Fl nV V)) (ivOut w.1) w.2
      (ivInputK D w.1.1.roots, w.1.2.1) h64 hl
    refine ⟨hb.1, hb.2.1, fun c hc => hb.2.2 c ?_⟩
    rw [← he]
    exact hc
  -- The run before the openings, and its queries.
  set X := preU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
    (withSetupG (uSetupK D hs) (uFixK D) (ivAdvK D A₀)) with hXdef
  have hX : IsTotalQueryBound X (setupQSK D + (setupQSK D + Q + 1) + (uSpecK Fl nV V).K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _
      (isTotalQueryBound_setupK1 hs _) (isTotalQueryBound_ivAdvK D A₀ _ hA₀))
  -- The openings, once.
  have hdoom := prEvent_doomF_le εExact kShapes kShapes_nodup (uView (uRoundsK Fl nV V))
    (uOpsK D Fl nV V C hs) (hops_uniK D Fl nV V C hs) X _ hX 10122 kShapes_QO_le
  -- The seed's pair.
  have hpair := prEvent_pairTr_expL_le (uView (uRoundsK Fl nV V)) X (uOpsK D Fl nV V C hs) _ hX
    name name_length
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS : setupQSK D ≤ 3 * 2 ^ 24 := (setupQSK_le D hs).trans (by norm_num)
  have hn := hN.chain
  have hq : ((uOpsK D Fl nV V C hs).map fun o => o.S.QO).sum ≤ 5 * 10122 :=
    (sumQO_leK D Fl nV V C hs).trans (by norm_num)
  exact le_uniBound128 e Q (setupQSK D) (uSpecK Fl nV V).K.nQ _ (uSpecK Fl nV V).nRf 10122 hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) le_rfl _ _ _ hdoom hpair (maxErrK_uniK D Fl nV V hs R e herr)

/-- `fsLayer128K_of_gameV` with the numbers from the rounds' sizes (`uniNumbersK_of`). -/
theorem fsLayer128K_of_gameV' (hnQ : (uSpecK Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK Fl nV V, r.nv ≤ 2 ^ 30) (hI : UniIvK D) (hG : UniGameLeVK D Fl nV V C hs) :
    FsLayer128K F D Fl nV V C :=
  fsLayer128K_of_gameV D Fl nV V C hs (uniNumbersK_of D Fl nV V C hs hnQ hnv) hI hG

end Layer

end UniKeccakSound

/-- info: 'UniKeccakSound.hlab_uniK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hlab_uniK

/-- info: 'UniKeccakSound.fsLayer128K_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K_of_gameV
