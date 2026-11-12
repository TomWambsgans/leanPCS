-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Fs/ExtractK3.lean`'s, `Fs/VerifierK3.lean`'s and
-- `Fs/CoupleK3.lean`'s proofs for π1-rec4 (`verifyWithK4`, the wide chain, the rate model's game `rpmGameSR`), with
-- `UniSound/FsVerifier.lean`'s chain lemmas for the wide chain.
import UniKeccakSound.Rec4.Bridge4
import UniKeccakSound.Rec4.Link4
import UniKeccakSound.Fs.CoupleK3
import UniKeccakSound.Fs.VerifierK3
import UniKeccakSound.Fs.ExtractK3

/-!
# π1-rec4's experiment and the rate model's random-permutation game, coupled

* **`uniExtractBridgeK4`**: the extractor's reading (round `0`'s message is `C1`'s root the stream names, as at
  π1-rec3);
* **`uniVerifierBridgeK4_of_walk`**: the verifier bridge from the walk (`UniWalkK4`, `UniWalkRejectK4`) and the
  chain program's roots (`UniOutRootsK4`): `verifyWithK4` is the walk then the three openings, the composed verifier
  (rate model) is the wide chain over Keccak-256's rate then the same openings (`simulateQ_verWR`);
* **`uniGameLeVK4_of`**: the coupling `UniGameLeVK4` from the setup bridge, the verifier bridge and the extractor's
  reading, as π1-rec3's (`uniGameLeVK3_of`), with `keccakSoundnessExperiment4` and `rpmGameSR`.
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## The wide chain's outcomes -/

section Chain

variable {ι : Type} {spec : OracleSpec ι}

/-- A run of the wide chain returns one answer per step and the seed's. -/
theorem length_of_mem_runMW (H : List UInt8 → OracleComp spec (Bytes32 × TailP)) :
    ∀ (y : List UInt8) (es : List (List UInt8)), ∀ ans ∈ support (ChainSpecW.runMW H y es),
      ans.length = es.length + 1
  | y, [], ans, h => by
    simp only [ChainSpecW.runMW, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl
  | y, e :: es, ans, h => by
    simp only [ChainSpecW.runMW, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rest, hrest, rfl⟩ := h
    simp [length_of_mem_runMW H _ es rest hrest]

theorem doneFits_zipW (b : Array UInt8) (pv : ℕ → ℕ) : ∀ (j o : ℕ) (rs : List RoundSpec) (ch : List (List E)),
    (hl : ch.length = rs.length) → (∀ i (h : i < ch.length), (ch[i]'h).length = (rs[i]'(by omega)).ns + 1) →
    DoneFits rs ((msgsAtW b pv j o rs).zip ch)
  | _, _, [], [], _, _ => by simp [msgsAtW, DoneFits]
  | j, o, r :: rs, c :: ch, hl, hc => by
    simp only [msgsAtW, List.zip_cons_cons, DoneFits]
    refine ⟨⟨?_, by simp [msgOfW]⟩, hc 0 (by simp), doneFits_zipW b pv _ _ rs ch (by simpa using hl)
      (fun i h => hc (i + 1) (by simp; omega))⟩
    rcases r with ⟨_ | _, nv, ns⟩ <;> simp [msgOfW]
  | _, _, [], _ :: _, hl, _ => by simp at hl
  | _, _, _ :: _, [], hl, _ => by simp at hl

/-- **An outcome of π1-rec4's wide chain completes its rounds.** -/
theorem doneFits_of_mem_chain4 (κ nV np : ℕ) (π : UPf) (ch : List (List E))
    (H : List UInt8 → OracleComp spec (Bytes32 × TailP))
    (hch : ch ∈ support ((uSpec4 κ nV np).chain H (uView4 κ nV np π).1 (uView4 κ nV np π).2)) :
    DoneFits (rec4Rounds κ nV np) (uDone4 κ nV np π ch) ∧ ch.length = (rec4Rounds κ nV np).length := by
  rw [ChainSpecW.chain, support_map] at hch
  obtain ⟨ans, hans, rfl⟩ := hch
  have hl := length_of_mem_runMW H _ _ ans hans
  rw [ChainSpecW.absorbsS, length_absorbsW] at hl
  have hlen : ((uSpec4 κ nV np).chalsOf ans).length = (rec4Rounds κ nV np).length := by
    simp only [ChainSpecW.chalsOf, List.length_map, List.length_zip, List.length_tail, hl, uSpec4_rounds]
    omega
  refine ⟨doneFits_zipW _ _ _ _ _ _ hlen (fun i h => ?_), hlen⟩
  simp only [ChainSpecW.chalsOf, List.getElem_map, List.getElem_zip, length_chalsW]
  rfl

theorem msgsAtW_getElem_fst (b : Array UInt8) (pv : ℕ → ℕ) : ∀ (j o : ℕ) (rs : List RoundSpec) (i : ℕ)
    (h : i < rs.length),
    ((msgsAtW b pv j o rs)[i]'(by rw [length_msgsAtW]; exact h)).1.isSome = (rs[i]'h).root
  | _, _, [], _, h => absurd h (by simp)
  | j, o, r :: rs, 0, _ => by
    simp only [msgsAtW, List.getElem_cons_zero, msgOfW]
    cases r.root <;> rfl
  | j, o, r :: rs, i + 1, h => by
    simp only [msgsAtW, List.getElem_cons_succ]
    exact msgsAtW_getElem_fst b pv _ _ rs i _

/-- **The root the chain reads at a round with a root is the transcript's.** -/
theorem root_at4 (κ nV np : ℕ) (π : UPf) (ch : List (List E)) (i : ℕ) (hi : i < (rec4Rounds κ nV np).length)
    (hch : ch.length = (rec4Rounds κ nV np).length)
    (hroot : ((rec4Rounds κ nV np).getD i ⟨false, 0, 0⟩).root = true) :
    ofB (((msgK (uView4 κ nV np) π i).1).getD (Vector.replicate 32 0)) =
      rootOf (((uDone4 κ nV np π ch).getD i default).1.1.getD default) := by
  have hl : i < (msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).length := by
    rw [length_msgsAtW]; exact hi
  have hs := msgsAtW_getElem_fst π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np) i hi
  rw [List.getD_eq_getElem _ _ hi] at hroot
  rw [hroot] at hs
  have e1 : msgK (uView4 κ nV np) π i = toRMsg ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np))[i]'hl) := by
    show ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).map toRMsg).getD i (none, []) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  have e2 : (uDone4 κ nV np π ch).getD i default =
      ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np))[i]'hl, ch[i]'(by omega)) := by
    show ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).zip ch).getD i default = _
    rw [List.getD_eq_getElem _ _ (by simp [length_msgsAtW]; omega), List.getElem_zip]
  rw [e1, e2]
  rcases hm : ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np))[i]'hl).1 with _ | h
  · rw [hm] at hs
    exact absurd hs (by simp)
  · simp only [toRMsg, hm, Option.map_some, Option.getD_some]
    exact Soundness.ofB_toB_root _

/-- The wide chain over a simulated hash. -/
theorem simulateQ_runMW {ι' : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec (OracleComp spec'))
    (H : List UInt8 → OracleComp spec (Bytes32 × TailP)) :
    ∀ (y : List UInt8) (es : List (List UInt8)),
      simulateQ impl (ChainSpecW.runMW H y es) = ChainSpecW.runMW (fun x => simulateQ impl (H x)) y es
  | y, [] => by simp [ChainSpecW.runMW]
  | y, e :: es => by
    simp only [ChainSpecW.runMW, simulateQ_bind, simulateQ_pure]
    congr 1
    funext a
    rw [simulateQ_runMW impl H _ es]

end Chain

/-- **The composed verifier over the permutation**: the wide chain over Keccak-256's rate, then the openings. -/
theorem simulateQ_verWR {St M : Type} (W : ChainSpecW E St) (view : UPf → St × List (RMsg E))
    (ops : List (GOp UPf E M)) (π : UPf) :
    simulateQ keccakCallsROverQueryPermutation (verWR W view ops π) =
      W.chain (hashRP Common.queryPermutation) (view π).1 (view π).2 >>= fun ch =>
        simulateQ keccakCallsOverQueryPermutation (gopsRun view ops π ch >>= fun b => pure (ch, b)) := by
  rw [verWR, simulateQ_bind]
  congr 1
  · rw [ChainSpecW.chain, ChainSpecW.chain, simulateQ_map, simulateQ_runMW]
    simp only [simulateQ_hashR]
  · funext ch
    rw [simulateQ_bind, simulateQ_liftR, simulateQ_bind]
    rfl

/-! ## The extractor's reading -/

/-- **Round `0`'s message is `C1`'s root** the stream names, its out-of-domain answer after it. -/
theorem msgK_uView4_c1 (κ nV np : ℕ) (π : UPf) : msgK (uView4 κ nV np) π 0 =
    (some (toB (c1RootOfK (kpOf π))), [scalarAt π.proof.stream (24 + 32 + 24 * 0)]) := by
  have h0 : pv4 κ 0 = 0 := by unfold pv4; rw [ite_eq_right (by omega)]
  show ((msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).map toRMsg).getD 0 (none, []) = _
  rw [show rec4Rounds κ nV np = ⟨true, 1, 3⟩ :: (kRoundsMid κ ++ [⟨true, 65, 4⟩, ⟨false, nV, 3⟩] ++
      List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) by simp [rec4Rounds]]
  simp only [msgsAtW, List.map_cons, List.getD_cons_zero, msgOfW, h0]
  rfl

/-- **The extractor's reading at π1-rec4**, with `C1`'s variables below `256`. -/
theorem uniExtractBridgeK4 (D : KDeployment) (F : KeccakVm.KeccakFlockSpec) (κ nV np : ℕ)
    (hs : UniShapesK D) (hc1 : (c1LayoutK D.shape).vars < 256) : UniExtractBridgeK4 D κ nV np hs F := by
  intro t T z q hq hrel
  have htr : Soundness.treeTr t ++ evalTr (permutationQueries T) = Soundness.trOf
      (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, Soundness.treeTr, evalTr, List.map_append]
  have h0 : extractorK (fun i => (uniTcK hs i).commit) (uView4 κ nV np)
      (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) =
      ((uniTcK hs 0).commit.cands
        (histOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB (c1RootOfK (kpOf z.1)))).map some := by
    rw [htr]
    show optC _ _ _ (msgK (uView4 κ nV np) z.1 0) = _
    rw [msgK_uView4_c1]
    rfl
  rw [h0] at hq
  have hq' : q ∈ (uniTcK hs 0).commit.cands
      (histOfTr (Soundness.trOf
        (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (tableOfTr (Soundness.trOf
        (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (toB (c1RootOfK (kpOf z.1))) := by
    obtain ⟨q', hq', he⟩ := List.mem_map.mp hq
    rw [← Option.some.inj he]
    exact hq'
  obtain ⟨st, hst, rfl⟩ := mem_uniTcK_zero hs _ _ _ q hq'
  have hμ : (c1LayoutK D.shape).vars = wvK D 0 := (wvK_zero D hc1).symm
  have hadm : Whir.Admissible (wvK D 0) logInvRate := (shapeKK hs 0 (by decide)).adm
  have hst2 : st ∈ LeanVM.Extraction.decodeStacks (wvK D 0) 1
      (c1WordK D (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (PcsQuotient.Tree.evaluations t ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) (kpOf z.1)) := by
    refine Soundness.mem_decodeStacks_congr hadm (fun p hp => ?_) st hst
    rw [c1WordK_eq_committed, hμ]
    exact Soundness.wordOfMerkle_merkleWord_eq _ _ _ _ hp
  have hrel' : D.Relation F (rowsOfBytes (rowBytes z.1.proof.stream)) z.1.input
      (kvStack D.prog (D.sizes (rowsOfBytes (rowBytes z.1.proof.stream))) D.shape
        fun i => st.toArray.getD i 0) := hrel
  rw [rowsOfBytes_rowBytes] at hrel'
  obtain ⟨st', hst', hP⟩ := exists_stack_cast hμ
    (fun f => D.Relation F (rowsOf z.1.proof.stream) z.1.input
      (kvStack D.prog (D.sizes (rowsOf z.1.proof.stream)) D.shape f)) _ st hst2 hrel'
  exact extractFromK_spec F D z.1.input _ (kpOf z.1) st' hst' hP

/-! ## The verifier bridge from the walk -/

section Rest

variable (shape : UniStatement.Shape) (roots : SetupRootsK) (proof : KeccakProof)
variable {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState)

/-- **`verifyWithK4` is the run, then `restRK`** on an accepting run's result. -/
theorem verifyWithK4_eq_rest [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) :
    verifyWithK4 P shape keccakRec4 iv roots input proof =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK4 P shape iv input.toList proof.stream keccakRec4 .point) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => restRK shape roots proof P r := by
  rw [bind_map_left]
  rfl

end Rest

/-- **THE VERIFIER BRIDGE at π1-rec4**, from the walk (`UniWalkK4`, `UniWalkRejectK4`) and the chain program's roots
(`UniOutRootsK4`). -/
theorem uniVerifierBridgeK4_of_walk (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)
    (hW : UniWalkK4 D κ nV np C) (hR : UniWalkRejectK4 D κ nV np) (hO : UniKeccakSound.UniOutRootsK4 D C) :
    UniVerifierBridgeK4 D κ nV np C hs := by
  intro π s
  rw [verifyWithK4_eq_rest]
  by_cases hlen : π.proof.stream.size = uLen4 κ nV np
  swap
  · refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb => ?_) s)).trans zero_le
    rw [mem_support_bind_iff] at hb
    obtain ⟨p, hp, hb⟩ := hb
    rw [support_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    simp only [hR π hlen o ho, Bool.not_false, ↓reduceIte, support_pure,
      Set.mem_singleton_iff] at hb
    simp [hb]
  rw [show (kpOf π).stream = π.proof.stream from rfl, hW Common.queryPermutation π hlen, bind_map_left,
    simulateQ_verWR]
  refine mono_bind_supp _ _ _ _ _ _ (fun ch hch s => ?_) s
  obtain ⟨hfits, hlch⟩ := doneFits_of_mem_chain4 κ nV np π ch _ hch
  dsimp only
  cases hacc : uAccB4 D κ nV np C π ch
  · rw [ite_eq_left (show (!false) = true from rfl), Soundness.zero_pure _ false _ (by simp) s]
    exact zero_le
  rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
  have hz : (C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).ZerosVanish (uDone4 κ nV np π ch) (uTail4 κ nV np π) :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hacc).2
  by_cases hg : GoodRK D.shape (uOut4 D κ nV np C π ch)
  swap
  · refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb hbt => ?_) s)).trans zero_le
    exact hg (restRK_good D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, ho, hm, l1, l2, l3⟩ := hg
  have hwf : WellFormedK D (uOut4 D κ nV np C π ch) := by
    refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, hm⟩
    · simp [claimsOf, ho]; exact l1
    · simp [claimsOf, ho]; exact l2
    · simp [claimsOf, ho]; exact l3
  have hcheck : uniCheck4 D κ nV np C π ch := ⟨hfits, hz, hwf⟩
  have hwo : (uOut4 D κ nV np C π ch).openings.map Prod.fst = commitments := by rw [ho]; rfl
  have e1 : ptvK (uOut4 D κ nV np C π ch) .c1 = (p1, v1) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e2 : ptvK (uOut4 D κ nV np C π ch) .c2 = (p2, v2) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e3 : ptvK (uOut4 D κ nV np C π ch) .setup = (p3, v3) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have hroots : (uOut4 D κ nV np C π ch).roots =
      (((uDone4 κ nV np π ch).getD 0 default).1.1.getD default,
        ((uDone4 κ nV np π ch).getD (28 + κ) default).1.1.getD default) :=
    hO _ _ _ _
  have hr1 : ofB (((msgK (uView4 κ nV np) π 0).1).getD (Vector.replicate 32 0)) =
      rootOf (uOut4 D κ nV np C π ch).roots.1 := by
    rw [hroots]
    exact root_at4 κ nV np π ch 0 (by rw [length_rec4Rounds]; omega) hlch (by rw [rec4Rounds_zero])
  have hr2 : ofB (((msgK (uView4 κ nV np) π (28 + κ)).1).getD (Vector.replicate 32 0)) =
      rootOf (uOut4 D κ nV np C π ch).roots.2 := by
    rw [hroots]
    exact root_at4 κ nV np π ch _ (by rw [length_rec4Rounds]; omega) hlch (by
      show ((uniK (rec4Rounds κ nV np)).spec (28 + κ)).root = true
      rw [rec4Rounds_spec_c2])
  rw [restRK_unroll D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ p1 v1 p2 v2 p3 v3 ho hm,
    pcsOpenK_eq, pcsOpenK_eq, pcsOpenK_eq]
  unfold uOps4 uniOps4
  -- C1
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show ver4 D κ nV np C 0 _ π ch = _
    unfold ver4 ood4
    simp only [comK]
    rw [e1]
    simp only [GOp.root, op4]
    rw [hr1]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- C2
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show ver4 D κ nV np C 1 _ π ch = _
    unfold ver4 ood4
    simp only [comK]
    rw [e2]
    simp only [GOp.root, op4]
    rw [hr2]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- the setup
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show ver4 D κ nV np C 2 _ π ch = _
    unfold ver4 ood4
    simp only [comK]
    rw [e3]
    rw [show GOp.root (uView4 κ nV np)
        (op4 κ nV np C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) (colFK D))) π =
        toB π.roots.bytecode from rfl, Soundness.ofB_toB_root]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  rw [seqAnd, sim_gopsRun_nil, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk3 : k < 3 := hk
  interval_cases k <;> rfl

/-! ## The coupling -/

theorem contractIvKWith_eq4 {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : KeccakState → m KeccakState) (D : KDeployment) (roots : SetupRootsK) :
    contractIvKWith P D.shape keccakRec4 D.programIv roots = digestBytes <$> keccak256With P (ivInputK4 D roots) := by
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The Keccak experiment's IV at π1-rec4 is the composed one**, Keccak-256 over `π`. -/
theorem ivWithK_eq4 (D : KDeployment) (roots : SetupRootsK) :
    D.ivWith Common.queryPermutation keccakRec4 roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK4 D roots)) := by
  rw [KDeployment.ivWith, contractIvKWith_eq4, hash256, callKeccak256, simulateQ_bind,
    simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

theorem keccakSoundnessExperiment4_eq (D : KDeployment) (A : KAdversary) :
    keccakSoundnessExperiment4 D A = Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
      D.verifierWith4 Common.queryPermutation (D.setupRoots a.1) a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome)) := by
  unfold keccakSoundnessExperiment4 prefixUK
  simp only [bind_assoc, pure_bind]

theorem rpmGameSR_eqK4 (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)
    (hS : UniSetupBridgeK D hs) (A : KAdversary) :
    Common.runWithRandomPermutation
        (rpmGameSR (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK4 D κ nV np C hs)) =
      Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
        simulateQ keccakCallsROverQueryPermutation (uVerIvK4 D κ nV np C hs (piOfK D a)) >>= fun v =>
          pure ((piOfK D a, v), Soundness.treeTr a.1, a.2.2)) := by
  unfold rpmGameSR prefixUK
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_uAdvK, rootsK_toB, uFixK_toB]
  rfl

section Step

variable (D : KDeployment) (F : KeccakVm.KeccakFlockSpec) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np)
  (hs : UniShapesK D)

/-- **One outcome of the setup and the adversary** (π1-rec4). -/
theorem step_leK4 (hV : UniVerifierBridgeK4 D κ nV np C hs) (hX : UniExtractBridgeK4 D κ nV np hs F)
    (a : LeanVM.Prover.Tree × ((Vector UInt8 32 × KeccakProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges KeccakState) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (D.verifierWith4 Common.queryPermutation (D.setupRoots a.1) a.2.1.1 a.2.1.2)).run' s}[
        KBreaksKnowledgeSoundness F D (uniExtractorK F D)
          (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2))] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsROverQueryPermutation (uVerIvK4 D κ nV np C hs (piOfK D a)))).run' s}[
        UniBreaksRel4 D κ nV np C hs F
          (ivOut (piOfK D a, v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2))] := by
  have hL : D.verifierWith4 Common.queryPermutation (D.setupRoots a.1) a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK4 D (D.setupRoots a.1))) >>= fun iv =>
        verifyWithK4 Common.queryPermutation D.shape keccakRec4 iv.toList (D.setupRoots a.1) a.2.1.1 a.2.1.2 := by
    rw [KDeployment.verifierWith4, ivWithK_eq4, bind_map_left]
  have hR : simulateQ keccakCallsROverQueryPermutation (uVerIvK4 D κ nV np C hs (piOfK D a)) =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK4 D (D.setupRoots a.1))) >>= fun iv =>
        (fun v => (iv, v)) <$> simulateQ keccakCallsROverQueryPermutation
          (verWR (uSpec4 κ nV np) (uView4 κ nV np) (uOps4 D κ nV np C hs) (setIv iv (piOfK D a))) := by
    rw [uVerIvK4, simulateQ_bind, simulateQ_liftR]
    simp only [simulateQ_map]
    rfl
  rw [hL, hR]
  refine Soundness.mono_bind Common.lazyRandomPermutationOracles _ _ _ _ _ (fun iv s' => ?_) s
  by_cases hext : ∃ q, uniExtractorK F D a.2.1.1 (PcsQuotient.Tree.evaluations a.1) a.2.2 a.2.1.2 = some q ∧
      D.Relation F a.2.1.2.rows a.2.1.1 q
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)) zero_le
    intro acc _ hb
    exact hb.2 hext
  have hnone : ∀ (v : List (List E) × List Bool), ∀ c ∈ extractorK (fun i => (uniTcK hs i).commit)
      (uView4 κ nV np)
      ((setIv iv (piOfK D a), v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2)),
      ∀ q, c = some q → ¬ RelK F D (uSt4 κ nV np (setIv iv (piOfK D a))) q := by
    intro v c hc q hq hrel
    subst hq
    exact hext (hX a.1 a.2.2 (setIv iv (piOfK D a), v) q hc hrel)
  have hacc := hV (setIv iv (piOfK D a)) s'
  calc _ ≤ Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
          (verifyWithK4 Common.queryPermutation D.shape keccakRec4 iv.toList (D.setupRoots a.1) a.2.1.1
            a.2.1.2)).run' s'}[b = true] := prEvent_mono _ _ _ fun b hb => hb.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [run'_map_lazyK, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v⟩

end Step

/-- **The coupling at π1-rec4 from the bridge facts.** -/
theorem uniGameLeVK4_of (D : KDeployment) (F : KeccakVm.KeccakFlockSpec) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np)
    (hs : UniShapesK D) (hS : UniSetupBridgeK D hs) (hV : UniVerifierBridgeK4 D κ nV np C hs)
    (hX : UniExtractBridgeK4 D κ nV np hs F) : UniGameLeVK4 D κ nV np C hs F := by
  intro A
  rw [keccakSoundnessExperiment4_eq D A, rpmGameSR_eqK4 D κ nV np C hs hS A]
  exact Soundness.prEvent_le_of_continuations (prefixUK D A)
    (fun a => D.verifierWith4 Common.queryPermutation (D.setupRoots a.1) a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsROverQueryPermutation (uVerIvK4 D κ nV np C hs (piOfK D a)))
    (fun a acc => (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome))
    (fun a v => ((piOfK D a, v), Soundness.treeTr a.1, a.2.2))
    (KBreaksKnowledgeSoundness F D (uniExtractorK F D))
    (fun z => UniBreaksRel4 D κ nV np C hs F (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step_leK4 D F κ nV np C hs hV hX a s

/-- **The coupling at π1-rec4, from the walk**: the setup bridge and `C1`'s variables below `256`
(`LayoutVarsSmallK`), the walk and the chain program's roots. -/
theorem uniGameLeVK4_holds (D : KDeployment) (F : KeccakVm.KeccakFlockSpec) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np)
    (hs : UniShapesK D) (hsmall : LayoutVarsSmallK D) (hW : UniWalkK4 D κ nV np C)
    (hR : UniWalkRejectK4 D κ nV np) (hO : UniKeccakSound.UniOutRootsK4 D C) : UniGameLeVK4 D κ nV np C hs F :=
  uniGameLeVK4_of D F κ nV np C hs (uniSetupBridgeK D hs hsmall.setup)
    (uniVerifierBridgeK4_of_walk D κ nV np C hs hW hR hO) (uniExtractBridgeK4 D F κ nV np hs hsmall.c1)

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.uniGameLeVK4_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniGameLeVK4_holds
