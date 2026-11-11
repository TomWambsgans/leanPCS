-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsGame.lean`
-- (`duplexVm_uVerIv`, `cost_uVerIv`, `isTotalQueryBound_ivAdv`, `expU_ivAdv`, `extractorK_append`,
-- `uniBreaksRel_congr`), `Fs128.lean` (`hlab_uni`) and `FsCost.lean` (`uniNumbers_of`) to π2's composed verifier.
import RecCompose.FsOps
import RecCompose.FsWalk
import RecCompose.FsBytes
import UniSound.FsCost
import UniSound.FsGame

/-!
# π2's composed verifier: its calls, its IV moved into the adversary, the seed

The facts the assembly of π2's Fiat–Shamir layer takes about the composed verifier (`p2Ver`) and its IV:

* **the lengths** of what it hashes: the circuit's encoding (`cc_encoding_length`, `24464` bytes, from its parts'
  lengths and the data's list lengths only), σ's and κ's inputs (`4 · 2^24`, `8 · 2^24` bytes), the digest's
  (`24528`), the IV's (`137`); the chain's queries (`nQ_p2 = 6`);
* **`duplexVm_p2Ver`**, **`cost_p2Ver`**: the verifier uses only the two calls, and calls `π` at most `2^49` times
  (every query short: at most `80986` queries of at most `2^32` blocks);
* **the IV moved into the adversary** (`expU_p2IvAdv`, `isTotalQueryBound_p2IvAdv`): the game with the IV in the
  verifier is the one whose adversary computes it last, its log four entries longer (`ivLog`), none of a Merkle
  node's `64` or a leaf's `512` bytes, so the extractor reads the same word (`extractorK_ivLog`);
* **the seed** (`hlab_p2`): the label's first `32` bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's
  last query;
* `p2BreaksRel_congr`: the composed event reads the transcript through its answers only.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

/-! ## The circuit's encoding -/

theorem length_le64 (n : ℕ) : (le64 n).length = 8 := by simp [le64]

theorem length_coeff (c : Coeff) : c.encoding.length = 32 := by
  simp [Coeff.encoding, length_le64]

/-- A linear form's encoding's length. -/
def linLen (l : Lin) : ℕ := 8 + 40 * l.terms.length + (match l.constant with | none => 8 | some _ => 40)

/-- A formula's encoding's length. -/
def formLen (f : Formula) : ℕ :=
  linLen f.lin + 8 + (f.products.map fun p => 32 + linLen p.2.1 + linLen p.2.2).sum

theorem length_lin (l : Lin) : l.encoding.length = linLen l := by
  rcases l with ⟨terms, constant⟩
  unfold Lin.encoding linLen
  have ht : (terms.flatMap fun t ↦ t.1.encoding ++ le64 t.2).length = 40 * terms.length := by
    rw [List.length_flatMap]
    have : (terms.map fun t ↦ (t.1.encoding ++ le64 t.2).length) = terms.map fun _ ↦ 40 := by
      apply List.map_congr_left
      intro t _
      simp [length_coeff, length_le64]
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  cases constant <;> simp [ht, length_le64, length_coeff] <;> omega

theorem length_formula (f : Formula) :
    (f.lin.encoding ++ le64 f.products.length ++
      f.products.flatMap fun p ↦ p.1.encoding ++ p.2.1.encoding ++ p.2.2.encoding).length = formLen f := by
  unfold formLen
  rw [List.length_append, List.length_append, length_lin, length_le64, List.length_flatMap]
  congr 2
  apply List.map_congr_left
  intro p _
  simp only [List.length_append, length_coeff, length_lin, Nat.add_assoc]

theorem length_flatMap_const {α : Type} (l : List α) (f : α → List UInt8) (k : ℕ) (h : ∀ a, (f a).length = k) :
    (l.flatMap f).length = k * l.length := by
  rw [List.length_flatMap, List.map_congr_left (fun a _ ↦ h a), List.map_const', List.sum_replicate, smul_eq_mul,
    Nat.mul_comm]

theorem formulas_len : (cc.formulas.map formLen).sum = 16728 := by decide +kernel

theorem publicTerms_len : (cc.publicTerms.map fun t ↦ 8 + linLen t.value).sum = 1992 := by decide +kernel

theorem pairs_length : cc.pairs.length = 134 := by decide +kernel

theorem reads_length : cc.reads.length = 21 := by decide +kernel

/-- **The circuit's encoding has `24464` bytes** (`Circuit::digest`'s bytes before the setup columns' hashes). -/
theorem cc_encoding_length : cc.encoding.length = 24464 := by
  unfold RecStatement.Circuit.encoding
  simp only [List.length_append, length_le64]
  rw [List.length_flatMap, List.map_congr_left (fun f _ ↦ length_formula f), formulas_len,
    length_flatMap_const _ _ 40 (fun p ↦ by simp [length_le64]), pairs_length,
    length_flatMap_const _ _ 16 (fun rd ↦ by cases rd <;> simp [length_le64]), reads_length, List.length_flatMap,
    List.map_congr_left (fun t _ ↦ by rw [List.length_append, length_le64, length_lin]), publicTerms_len]

/-! ## The IV's inputs -/

theorem length_ivTag : RecStatement.ivTag.length = 16 := by decide +kernel

theorem length_digestBytes' (d : Digest) : (digestBytes d).length = 32 := UniSound.length_digestBytes d

theorem length_pi1IvAt (D : RecDeployment) (r : UniKeccak.SetupRootsK) : (D.pi1IvAt r).length = 32 :=
  RecDeployment.pi1IvAt_length D r

theorem length_elementBytes24 (x : E) : (UniKeccak.elementBytes24 x).length = 24 := by
  simp [UniKeccak.elementBytes24, FsBytes.length_elementWord]

theorem length_ivIn (D : RecDeployment) (roots : RecSetupRoots) (d : Bytes32) : (ivIn D roots d).length = 137 := by
  simp only [ivIn, List.length_append, length_ivTag, length_pi1IvAt, length_digestBytes', Vector.length_toList,
    length_elementBytes24, List.length_singleton]

theorem length_sigmaBytes (c : Pi2Circuit) : (sigmaBytes c).length = 4 * c.n := by
  rw [sigmaBytes, length_flatMap_const _ _ 4 (fun i ↦ by simp [length_le64]), List.length_range]

theorem length_kappaBytes (c : Pi2Circuit) : (kappaBytes c).length = 8 * c.n := by
  rw [kappaBytes, length_flatMap_const _ _ 8 (fun i ↦ length_le64 _), List.length_range]

theorem length_digIn (c : Pi2Circuit) (sg kp : Bytes32) : (digIn c sg kp).length = c.circuit.encoding.length + 64 := by
  simp only [digIn, List.length_append, Vector.length_toList]

section Real

variable {D : RecDeployment} (hD : RecDeployment.Real D)
include hD

theorem circuitAt_circuit (r : UniKeccak.SetupRootsK) : (D.circuitAt r).circuit = cc := hD.1 _

theorem circuitAt_n (r : UniKeccak.SetupRootsK) : (D.circuitAt r).n = 2 ^ 24 := by
  unfold Pi2Circuit.n
  rw [circuitAt_circuit hD]
  rfl

theorem length_sigma_real (r : UniKeccak.SetupRootsK) : (sigmaBytes (D.circuitAt r)).length = 4 * 2 ^ 24 := by
  rw [length_sigmaBytes, circuitAt_n hD]

theorem length_kappa_real (r : UniKeccak.SetupRootsK) : (kappaBytes (D.circuitAt r)).length = 8 * 2 ^ 24 := by
  rw [length_kappaBytes, circuitAt_n hD]

theorem length_digIn_real (r : UniKeccak.SetupRootsK) (sg kp : Bytes32) :
    (digIn (D.circuitAt r) sg kp).length = 24528 := by
  rw [length_digIn, circuitAt_circuit hD, cc_encoding_length]

end Real

/-! ## The chain's queries -/

/-- **The chain asks `6` queries**: the seed, then `3 + 1 + 1` steps. -/
theorem nQ_p2 : pi2Spec.K.nQ = 6 := rfl

/-! ## The IV's calls -/

theorem eval_hash256 (T : KTable) (x : List UInt8) :
    evalWithAnswerFn (QueryImpl.ofFn T) (hash256 x) = viewT T x := by
  simp only [hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_hash256 (T : KTable) (x : List UInt8) :
    (tableQueryLog (hash256 x) T).map Sigma.fst = [Sum.inl x] := by
  simp only [hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

theorem eval_p2IvKC4 (D : RecDeployment) (π : P2Pf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (p2IvKC4 D π) =
      let c := D.circuitAt (p2Roots π).pi1
      let sg := viewT T (sigmaBytes c)
      let kp := viewT T (kappaBytes c)
      let d := viewT T (digIn c sg kp)
      (sg, kp, d, viewT T (ivIn D (p2Roots π) d)) := by
  simp only [p2IvKC4, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_hash256]

theorem log_p2IvKC4 (D : RecDeployment) (π : P2Pf) (T : KTable) :
    (tableQueryLog (p2IvKC4 D π) T).map Sigma.fst =
      let c := D.circuitAt (p2Roots π).pi1
      let sg := viewT T (sigmaBytes c)
      let kp := viewT T (kappaBytes c)
      let d := viewT T (digIn c sg kp)
      [Sum.inl (sigmaBytes c), Sum.inl (kappaBytes c), Sum.inl (digIn c sg kp), Sum.inl (ivIn D (p2Roots π) d)] := by
  simp only [p2IvKC4, tableQueryLog_bind, tableQueryLog_pure, List.map_append, log_hash256, eval_hash256,
    List.append_nil, List.cons_append, List.nil_append]

theorem hOnly_p2IvKC4 (D : RecDeployment) (π : P2Pf) : LeanVM.Rpm.HOnly (p2IvKC4 D π) :=
  (hOnly_hash256 _).bind fun _ => (hOnly_hash256 _).bind fun _ => (hOnly_hash256 _).bind fun _ =>
    (hOnly_hash256 _).bind fun _ => trivial

theorem isTotalQueryBound_p2IvKC4 (D : RecDeployment) (π : P2Pf) : IsTotalQueryBound (p2IvKC4 D π) 4 := by
  simp only [p2IvKC4, hash256, callKeccak256, bind_assoc, pure_bind]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
    isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
      isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
        isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩⟩⟩⟩

/-- **The composed verifier uses only Keccak-256's sponge and Keccak-f[1600] through it.** -/
theorem duplexVm_p2Ver (D : RecDeployment) (π : P2Pf) : LeanVM.Rpm.DuplexVm (p2Ver D π) [] := by
  unfold p2Ver
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun x => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_p2IvKC4 D π).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_verU _ _ _ (fun π ch => duplexVm_gopsRun _ _ π ch) _)
      fun _ => trivial

/-- **The adversary with the IV asks four more queries.** -/
theorem isTotalQueryBound_p2IvAdv (D : RecDeployment) (A₀ : SOut → OracleComp KeccakCalls P2Pf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : SOut) : IsTotalQueryBound (p2IvAdv D A₀ s) (n + 4) := by
  unfold p2IvAdv
  exact isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_p2IvKC4 D _)

/-! ## The event reads the transcript's answers only -/

/-- **`P2BreaksRel` reads the transcript through its answers only.** -/
theorem p2BreaksRel_congr (D : RecDeployment) (P : RecSetupRoots → Pi2St → Stk → Prop)
    (z : P2Pf × (List (List E) × List Bool)) (tr tr' : Transcript) (h : ∀ x, lookTr tr x = lookTr tr' x)
    (hz : P2BreaksRel D P (z, tr)) : P2BreaksRel D P (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-! ## The IV's log leaves the extractor's word -/

theorem p2Tc_leafLen : (p2Tc 0).leafLen = 512 := by
  rw [p2Tc_zero]
  rfl

/-- **The extractor reads the same word after the IV's log**: none of its four entries has a Merkle node's `64` or a
leaf's `512` bytes. -/
theorem extractorK_ivLog (D : RecDeployment) (hD : RecDeployment.Real D) (z : P2Pf × (List (List E) × List Bool))
    (tr : Transcript) (π : P2Pf) (x : Bytes32 × Bytes32 × Bytes32 × Bytes32) :
    extractorK (fun i => (p2Tc i).commit) p2View (z, tr ++ ivLog D π x) =
      extractorK (fun i => (p2Tc i).commit) p2View (z, tr) := by
  have hs := length_sigma_real hD (p2Roots π).pi1
  have hk := length_kappa_real hD (p2Roots π).pi1
  have hd := length_digIn_real hD (p2Roots π).pi1 x.1 x.2.1
  have hi := length_ivIn D (p2Roots π) x.2.2.1
  have hl := p2Tc_leafLen
  have e : tr ++ ivLog D π x = (((tr ++ [(sigmaBytes (D.circuitAt (p2Roots π).pi1), x.1)]) ++
      [(kappaBytes (D.circuitAt (p2Roots π).pi1), x.2.1)]) ++
      [(digIn (D.circuitAt (p2Roots π).pi1) x.1 x.2.1, x.2.2.1)]) ++ [(ivIn D (p2Roots π) x.2.2.1, x.2.2.2)] := by
    simp [ivLog]
  rw [e, UniSound.extractorK_append p2Tc p2View z _ _ (by rw [hi]; decide) (by rw [hi, hl]; decide),
    UniSound.extractorK_append p2Tc p2View z _ _ (by rw [hd]; decide) (by rw [hd, hl]; decide),
    UniSound.extractorK_append p2Tc p2View z _ _ (by rw [hk]; decide) (by rw [hk, hl]; decide),
    UniSound.extractorK_append p2Tc p2View z _ _ (by rw [hs]; decide) (by rw [hs, hl]; decide)]

/-! ## The IV moved into the adversary -/

theorem logImplKC_call_bind {α : Type} (x : List UInt8) (k : Digest → OracleComp KeccakCalls α) (l : Transcript) :
    (simulateQ logImplKC (callKeccak256 x >>= k)).run l =
      callKeccak256 x >>= fun u => (simulateQ logImplKC (k u)).run (l ++ [(x, toB u)]) := by
  rw [callKeccak256, loggedKC_run_query_bind]
  rfl

theorem logImplKC_p2IvKC4 {β : Type} (D : RecDeployment) (π : P2Pf)
    (g : Bytes32 × Bytes32 × Bytes32 × Bytes32 → β) (l : Transcript) :
    (simulateQ logImplKC (g <$> p2IvKC4 D π)).run l =
      p2IvKC4 D π >>= fun x => pure (g x, l ++ ivLog D π x) := by
  simp only [p2IvKC4, hash256, map_bind, bind_assoc, pure_bind, map_pure, logImplKC_call_bind, simulateQ_pure,
    StateT.run_pure, ivLog, List.append_assoc, List.cons_append, List.nil_append]

/-- **The IV moved into the adversary**: the game with π2's IV in the verifier is, up to writing the IV in the proof
and appending its four entries to the log, the experiment whose adversary computes the IV last. -/
theorem expU_p2IvAdv (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1)
    (A₀ : SOut → OracleComp KeccakCalls P2Pf) :
    expU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) (gopsRun p2View (p2Ops D)) =
      (fun w => (ivOut2 w.1, w.2 ++ ivLog D w.1.1 w.1.2.1)) <$> kcGameS (p2Setup D hs) p2Fix A₀ (p2Ver D) := by
  have hw : withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀) =
      withSetupG (p2Setup D hs) p2Fix A₀ >>= fun π => (fun x => setIv2 x.2.2.2 π) <$> p2IvKC4 D π := by
    simp only [withSetupG, p2IvAdv, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [expU, kcGameS, hw, loggedKC, UniSound.logImplKC_bind]
  simp only [logImplKC_p2IvKC4, p2Ver, bind_assoc, pure_bind, map_bind, map_pure, bind_map_left, ivOut2]
  rfl

/-! ## The composed verifier's calls of `π` -/

/-- The openings' query counts: `8 · 10122` (`Q`'s three in one opening). -/
theorem sumQO_p2 (D : RecDeployment) : ((p2Ops D).map fun o => o.QO).sum = 80976 := by
  simp [p2Ops, p2Pcs5, PcsOp.gop, qOp]

/-- **A PCS claim's opening makes short queries only** (`UniKeccakSound.allQ_pcsOpenC`). -/
theorem allQ_pcsOp (o : PcsOp) (r : Digest) (π : P2Pf) (ch : List (List E)) :
    AllQueriesSatisfy (o.gop.ver r π ch) Short := by
  show AllQueriesSatisfy (o.ver r π ch) Short
  unfold PcsOp.ver
  split
  · trivial
  · exact UniKeccakSound.allQ_pcsOpenC _ _ _ _ _ _

/-- **The composition's openings make short queries only.** -/
theorem allQ_p2Ops (D : RecDeployment) : ∀ o ∈ p2Ops D, ∀ r π ch, AllQueriesSatisfy (o.ver r π ch) Short := by
  intro o ho r π ch
  simp only [p2Ops, p2Pcs5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact allQ_pcsOp _ r π ch
  · exact allQ_pcsOp _ r π ch
  · exact allQ_pcsOp _ r π ch
  · exact allQ_pcsOp _ r π ch
  · exact allQ_pcsOp _ r π ch
  · exact allQueriesSatisfy_bind (allQ_pcsOp qIdOp r π ch) fun _ =>
      allQueriesSatisfy_bind (allQ_pcsOp qPushOp r π ch) fun _ =>
        allQueriesSatisfy_bind (allQ_pcsOp qSumOp r π ch) fun _ => LeanVM.Rpm.allQ_pure _

/-- The bytes a step absorbs: at most `520 + 32 + 24 B` for messages of at most `B` scalars. -/
theorem length_mem_absorbsI_p2 (s : FSt2) (B : ℕ) : ∀ (i : ℕ) (rs : List RoundSpec)
    (ms : List (RMsg E)), (∀ m ∈ ms, m.2.length ≤ B) →
      ∀ e ∈ absorbsI (pi2Spec.encAt s) i rs ms, e.length ≤ pLen + 32 + 24 * B
  | _, [], _, _, e, he => by simp [absorbsI] at he
  | i, r :: rs, ms, hm, e, he => by
    simp only [absorbsI, List.mem_cons, List.mem_append, List.mem_replicate] at he
    rcases he with rfl | ⟨-, rfl⟩ | he
    · have hB : (ms.headD (none, [])).2.length ≤ B := by
        rcases ms with _ | ⟨m, ms⟩
        · simp
        · exact hm m List.mem_cons_self
      have h1 := UniSound.length_uniEnc (ms.headD (none, []))
      have h2 : 24 * (ms.headD (none, [])).2.length ≤ 24 * B := Nat.mul_le_mul_left 24 hB
      unfold ChainSpecU.encAt
      have he : (pi2Spec.enc (ms.headD (none, []))).length = (UniSound.uniEnc (ms.headD (none, []))).length := rfl
      split_ifs
      · rw [List.length_append]
        have hp : (pi2Spec.pre s).length = pLen := by
          show s.2.2.toList.length = pLen
          simp
        omega
      · omega
    · simp
    · exact length_mem_absorbsI_p2 s B (i + 1) rs ms.tail (fun m hm' => hm m (List.mem_of_mem_tail hm')) e he

theorem allQ_hash256' {x : List UInt8} (hx : x.length ≤ 2 ^ 32) : AllQueriesSatisfy (hash256 x) Short :=
  UniSound.allQ_hash256 (hx.trans (by norm_num))

/-- **The composed verifier calls `π` at most `2^49` times**: at most `4 + 6 + 80976` queries (the IV's, the chain's,
the eight openings'), each short. -/
theorem cost_p2Ver (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) :
    Common.QueryCostAtMost (p2Ver D π) LeanVM.Rpm.hashBlocks (2 ^ 49) := by
  have htot : IsTotalQueryBound (p2Ver D π) (4 + (6 + 80976)) := by
    unfold p2Ver
    refine isTotalQueryBound_bind (isTotalQueryBound_p2IvKC4 D π) fun x =>
      (isQueryBound_map_iff _ _ _ _ _).mpr ?_
    unfold verU
    refine IsTotalQueryBound.mono (isTotalQueryBound_bind (isTotalQueryBound_chainU _ _ _) fun ch =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_gopsRun _ _ _ _) fun _ => trivial) ?_
    rw [nQ_p2, sumQO_p2 D]
  have hiv : AllQueriesSatisfy (p2IvKC4 D π) Short := by
    unfold p2IvKC4
    refine allQueriesSatisfy_bind (allQ_hash256' (by rw [length_sigma_real hD]; norm_num)) fun sg => ?_
    refine allQueriesSatisfy_bind (allQ_hash256' (by rw [length_kappa_real hD]; norm_num)) fun kp => ?_
    refine allQueriesSatisfy_bind (allQ_hash256' (by rw [length_digIn_real hD]; norm_num)) fun d => ?_
    refine allQueriesSatisfy_bind (allQ_hash256' (by rw [length_ivIn]; norm_num)) fun _ => ?_
    exact LeanVM.Rpm.allQ_pure _
  have hall : AllQueriesSatisfy (p2Ver D π) Short := by
    unfold p2Ver
    refine allQueriesSatisfy_bind hiv fun x => ?_
    rw [map_eq_bind_pure_comp]
    refine allQueriesSatisfy_bind ?_ fun _ => LeanVM.Rpm.allQ_pure _
    have hmsg : ∀ m ∈ (p2View (setIv2 x.2.2.2 π)).2, m.2.length ≤ 18 := by
      intro m hm
      have e : (p2View (setIv2 x.2.2.2 π)).2 = (p2Msgs (setIv2 x.2.2.2 π)).map UniSound.toRMsg := rfl
      rw [e, p2Msgs_eq] at hm
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> simp [UniSound.toRMsg]
    unfold verU ChainSpecU.chain
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine allQueriesSatisfy_bind (UniSound.allQ_runM _ _ ?_ ?_) fun sts => ?_
    · show (p2Label _).length ≤ _
      rw [p2Label_length]
      norm_num
    · intro e he
      have := length_mem_absorbsI_p2 _ 18 0 _ _ hmsg e he
      simp only [pLen] at this
      omega
    · simp only [Function.comp_apply, pure_bind]
      exact allQueriesSatisfy_bind (UniKeccakSound.allQ_gopsRunK _ _ _ _ (allQ_p2Ops D)) fun _ =>
        LeanVM.Rpm.allQ_pure _
  refine (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) htot
    (hall.mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)).mono ?_
  norm_num

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem p2Label_take32 (s : FSt2) : (p2Label s).take 32 = RecStatement.name ++ s.1.toList.take 16 := by
  unfold p2Label
  rw [List.append_assoc, List.take_append, List.take_of_length_le (l := RecStatement.name) (by rw [name_length]; omega),
    name_length, List.take_append_of_le_length (l₁ := s.1.toList) (by simp)]

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last query** (`p2IvAdv`:
π2's IV of the proof the setup fixes). -/
theorem hlab_p2 (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1) (A₀ : SOut → OracleComp KeccakCalls P2Pf)
    (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) T).map Sigma.fst ∧
      (pi2Spec.label (p2View (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)))).1).take 32 =
        RecStatement.name ++ (viewT T w).toList.take (32 - RecStatement.name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (p2Setup D hs) p2Fix (p2IvAdv D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (p2Setup D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  set c := D.circuitAt (p2Roots (p2Fix s π)).pi1
  set d := viewT T (digIn c (viewT T (sigmaBytes c)) (viewT T (kappaBytes c)))
  refine ⟨ivIn D (p2Roots (p2Fix s π)) d, ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [p2IvAdv, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_p2IvKC4]
    dsimp only
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (p2IvAdv D A₀ s) =
        setIv2 (viewT T (ivIn D (p2Roots (p2Fix s π)) d)) π := by
      simp only [p2IvAdv, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_p2IvKC4]
      rfl
    rw [hev, name_length]
    show (p2Label (p2View (p2Fix s (setIv2 _ π))).1).take 32 = _
    rw [p2Label_take32]
    rfl

end RecCompose

/-- info: 'RecCompose.cc_encoding_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.cc_encoding_length

/-- info: 'RecCompose.duplexVm_p2Ver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.duplexVm_p2Ver

/-- info: 'RecCompose.cost_p2Ver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.cost_p2Ver

/-- info: 'RecCompose.isTotalQueryBound_p2IvAdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.isTotalQueryBound_p2IvAdv

/-- info: 'RecCompose.expU_p2IvAdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.expU_p2IvAdv

/-- info: 'RecCompose.extractorK_ivLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.extractorK_ivLog

/-- info: 'RecCompose.hlab_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hlab_p2

/-- info: 'RecCompose.p2BreaksRel_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.p2BreaksRel_congr
