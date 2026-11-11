-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsVerifier.lean` (`uniVerifierBridge_of_walk`) to π2's contract
-- (`formal/RecStatement/RecStatement/Security.lean`, `contractWith`) on the EIP's PCS claims, after
-- `formal/UniKeccakSound/UniKeccakSound/Fs/VerifierK.lean` (each claim's opening `pcsOpenC` answered over `π`,
-- `pcsOpenK_eq`).
import RecCompose.FsOps
import RecCompose.FsExtract
import UniSound.FsVerifier
import UniSound.FsWalkProof
import UniKeccakSound.Fs.VerifierK

/-!
# π2's verifier bridge

**`pi2VerifierBridge`**: from any state of the lazily sampled permutation, π2's contract past its IV
(`contractRest`: π2's run on the stream, then its eight claims opened) accepts at most as often as the composed
verifier (the chain `pi2Spec`, then the openings `p2Ops`) passes `p2Check` with every opening accepting, from the
walk (`Pi2Walk`, `Pi2WalkReject`):

* a stream of another length is rejected (`Pi2WalkReject`);
* on a stream of `1064` bytes the run is the chain (`Pi2Walk` at `F = π`), which both sides run first;
* per challenges: the run's verdict `all ≠ 0`; the contract's loop is the eight claims one after the other, their
  verdicts and-ed (`forIn_seqAndK`); **each claim's opening is the composed one** answered over `π` (`pi1Open`,
  `wOpen`, `sOpen`, `qOpen`: the claim decoded by `claimOfWords`, its root the root word's, the stream's or the
  setup's, its point of its stack's variables, `UniKeccakSound.pcsOpenK_eq`), so the loop is the eight openings
  `p2Ops8` and-ed (`seqAndK_gops`), and the composed openings `p2Ops` are the eight with `Q`'s three and-ed
  (`gopsRun_p2Ops`).

π1's three claims' words are `Data.pi1Calls`' (`pi1Words`): each its root word (the stream's `C1`, `C2` root, or the
setup's), then `3 + n` words in all at `n = 27, 26, 23` (`pi1Words_length_k`), so a π1 claim that decodes is a point
claim of its stack's variables.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

section With

variable {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)

/-- **π2's contract past its IV** (`contractWith` after `ivWith`): π2's run at the IV, then the eight claims. -/
def contractRest (D : RecDeployment) (roots : RecSetupRoots) (iv : List UInt8) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood
      proof.stream r
    if calls.length ≠ 8 then return (false, calls) else
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenWords F words p)
    return (ok, calls)

theorem contractWith_eq (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.contractWith F roots input proof = D.ivWith F roots >>= fun iv => contractRest F D roots iv input proof := rfl

/-- The eight claims' words at the real circuit. -/
def callsC (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof) (r : RecStatement.Reduced) :
    List (List (List UInt8)) :=
  pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood proof.stream r

/-- **The contract past its run**, on what it reads of the run's outcome (its verdict and result), at the real
circuit. -/
def restC (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof)
    (p : Bool × Except UniStatement.UniError RecStatement.Reduced) : m (Bool × List (List (List UInt8))) :=
  match p.2 with
  | .error _ => pure (false, [])
  | .ok r =>
    if !p.1 then pure (false, []) else
    if (callsC D roots proof r).length ≠ 8 then pure (false, callsC D roots proof r)
    else
      forIn ((callsC D roots proof r).zip proof.openings) true (fun x s => do
        let b ← pcsOpenWords F x.1 x.2
        pure (ForInStep.yield (s && b))) >>= fun ok =>
      pure (ok, callsC D roots proof r)

end With

/-- **The contract past its IV reads the run's verdict and result only**, at the real circuit. -/
theorem contractRest_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (D : RecDeployment) (roots : RecSetupRoots) (iv : List UInt8) (input : Vector UInt8 32) (proof : RecProof)
    (hc : (D.circuitAt roots.pi1).circuit = cc) :
    contractRest F D roots iv input proof =
      ((fun o : RecStatement.Outcome => (o.accepts, o.result)) <$>
        runWith F (Spec.of cc) iv input.toList proof.stream) >>= restC F D roots proof := by
  rw [bind_map_left]
  simp only [contractRest, hc]
  rfl

/-- **VERIFIER**: from any state of the lazily sampled permutation, π2's contract past its IV on a proof (its IV,
commitments, input and recursive proof) accepts at most as often as the composed verifier on it passes `p2Check` with
every opening accepting. -/
def Pi2VerifierBridge (D : RecDeployment) : Prop :=
  ∀ (π : P2Pf) (s : Common.PermutationEdges LeanVM.Semantics.KeccakState),
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles
        (contractRest Common.queryPermutation D (p2Roots π) π.iv.toList π.input π.proof)).run' s}[x.1 = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation
          (verU pi2Spec p2View (gopsRun p2View (p2Ops D)) π))).run' s}[
        p2Check π v.1 ∧ ∀ k < (p2Ops D).length, v.2.getD k false = true]

/-! ## The run rejects: the contract rejects -/

theorem restC_reject (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof)
    (p : Bool × Except UniStatement.UniError RecStatement.Reduced) (hp : p.1 = false) :
    ∀ x ∈ support (restC (m := OracleComp Common.RandomPermutationOracles) Common.queryPermutation D roots proof p),
      x.1 = false := by
  intro x hx
  obtain ⟨b, r⟩ := p
  simp only at hp
  subst hp
  cases r with
  | error e =>
    simp only [restC, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | ok r =>
    simp only [restC, Bool.not_false, ite_true, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

/-! ## The composed verifier: the chain, then the openings -/

/-- **The composed verifier, its two calls answered over `π`**: the chain over Keccak-256 the sponge over `π`, then
the openings (`UniSound.simulateQ_verU` for π2). -/
theorem simulateQ_verU2 {β : Type} (post : P2Pf → List (List E) → OracleComp KeccakCalls β) (π : P2Pf) :
    simulateQ keccakCallsOverQueryPermutation (verU pi2Spec p2View post π) =
      pi2Spec.chain (fun x => toB <$> keccak256With Common.queryPermutation x) (p2View π).1 (p2View π).2 >>=
        fun ch => simulateQ keccakCallsOverQueryPermutation (post π ch >>= fun b => pure (ch, b)) := by
  rw [verU, simulateQ_bind]
  congr 1
  rw [ChainSpecU.chain, ChainSpecU.chain, simulateQ_map, UniSound.simulateQ_runM]
  simp only [UniSound.simulateQ_hash256]

/-- **The chain's possible challenges have the rounds' lengths** (`3`, `1`, `1`). -/
theorem chain_lengths {ι : Type} {spec : OracleSpec.{0, 0} ι} (π : P2Pf) (ch : List (List E))
    (H : List UInt8 → OracleComp spec Bytes32)
    (hch : ch ∈ support (pi2Spec.chain H (p2View π).1 (p2View π).2)) :
    ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧ (ch.getD 2 []).length = 1 := by
  rw [ChainSpecU.chain, support_map] at hch
  obtain ⟨sts, hsts, rfl⟩ := hch
  have hl := UniSound.length_of_mem_runM H _ _ sts hsts
  rw [ChainSpecU.absorbsS, length_absorbsI] at hl
  have h5 : (sts.tail.map (chalL pi2Spec.K.lim)).length = 5 := by
    rw [List.length_map, List.length_tail, hl]
    rfl
  have hc : pi2Spec.K.chalsOf sts = groupK (RecPiop.pi2Rounds 4) (sts.tail.map (chalL pi2Spec.K.lim)) := rfl
  rw [hc]
  generalize sts.tail.map (chalL pi2Spec.K.lim) = l at h5 ⊢
  simp [groupK, RecPiop.pi2Rounds, h5]

/-! ## The contract's loop, the calls and-ed -/

/-- The calls one after the other, their verdicts and-ed from `ok`, then `kf`. -/
def seqAndK {γ : Type} : List (OracleComp Common.RandomPermutationOracles Bool) → Bool →
    (Bool → OracleComp Common.RandomPermutationOracles γ) → OracleComp Common.RandomPermutationOracles γ
  | [], ok, kf => kf ok
  | P :: Ps, ok, kf => P >>= fun b => seqAndK Ps (ok && b) kf

theorem seqAndK_cons {γ : Type} (P : OracleComp Common.RandomPermutationOracles Bool)
    (Ps : List (OracleComp Common.RandomPermutationOracles Bool)) (ok : Bool)
    (kf : Bool → OracleComp Common.RandomPermutationOracles γ) :
    seqAndK (P :: Ps) ok kf = P >>= fun b => seqAndK Ps (ok && b) kf := rfl

/-- **The contract's loop is the calls one after the other, and-ed.** -/
theorem forIn_seqAndK {γ : Type} :
    ∀ (l : List (List (List UInt8) × Compile.Proof)) (ok : Bool)
      (kf : Bool → OracleComp Common.RandomPermutationOracles γ),
      (forIn l ok (fun x s => do
          let b ← pcsOpenWords Common.queryPermutation x.1 x.2
          pure (ForInStep.yield (s && b))) >>= kf) =
        seqAndK (l.map fun x => pcsOpenWords Common.queryPermutation x.1 x.2) ok kf
  | [], ok, kf => by simp [seqAndK]
  | x :: l, ok, kf => by
    simp only [List.forIn_cons, bind_assoc, pure_bind, List.map_cons, seqAndK_cons]
    congr 1
    funext b
    exact forIn_seqAndK l (ok && b) kf

/-- **The composed openings one after the other, answered over `π`, are their run and-ed.** -/
theorem seqAndK_gops {γ : Type} (π : P2Pf) (ch : List (List E)) :
    ∀ (L : List (GOp P2Pf E Stk)) (ok : Bool) (kf : Bool → OracleComp Common.RandomPermutationOracles γ),
      seqAndK (L.map fun o => simulateQ keccakCallsOverQueryPermutation (GOp.run p2View o π ch)) ok kf =
        simulateQ keccakCallsOverQueryPermutation (gopsRun p2View L π ch) >>= fun bs => kf (bs.foldl (· && ·) ok)
  | [], ok, kf => by simp [seqAndK, gopsRun]
  | o :: L, ok, kf => by
    simp only [List.map_cons, seqAndK_cons, gopsRun, simulateQ_bind, simulateQ_map, bind_assoc, bind_map_left,
      List.foldl_cons]
    congr 1
    funext b
    exact seqAndK_gops π ch L (ok && b) kf

/-! ## Decoding a claim -/

/-- **A claim's words decode to its fields** (`claimOfWords`): a root word of `32` bytes, the out-of-domain answer's
word, the point's and the value's. -/
theorem claimOfWords_mk (root : List UInt8) (hr : root.length = 32) (ood : E) (pt : List E) (v : E) :
    claimOfWords ([root, UniStatement.elementWord ood] ++ claimWords (pt, v)) = some (rootOfWord root, ood, pt, v) := by
  rw [show [root, UniStatement.elementWord ood] ++ claimWords (pt, v) = root :: UniStatement.elementWord ood ::
    (pt.map UniStatement.elementWord ++ [UniStatement.elementWord v]) by simp [claimWords]]
  have hg : (UniStatement.elementWord ood :: (pt.map UniStatement.elementWord ++ [UniStatement.elementWord v])).getLast? =
      some (UniStatement.elementWord v) := by
    rw [← List.cons_append, List.getLast?_concat]
  simp [claimOfWords, hr, hg, FsBytes.mapM_comp_elementOfWord, FsBytes.elementOfWord_elementWord]

/-- **A claim's fields from its words**: its root is the first word's, and its point has three words fewer. -/
theorem claimOfWords_spec {ws : List (List UInt8)} {root : Digest} {ood : E} {pt : List E} {v : E}
    (h : claimOfWords ws = some (root, ood, pt, v)) : root = rootOfWord (ws.headD []) ∧ pt.length + 3 = ws.length := by
  unfold claimOfWords at h
  cases hh : ws.head? with
  | none => simp [hh] at h
  | some hd =>
    cases h1 : ws[1]? with
    | none => simp [hh, h1] at h
    | some oodW =>
      cases hl : ws.getLast? with
      | none => simp [hh, h1, hl] at h
      | some vW =>
        by_cases hc : 3 ≤ ws.length ∧ hd.length = 32
        · cases ho : elementOfWord oodW with
          | none => simp [hh, h1, hl, hc, ho] at h
          | some o =>
            cases hp : ((ws.drop 2).dropLast).mapM elementOfWord with
            | none => simp [hh, h1, hl, hc, hp] at h
            | some p =>
              cases hv : elementOfWord vW with
              | none => simp [hh, h1, hl, hc, hp, hv] at h
              | some vv =>
                simp [hh, h1, hl, hc, ho, hp, hv] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                refine ⟨?_, ?_⟩
                · cases ws with
                  | nil => simp at hh
                  | cons a ws => simp at hh; subst hh; rfl
                · have := FsBytes.length_of_mapM _ _ _ hp
                  simp at this
                  omega
        · simp [hh, h1, hl, hc] at h

/-- The stream's 32 bytes at a place it holds. -/
theorem streamWord_length (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) : (streamWord b o).length = 32 := by
  simp [streamWord]
  omega

/-- **The eight claims' words at the real circuit**: π1's three, then `W`'s, the setup's and `Q`'s three, each its root
word, its out-of-domain answer's word, its point's and value's. -/
theorem pcsCalls_cc (pi1 : List (List CallWord)) (sr : List UInt8) (so : E) (stream : Array UInt8)
    (r : RecStatement.Reduced) :
    pcsCalls cc pi1 sr so stream r = pi1.map (·.map (callWord cc.reads stream r)) ++
      [[streamWord stream 520, UniStatement.elementWord r.oods.1] ++ claimWords r.witness,
        [sr, UniStatement.elementWord so] ++ claimWords r.setup,
        [streamWord stream 576, UniStatement.elementWord r.oods.2] ++ claimWords r.quotient,
        [streamWord stream 576, UniStatement.elementWord r.oods.2] ++ claimWords r.pushes,
        [streamWord stream 576, UniStatement.elementWord r.oods.2] ++ claimWords r.sum] := by
  have h1 : rootsAt cc.reads = [0, 32, 520, 576] := by decide
  have h2 : rootReads cc.reads = 2 := by decide
  unfold pcsCalls
  rw [h1, h2]
  rfl

/-! ## π1's three claims -/

section Pi1

variable (D : RecDeployment) (hc : D.pi1Calls = Data.pi1Calls)
include hc

theorem pi1Words_length (π : P2Pf) (ch : List (List E)) : (pi1Words D π ch).length = 3 := by
  rw [pi1Words, hc]
  rfl

theorem pi1Words_head (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) :
    ((pi1Words D π ch).getD k []).headD [] = ((pi1Words D π []).getD k []).headD [] := by
  rw [pi1Words, pi1Words, hc]
  interval_cases k <;> rfl

theorem pi1Words_length_k (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) :
    ((pi1Words D π ch).getD k []).length = pi1Vars k + 3 := by
  rw [pi1Words, hc]
  interval_cases k <;> rfl

/-- **π1's claim `k`** is its composed opening answered over `π`: both reject where its words do not decode; where
they do, its root is the root word's and its point has its stack's variables. -/
theorem pi1Open (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) (n : ℕ) (lo : 23 ≤ n) (hi : n ≤ 28)
    (hn : n = pi1Vars k) (q₀ : Column n) :
    pcsOpenWords Common.queryPermutation ((pi1Words D π ch).getD k []) (pi1Prf k π) =
      simulateQ keccakCallsOverQueryPermutation (GOp.run p2View
        (PcsOp.gop ⟨n, lo, hi, pi1Cl D k, pi1Prf k, .setup (fun π => pi1Root D π k) q₀⟩) π ch) := by
  unfold GOp.run
  show _ = simulateQ keccakCallsOverQueryPermutation (PcsOp.ver _ (ofB (pi1Root D π k)) π ch)
  unfold PcsOp.ver pcsOpenWords
  dsimp only
  unfold pi1Cl
  rcases hcl : claimOfWords ((pi1Words D π ch).getD k []) with _ | ⟨root, ood, pt, v⟩
  · simp
  · obtain ⟨hroot, hlen⟩ := claimOfWords_spec hcl
    have hpt : pt.length = n := by
      rw [pi1Words_length_k D hc π ch k hk, ← hn] at hlen
      omega
    have hr : ofB (pi1Root D π k) = root := by
      unfold pi1Root
      rw [Soundness.ofB_toB_root, hroot, pi1Words_head D hc π ch k hk]
    have hs : oodRead n = false := by
      rw [hn]
      interval_cases k <;> rfl
    simp only [Option.map_some]
    rw [hr, hpt, hs, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, UniKeccakSound.pcsOpenK_eq]

end Pi1

/-! ## π2's five claims -/

theorem msgK_p2View_0 (π : P2Pf) :
    msgK p2View π 0 = (some (toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 520))),
      (List.range 1).map fun k => UniSound.scalarAt π.proof.stream (552 + 24 * k)) := rfl

theorem msgK_p2View_1 (π : P2Pf) :
    msgK p2View π 1 = (some (toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 576))),
      (List.range 1).map fun k => UniSound.scalarAt π.proof.stream (608 + 24 * k)) := rfl

/-- **`W`'s claim** is its composed opening answered over `π`. -/
theorem wOpen (π : P2Pf) (ch : List (List E)) (hlen : π.proof.stream.size = sLen) :
    pcsOpenWords Common.queryPermutation
        ([streamWord π.proof.stream 520, UniStatement.elementWord (p2Reduced π ch).oods.1] ++
          claimWords (p2Reduced π ch).witness) π.proof.w =
      simulateQ keccakCallsOverQueryPermutation (GOp.run p2View wOp π ch) := by
  unfold pcsOpenWords
  rw [show (p2Reduced π ch).witness = ((p2Out π ch).witnessPoint, (p2Out π ch).fold) from rfl,
    claimOfWords_mk _ (streamWord_length _ _ (by rw [hlen]; decide))]
  dsimp only
  rw [p2Out_witnessPoint_length, ite_eq_left (show oodRead 24 = true from rfl), pcsOpenKO_eq,
    show rootOfWord (streamWord π.proof.stream 520) = _ from streamRoot_eq _ _ (by rw [hlen]; decide)]
  unfold GOp.run
  rw [show GOp.root p2View wOp π = toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 520)) from rfl,
    Soundness.ofB_toB_root]
  rfl

/-- **The setup's claim** is its composed opening answered over `π`. -/
theorem sOpen (π : P2Pf) (ch : List (List E)) :
    pcsOpenWords Common.queryPermutation
        ([digestBytes π.roots.pi2, UniStatement.elementWord π.roots.pi2Ood] ++
          claimWords (p2Reduced π ch).setup) π.proof.setup =
      simulateQ keccakCallsOverQueryPermutation (GOp.run p2View (PcsOp.gop ⟨25, by norm_num, by norm_num, sCl,
        fun π => π.proof.setup, .setup (fun π => toB π.roots.pi2) (col0 _)⟩) π ch) := by
  unfold pcsOpenWords
  rw [show (p2Reduced π ch).setup = ((p2Out π ch).setupPoint, (p2Inputs π ch).ξ) from rfl,
    claimOfWords_mk _ (FsBytes.length_digestBytes _)]
  dsimp only
  rw [p2Out_setupPoint_length, ite_eq_right (show ¬ oodRead 25 = true by decide), UniKeccakSound.pcsOpenK_eq,
    FsBytes.rootOfWord_digestBytes]
  unfold GOp.run
  rw [show GOp.root p2View (PcsOp.gop ⟨25, by norm_num, by norm_num, sCl, fun π => π.proof.setup,
    .setup (fun π => toB π.roots.pi2) (col0 _)⟩) π = toB π.roots.pi2 from rfl, Soundness.ofB_toB_root]
  rfl

/-- **`Q`'s claims** are their composed openings answered over `π`, on `Q`'s root word and out-of-domain answer. -/
theorem qOpen (π : P2Pf) (ch : List (List E)) (hlen : π.proof.stream.size = sLen) (lo : 23 ≤ 28) (hi : 28 ≤ 28)
    (cl : P2Pf → List (List E) → Option (E × List E × E)) (prf : P2Pf → Compile.Proof) (rd : Column 28 → Stk)
    (pt : List E) (v : E) (hpt : pt.length = 28) (hcl : cl π ch = some ((p2Reduced π ch).oods.2, pt, v)) :
    pcsOpenWords Common.queryPermutation
        ([streamWord π.proof.stream 576, UniStatement.elementWord (p2Reduced π ch).oods.2] ++ claimWords (pt, v))
        (prf π) =
      simulateQ keccakCallsOverQueryPermutation (GOp.run p2View (PcsOp.gop ⟨28, lo, hi, cl, prf, .round 1 rd⟩) π ch) := by
  unfold pcsOpenWords
  rw [claimOfWords_mk _ (streamWord_length _ _ (by rw [hlen]; decide))]
  dsimp only
  rw [hpt, ite_eq_left (show oodRead 28 = true from rfl), pcsOpenKO_eq,
    show rootOfWord (streamWord π.proof.stream 576) = _ from streamRoot_eq _ _ (by rw [hlen]; decide)]
  unfold GOp.run
  rw [show GOp.root p2View (PcsOp.gop ⟨28, lo, hi, cl, prf, .round 1 rd⟩) π =
    toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 576)) from rfl, Soundness.ofB_toB_root]
  show _ = simulateQ keccakCallsOverQueryPermutation (PcsOp.ver ⟨28, lo, hi, cl, prf, .round 1 rd⟩ _ π ch)
  unfold PcsOp.ver
  dsimp only
  rw [hcl]
  rfl

/-! ## The bridge -/

theorem restC_ok (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof) (r : RecStatement.Reduced)
    (h8 : (callsC D roots proof r).length = 8) :
    restC Common.queryPermutation D roots proof (true, .ok r) =
      forIn ((callsC D roots proof r).zip proof.openings) true (fun x s => do
        let b ← pcsOpenWords Common.queryPermutation x.1 x.2
        pure (ForInStep.yield (s && b))) >>= fun ok => pure (ok, callsC D roots proof r) := by
  simp only [restC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h8, ne_eq, not_true_eq_false]

theorem list3_eq {α : Type} (l : List α) (h : l.length = 3) (d : α) : l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [_, _, _], _ => rfl

/-- **The contract's eight calls are the eight composed openings**, answered over `π`. -/
theorem calls_eq (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) (hlen : π.proof.stream.size = sLen)
    (ch : List (List E)) :
    ((callsC D (p2Roots π) π.proof (p2Reduced π ch)).zip π.proof.openings).map
        (fun x => pcsOpenWords Common.queryPermutation x.1 x.2) =
      (p2Ops8 D).map fun o => simulateQ keccakCallsOverQueryPermutation (GOp.run p2View o π ch) := by
  have hw : (pi1CallsWith D.pi1Calls π.roots.pi1).map (·.map (callWord cc.reads π.proof.stream (p2Reduced π ch))) =
      pi1Words D π ch := rfl
  unfold callsC
  rw [pcsCalls_cc, show (p2Roots π).pi1 = π.roots.pi1 from rfl, hw,
    list3_eq (pi1Words D π ch) (pi1Words_length D hD.2.1 π ch) []]
  simp only [RecProof.openings, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
    List.map_cons, List.map_nil, p2Ops8, p2Pcs, p2Pcs5]
  refine List.cons_eq_cons.mpr ⟨pi1Open D hD.2.1 π ch 0 (by decide) _ _ _ rfl _, ?_⟩
  refine List.cons_eq_cons.mpr ⟨pi1Open D hD.2.1 π ch 1 (by decide) _ _ _ rfl _, ?_⟩
  refine List.cons_eq_cons.mpr ⟨pi1Open D hD.2.1 π ch 2 (by decide) _ _ _ rfl _, ?_⟩
  refine List.cons_eq_cons.mpr ⟨wOpen π ch hlen, ?_⟩
  refine List.cons_eq_cons.mpr ⟨sOpen π ch, ?_⟩
  refine List.cons_eq_cons.mpr ⟨qOpen π ch hlen (by norm_num) le_rfl qIdCl (fun π => π.proof.qId) (rdP 28) _ _
    (p2Out_quotientPoint_length π ch) rfl, ?_⟩
  refine List.cons_eq_cons.mpr ⟨qOpen π ch hlen (by norm_num) le_rfl qPushCl (fun π => π.proof.qPush) (rdP 28) _ _
    (p2Out_pushesPoint_length π ch) rfl, ?_⟩
  refine List.cons_eq_cons.mpr ⟨qOpen π ch hlen (by norm_num) le_rfl qSumCl (fun π => π.proof.qSum) (rdP 28) _ _
    (p2Out_sumPoint_length π ch) rfl, rfl⟩

/-- Verdicts and-ed true are each true. -/
theorem foldl_and_true : ∀ (bs : List Bool) (ok : Bool), bs.foldl (· && ·) ok = true →
    ok = true ∧ ∀ k < bs.length, bs.getD k false = true
  | [], ok, h => ⟨h, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | b :: bs, ok, h => by
    rw [List.foldl_cons] at h
    obtain ⟨hob, hbs⟩ := foldl_and_true bs (ok && b) h
    rw [Bool.and_eq_true] at hob
    refine ⟨hob.1, fun k hk => ?_⟩
    cases k with
    | zero => exact hob.2
    | succ k => exact hbs k (by simpa using hk)

/-- The openings' verdicts, answered over `π`, have their count. -/
theorem length_of_mem_sim_gopsRun (π : P2Pf) (ch : List (List E)) :
    ∀ (L : List (GOp P2Pf E Stk)) (bs : List Bool),
      bs ∈ support (simulateQ keccakCallsOverQueryPermutation (gopsRun p2View L π ch)) → bs.length = L.length
  | [], bs, h => by
    simp only [gopsRun, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    subst h
    rfl
  | o :: L, bs, h => by
    simp only [gopsRun, simulateQ_bind, simulateQ_map, mem_support_bind_iff, support_map, Set.mem_image] at h
    obtain ⟨b, -, bs', hbs', rfl⟩ := h
    simp [length_of_mem_sim_gopsRun π ch L bs' hbs']

/-- **Per challenges**: the contract past the run accepts at most as often as the composed openings all do, with the
check. -/
theorem step_ch (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) (hlen : π.proof.stream.size = sLen)
    (ch : List (List E))
    (hch : ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧ (ch.getD 2 []).length = 1)
    (s : Common.PermutationEdges LeanVM.Semantics.KeccakState) :
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles (restC Common.queryPermutation D (p2Roots π) π.proof
        ((p2Reduced π ch).out.all != 0,
          (Except.ok (p2Reduced π ch) : Except UniStatement.UniError RecStatement.Reduced)))).run' s}[x.1 = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation
          (gopsRun p2View (p2Ops D) π ch >>= fun b => pure (ch, b)))).run' s}[
        p2Check π v.1 ∧ ∀ k < (p2Ops D).length, v.2.getD k false = true] := by
  by_cases hall : (p2Reduced π ch).out.all = 0
  · have hf : ((p2Reduced π ch).out.all != 0) = false := by simp [hall]
    rw [hf]
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun x hx hx1 => ?_) s)).trans zero_le
    rw [restC_reject D (p2Roots π) π.proof _ rfl x hx] at hx1
    exact Bool.false_ne_true hx1
  have ht : ((p2Reduced π ch).out.all != 0) = true := by simp [hall]
  have hcheck : p2Check π ch := ⟨hlen, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2, hall⟩
  have h8 : (callsC D (p2Roots π) π.proof (p2Reduced π ch)).length = 8 := by
    unfold callsC
    rw [pcsCalls_cc, List.length_append, List.length_map, show (pi1CallsWith D.pi1Calls (p2Roots π).pi1).length =
      (pi1Words D π ch).length by simp [pi1Words, p2Roots], pi1Words_length D hD.2.1 π ch]
    rfl
  rw [ht, restC_ok D (p2Roots π) π.proof _ h8, forIn_seqAndK, calls_eq D hD π hlen ch, seqAndK_gops,
    gopsRun_p2Ops, bind_map_left, simulateQ_bind (impl := keccakCallsOverQueryPermutation)]
  refine UniSound.mono_bind_supp _ _ _ _ _ _ (fun bs hbs s => ?_) s
  rw [simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun hx => ?_) s
  obtain ⟨-, hbs8⟩ := foldl_and_true bs true hx
  have hl : bs.length = 8 := by
    have := length_of_mem_sim_gopsRun π ch (p2Ops8 D) bs hbs
    simpa [p2Ops8, p2Pcs, p2Pcs5] using this
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      bs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
    match bs, hl with
    | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  have e0 := hbs8 0 (by simp)
  have e1 := hbs8 1 (by simp)
  have e2 := hbs8 2 (by simp)
  have e3 := hbs8 3 (by simp)
  have e4 := hbs8 4 (by simp)
  have e5 := hbs8 5 (by simp)
  have e6 := hbs8 6 (by simp)
  have e7 := hbs8 7 (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4 e5 e6 e7
  subst e0 e1 e2 e3 e4 e5 e6 e7
  refine ⟨hcheck, fun k hk => ?_⟩
  have hk6 : k < 6 := by simpa [p2Ops, p2Pcs5] using hk
  interval_cases k <;> rfl

/-- **THE VERIFIER BRIDGE** at the real deployment, from the walk. -/
theorem pi2VerifierBridge (D : RecDeployment) (hD : RecDeployment.Real D) (hW : Pi2Walk) (hR : Pi2WalkReject) :
    Pi2VerifierBridge D := by
  intro π s
  rw [contractRest_eq Common.queryPermutation D (p2Roots π) π.iv.toList π.input π.proof (hD.1 _)]
  by_cases hlen : π.proof.stream.size = sLen
  swap
  · -- a stream of another length: the run rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun x hx hx1 => ?_) s)).trans zero_le
    rw [mem_support_bind_iff] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [support_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    rw [restC_reject D (p2Roots π) π.proof _ (hR π hlen o ho) x hx] at hx1
    exact Bool.false_ne_true hx1
  -- the run is the chain; both sides run it first
  rw [hW Common.queryPermutation π hlen, bind_map_left, simulateQ_verU2]
  exact UniSound.mono_bind_supp _ _ _ _ _ _
    (fun ch hch s => step_ch D hD π hlen ch (chain_lengths π ch _ hch) s) s

end RecCompose

/-- info: 'RecCompose.pi2VerifierBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2VerifierBridge
