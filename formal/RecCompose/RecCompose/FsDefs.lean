-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsChain.lean`, `FsOps.lean`, `FsGame.lean` (the IV in the verifier) and `FsCouple.lean`
-- (the bridge facts) to π2's transcript (`formal/RecStatement/RecStatement/Verifier.lean`, `Calls.lean`,
-- `Security.lean`); the openings are the EIP's PCS claims as `formal/UniKeccakSound/UniKeccakSound/Fs/OpsK.lean`'s
-- (`opK`: `pcsOpenC` on `plainShapeK`), π1's setup `ProofK.lean`'s `setupK1`.
import RecCompose.Layers
import RecCompose.Pi2Run
import UniSound.FsGame
import UniSound.FsExtract
import UniKeccakSound.Fs.ProofK
import Compose.ListChainUDoom128SG
import RecCompose.FsOod

/-!
# π2's Fiat–Shamir layer: the chain, the openings, the setup, the composed verifier

The objects `Compose.knowledgeSoundness_listChainU_closed128SG` is applied to for π2's verifier at the real
deployment's circuit (`cc = Data.circuit`, π2v4 over π1-rec4: `2^24` positions, rows of `16`, the reads the three
frame words, no stream byte):

* **the chain** (`pi2Spec`, `Compose.ChainSpecU`): the statement `FSt2` (π2's IV, the public input, the frame words'
  `96` bytes: the Keccak-256s of π1's three declared claims, `frameOf`), the label the seed's input
  `name ‖ iv ‖ input ‖ frame words` (`RecStatement.name`, 16 bytes; `176` bytes), no public data in the stream (round
  `0`'s message is `W`'s commitment at byte `0`), the messages as the stream carries them (`UniSound.uniEnc`: a root's
  32 bytes as they are, `24`-byte scalars), `RecPiop.pi2Rounds 4`;
* **the proof the chain reads** (`P2Pf`: the input, the recursive proof, the IV, the setup's commitments) and its view
  (`p2View`: the frame words of the declared claims, the stream's messages from byte `0`);
* **the seven openings**, in the contract's order: π1's three declared claims (`declOp k`: the contract's opening of
  the declared words at their point's length, any of version 1's sizes, at the root they name; nothing concluded of
  them), then π2's four as `PcsOp`s (`p2Pcs`: the EIP's PCS claim `(root, ood, point, value)` on a stack of `n`
  variables, opened by `UniKeccakSound.pcsOpenC` or, at `W`'s and `Q`'s sizes, `pcsOpenCO`, a `Compose.GOp` on the plain
  shape `UniKeccakSound.plainShapeK n`): `W` (round `0`, `24`), the setup (`25`, its stack read off the proof's
  commitments: `p2Stk`), `Q`'s two claims (round `1`, `28`, one root). For the chain's composition, three openings
  (`p2Ops`): π1's three and `W`'s as one (`wOpM`: the four verifiers in turn, its claim `W`'s), the setup's, `Q`'s two as
  one (`qOp`: its claims both on one stack, which the out-of-domain answer makes possible, `FsBind.lean`);
* **the setup** (`p2Setup`): π1's one tree (the Keccak setup stack's, `UniKeccakSound.setupK1`), then π2's tree of
  the circuit's setup table at π1's setup commitment; its output the setup's commitments (`RecSetupRoots`: each root
  with its out-of-domain answer, `UniKeccakSound.skOf`, `Pi2Circuit.setupOod`);
* **the composed verifier** (`p2Ver`): π2's IV (the circuit's digest, three Keccak-256 calls, then the IV's: the tag,
  π1's contract IV, the setup's root and out-of-domain answer, the digest, `log_n`), then the chain and the openings;
  the IV moved into the adversary (`p2IvAdv`);
* **the protocol** (`liftPiop2`): a protocol on `pi2K` (`Pi2FsLayer`'s) on the chain's statement, `stOf`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

-- `Layers.lean`'s instance of `SampleableType E` (the one `Pi2FsLayer`'s protocols are at), not `Completeness`'s.
attribute [local instance high] LeanVM.Protocol.instSampleableTypeE

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The circuit's public data -/

/-- The real deployment's circuit (`RecDeployment.Real`: at every setup commitment). -/
abbrev cc : RecStatement.Circuit := Data.circuit

/-- The public data's bytes in the stream: none (π1's three claims are read from the frame). -/
abbrev pLen : ℕ := 0

/-- The frame words' bytes: three Keccak-256s. -/
abbrev fLen : ℕ := 96

/-- The stream's bytes: `W`'s and `Q`'s commitments (roots and out-of-domain answers), the `2^4 + 2` values. -/
abbrev sLen : ℕ := 544

/-! ## The frame words -/

/-- The frame payloads the real circuit reads: π1's three claims' Keccak-256s. -/
theorem frameReads_cc : frameReads cc.reads = [0, 1, 2] := rfl

theorem length_claimHash (w : List (List UInt8)) : (claimHash w).length = 32 := by
  unfold claimHash
  exact length_digestBytes32 _

/-- **The frame words the verifier reads** (`runWith`'s seed's tail) of the declared claims. -/
def frameList (ds : List (List (List UInt8))) : List UInt8 := (frameReads cc.reads).flatMap (frameOf ds)

theorem frameList_eq (ds : List (List (List UInt8))) :
    frameList ds = frameOf ds 0 ++ (frameOf ds 1 ++ frameOf ds 2) := by
  unfold frameList
  rw [frameReads_cc]
  simp

theorem length_frameList (ds : List (List (List UInt8))) : (frameList ds).length = fLen := by
  rw [frameList_eq]
  simp [frameOf, length_claimHash]

/-- The frame words' bytes as a vector. -/
def frameBytes (p : RecProof) : Vector UInt8 fLen := Vector.ofFn fun i => (frameList p.pi1Claims).getD i.val 0

theorem frameBytes_toList (p : RecProof) : (frameBytes p).toList = frameList p.pi1Claims := by
  apply List.ext_getElem
  · simp [length_frameList]
  · intro i h1 h2
    simp [frameBytes, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The frame payload `p`'s word of the frame words' bytes. -/
def frameAtB (b : Vector UInt8 fLen) (p : ℕ) : List UInt8 := (b.toList.drop (32 * p)).take 32

theorem frameAtB_frameBytes (pf : RecProof) (p : ℕ) (hp : p < 3) :
    frameAtB (frameBytes pf) p = frameOf pf.pi1Claims p := by
  unfold frameAtB
  rw [frameBytes_toList, frameList_eq]
  have h0 := length_claimHash (pf.pi1Claims.getD 0 [])
  have h1 := length_claimHash (pf.pi1Claims.getD 1 [])
  have h2 := length_claimHash (pf.pi1Claims.getD 2 [])
  unfold frameOf
  interval_cases p
  · rw [Nat.mul_zero, List.drop_zero, List.take_left' h0]
  · rw [Nat.mul_one, List.drop_left' h0, List.take_left' h1]
  · rw [show 32 * 2 = 32 + 32 from rfl, ← List.drop_drop, List.drop_left' h0, List.drop_left' h1,
      List.take_of_length_le (by rw [h2])]

/-! ## The chain -/

/-- **π2's chain statement**: π2's IV, the public input, the frame words' `96` bytes. -/
abbrev FSt2 : Type := Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 fLen

/-- **The seed's input** (`runWith`): `name ‖ iv ‖ input ‖ frame words`. -/
def p2Label (s : FSt2) : List UInt8 := RecStatement.name ++ s.1.toList ++ s.2.1.toList ++ s.2.2.toList

theorem name_length : RecStatement.name.length = 16 := by decide +kernel

theorem p2Label_length (s : FSt2) : (p2Label s).length = 176 := by
  simp [p2Label, name_length, fLen]

theorem p2Label_take (s : FSt2) : (p2Label s).take RecStatement.name.length = RecStatement.name := by
  unfold p2Label
  rw [List.append_assoc, List.append_assoc]
  exact List.take_left' rfl

theorem p2Label_inj {s s' : FSt2} (h : p2Label s = p2Label s') : s = s' := by
  unfold p2Label at h
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  obtain ⟨h4, h5⟩ := List.append_inj h3 (by simp)
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := s'
  simp only at h2 h4 h5
  rw [Vector.toList_inj.mp h2, Vector.toList_inj.mp h4, Vector.toList_inj.mp h5]

theorem p2Stmt_inj (s s' : FSt2) (hl : p2Label s = p2Label s') (_hp : ([] : List UInt8) = []) : s = s' :=
  p2Label_inj hl

/-- The `ChainSpec` of π2's rounds (its label the seed's input: only its limbs and rounds are read). -/
def p2K : ChainSpec E FSt2 where
  lim := UniSound.uLimbs
  label := p2Label
  label_injective _ _ h := p2Label_inj h
  label_len s := by
    rw [p2Label_length]
    decide
  rounds := RecPiop.pi2Rounds 4

/-- **An input refers to a digest**: `Compose.Refers`, or the digest is the root the input absorbs after a state
(bytes `32 … 64`: `W`'s and `Q`'s; the third disjunct, after the public data, is the same at `pLen = 0`). -/
def p2Rf (y : List UInt8) (d : Bytes32) : Prop :=
  Refers y d ∨ UniSound.revRoot d = (y.drop 32).take 32 ∨ UniSound.revRoot d = (y.drop (32 + pLen)).take 32

open Classical in
/-- The digests an input refers to. -/
noncomputable def p2Refs (y : List UInt8) : List Bytes32 :=
  (Finset.univ.filter fun d : Bytes32 => p2Rf y d).toList

set_option maxRecDepth 100000 in
theorem p2Rf_refs (y : List UInt8) (d : Bytes32) (h : p2Rf y d) : d ∈ p2Refs y := by
  classical
  unfold p2Refs
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

open Classical in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most five digests. -/
theorem length_p2Refs (y : List UInt8) : (p2Refs y).length ≤ 5 := by
  unfold p2Refs
  rw [Finset.length_toList]
  have h1 : ∀ z : List UInt8,
      (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = z).card ≤ 1 :=
    fun z => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact UniSound.revRoot_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => p2Rf y u) ⊆
      ((Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
        (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop 32).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop (32 + pLen)).take 32) := by
    intro u hu'
    simp only [Finset.mem_filter] at hu'
    obtain ⟨-, h⟩ := hu'
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨Finset.mem_univ _, h⟩)
    · exact Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h2 := Finset.card_union_le (Finset.univ.filter fun u : Bytes32 => Refers y u)
    (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop 32).take 32)
  have h3 := card_refers_le y
  have h4 := h1 ((y.drop 32).take 32)
  have h5 := h1 ((y.drop (32 + pLen)).take 32)
  omega

/-- **π2's transcript as a chain over an encoding** (`KeccakChannel` on `RecPiop.pi2Rounds 4`, no public data in the
stream: round `0`'s message alone after the seed). -/
noncomputable def pi2Spec : ChainSpecU E FSt2 where
  K := p2K
  label := p2Label
  tag := RecStatement.name
  tag_le := by rw [name_length]; decide
  label_tag := p2Label_take
  pre _ := []
  pre_len _ _ := rfl
  stmt_inj := p2Stmt_inj
  enc := UniSound.uniEnc
  enc_inj := UniSound.uniEnc_inj
  Rf := p2Rf
  nRf := 5
  refs := p2Refs
  rf_refs := p2Rf_refs
  length_refs := length_p2Refs
  refers_rf y d h := Or.inl h
  rf_enc st r l := by
    refine Or.inr (Or.inl ?_)
    simp only [stepIn, UniSound.uniEnc]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]
  rf_pre _ st r l := by
    refine Or.inr (Or.inl ?_)
    simp only [stepIn, UniSound.uniEnc, List.nil_append]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]

@[simp] theorem pi2Spec_rounds : pi2Spec.K.rounds = RecPiop.pi2Rounds 4 := rfl

/-! ## The protocol on the chain's statement -/

/-- **π2's PIOP statement of a chain statement**: the public input, and the public scalars (`pi2Pubs`: the input's
four words, then each frame word's four). -/
def stOf (s : FSt2) : Pi2St := (s.2.1, pi2Pubs (Spec.of cc) s.2.1.toList (frameAtB s.2.2) #[])

/-- **A protocol on `pi2K` on the chain's statement** (`stOf`; the same rounds). -/
def liftPiop2 (R : Compose.Piop pi2K Stk) : Compose.Piop pi2Spec.K Stk where
  pre s := R.pre (stOf s)
  post s := R.post (stOf s)
  pre_post s := R.pre_post (stOf s)
  err := R.err
  sound j s p m hj hp := R.sound j (stOf s) p m hj hp

/-! ## The proof the chain reads -/

/-- **The composed setup's output**: the setup's commitments (π1's `F` root and out-of-domain answer, π2's setup root
and answer). -/
abbrev SOut : Type := RecSetupRoots

instance : Inhabited RecSetupRoots := ⟨⟨⟨default, 0⟩, default, 0⟩⟩

/-- **The proof as π2's composed verifier reads it**: the public input, the recursive proof, π2's IV, the setup's
commitments. -/
structure P2Pf where
  input : Vector UInt8 32
  proof : RecProof
  iv : Vector UInt8 32
  roots : SOut

/-- The proof with the setup's commitments (`fix`). -/
def p2Fix (s : SOut) (π : P2Pf) : P2Pf := { π with roots := s }

/-- The proof with an IV. -/
def setIv2 (iv : Vector UInt8 32) (π : P2Pf) : P2Pf := { π with iv := iv }

/-- The setup's commitments a proof carries. -/
def p2Roots (π : P2Pf) : RecSetupRoots := π.roots

/-- **The rounds' messages the stream carries**, from byte `0`. -/
def p2Msgs (π : P2Pf) : List UniSound.UMsg := UniSound.msgsAt π.proof.stream pLen (RecPiop.pi2Rounds 4)

/-- **What the chain reads of a proof**: the statement (the IV, the input, the frame words of the declared claims)
and the messages. -/
def p2View (π : P2Pf) : FSt2 × List (RMsg E) :=
  ((π.iv, π.input, frameBytes π.proof), (p2Msgs π).map UniSound.toRMsg)

/-- **The transcript's inputs to the arithmetic**: the public scalars, `α, β, γ`, `t`, the `16` fold values, `ξ`,
`s`, `ρ`. -/
def p2Inputs (π : P2Pf) (ch : List (List E)) : Inputs E :=
  let vals := ((p2Msgs π).getD 2 default).2
  ⟨(stOf (p2View π).1).2, (ch.getD 0 []).getD 0 0, (ch.getD 0 []).getD 1 0, (ch.getD 0 []).getD 2 0,
    (ch.getD 1 []).getD 0 0, vals.take 16, vals.getD 16 0, vals.getD 17 0, (ch.getD 2 []).getD 0 0⟩

/-- **The arithmetic's values** on the transcript. -/
def p2Out (π : P2Pf) (ch : List (List E)) : Out E := (Spec.of cc).core.run (p2Inputs π ch)

/-- **The run's result** on the transcript (`reduceWith`'s `Reduced`). -/
def p2Reduced (π : P2Pf) (ch : List (List E)) : RecStatement.Reduced :=
  ⟨(p2Inputs π ch).scalars, (p2Inputs π ch).scalars.map pairPoint,
    ((((p2Msgs π).getD 0 default).1.getD default), (((p2Msgs π).getD 1 default).1.getD default)),
    ((((p2Msgs π).getD 0 default).2.getD 0 0), (((p2Msgs π).getD 1 default).2.getD 0 0)),
    p2Inputs π ch, p2Out π ch⟩

/-! ## The shapes, the decoders -/

/-- **An opening's shape**: the plain shape of a stack of `n` variables (`UniKeccakSound.plainShapeK`, version 1's
sizes `2^23 ..= 2^28`). -/
@[reducible] noncomputable def shK (n : ℕ) (h1 : 23 ≤ n) (h2 : n ≤ 28) : WhirShape :=
  UniKeccakSound.plainShapeK n h1 h2

/-- **The decoders**: `W`'s (round `0`, `24` variables) and `Q`'s (round `1`, `28`), `tableCode` of their plain
shapes, the candidates read back as stacks (`rdTab`). -/
noncomputable def p2Tc (i : ℕ) : TableCode Stk :=
  if i = 0 then tableCode (UniSound.plainL 24) logInvRate (shK 24 (by norm_num) (by norm_num)).adm UniSound.rdTab
  else tableCode (UniSound.plainL 28) logInvRate (shK 28 (by norm_num) (by norm_num)).adm UniSound.rdTab

/-! ## The claims, the openings -/

/-- **π1's `k`-th declared claim's words** (the frame's payload `k`). -/
def declWords (π : P2Pf) (k : ℕ) : List (List UInt8) := π.proof.pi1Claims.getD k []

/-- π1's `k`-th declared claim's root: its root word's (`rootOfWord`). -/
def pi1Root (π : P2Pf) (k : ℕ) : Bytes32 := toB (rootOfWord ((declWords π k).headD []))

/-- π1's `k`-th opening proof: `C1`'s, `C2`'s, the setup's. -/
def pi1Prf (k : ℕ) (π : P2Pf) : Compile.Proof :=
  if k = 0 then π.proof.c1 else if k = 1 then π.proof.c2 else π.proof.f

/-- `W`'s claim: its out-of-domain answer (the run's), its fold at `ρ`. -/
def wCl (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  some ((p2Reduced π ch).oods.1, (p2Out π ch).witnessPoint, (p2Out π ch).fold)

/-- The setup's claim: its out-of-domain answer (the setup's), at `(w, β)`, value `ξ`. -/
def sCl (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  some (π.roots.pi2Ood, (p2Out π ch).setupPoint, (p2Inputs π ch).ξ)

/-- `Q`'s identity claim. -/
def qIdCl (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  some ((p2Reduced π ch).oods.2, (p2Out π ch).quotientPoint, (p2Out π ch).quotientValue)

/-- `Q`'s pushes' claim. -/
def qPushCl (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  some ((p2Reduced π ch).oods.2, (p2Out π ch).pushesPoint, (p2Out π ch).pushesValue)


/-- **A PCS claim's opening** of the contract: a stack of `n` variables (`2^23 ..= 2^28` words), the claim (its
out-of-domain answer, point, value) read off the proof and the challenges (`none`: the contract rejects), its opening
proof, and what it opens. -/
structure PcsOp where
  n : ℕ
  lo : 23 ≤ n
  hi : n ≤ 28
  cl : P2Pf → List (List E) → Option (E × List E × E)
  prf : P2Pf → Compile.Proof
  tgt : Tgt P2Pf Stk n

/-- The root an opening reads (`GOp.root`): its round's, from the message the chain absorbed, or its setup's. -/
def PcsOp.rootB (o : PcsOp) (π : P2Pf) : Bytes32 :=
  match o.tgt with
  | .round i _ => ((msgK p2View π i).1).getD (Vector.replicate 32 0)
  | .setup r _ => r π

/-- **What an opening's claim says of a stack**: the point has the stack's variables, and the stack's polynomial
(`WhirBridge.Pcs.colEval`) has the value at the point (the PCS claim's point claim; its out-of-domain claim, at a point
π2's openings read off Keccak-256, is the openings' doom's: `FsOps.lean`'s `PcsOp.DoomedH`). -/
def PcsOp.holds (o : PcsOp) (π : P2Pf) (ch : List (List E)) (q : Column o.n) : Prop :=
  ∃ ood pt v, o.cl π ch = some (ood, pt, v) ∧ pt.length = o.n ∧ Pcs.colEval q pt = v

/-- **An opening's verifier** at the root it reads: the claim's PCS opening, or a rejection; at `W`'s and `Q`'s sizes
(`RecStatement.oodRead`: `W`'s `24`, `Q`'s `28`) the out-of-domain point read off Keccak-256 (`pcsOpenCO`, the contract's
`pcsOpenKO`), at the others (π1's, the setup's) at `oodPoint` (`UniKeccakSound.pcsOpenC`, the contract's `UniKeccak.pcsOpenK`). -/
def PcsOp.ver (o : PcsOp) (r : Digest) (π : P2Pf) (ch : List (List E)) : OracleComp KeccakCalls Bool :=
  match o.cl π ch with
  | none => pure false
  | some (ood, pt, v) =>
    if RecStatement.oodRead o.n then pcsOpenCO o.n r ood pt v (o.prf π)
    else UniKeccakSound.pcsOpenC o.n r ood pt v (o.prf π)

theorem PcsOp.queries (o : PcsOp) (r : Digest) (π : P2Pf) (ch : List (List E)) :
    IsTotalQueryBound (o.ver r π ch) 10150 := by
  unfold PcsOp.ver
  split
  · trivial
  · split
    · exact isTotalQueryBound_pcsOpenCO _ _ _ _ _ _
    · exact (UniKeccakSound.isTotalQueryBound_pcsOpenC _ _ _ _ _ _).mono (by norm_num)

theorem PcsOp.duplex (o : PcsOp) (r : Digest) (π : P2Pf) (ch : List (List E)) :
    LeanVM.Rpm.DuplexVm (o.ver r π ch) [] := by
  unfold PcsOp.ver
  split
  · trivial
  · split
    · exact duplexVm_pcsOpenCO _ _ _ _ _ _
    · exact UniKeccakSound.duplexVm_pcsOpenC _ _ _ _ _ _

/-- **An opening as a `Compose.GOp`** on its plain shape. -/
noncomputable def PcsOp.gop (o : PcsOp) : GOp P2Pf E Stk :=
  ⟨o.n, logInvRate, (shK o.n o.lo o.hi).adm, o.holds, o.ver, 10150, o.queries, o.duplex, o.tgt⟩

/-- A dummy column (a setup target's fixed stack, not read: `p2Stk` gives the stacks). -/
def col0 (μ : ℕ) : Column μ := UniSound.colOf #[] μ

/-- A round's candidate read back as a stack (`rdTab` of the plain layout's table). -/
def rdP (n : ℕ) (q : Column n) : Stk := UniSound.rdTab (tabOf (UniSound.plainL n) q)

/-- `W`'s claim's opening. -/
def wPcs : PcsOp := ⟨24, by norm_num, by norm_num, wCl, fun π => π.proof.w, .round 0 (rdP 24)⟩

/-- The setup's claim's opening (its root the proof's). -/
def sPcs : PcsOp :=
  ⟨25, by norm_num, by norm_num, sCl, fun π => π.proof.setup, .setup (fun π => toB π.roots.pi2) (col0 _)⟩

/-- `Q`'s identity claim's opening. -/
def qIdOp : PcsOp := ⟨28, by norm_num, by norm_num, qIdCl, fun π => π.proof.qId, .round 1 (rdP 28)⟩

/-- `Q`'s pushes' claim's opening. -/
def qPushOp : PcsOp := ⟨28, by norm_num, by norm_num, qPushCl, fun π => π.proof.qPush, .round 1 (rdP 28)⟩

/-- **π2's four PCS claims' openings**, in the contract's order: `W` (round `0`), the setup, `Q`'s two (round `1`). -/
def p2Pcs : List PcsOp := [wPcs, sPcs, qIdOp, qPushOp]

/-- **π1's `k`-th declared claim's opening** (the contract's `pcsOpenWords` on the declared words): decoded
(`claimOfWords`), then opened at its point's length, the out-of-domain point read off Keccak-256 at `W`'s and `Q`'s
sizes (`oodRead`, `pcsOpenCO`) and `oodPoint` at the others (`UniKeccakSound.pcsOpenC`); a word list that does not
decode is rejected. -/
def declVer (k : ℕ) (π : P2Pf) : OracleComp KeccakCalls Bool :=
  match claimOfWords (declWords π k) with
  | none => pure false
  | some (_, ood, pt, v) =>
    if RecStatement.oodRead pt.length then pcsOpenCO pt.length (ofB (pi1Root π k)) ood pt v (pi1Prf k π)
    else UniKeccakSound.pcsOpenC pt.length (ofB (pi1Root π k)) ood pt v (pi1Prf k π)

theorem declVer_queries (k : ℕ) (π : P2Pf) : IsTotalQueryBound (declVer k π) 10150 := by
  unfold declVer
  split
  · trivial
  · split
    · exact isTotalQueryBound_pcsOpenCO _ _ _ _ _ _
    · exact (UniKeccakSound.isTotalQueryBound_pcsOpenC _ _ _ _ _ _).mono (by norm_num)

theorem declVer_duplex (k : ℕ) (π : P2Pf) : LeanVM.Rpm.DuplexVm (declVer k π) [] := by
  unfold declVer
  split
  · trivial
  · split
    · exact duplexVm_pcsOpenCO _ _ _ _ _ _
    · exact UniKeccakSound.duplexVm_pcsOpenC _ _ _ _ _ _

/-- **π1's `k`-th declared claim's opening as a `GOp`**: a setup opening at the root the claim names, of no stack
(nothing is concluded of it: its claim `True`; `wOpM` carries it). -/
noncomputable def declOp (k : ℕ) : GOp P2Pf E Stk :=
  ⟨23, logInvRate, (shK 23 (by norm_num) (by norm_num)).adm, fun _ _ _ => True, fun _ π _ => declVer k π, 10150,
    fun _ π _ => declVer_queries k π, fun _ π _ => declVer_duplex k π, .setup (fun π => pi1Root π k) (col0 _)⟩

/-- **The seven openings** as `GOp`s, in the contract's order: π1's three declared claims, then π2's four. -/
noncomputable def p2Ops7 : List (GOp P2Pf E Stk) := [declOp 0, declOp 1, declOp 2] ++ p2Pcs.map PcsOp.gop

/-- **π1's three declared claims and `W`'s as one opening**: the four verifiers in turn (their verdicts and-ed), its
claim `W`'s (π1's claims conclude nothing), at `W`'s root. -/
noncomputable def wOpM : GOp P2Pf E Stk :=
  ⟨24, logInvRate, (shK 24 (by norm_num) (by norm_num)).adm, wPcs.holds,
    fun r π ch => declVer 0 π >>= fun a => declVer 1 π >>= fun b => declVer 2 π >>= fun c =>
      wPcs.ver r π ch >>= fun d => pure (a && (b && (c && d))),
    4 * 10150,
    fun r π ch => (isTotalQueryBound_bind (declVer_queries 0 π) fun a =>
      isTotalQueryBound_bind (declVer_queries 1 π) fun b =>
        isTotalQueryBound_bind (declVer_queries 2 π) fun c =>
          isTotalQueryBound_bind (ob := fun d => (pure (a && (b && (c && d))) : OracleComp KeccakCalls Bool))
            (n₂ := 0) (wPcs.queries r π ch) fun _ => trivial).mono (by norm_num),
    fun r π ch => LeanVM.Rpm.DuplexVm.bind (declVer_duplex 0 π) fun _ =>
      LeanVM.Rpm.DuplexVm.bind (declVer_duplex 1 π) fun _ =>
        LeanVM.Rpm.DuplexVm.bind (declVer_duplex 2 π) fun _ =>
          LeanVM.Rpm.DuplexVm.bind (wPcs.duplex r π ch) fun _ => trivial,
    .round 0 (rdP 24)⟩

/-- **`Q`'s two claims as one opening**: the two verifiers in turn (their verdicts and-ed); its claims both on one
stack. -/
noncomputable def qOp : GOp P2Pf E Stk :=
  ⟨28, logInvRate, (shK 28 (by norm_num) (by norm_num)).adm,
    fun π ch q => qIdOp.holds π ch q ∧ qPushOp.holds π ch q,
    fun r π ch => qIdOp.ver r π ch >>= fun a => qPushOp.ver r π ch >>= fun b => pure (a && b),
    2 * 10150,
    fun r π ch => (isTotalQueryBound_bind (qIdOp.queries r π ch) fun a =>
      isTotalQueryBound_bind (ob := fun b => (pure (a && b) : OracleComp KeccakCalls Bool)) (n₂ := 0)
        (qPushOp.queries r π ch) fun _ => trivial).mono (by norm_num),
    fun r π ch => LeanVM.Rpm.DuplexVm.bind (qIdOp.duplex r π ch) fun _ =>
      LeanVM.Rpm.DuplexVm.bind (qPushOp.duplex r π ch) fun _ => trivial,
    .round 1 (rdP 28)⟩

/-- **The openings of the chain's composition**: π1's three and `W`'s as one, the setup's, `Q`'s two as one. -/
noncomputable def p2Ops : List (GOp P2Pf E Stk) := [wOpM, sPcs.gop, qOp]

/-- The setup's table at π1's setup commitment (`Pi2Circuit.setupStack` of the circuit for π1's contract IV). -/
def setupStackAt (D : RecDeployment) (roots : RecSetupRoots) : Array K := (D.circuitAt roots.pi1).setupStack

/-- The setup's table as a column of `2^25` words, at π1's setup commitment. -/
def setupCol (D : RecDeployment) (r1 : UniKeccak.SetupRootsK) : Column 25 :=
  UniSound.colOf (D.circuitAt r1).setupStack 25

/-- **The openings' stacks**: the setup's table at the proof's commitments for the setup's opening (the only one of
`2^25` words), none for the others. -/
noncomputable def p2Stk (D : RecDeployment) (o : GOp P2Pf E Stk) : Option (P2Pf → Column o.μ) :=
  if h : o.μ = 25 then some fun π => cast (by rw [h]) (setupCol D π.roots.pi1) else none

/-! ## The setup -/

/-- The plain shape of `2^25` words, on which the setup's tree is built. -/
@[reducible] noncomputable def sh25 : WhirShape := UniSound.plainShape 25 (by norm_num) (by norm_num)

/-- **The setup's commitments** from its two roots: π1's (`F`'s root and the Keccak setup stack's out-of-domain
answer there, `UniKeccakSound.skOf`), π2's (its root and the setup table's answer there, `Pi2Circuit.setupOod`). -/
def setupOut (D : RecDeployment) (r r2 : Bytes32) : SOut :=
  ⟨UniKeccakSound.skOf D.pi1 (UniSound.rootsOfS r), ofB r2,
    (D.circuitAt (UniKeccakSound.skOf D.pi1 (UniSound.rootsOfS r))).setupOod (ofB r2)⟩

/-- **The composed setup**: π1's one tree (the Keccak setup stack's, `UniKeccakSound.setupK1`), then π2's, of the
setup's table at π1's setup commitment; the commitments. -/
noncomputable def p2Setup (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1) : OracleComp KeccakCalls SOut :=
  UniKeccakSound.setupK1 hs (UniKeccakSound.colFK D.pi1) >>= fun r =>
    stackSetupS sh25 (setupCol D (UniKeccakSound.skOf D.pi1 (UniSound.rootsOfS r))) >>= fun r2 =>
      pure (setupOut D r r2)

/-! ## π2's IV, the composed verifier -/

/-- σ's hash input (`digestWith`): its tags, four little-endian bytes each. -/
def sigmaBytes (c : Pi2Circuit) : List UInt8 := (List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4

/-- κ's hash input: eight bytes each. -/
def kappaBytes (c : Pi2Circuit) : List UInt8 := (List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat

/-- The circuit's digest's input (`digestWith`): the encoding, σ's and κ's hashes. -/
def digIn (c : Pi2Circuit) (sg kp : Bytes32) : List UInt8 := c.circuit.encoding ++ sg.toList ++ kp.toList

/-- π2's IV's input (`prover::iv`, v3): the tag, π1's contract IV, π2's setup root and out-of-domain answer (its 24
bytes), the circuit's digest, `log_n`. -/
def ivIn (D : RecDeployment) (roots : RecSetupRoots) (d : Bytes32) : List UInt8 :=
  ivTag ++ D.pi1IvAt roots.pi1 ++ digestBytes roots.pi2 ++ UniKeccak.elementBytes24 roots.pi2Ood ++ d.toList ++
    [cc.logN.toUInt8]

/-- **π2's IV** as the composed verifier computes it, with its intermediate answers: σ's and κ's hashes, the circuit's
digest, then the IV (`prover::iv`), four Keccak-256 calls. -/
def p2IvKC4 (D : RecDeployment) (π : P2Pf) : OracleComp KeccakCalls (Bytes32 × Bytes32 × Bytes32 × Bytes32) :=
  hash256 (sigmaBytes (D.circuitAt (p2Roots π).pi1)) >>= fun sg =>
    hash256 (kappaBytes (D.circuitAt (p2Roots π).pi1)) >>= fun kp =>
      hash256 (digIn (D.circuitAt (p2Roots π).pi1) sg kp) >>= fun d =>
        hash256 (ivIn D (p2Roots π) d) >>= fun iv => pure (sg, kp, d, iv)

/-- The four IV calls' log (input, answer), from their answers. -/
def ivLog (D : RecDeployment) (π : P2Pf) (x : Bytes32 × Bytes32 × Bytes32 × Bytes32) : Transcript :=
  [(sigmaBytes (D.circuitAt (p2Roots π).pi1), x.1), (kappaBytes (D.circuitAt (p2Roots π).pi1), x.2.1),
    (digIn (D.circuitAt (p2Roots π).pi1) x.1 x.2.1, x.2.2.1), (ivIn D (p2Roots π) x.2.2.1, x.2.2.2)]

/-- **The composed verifier with the IV**: π2's IV, then the chain and the openings on the proof carrying it. -/
noncomputable def p2Ver (D : RecDeployment) (π : P2Pf) :
    OracleComp KeccakCalls ((Bytes32 × Bytes32 × Bytes32 × Bytes32) × (List (List E) × List Bool)) :=
  p2IvKC4 D π >>= fun x => (fun v => (x, v)) <$>
    verU pi2Spec p2View (gopsRun p2View p2Ops) (setIv2 x.2.2.2 π)

/-- The outcome with the IV written in the proof. -/
def ivOut2 (z : P2Pf × ((Bytes32 × Bytes32 × Bytes32 × Bytes32) × (List (List E) × List Bool))) :
    P2Pf × (List (List E) × List Bool) :=
  (setIv2 z.2.1.2.2.2 z.1, z.2.2)

/-- **The two-oracle adversary with the IV**: `A₀`, then the IV of the proof the setup fixes. -/
def p2IvAdv (D : RecDeployment) (A₀ : SOut → OracleComp KeccakCalls P2Pf) (s : SOut) :
    OracleComp KeccakCalls P2Pf :=
  A₀ s >>= fun π => (fun x => setIv2 x.2.2.2 π) <$> p2IvKC4 D (p2Fix s π)

/-- **The adversary of the composed game**: π2's adversary given the setup's commitments, its input and proof. -/
def p2Adv (A : RecAdversary) (s : SOut) : OracleComp Common.RandomPermutationOracles P2Pf :=
  (fun z : Vector UInt8 32 × RecProof => (⟨z.1, z.2, Vector.replicate 32 0, s⟩ : P2Pf)) <$> A s

/-! ## The check, the links -/

/-- **The verifier's check** (what an accepting run satisfies): the stream of `544` bytes, the challenges of the
rounds' lengths, and the value the contract requires nonzero. -/
def p2Check (π : P2Pf) (ch : List (List E)) : Prop :=
  π.proof.stream.size = sLen ∧ ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧
    (ch.getD 2 []).length = 1 ∧ (p2Out π ch).all ≠ 0

/-- **A candidate is good**: at `W`'s round, a stack satisfying `W`'s claim; at `Q`'s, one satisfying `Q`'s two. -/
def p2Good (i : ℕ) (π : P2Pf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧ ClaimOn 24 q ((p2Out π ch).witnessPoint, (p2Out π ch).fold)
  else if i = 1 then ∃ q, c = some q ∧
      ClaimOn 28 q ((p2Out π ch).quotientPoint, (p2Out π ch).quotientValue) ∧
      ClaimOn 28 q ((p2Out π ch).pushesPoint, (p2Out π ch).pushesValue)
  else True

/-- **The setup's table is good**: it satisfies the setup's claim. -/
def p2GoodS (D : RecDeployment) (π : P2Pf) (ch : List (List E)) : Prop :=
  ClaimOn 25 (fun j ↦ (setupStackAt D (p2Roots π)).getD j 0) ((p2Out π ch).setupPoint, (p2Inputs π ch).ξ)

/-! ## The composed event, the bridge facts -/

/-- **π2's break on the composed game's outcome**: the check, the openings accept, and no candidate of `W`'s root read
off the transcript has `P`. -/
def P2BreaksRel (P : RecSetupRoots → Pi2St → Stk → Prop) (z : OutK P2Pf E (List Bool)) : Prop :=
  p2Check z.1.1 z.1.2.1 ∧ (∀ k < p2Ops.length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (p2Tc i).commit) p2View z, ∀ q, c = some q →
      ¬ P (p2Roots z.1.1) (stOf (p2View z.1.1).1) q

/-- The setup's commitments of its trees. -/
def rootsB2 (t : RecSetupTrees) : SOut := t.roots

/-- The setup's Keccak-256 evaluations as a transcript. -/
def setupTr2 (t : RecSetupTrees) : Transcript := t.evaluations.map fun e => (e.1, toB e.2)

/-- **SETUP**: the composed setup over `π`, logged, is the Statement's `setupTreesWith` over `π`, its output the
trees' commitments, its log the trees' evaluations. -/
def Pi2SetupBridge (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1) : Prop :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC (p2Setup D hs)) =
    (fun t : RecSetupTrees => (rootsB2 t, setupTr2 t)) <$> D.setupTreesWith Common.queryPermutation

/-- **WALK**: on a stream of `544` bytes, in every lawful monad and over every permutation, π2's run (on the frame
words of the declared claims) has the verdict and result of the chain's challenges read by the value the contract
requires nonzero and the result `p2Reduced`, the chain over Keccak-256 the sponge over the permutation. -/
def Pi2Walk : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (π : P2Pf), π.proof.stream.size = sLen →
      (fun o : RecStatement.Outcome => (o.accepts, o.result)) <$>
          runWith F (Spec.of cc) π.iv.toList π.input.toList (frameOf π.proof.pi1Claims) π.proof.stream =
        (fun ch => ((p2Reduced π ch).out.all != 0,
            (Except.ok (p2Reduced π ch) : Except UniStatement.UniError RecStatement.Reduced))) <$>
          pi2Spec.chain (fun x => toB <$> keccak256With F x) (p2View π).1 (p2View π).2

/-- **WALK REJECTS**: on a stream of another length, every outcome of π2's run over `π` rejects. -/
def Pi2WalkReject : Prop :=
  ∀ π : P2Pf, π.proof.stream.size ≠ sLen →
    ∀ o ∈ support (runWith Common.queryPermutation (Spec.of cc) π.iv.toList π.input.toList
      (frameOf π.proof.pi1Claims) π.proof.stream),
      o.accepts = false

/-- **EXTRACTOR READING**: on a stream holding `W`'s root, a candidate of `W`'s root that the composed extractor reads
off the setup's log and a permutation transcript is a stack of π2's extractor's list (`wCandidates`) on the setup's
evaluations and that transcript. -/
def Pi2ExtractBridge (D : RecDeployment) : Prop :=
  ∀ (t : RecSetupTrees) (T : Common.OracleQueryLog) (z : P2Pf × (List (List E) × List Bool)) (q : Stk),
    pLen + 32 ≤ z.1.proof.stream.size →
    some q ∈ extractorK (fun i => (p2Tc i).commit) p2View (z, setupTr2 t ++ evalTr (permutationQueries T)) →
      ∃ w ∈ wCandidates D t.roots (preimagesOf t.evaluations T) z.1.proof, stkOf w = q

end RecCompose
