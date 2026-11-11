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
deployment's circuit (`cc = Data.circuit`: `2^24` positions, rows of `16`, the reads `C1`'s and `C2`'s roots then
`19` elements, `520` bytes):

* **the chain** (`pi2Spec`, `Compose.ChainSpecU`): the statement `FSt2` (π2's IV, the public input, the public
  data's `520` bytes), the label the seed's input `name ‖ iv ‖ input` (`RecStatement.name`, 16 bytes), the public
  data the statement's bytes before round `0`'s message (`W`'s root), the messages as the stream carries them
  (`UniSound.uniEnc`: a root's 32 bytes as they are, `24`-byte scalars), `RecPiop.pi2Rounds 4`;
* **the proof the chain reads** (`P2Pf`: the input, the recursive proof, the IV, the setup's commitments) and its view
  (`p2View`: the stream's messages from byte `520`);
* **the eight openings** (`p2Pcs`, each a `PcsOp`: the EIP's PCS claim `(root, ood, point, value)` on a stack of `n`
  variables, opened by `UniKeccakSound.pcsOpenC`, a `Compose.GOp` on the plain shape `UniKeccakSound.plainShapeK n`),
  in the contract's order: π1's `C1`, `C2`, `F` (`27`, `26`, `23` variables at the reference shape, their claims the
  calls' words; nothing concluded of them), π2's `W` (round `0`, `24`), the setup (`25`, its stack read off the
  proof's commitments: `p2Stk`), `Q`'s three claims (round `1`, `28`, one root). For the chain's composition the
  first five and `Q`'s three as **one** opening (`p2Ops`, `qOp`: the three verifiers in turn, its claims all three on
  one stack), which the out-of-domain answer makes possible (`FsOps.lean`);
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

/-- The real deployment's circuit (`RecDeployment.Real`: at every IV). -/
abbrev cc : RecStatement.Circuit := Data.circuit

/-- The public data's bytes (`2 · 32 + 19 · 24`). -/
abbrev pLen : ℕ := 520

/-- The stream's bytes: the public data, `W`'s and `Q`'s commitments (roots and out-of-domain answers), the `2^4 + 2`
values. -/
abbrev sLen : ℕ := 1064

/-! ## The chain -/

/-- **π2's chain statement**: π2's IV, the public input, the public data's `520` bytes. -/
abbrev FSt2 : Type := Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 pLen

/-- **The seed's input** (`runWith`): `name ‖ iv ‖ input`. -/
def p2Label (s : FSt2) : List UInt8 := RecStatement.name ++ s.1.toList ++ s.2.1.toList

theorem name_length : RecStatement.name.length = 16 := by decide +kernel

theorem p2Label_length (s : FSt2) : (p2Label s).length = 80 := by
  simp [p2Label, name_length]

theorem p2Label_take (s : FSt2) : (p2Label s).take RecStatement.name.length = RecStatement.name := by
  unfold p2Label
  rw [List.append_assoc]
  exact List.take_left' rfl

theorem p2Label_inj {s s' : FSt2} (h : p2Label s = p2Label s') : s.1 = s'.1 ∧ s.2.1 = s'.2.1 := by
  unfold p2Label at h
  rw [List.append_assoc, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, Vector.toList_inj.mp h3⟩

theorem p2Stmt_inj (s s' : FSt2) (hl : p2Label s = p2Label s') (hp : s.2.2.toList = s'.2.2.toList) :
    s = s' := by
  obtain ⟨h1, h2⟩ := p2Label_inj hl
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := s'
  simp only at h1 h2 hp
  rw [h1, h2, Vector.toList_inj.mp hp]

/-- The `ChainSpec` of π2's rounds (its label the seed's input and the public data: only its limbs and rounds are
read). -/
def p2K : ChainSpec E FSt2 where
  lim := UniSound.uLimbs
  label s := p2Label s ++ s.2.2.toList
  label_injective s s' h := by
    have hl : (p2Label s).length = (p2Label s').length := by rw [p2Label_length, p2Label_length]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact p2Stmt_inj s s' h1 h2
  label_len s := by
    have : (p2Label s ++ s.2.2.toList).length = 600 := by
      simp [p2Label_length, pLen]
    rw [this]
    decide
  rounds := RecPiop.pi2Rounds 4

/-- **An input refers to a digest**: `Compose.Refers`, or the digest is the root the input absorbs after a state
(bytes `32 … 64`, `Q`'s) or after a state and the public data (bytes `552 … 584`, `W`'s). -/
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

/-- **π2's transcript as a chain over an encoding** (`KeccakChannel` on `RecPiop.pi2Rounds 4`, the public data
before `W`'s root). -/
noncomputable def pi2Spec : ChainSpecU E FSt2 where
  K := p2K
  label := p2Label
  tag := RecStatement.name
  tag_le := by rw [name_length]; decide
  label_tag := p2Label_take
  pre s := s.2.2.toList
  pre_len s s' := by simp
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
  rf_pre s st r l := by
    refine Or.inr (Or.inr ?_)
    simp only [stepIn, UniSound.uniEnc]
    rw [show (st.toList ++ (s.2.2.toList ++ (UniSound.revRoot r ++ UniSound.scalars24 l))).drop (32 + pLen) =
        UniSound.revRoot r ++ UniSound.scalars24 l by
      rw [← List.drop_drop, List.drop_left' (by simp), List.drop_left' (by simp)]]
    rw [List.take_left' (by simp)]

@[simp] theorem pi2Spec_rounds : pi2Spec.K.rounds = RecPiop.pi2Rounds 4 := rfl

/-! ## The protocol on the chain's statement -/

/-- **π2's PIOP statement of a chain statement**: the public input, and the public scalars (`pi2Pubs`: the input's
four words, then the reads' scalars of the public data). -/
def stOf (s : FSt2) : Pi2St := (s.2.1, pi2Pubs (Spec.of cc) s.2.1.toList s.2.2.toArray)

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

/-- The public data's `520` bytes (missing bytes `0`). -/
def pubBytes (b : Array UInt8) : Vector UInt8 pLen := Vector.ofFn fun i => b.getD i.val 0

/-- **The rounds' messages the stream carries**, from byte `520`. -/
def p2Msgs (π : P2Pf) : List UniSound.UMsg := UniSound.msgsAt π.proof.stream pLen (RecPiop.pi2Rounds 4)

/-- **What the chain reads of a proof**: the statement (the IV, the input, the public data) and the messages. -/
def p2View (π : P2Pf) : FSt2 × List (RMsg E) :=
  ((π.iv, π.input, pubBytes π.proof.stream), (p2Msgs π).map UniSound.toRMsg)

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

/-- The Keccak π1's `k`-th claim's variables at the reference shape: `27`, `26`, `23` (`C1`, `C2`, the setup). -/
def pi1Vars (k : ℕ) : ℕ := if k = 0 then 27 else if k = 1 then 26 else 23

/-! ## The claims, the openings -/

/-- π1's claims' words, from the stream and the run's result (`pcsCalls`' first three). -/
def pi1Words (D : RecDeployment) (π : P2Pf) (ch : List (List E)) : List (List (List UInt8)) :=
  (pi1CallsWith D.pi1Calls π.roots.pi1).map (·.map (callWord cc.reads π.proof.stream (p2Reduced π ch)))

/-- π1's `k`-th claim's root: its root word's (`rootOfWord`; the word is the stream's or the setup's, not the run's). -/
def pi1Root (D : RecDeployment) (π : P2Pf) (k : ℕ) : Bytes32 :=
  toB (rootOfWord (((pi1Words D π []).getD k []).headD []))

/-- **π1's `k`-th claim** decoded from its words (`claimOfWords`): its out-of-domain answer, point and value. -/
def pi1Cl (D : RecDeployment) (k : ℕ) (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  (claimOfWords ((pi1Words D π ch).getD k [])).map fun c => c.2

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

/-- `Q`'s claim at `h`'s top coefficient. -/
def qSumCl (π : P2Pf) (ch : List (List E)) : Option (E × List E × E) :=
  some ((p2Reduced π ch).oods.2, (p2Out π ch).sumPoint, (p2Out π ch).sumValue)

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

/-- **An opening's verifier** at the root it reads: the claim's PCS opening, or a rejection; at π2's sizes
(`RecStatement.pi2Size`: `24`, `25`, `28`) the out-of-domain point read off Keccak-256 (`pcsOpenCO`, the contract's
`pcsOpenKO`), at π1's at `oodPoint` (`UniKeccakSound.pcsOpenC`, the contract's `UniKeccak.pcsOpenK`). -/
def PcsOp.ver (o : PcsOp) (r : Digest) (π : P2Pf) (ch : List (List E)) : OracleComp KeccakCalls Bool :=
  match o.cl π ch with
  | none => pure false
  | some (ood, pt, v) =>
    if RecStatement.pi2Size o.n then pcsOpenCO o.n r ood pt v (o.prf π)
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

/-- `Q`'s identity claim's opening. -/
def qIdOp : PcsOp := ⟨28, by norm_num, by norm_num, qIdCl, fun π => π.proof.qId, .round 1 (rdP 28)⟩

/-- `Q`'s pushes' claim's opening. -/
def qPushOp : PcsOp := ⟨28, by norm_num, by norm_num, qPushCl, fun π => π.proof.qPush, .round 1 (rdP 28)⟩

/-- `Q`'s sum claim's opening. -/
def qSumOp : PcsOp := ⟨28, by norm_num, by norm_num, qSumCl, fun π => π.proof.qSum, .round 1 (rdP 28)⟩

/-- **The first five openings**, in the contract's order: π1's `C1`, `C2`, `F` (their roots the claims' root words),
π2's `W` (round `0`) and the setup (its root the proof's). -/
def p2Pcs5 (D : RecDeployment) : List PcsOp :=
  [⟨27, by norm_num, by norm_num, pi1Cl D 0, pi1Prf 0, .setup (fun π => pi1Root D π 0) (col0 _)⟩,
    ⟨26, by norm_num, by norm_num, pi1Cl D 1, pi1Prf 1, .setup (fun π => pi1Root D π 1) (col0 _)⟩,
    ⟨23, by norm_num, by norm_num, pi1Cl D 2, pi1Prf 2, .setup (fun π => pi1Root D π 2) (col0 _)⟩,
    ⟨24, by norm_num, by norm_num, wCl, fun π => π.proof.w, .round 0 (rdP 24)⟩,
    ⟨25, by norm_num, by norm_num, sCl, fun π => π.proof.setup, .setup (fun π => toB π.roots.pi2) (col0 _)⟩]

/-- **The eight openings**, in the contract's order: the first five, then `Q`'s three. -/
def p2Pcs (D : RecDeployment) : List PcsOp := p2Pcs5 D ++ [qIdOp, qPushOp, qSumOp]

/-- The eight openings as `GOp`s. -/
noncomputable def p2Ops8 (D : RecDeployment) : List (GOp P2Pf E Stk) := (p2Pcs D).map PcsOp.gop

/-- **`Q`'s three claims as one opening**: the three verifiers in turn (their verdicts and-ed); its claims all three
on one stack. -/
noncomputable def qOp : GOp P2Pf E Stk :=
  ⟨28, logInvRate, (shK 28 (by norm_num) (by norm_num)).adm,
    fun π ch q => qIdOp.holds π ch q ∧ qPushOp.holds π ch q ∧ qSumOp.holds π ch q,
    fun r π ch => qIdOp.ver r π ch >>= fun a => qPushOp.ver r π ch >>= fun b =>
      qSumOp.ver r π ch >>= fun c => pure (a && (b && c)),
    3 * 10150,
    fun r π ch => (isTotalQueryBound_bind (qIdOp.queries r π ch) fun a =>
      isTotalQueryBound_bind (qPushOp.queries r π ch) fun b =>
        isTotalQueryBound_bind (ob := fun c => (pure (a && (b && c)) : OracleComp KeccakCalls Bool)) (n₂ := 0)
          (qSumOp.queries r π ch) fun _ => trivial).mono (by norm_num),
    fun r π ch => LeanVM.Rpm.DuplexVm.bind (qIdOp.duplex r π ch) fun _ =>
      LeanVM.Rpm.DuplexVm.bind (qPushOp.duplex r π ch) fun _ =>
        LeanVM.Rpm.DuplexVm.bind (qSumOp.duplex r π ch) fun _ => trivial,
    .round 1 (rdP 28)⟩

/-- **The openings of the chain's composition**: the first five, then `Q`'s as one. -/
noncomputable def p2Ops (D : RecDeployment) : List (GOp P2Pf E Stk) := (p2Pcs5 D).map PcsOp.gop ++ [qOp]

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
    verU pi2Spec p2View (gopsRun p2View (p2Ops D)) (setIv2 x.2.2.2 π)

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

/-- **The verifier's check** (what an accepting run satisfies): the stream of `1064` bytes, the challenges of the
rounds' lengths, and the value the contract requires nonzero. -/
def p2Check (π : P2Pf) (ch : List (List E)) : Prop :=
  π.proof.stream.size = sLen ∧ ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧
    (ch.getD 2 []).length = 1 ∧ (p2Out π ch).all ≠ 0

/-- **A candidate is good**: at `W`'s round, a stack satisfying `W`'s claim; at `Q`'s, one satisfying `Q`'s three. -/
def p2Good (i : ℕ) (π : P2Pf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧ ClaimOn 24 q ((p2Out π ch).witnessPoint, (p2Out π ch).fold)
  else if i = 1 then ∃ q, c = some q ∧
      ClaimOn 28 q ((p2Out π ch).quotientPoint, (p2Out π ch).quotientValue) ∧
      ClaimOn 28 q ((p2Out π ch).pushesPoint, (p2Out π ch).pushesValue) ∧
      ClaimOn 28 q ((p2Out π ch).sumPoint, (p2Out π ch).sumValue)
  else True

/-- **The setup's table is good**: it satisfies the setup's claim. -/
def p2GoodS (D : RecDeployment) (π : P2Pf) (ch : List (List E)) : Prop :=
  ClaimOn 25 (fun j ↦ (setupStackAt D (p2Roots π)).getD j 0) ((p2Out π ch).setupPoint, (p2Inputs π ch).ξ)

/-! ## The composed event, the bridge facts -/

/-- **π2's break on the composed game's outcome**: the check, the openings accept, and no candidate of `W`'s root read
off the transcript has `P`. -/
def P2BreaksRel (D : RecDeployment) (P : RecSetupRoots → Pi2St → Stk → Prop) (z : OutK P2Pf E (List Bool)) : Prop :=
  p2Check z.1.1 z.1.2.1 ∧ (∀ k < (p2Ops D).length, z.1.2.2.getD k false = true) ∧
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

/-- **WALK**: on a stream of `1064` bytes, in every lawful monad and over every permutation, π2's run's verdict and
result are the chain's challenges read by the value the contract requires nonzero and the result `p2Reduced`, the
chain over Keccak-256 the sponge over the permutation. -/
def Pi2Walk : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (π : P2Pf), π.proof.stream.size = sLen →
      (fun o : RecStatement.Outcome => (o.accepts, o.result)) <$>
          runWith F (Spec.of cc) π.iv.toList π.input.toList π.proof.stream =
        (fun ch => ((p2Reduced π ch).out.all != 0,
            (Except.ok (p2Reduced π ch) : Except UniStatement.UniError RecStatement.Reduced))) <$>
          pi2Spec.chain (fun x => toB <$> keccak256With F x) (p2View π).1 (p2View π).2

/-- **WALK REJECTS**: on a stream of another length, every outcome of π2's run over `π` rejects. -/
def Pi2WalkReject : Prop :=
  ∀ π : P2Pf, π.proof.stream.size ≠ sLen →
    ∀ o ∈ support (runWith Common.queryPermutation (Spec.of cc) π.iv.toList π.input.toList π.proof.stream),
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
