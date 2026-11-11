-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The walk is `formal/UniKeccakComplete`'s
-- (`K/Rec4CostBound.lean`'s `wc_proveStreamRec4With`, `costP_proveRec4With`) redone for the lengths of the hashed
-- inputs, in `Pi2AlphaLen`'s calculus (`WS`, `LenP`). Ported from this library's π1-rec3 version
-- (`Pi1KeccakCensus.lean`, retired). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness`'s `HashOK`.
import RecCompose.Pi1Rec4Transfer
import RecCompose.Pi2AlphaLen

/-!
# π1-rec4's honest prover hashes nothing of `2^26` bytes

`Pi2P1.Pi1HashShort` asks every Keccak-256 query of π1's two-call prover to be shorter than `2^26` bytes (the length
of π2's `σ` hash, which starts the chain that makes `α`'s input fresh). For the recursion's prover `p1kK4`:

* **`ws_proveStreamRec4K`**: π1-rec4's stream (UniKeccakComplete's `proveStreamRec4With` at `H = callKeccak256`,
  `W = rateSigma`) hashes only short inputs, writing at most `streamBytes4` bytes, its claims of at most
  `batchVarsBound` coordinates (`wc_proveStreamRec4With`'s walk in `WS`: the wide draws hash the state and the stream,
  at most `2^14` bytes; Flock's `42` draws; the commitments' trees `512`-byte rows and `64`-byte nodes,
  `Pi2A.hashOK_commitReal`);
* **`hashOK_proveRec4K`**: the prover: the setup's tree, the Keccak contract's IV (`163` bytes and the program IV), the
  seed (`80` bytes), the stream, three PCS openings of a point of at most `2^14` coordinates
  (`Pi2A.hashOK_pcsProveH`);
* **`hashOK_uniProverRec4_ref`**: at the reference shape (stream `6952 + 3696 ≤ 2^14` bytes, `27` batch variables) and
  a program IV of at most `2^16` bytes;
* **`hashShort_p1kK4`**: hence the recursion's prover (`hashOK_p1kK4_of`: its Fiat–Shamir hashes are no queries), at
  the real deployment.
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniKeccakComplete UniKeccakComplete.Rec4
open RecStatement (RecDeployment)
open E2ECompleteness (HashOK hashOK_callKeccak256)
open UniKeccakComplete.Cost (WC WInv StreamOK wc_seq wc_mono wc_pure wc_forIn_list wc_sendInteger wc_sendRoot
  wc_sendScalar)
open UniKeccakComplete.Bounds (batchVarsBound)
open Pi2A (Short WS ws_of_wc ws_seq ws_lift lenP_of_hashOK two26)

/-! ## π1-rec4's stream -/

/-- **From Flock to `C2`'s root, only short inputs.** -/
theorem ws_midB4 (tr : Trace) (bus : List E)
    (hk : flockBlocks4 (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4 ≤ 16384) :
    WS (midB4 callKeccak256 (commitReal callKeccak256) tr bus)
      (flockBytes (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4 + 56) fun _ _ ↦ True := by
  unfold midB4
  refine ws_seq (ws_of_wc (wc_flockProve4 _ _ _ _) hk) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (Pi2A.hashOK_commitReal _ _ _)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendScalar _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  exact ws_of_wc (k := 0) (wc_mono (wc_pure _) le_rfl (Nat.zero_le _) fun _ _ _ ↦ trivial) (by norm_num)

/-- **π1-rec4's stream hashes only short inputs** (`wc_proveStreamRec4With`'s walk), given Flock's blocks and the
batch's variables at most `2^14`. -/
theorem ws_proveStreamRec4K (tr : Trace)
    (hk : flockBlocks4 (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4 ≤ 16384)
    (hV : 2 + batchVarsBound tr.shape ≤ 16384) :
    WS (proveStreamRec4With callKeccak256 rateSigma (commitReal callKeccak256) tr)
      (streamBytes4 tr.shape tr.rows.length) (StreamOK (batchVarsBound tr.shape)) := by
  unfold proveStreamRec4With streamBytes4
  refine ws_seq (ws_of_wc (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl) (by simp))
    (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (Pi2A.hashOK_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendScalar _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sampleWideW_sigma 4) (by norm_num)) (fun bus _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_midB4 tr bus hk) (fun x _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sampleWideW_sigma 5) (by norm_num)) (fun pd _ _ ↦ ?_) (by omega)
  exact ws_of_wc (wc_mono (wc_tailT4 _ _ _ _ _ _) le_rfl (by omega) fun _ _ h ↦ h) hV

/-! ## π1-rec4's prover -/

set_option hygiene false in
/-- One step of the three openings' walk (`hc`, `h1` … `h3` the local facts on the claims). -/
macro "p1k4_hop_step" : tactic => `(tactic| first
  | exact E2ECompleteness.HashOK.pure _ _
  | refine E2ECompleteness.HashOK.bind (Pi2A.hashOK_pcsProveH _ _ _ _ _ _ (le_trans (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3)) (by omega))) fun _ ↦ ?_)

/-- **π1-rec4's honest prover at `W = rateSigma` hashes only short inputs** (`costP_proveRec4With`'s walk). -/
theorem hashOK_proveRec4K (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hk : flockBlocks4 (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4 ≤ 16384)
    (hV : 2 + batchVarsBound tr.shape ≤ 16384)
    (hS : streamBytes4 tr.shape tr.rows.length ≤ 16384) (hIv : programIv.length ≤ 2 ^ 16) :
    HashOK Short (proveRec4With callKeccak256 rateSigma callKeccakF1600 PcsQuotient.nonceFuel programIv tr) := by
  unfold proveRec4With setupTreeOf contractIvOf seedOf
  simp only [bind_assoc, pure_bind]
  refine E2ECompleteness.HashOK.bind (Pi2A.hashOK_commitWithH _ _) fun tree ↦ ?_
  refine E2ECompleteness.HashOK.bind (hashOK_callKeccak256 ?_) fun d ↦ ?_
  · show _ < 2 ^ 26
    simp only [List.length_append, Cost.ivTag_length, Cost.len_digestBytes, Cost.shapeBytes_length,
      Cost.elementBytes24_length, Cost.variantBytesK_length]
    rw [two26]
    have : (2 : ℕ) ^ 16 = 65536 := by norm_num
    omega
  refine E2ECompleteness.HashOK.bind (hashOK_callKeccak256 ?_) fun seed ↦ ?_
  · show _ < 2 ^ 26
    simp only [List.length_append, Cost.name_length, Cost.len_digestBytes, hpub, two26]
    omega
  refine (Pi2A.LenP.bind (ws_proveStreamRec4K tr hk hV (UniComplete.Wr.start seed)
    (by simp [WInv, UniComplete.Wr.start]) (by simpa [UniComplete.Wr.start] using hS))
    fun z hz ↦ lenP_of_hashOK ?_).toHashOK
  obtain ⟨⟨_, hc0⟩, -, -, -⟩ := hz
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  obtain ⟨out, _⟩ := z
  dsimp only at hc ⊢
  unfold Rec3.openingsTail3
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    dsimp only <;> repeat p1k4_hop_step

/-- **UniKeccakComplete's two-call π1-rec4 prover at `W = rateSigma` hashes only short inputs**, at the reference
shape, a program IV of at most `2^16` bytes and row counts that fit. -/
theorem hashOK_uniProverRec4_ref (D : UniKeccak.KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) :
    HashOK Short (uniProverRec4With callKeccak256 rateSigma callKeccakF1600 D input rows q) := by
  have hlen : rows.length = 6 := hfit.1
  obtain ⟨-, -, -, h4⟩ := Cost.reference_stackVars
  have esh : (honestTrace D input rows q).shape = D.shape := rfl
  have erows : (honestTrace D input rows q).rows = rows := rfl
  have e : keccakR1csLogSize + D.shape.heights.getD opSha3 0 = 32 := by
    rw [hD]
    exact Cost.reference_flockLogN
  have hs := proverStream4_reference D hD
  unfold uniProverRec4With
  refine hashOK_proveRec4K D.programIv (honestTrace D input rows q) (by simp [honestTrace]) ?_ ?_ ?_ hIv
  · rw [esh, e, flockBlocks4_reference]
    norm_num
  · rw [esh, hD]
    omega
  · rw [esh, erows, hlen, hs]
    norm_num

/-- **The recursion's π1-rec4 prover hashes only inputs shorter than `2^26` bytes**, at the real deployment and row
counts that fit (`Pi2P1.Pi1HashShort`'s content). -/
theorem hashShort_p1kK4 {D : RecDeployment} (hD : D.Real) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) :
    HashOK (fun x ↦ x.length < 2 ^ 26) (p1kK4 D input rows q) :=
  hashOK_p1kK4_of D input rows q _
    (hashOK_uniProverRec4_ref D.pi1 (real_shape hD) (real_programIv hD) input rows q hfit)

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.hashOK_uniProverRec4_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.hashOK_uniProverRec4_ref

/-- info: 'RecCompose.Pi1K.hashShort_p1kK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.hashShort_p1kK4
