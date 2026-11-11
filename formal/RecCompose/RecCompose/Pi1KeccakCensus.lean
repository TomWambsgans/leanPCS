-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The walk is `formal/UniKeccakComplete`'s
-- (`K/Rec3ProverCost.lean`'s `wc_proveStreamRec3With`, `costP_proveRec3With`) redone for the lengths of the hashed
-- inputs, in `Pi2AlphaLen`'s calculus (`WS`, `LenP`).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness`'s `HashOK`.
import RecCompose.Pi1KeccakTransfer
import RecCompose.Pi2AlphaLen

/-!
# π1-rec3's honest prover hashes nothing of `2^26` bytes

`Pi2P1.Pi1HashShort` asks every Keccak-256 query of π1's two-call prover to be shorter than `2^26` bytes (the length
of π2's `σ` hash, which starts the chain that makes `α`'s input fresh). For the recursion's prover `p1kK`:

* **`ws_proveStreamRec3K`**: π1-rec3's stream (UniKeccakComplete's `proveStreamRec3With` over `callKeccak256`) hashes
  only short inputs, writing at most `streamBytes3` bytes, its claims of at most `batchVarsBound` coordinates
  (`wc_proveStreamRec3With`'s walk in `WS`: the draws hash the state and the stream, at most `2^14` bytes; the
  commitments' trees `512`-byte rows and `64`-byte nodes, `Pi2A.hashOK_commitReal`);
* **`hashOK_proveRec3K`**: the prover: the setup's tree, the Keccak contract's IV (`163` bytes and the program IV), the
  seed (`80` bytes), the stream, three PCS openings of a point of at most `2^14` coordinates
  (`Pi2A.hashOK_pcsProveH`);
* **`hashOK_uniProverRec3_ref`**: UniKeccakComplete's two-call π1-rec3 prover with Flock's honest prover, at the
  reference shape (stream `6904 + 3696 ≤ 2^14` bytes, `27` batch variables) and a program IV of at most `2^16` bytes;
* **`hashShort_p1kK`**: hence the recursion's prover (`hashOK_p1kK_of`: its Fiat–Shamir hashes are no queries), at the
  real deployment.
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniKeccakComplete
open RecStatement (RecDeployment)
open E2ECompleteness (HashOK hashOK_callKeccak256)
open UniKeccakComplete.Cost (WC WInv StreamOK wc_seq wc_mono wc_pure wc_forIn_list wc_sendInteger wc_sendRoot wc_sendScalar
  wc_sampleW wc_map wc_sendScalars wc_get_pure length_claims)
open UniKeccakComplete.Bounds (batchVarsBound valuesBound)
open Pi2A (Short WS ws_of_wc ws_seq ws_lift lenP_of_hashOK two26)

/-! ## π1-rec3's stream -/

/-- **π1-rec3's stream hashes only short inputs** (`wc_proveStreamRec3With`'s walk), given Flock's prover's cost
with at most `2^14` blocks beyond its bytes and a batch of at most `2^14` variables. -/
theorem ws_proveStreamRec3K (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (tr : Trace)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakRec3 tr.qflock) kF wF
      fun _ _ ↦ True) (hkF : kF ≤ 16384) (hV : batchVarsBound tr.shape ≤ 16384) :
    WS (Rec3.proveStreamRec3With callKeccak256 (commitReal callKeccak256) flock tr)
      (Rec3.streamBytes3 tr.shape tr.rows.length wF) (StreamOK (batchVarsBound tr.shape)) := by
  unfold Rec3.proveStreamRec3With Rec3.streamBytes3
  refine ws_seq (ws_of_wc (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl) (by simp))
    (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (Pi2A.hashOK_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendScalar _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (Rec3.wc_drawRunW 4) (by norm_num)) (fun alphas _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun beta _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun gamma _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_map some hF) hkF) (fun flockOut _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (Pi2A.hashOK_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendScalar _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun t _ _ ↦ ?_) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine ws_seq (ws_of_wc (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun rho _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun lambda _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_mono (Rec3.wc_batchRounds3 _ _ _) hvars (Nat.mul_le_mul_left 96 hvars)
    fun r _ h ↦ h) hV) (fun r _ hr ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h) (by norm_num))
    (fun _ _ _ ↦ ?_) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine ws_of_wc (k := 0) (wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _)
    fun _ _ h ↦ h) (by norm_num)
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

/-! ## π1-rec3's prover -/

set_option hygiene false in
/-- One step of the three openings' walk (`hc`, `h1` … `h3` the local facts on the claims). -/
macro "p1k_hop_step" : tactic => `(tactic| first
  | exact E2ECompleteness.HashOK.pure _ _
  | refine E2ECompleteness.HashOK.bind (Pi2A.hashOK_pcsProveH _ _ _ _ _ _ (le_trans (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3)) hV)) fun _ ↦ ?_)

/-- **π1-rec3's honest prover hashes only short inputs** (`costP_proveRec3With`'s walk). -/
theorem hashOK_proveRec3K (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ)
    (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakRec3 tr.qflock) kF wF
      fun _ _ ↦ True) (hkF : kF ≤ 16384) (hV : batchVarsBound tr.shape ≤ 16384)
    (hS : Rec3.streamBytes3 tr.shape tr.rows.length wF ≤ 16384) (hIv : programIv.length ≤ 2 ^ 16) :
    HashOK Short
      (Rec3.proveRec3With callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock programIv tr) := by
  unfold Rec3.proveRec3With setupTreeOf contractIvOf seedOf
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
  refine (Pi2A.LenP.bind (ws_proveStreamRec3K flock kF wF tr hF hkF hV (UniComplete.Wr.start seed)
    (by simp [WInv, UniComplete.Wr.start]) (by simpa [UniComplete.Wr.start] using hS))
    fun z hz ↦ lenP_of_hashOK ?_).toHashOK
  obtain ⟨⟨_, hc0⟩, -, -, -⟩ := hz
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  obtain ⟨out, _⟩ := z
  dsimp only at hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat p1k_hop_step

/-- **UniKeccakComplete's two-call π1-rec3 prover with Flock's honest prover hashes only short inputs**, at the
reference shape, a program IV of at most `2^16` bytes and row counts that fit. -/
theorem hashOK_uniProverRec3_ref (D : UniKeccak.KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) :
    HashOK Short
      (Rec3.uniProverRec3With callKeccak256 callKeccakF1600 (flockProveH callKeccak256) D input rows q) := by
  have hlen : rows.length = 6 := hfit.1
  obtain ⟨-, -, -, h4⟩ := Cost.reference_stackVars
  have esh : (honestTrace D input rows q).shape = D.shape := rfl
  have erows : (honestTrace D input rows q).rows = rows := rfl
  have e : keccakR1csLogSize + D.shape.heights.getD opSha3 0 = 32 := by
    rw [hD]
    exact Cost.reference_flockLogN
  have hs := Rec3.proverStream3_reference D hD fun _ _ ↦ 3696
  unfold Rec3.proverStream3 at hs
  beta_reduce at hs
  have hF : WC (flockProveH callKeccak256 32 UniKeccak.keccakRec3 (honestTrace D input rows q).qflock) 49 3696
      fun _ _ ↦ True := by
    have h := flockCost_flockProveH 32 UniKeccak.keccakRec3 (honestTrace D input rows q).qflock
    rw [flockBlocks_rec3_reference, flockBytes_rec3_reference] at h
    exact h
  unfold Rec3.uniProverRec3With
  refine hashOK_proveRec3K (flockProveH callKeccak256) 49 3696 D.programIv
    (honestTrace D input rows q) (by simp [honestTrace]) ?_ (by norm_num) ?_ ?_ hIv
  · rw [esh, e]
    exact hF
  · rw [esh, hD]
    omega
  · rw [esh, erows, hlen]
    omega

/-- **The recursion's π1 prover hashes only inputs shorter than `2^26` bytes**, at the real deployment and row counts
that fit (`Pi2P1.Pi1HashShort`'s content). -/
theorem hashShort_p1kK {D : RecDeployment} (hD : D.Real) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) :
    HashOK (fun x ↦ x.length < 2 ^ 26) (p1kK D input rows q) :=
  hashOK_p1kK_of D input rows q _
    (hashOK_uniProverRec3_ref D.pi1 (real_shape hD) (real_programIv hD) input rows q hfit)

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.hashOK_uniProverRec3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.hashOK_uniProverRec3_ref

/-- info: 'RecCompose.Pi1K.hashShort_p1kK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.hashShort_p1kK
