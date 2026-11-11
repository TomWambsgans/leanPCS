-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProverCost.lean`, `VerifierHCost.lean`, `Rec3ProverCost.lean` and `Rec3ProbExp.lean`'s `cost_stagedU3`, for
-- `Pi2ProbStaged`'s staged run (`pi2Staged`: the setup, π1-rec4's honest prover, π1-rec4's graph, π2's honest prover
-- `crates/leanvm/rec/src/pi2/prover.rs`, the contract `formal/RecStatement`); uses
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean` (`cost_openingWithH`, `cost_proveOpeningWithH`,
-- `qc_commitWithH`), `FsCost.lean`'s encoding length, and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the block cost `hashBlocks` and the weight calculus
-- `Common.QueryCostAtMost`.
import RecCompose.Pi2ProbStaged
import RecCompose.IvLength
import RecCompose.FsCost
import UniKeccakSound.Fs.LayerK

/-!
# The block count of π2's staged run (`Pi2RunCost`, π2v4)

**`pi2RunCost_of hD hP1 : Pi2RunCost D C Fa P1k pi2RunN`**, **`pi2RunN_le : pi2RunN ≤ 2^50`**: at the real deployment
(`hD`), the staged run at a π1 prover of at most `2^47` block calls (`Pi1Cost D P1k`, named) makes at most `pi2RunN`
block calls (`hashBlocks`: a Keccak-256 of `n` bytes `⌊n / 136⌋ + 1`, a Keccak-f[1600] one).

`pi2RunN = costA setupR + (1 + 1 + 1 + (treeQ + 28) + 1 + costC)`:

* stage A (`costA`): the setup twice (`setup2`: π1's one tree, `treeCost 23` at the reference shape,
  `UniKeccakSound.setupVars_ref`; π2's setup tree `treeCost 25`), π1-rec4's prover (`2^47`, `Pi1Cost`), the graph's
  three openings (`gOpen`: a PCS claim's check, `UniKeccakComplete.Cost.openCost`), π2's IV (`ivC`: `σ`'s `4 · 2^24`
  bytes, `κ`'s `8 · 2^24`, the encoding's `27392 + 64`, the IV's `137`), the seed (`176` bytes: the frame words of the
  three declared claims, `frameWords_choice_le`), `W`'s tree (`treeCost 24`) and out-of-domain point (`24` hashes of
  `46` bytes, `qc_oodPointM`);
* the chain (`88`, `32`, `32` bytes), `Q`'s tree (`treeCost 28`) and point (`28` hashes), `t` (`88` bytes);
* stage C (`costC`): `ρ` (`464` bytes), π2's prover's four PCS openings (`PcsZ.cost_pcsProveZH`) and the contract on
  π2's honest stream (at most `1216` bytes, `contractC`): its IV, its seed (`176` bytes), its walk (`10` blocks beyond
  the channel's potential `3 · 1216`, UniComplete's `CC` calculus), its seven PCS claims' checks (`cOpen`: a check's
  `openCost`, and at `W`'s and `Q`'s sizes the point's `28` hashes, `cost_pcsVerifyO`).

The calculus: `CP X c P` (at most `c` block calls, every outcome satisfying `P`, any budget beyond left over), on
UniComplete's `CostP`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open RecStatement
open UniStatement (Chan ChanM)
open E2ECompleteness.Cost (QC qc_pure qc_H qc_H_le qc_commitWithH treeCost vOpen blockFactor)
open UniKeccakComplete.Cost (CostP costP_query_bind costP_of_qc CC cc_bind cc_mono cc_seq cc_free cc_pure cc_forIn_list cc_sampleH cc_nextScalar cc_nextInteger cc_nextRoot cc_nextScalars cc_finish len_digestBytes pot Inv)
open LeanVM.Protocol.Verifier (whirBound costHeight)

namespace RecCompose.Pi2G

namespace Cost2

/-! ## Costs with a postcondition and any budget left over -/

/-- **At most `c` block calls**, every outcome satisfying `P`, any extra budget left over. -/
def CP {α : Type} (X : OracleComp KeccakCalls α) (c : ℕ) (P : α → Prop) : Prop :=
  ∀ m, CostP X (c + m) fun a r ↦ P a ∧ m ≤ r

section Calculus

variable {α β : Type}

theorem costP_budget {X : OracleComp KeccakCalls α} {n n' m : ℕ} {P : α → Prop}
    (h : CostP X n fun a r ↦ P a ∧ m ≤ r) (hn : n ≤ n') : CostP X n' fun a r ↦ P a ∧ m ≤ r := by
  induction X using OracleComp.inductionOn generalizing n n' with
  | pure a => exact ⟨h.1, h.2.trans hn⟩
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun u ↦ ih u (h.2 u) (by omega)⟩

theorem CP.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {c₁ c₂ : ℕ} {P : α → Prop}
    {Q : β → Prop} (hX : CP X c₁ P) (hf : ∀ a, P a → CP (f a) c₂ Q) : CP (X >>= f) (c₁ + c₂) Q := by
  intro m
  rw [show c₁ + c₂ + m = c₁ + (c₂ + m) by omega]
  exact UniKeccakComplete.Cost.CostP.bind (hX (c₂ + m)) fun a r h ↦ costP_budget (hf a h.1 m) h.2

theorem CP.mono {X : OracleComp KeccakCalls α} {c c' : ℕ} {P P' : α → Prop} (h : CP X c P) (hc : c ≤ c')
    (hP : ∀ a, P a → P' a) : CP X c' P' := by
  intro m
  have h1 := h (m + (c' - c))
  rw [show c + (m + (c' - c)) = c' + m by omega] at h1
  exact UniKeccakComplete.Cost.CostP.mono h1 fun a r h ↦ ⟨hP a h.1, by omega⟩

theorem cp_of_qc {X : OracleComp KeccakCalls α} {c : ℕ} (h : QC X c) : CP X c fun _ ↦ True :=
  fun m ↦ UniKeccakComplete.Cost.CostP.mono (costP_of_qc h m) fun _ _ hr ↦ ⟨trivial, hr⟩

theorem cp_pure (a : α) {P : α → Prop} (h : P a) : CP (pure a : OracleComp KeccakCalls α) 0 P :=
  fun m ↦ ⟨h, Nat.le_add_left m 0⟩

theorem CP.toQC {X : OracleComp KeccakCalls α} {c : ℕ} {P : α → Prop} (h : CP X c P) : QC X c := by
  have h0 := h 0
  rw [Nat.add_zero] at h0
  exact UniKeccakComplete.Cost.CostP.toQC h0

theorem cp_H (x : List UInt8) : CP (callKeccak256 x) (x.length / 136 + 1) fun _ ↦ True := cp_of_qc (qc_H x)

/-- A hash of fewer than `136 · k` bytes, at most `k` blocks. -/
theorem cp_H_le {x : List UInt8} {k : ℕ} (hx : x.length < 136 * k) : CP (callKeccak256 x) k fun _ ↦ True :=
  cp_of_qc (qc_H_le hx)

theorem CP.bind_le {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {c₁ c₂ c : ℕ} {P : α → Prop}
    {Q : β → Prop} (hX : CP X c₁ P) (hf : ∀ a, P a → CP (f a) c₂ Q) (h : c₁ + c₂ ≤ c) : CP (X >>= f) c Q :=
  (hX.bind hf).mono h fun _ h ↦ h

/-- A loop whose steps on the list's elements cost at most `c` each. -/
theorem qc_forIn_mem {γ : Type} (l : List γ) (b : β) (f : γ → β → OracleComp KeccakCalls (ForInStep β)) {c : ℕ}
    (hf : ∀ a ∈ l, ∀ s, QC (f a s) c) : QC (forIn l b f) (l.length * c) := by
  induction l generalizing b with
  | nil => exact qc_pure _ _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a List.mem_cons_self b).bind_le (b := l.length * c) (fun s ↦ ?_) (by simp [Nat.succ_mul]; omega)
    cases s with
    | done b => exact qc_pure _ _
    | yield b => exact ih b (fun a ha ↦ hf a (List.mem_cons_of_mem _ ha))

end Calculus

/-! ## Lengths -/

theorem length_flatMap_const {γ δ : Type} (f : γ → List δ) (k : ℕ) (hf : ∀ x, (f x).length = k) :
    ∀ l : List γ, (l.flatMap f).length = k * l.length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f k hf l, List.length_cons]
    ring

theorem length_le64 (n : ℕ) : (le64 n).length = 8 := by simp [le64]

theorem length_pi1Iv (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniKeccak.SetupRootsK) :
    (pi1Iv s programIv roots).length = 32 :=
  RecStatement.pi1Iv_length s programIv roots

theorem name_length : RecStatement.name.length = 16 := by decide +kernel

theorem ivTag_length : RecStatement.ivTag.length = 16 := by decide +kernel

theorem encoding_length : Data.circuit.encoding.length = 27392 := RecCompose.cc_encoding_length

theorem programIv_length : UniStatement.programIv.length = 32 := by decide +kernel

/-! ## The setup, the IV, the seed -/

/-- The setup's blocks: π1's one tree (the Keccak setup stack), π2's setup tree (`2^25` words). -/
noncomputable def setup2 (D : RecDeployment) : ℕ := treeCost (UniStatement.setupLayout D.pi1.shape).vars + treeCost 25

theorem circuit_logN {D : RecDeployment} (hD : D.Real) (roots : UniKeccak.SetupRootsK) :
    (D.circuitAt roots).circuit.logN = 24 := by
  rw [RecDeployment.circuitAt, hD.1]
  rfl

theorem qc_setupTreesWithH2 {D : RecDeployment} (hD : D.Real) :
    QC (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) (setup2 D) := by
  unfold Pi2H.setupTreesWithH Pi2H.setupTreeWithH setup2
  refine E2ECompleteness.Cost.QC.bind_le (b := treeCost 25) (qc_commitWithH _ _)
    (fun t1 ↦ E2ECompleteness.Cost.QC.bind_le (c := treeCost 25) (qc_commitWithH _ _) (fun _ ↦ qc_pure _ 0) ?_)
    le_rfl
  rw [circuit_logN hD]
  decide

/-- π2's IV's blocks: `σ`'s `4 · 2^24` bytes, `κ`'s `8 · 2^24`, the encoding and the two digests, the IV's preimage
(`137` bytes: the tag, π1's IV, the setup's root and answer, the digest, `log_n`). -/
noncomputable def ivC : ℕ := (4 * 2 ^ 24) / 136 + 1 + ((8 * 2 ^ 24) / 136 + 1) + ((27392 + 64) / 136 + 1) + (137 / 136 + 1)

theorem cp_ivOfH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) :
    CP (Pi2H.ivOfH callKeccak256 D roots) ivC fun iv ↦ iv.length = 32 := by
  have hc : (D.circuitAt roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
  have hn : (D.circuitAt roots.pi1).n = 2 ^ 24 := by rw [Pi2Circuit.n, hc]; rfl
  unfold Pi2H.ivOfH Pi2H.digestWithH Pi2H.ivWithH
  simp only [bind_assoc, pure_bind]
  refine CP.bind_le (cp_H_le (k := (4 * 2 ^ 24) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := (8 * 2 ^ 24) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := (27392 + 64) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := 137 / 136 + 1) ?_) (fun _ _ ↦ cp_pure _ (len_digestBytes _)) le_rfl) le_rfl) le_rfl)
    (by unfold ivC; omega)
  · rw [length_flatMap_const _ 4 (fun i ↦ by simp [length_le64]), List.length_range, hn]
    omega
  · rw [length_flatMap_const _ 8 (fun i ↦ length_le64 _), List.length_range, hn]
    omega
  · simp only [List.length_append, len_digestBytes, hc, encoding_length]
    omega
  · simp only [List.length_append, ivTag_length, len_digestBytes, RecDeployment.pi1IvAt, length_pi1Iv,
      UniKeccakComplete.Cost.elementBytes24_length, List.length_singleton]
    omega

/-! ## π2's prover's stream -/

theorem run_sendRoot2 (h : E × E) (s : UniComplete.Wr) :
    (UniComplete.sendRoot (m := OracleComp KeccakCalls) h).run s =
      pure ((), { s with stream := s.stream ++ (UniStatement.rootWord h).toArray }) := rfl

theorem run_sendScalar2 (x : E) (s : UniComplete.Wr) :
    (UniComplete.sendScalar (m := OracleComp KeccakCalls) x).run s =
      pure ((), { s with stream := s.stream ++ (UniComplete.scalarWire x).toArray }) := rfl

theorem run_sendScalars2 (xs : List E) (s : UniComplete.Wr) :
    (UniComplete.sendScalars (m := OracleComp KeccakCalls) xs).run s =
      pure ((), { s with stream := s.stream ++ (xs.flatMap UniComplete.scalarWire).toArray }) := rfl

/-- **The public values' writes**: the state grows by their bytes. -/
theorem run_sendPublic (l : List (Read × PublicValue)) (s : UniComplete.Wr) :
    ∃ s' : UniComplete.Wr, (sendPublic (m := OracleComp KeccakCalls) l).run s = pure ((), s') ∧
      s'.absorbed = s.absorbed ∧ s'.stream.size = s.stream.size + (Pi2S.publicWire l).length :=
  ⟨{ s with stream := s.stream ++ (l.flatMap publicBytes).toArray }, rfl, rfl, by simp [Pi2S.publicWire]⟩

/-- A public value's bytes: at most `32`, when its read is not an integer. -/
theorem length_publicBytes_le (p : Read × PublicValue) (hp : ∀ b, p.1 ≠ .integer b) : (publicBytes p).length ≤ 32 := by
  rcases p with ⟨r, v⟩
  cases r with
  | integer b => exact absurd rfl (hp b)
  | root => cases v <;> simp [publicBytes]
  | scalar => cases v <;> simp [publicBytes]
  | narrow => cases v <;> simp [publicBytes, narrowWire]
  | frame q => cases v <;> simp [publicBytes]

/-- The public values' bytes: at most `32` a value, when no read is an integer. -/
theorem length_publicWire_le : ∀ (l : List (Read × PublicValue)), (∀ p ∈ l, ∀ b, p.1 ≠ .integer b) →
    (Pi2S.publicWire l).length ≤ 32 * l.length
  | [], _ => by simp [Pi2S.publicWire]
  | p :: rest, h => by
    have h1 := length_publicBytes_le p (h p List.mem_cons_self)
    have h2 := length_publicWire_le rest fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
    simp only [Pi2S.publicWire, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
    omega

theorem data_reads_length : Data.reads.length = 3 := rfl

/-- A read is an integer. -/
def isInteger : Read → Bool
  | .integer _ => true
  | _ => false

theorem data_reads_isInteger : ∀ r ∈ Data.reads, isInteger r = false := by decide +kernel

theorem data_reads_integer : ∀ r ∈ Data.reads, ∀ b, r ≠ .integer b := by
  intro r hr b hb
  have := data_reads_isInteger r hr
  rw [hb] at this
  cases this

/-- **The public values' bytes on the real circuit**: at most `3 · 32` (π2v4: frame reads only, none in fact). -/
theorem length_publicWire_data (values : List PublicValue) : (Pi2S.publicWire (Data.reads.zip values)).length ≤ 96 := by
  refine (length_publicWire_le _ fun p hp b ↦ data_reads_integer _ (List.of_mem_zip hp).1 b).trans ?_
  rw [List.length_zip, data_reads_length]
  have : min 3 values.length ≤ 3 := min_le_left _ _
  omega

/-- A declared claim's Keccak-256 has `32` bytes. -/
theorem claimHash_length (w : List (List UInt8)) : (claimHash w).length = 32 := by
  unfold claimHash
  exact len_digestBytes _

/-- **The frame's words on the real circuit**: three payloads of `32` bytes. -/
theorem frame_len_data_eq (cl : List (List (List UInt8))) :
    ((frameReads Data.circuit.reads).flatMap (frameOf cl)).length = 96 := by
  show ([0, 1, 2].flatMap (frameOf cl)).length = 96
  simp [frameOf, claimHash_length]

theorem frame_len_data (cl : List (List (List UInt8))) :
    ((frameReads Data.circuit.reads).flatMap (frameOf cl)).length ≤ 96 :=
  (frame_len_data_eq cl).le

theorem frame_len {D : RecDeployment} (hD : D.Real) (roots : UniKeccak.SetupRootsK) (cl : List (List (List UInt8))) :
    ((frameReads (Spec.of (D.circuitAt roots).circuit).reads).flatMap (frameOf cl)).length ≤ 96 := by
  have hc : (D.circuitAt roots).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
  rw [show (Spec.of (D.circuitAt roots).circuit).reads = (D.circuitAt roots).circuit.reads from rfl, hc]
  exact frame_len_data cl

/-- **The seed's frame words** at the witness π2's prover takes: `96` bytes (the frame's three payloads) on an honest
witness, none otherwise. -/
theorem frameWords_choice {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8) (claims : List (List (List UInt8))) :
    (frameWordsOf (Pi2E.pi2Choice D C.G Fa.pubOf roots input s claims).1).length = 0 ∨
      (frameWordsOf (Pi2E.pi2Choice D C.G Fa.pubOf roots input s claims).1).length = 96 := by
  unfold Pi2E.pi2Choice
  split
  · rename_i h
    right
    rw [Pi2S.frameWordsOf_eq (frameOf claims) _ _ h.choose_spec.1]
    have hc : (D.circuitAt roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
    rw [hc]
    exact frame_len_data_eq claims
  · left
    simp [frameWordsOf]

theorem frameWords_choice_le {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8) (claims : List (List (List UInt8))) :
    (frameWordsOf (Pi2E.pi2Choice D C.G Fa.pubOf roots input s claims).1).length ≤ 96 := by
  rcases frameWords_choice hD C Fa roots input s claims with h | h <;> omega

/-- A list of computations of one block each, then a continuation on lists of their length. -/
theorem qc_mapM_bind {α : Type} (g : ℕ → OracleComp KeccakCalls E) (hg : ∀ j, QC (g j) 1) :
    ∀ (l : List ℕ) (f : List E → OracleComp KeccakCalls α) (c : ℕ),
      (∀ zs : List E, zs.length = l.length → QC (f zs) c) → QC (l.mapM g >>= f) (l.length + c)
  | [], f, c, hf => by
    rw [List.mapM_nil, pure_bind]
    simpa using hf [] rfl
  | j :: l, f, c, hf => by
    rw [List.mapM_cons, bind_assoc]
    refine (hg j).bind_le (b := l.length + c) (fun e ↦ ?_) (by simp only [List.length_cons]; omega)
    rw [bind_assoc]
    simp only [pure_bind]
    exact qc_mapM_bind g hg l (fun zs ↦ f (e :: zs)) c (fun zs hz ↦ hf _ (by simp [hz]))

/-- A coordinate of the out-of-domain point: one Keccak-256 of `46` bytes. -/
theorem qc_coord (n : ℕ) (r : Digest) (j : ℕ) :
    QC (do return WhirBridge.Pcs.elemOf ((digestBytes (← callKeccak256 (WhirBridge.Pcs.oodInput n r j))).drop 8) :
      OracleComp KeccakCalls E) 1 := by
  refine (qc_H_le (k := 1) ?_).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
  have : (WhirBridge.Pcs.oodInput n r j).length = 46 := by
    simp [WhirBridge.Pcs.oodInput, WhirBridge.Pcs.oodTag, WhirBridge.Pcs.digestBytes_length']
  omega

/-- **The out-of-domain point**: `n` blocks (`n` hashes of `46` bytes). -/
theorem qc_oodPointM (n : ℕ) (r : Digest) : QC (WhirBridge.Pcs.oodPointM callKeccak256 n r) n := by
  have h := qc_mapM_bind _ (qc_coord n r) (List.range n) pure 0 fun _ _ ↦ qc_pure _ 0
  rwa [bind_pure, List.length_range, Nat.add_zero] at h

/-- **Before `α`**: `W`'s tree and out-of-domain point; the public values and the root written. -/
theorem cp_pre2 (G : RecPiop.Circuit E) (hG : G.logN = 24) (reads : List Read)
    (values : List PublicValue) (w : ℕ → K) (s : UniComplete.Wr) :
    CP ((pre2 callKeccak256 G (WhirBridge.Pcs.oodPointM callKeccak256) reads values w).run s) (treeCost 24 + 24)
      fun z ↦ z.2.absorbed = s.absorbed ∧
        z.2.stream.size = s.stream.size + (Pi2S.publicWire (reads.zip values)).length + 56 := by
  obtain ⟨s', h, ha, hs⟩ := run_sendPublic (reads.zip values) s
  unfold pre2
  simp only [StateT.run_bind, h, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, run_sendScalar2,
    StateT.run_pure]
  refine CP.bind_le (cp_of_qc (qc_commitWithH _ _)) (fun t _ ↦ CP.bind_le (cp_of_qc (qc_oodPointM _ _))
    (fun z _ ↦ cp_pure _ ⟨ha, ?_⟩) le_rfl) ?_
  · simp [hs]
  · rw [hG]
    decide

/-- **From `γ` to `t`**: `Q`'s tree and out-of-domain point; its root written. -/
theorem cp_mid2 (G : RecPiop.Circuit E) (hG : G.logN = 24) (S : CoreSpec E)
    (pubs : List E) (w : ℕ → K) (α β γ : E) (s : UniComplete.Wr) :
    CP ((mid2 callKeccak256 G S (WhirBridge.Pcs.oodPointM callKeccak256) pubs w α β γ).run s) (treeCost 28 + 28)
      fun z ↦ z.2.absorbed = s.absorbed ∧ z.2.stream.size = s.stream.size + 56 := by
  unfold mid2
  simp only [StateT.run_bind, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, run_sendScalar2,
    StateT.run_pure]
  refine CP.bind_le (cp_of_qc (qc_commitWithH _ _)) (fun t _ ↦ CP.bind_le (cp_of_qc (qc_oodPointM _ _))
    (fun z _ ↦ cp_pure _ ⟨rfl, ?_⟩) le_rfl) ?_
  · simp
  · rw [hG]
    decide

theorem length_foldValues (m r : ℕ) (T : Array K) (t : E) : (foldValues m r T t).length = 2 ^ r := by
  simp [foldValues]

/-- **After `t`**: the values at `t` written, `ρ` (`464` bytes, `4` blocks). -/
theorem cp_post2 (G : RecPiop.Circuit E) (hW : G.logW = 4) (setupStack : Array K) (input : List UInt8)
    (values : List PublicValue) (w : ℕ → K) (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K)
    (qT : LeanVM.Prover.Tree) (α β γ t : E) (wP qP : List E) (s : UniComplete.Wr) (hs : s.absorbed = s.stream.size) :
    CP ((post2 callKeccak256 G setupStack input values w wS wT qS qT α β γ t wP qP).run s) 4 fun z ↦
      z.1.stream.size = s.stream.size + 432 := by
  unfold post2
  simp only [StateT.run_bind, pure_bind, bind_assoc, run_sendScalars2, UniComplete.sampleW, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure]
  refine CP.bind_le (cp_H_le (k := 4) ?_) (fun _ _ ↦ cp_pure _ ?_) le_rfl
  · simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, Array.size_append,
      List.size_toArray, UniKeccakComplete.Cost.length_flatMap_scalarWire, length_foldValues, hW, hs,
      List.length_cons, List.length_nil, Nat.min_self]
    omega
  · simp [length_foldValues, hW]

/-! ## The graph's three claims' openings -/

theorem mapM_option_length {γ δ : Type} {f : γ → Option δ} :
    ∀ {l : List γ} {l' : List δ}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [mapM_option_length hl]

theorem mem_of_mapM_some {γ δ : Type} {f : γ → Option δ} :
    ∀ {l : List γ} {l' : List δ}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil] at h
    cases h
    simp at hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, hfx⟩ := mem_of_mapM_some hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem length_wordBytes_le (s : Array UInt8) (vals : Array RecGraph.Value) (w : RecGraph.Word) :
    (RecGraph.wordBytes s vals w).length ≤ 32 := by
  cases w with
  | node id => simp [RecGraph.wordBytes]
  | const w => simp [RecGraph.wordBytes, RecGraph.beBytes32]
  | stream a => simp [RecGraph.wordBytes]

theorem length_flatMap_le {γ δ : Type} (f : γ → List δ) (k : ℕ) (hf : ∀ x, (f x).length ≤ k) :
    ∀ l : List γ, (l.flatMap f).length ≤ k * l.length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf x
    have := length_flatMap_le f k hf l
    rw [Nat.mul_succ]
    omega

/-- The graph's opening: one PCS claim's check (`UniKeccakComplete.Cost.openCost`). -/
noncomputable def gOpen : ℕ := UniKeccakComplete.Cost.openCost

/-- **π1-rec4's graph with its three claims' openings**: at most `3 · gOpen` blocks. -/
theorem qc_pi1GraphVerifierWithH (D : RecDeployment) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (p : UniKeccak.KeccakProof) :
    QC (Pi2H.pi1GraphVerifierWithH callKeccak256 callKeccakF1600 D roots input p) (3 * gOpen) := by
  unfold Pi2H.pi1GraphVerifierWithH
  split
  · exact qc_pure _ _
  · split
    · exact qc_pure _ _
    · split
      · exact qc_pure _ _
      · split
        · exact qc_pure _ _
        · refine (qc_forIn_mem _ _ _ (c := gOpen) fun x hx s ↦ ?_).bind_le (fun _ ↦ qc_pure _ 0) ?_
          · exact (UniKeccakComplete.Cost.qc_pcsOpenKH _ _ _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) (by unfold gOpen; omega)
          · rw [List.length_zip, Nat.add_zero]
            exact Nat.mul_le_mul_right _ ((min_le_right _ _).trans (by simp))

/-! ## The contract -/

section VerifyO

open E2ECompleteness.Cost

/-- **The PCS check with the out-of-domain point read off Keccak-256**: its IV (`6` blocks), the seed's permutation,
the point (`n ≤ 28` blocks), then the compiled run of the claim's program. -/
theorem cost_pcsVerifyO {n : ℕ} (x : WhirBridge.Pcs.Claim1 n) (π : Compile.Proof) :
    QC (WhirBridge.Pcs.pcsVerifyWithHashO callKeccak256 callKeccakF1600 x π)
      (6 + 1 + (28 + 3 * (2 + ((4 + (2 + whirBound)) + 0)))) := by
  unfold WhirBridge.Pcs.pcsVerifyWithHashO LeanVM.Protocol.Compile.runProofWithHash
  split
  · rename_i hn
    have hw : Whir.Admissible n WhirBridge.logInvRate := WhirBridge.Pcs.admissible_v1 n hn.1 hn.2
    have hn28 : n ≤ 28 := hn.2
    refine (qc_H_le (k := 6) ?_).bind_le (b := 1 + (28 + 3 * (2 + ((4 + (2 + whirBound)) + 0))))
      (fun iv ↦ (qc_F _).bind_le (b := 28 + 3 * (2 + ((4 + (2 + whirBound)) + 0))) (fun seed ↦ ?_) le_rfl)
      (by omega)
    · rw [WhirBridge.Pcs.claimBytes_length]; omega
    · split
      · unfold WhirBridge.Pcs.oodPointM
        refine (qc_mapM_bind _ (qc_coord n x.root) (List.range n) _ (3 * (2 + ((4 + (2 + whirBound)) + 0)))
          fun z hz ↦ ?_).mono (by rw [List.length_range]; omega)
        rw [List.length_range] at hz
        rw [UniKeccakComplete.prog_eq_openingProgram z hz x, E2ECompleteness.openingProgram_eq hw]
        refine (cost_runWithHash costHeight _ _ (2 + ((4 + (2 + whirBound)) + 0)) (fun _ ↦ True) ?_ ?_ ?_).bind_le
          (b := 0) (fun z ↦ by split <;> exact qc_pure _ 0) (by omega)
        · refine ⟨by unfold costHeight WhirBridge.logInvRate; omega, by omega, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact LeanVM.Protocol.Compile.Prog.Costs.bind (costs_vso _ _ _) fun _ _ ↦
            LeanVM.Protocol.Compile.Prog.Costs.ret' trivial
        · exact ⟨by unfold LeanVM.Rpm.maxWidth; omega,
            LeanVM.Rpm.WidthsLE.bind (widthsLE_vso _ _ _) fun _ ↦ trivial⟩
        · intro r hr
          simp at hr
      · exact qc_pure _ _
  · exact qc_pure _ _

end VerifyO

/-- The contract's opening: one PCS claim's check, with the out-of-domain point's `28` hashes at `W`'s and `Q`'s
sizes. -/
noncomputable def cOpen : ℕ := UniKeccakComplete.Cost.openCost + 28

theorem qc_pcsOpenKOH (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    QC (Pi2H.pcsOpenKOH callKeccak256 callKeccakF1600 n root ood pt v p) cOpen := by
  unfold Pi2H.pcsOpenKOH
  split
  · exact (cost_pcsVerifyO _ _).mono (by unfold cOpen UniKeccakComplete.Cost.openCost E2ECompleteness.Cost.vOpen; omega)
  · exact qc_pure _ _

/-- **The check of a claim's words**: at most `cOpen` blocks. -/
theorem qc_pcsOpenWordsH (words : List (List UInt8)) (p : Compile.Proof) :
    QC (Pi2H.pcsOpenWordsH callKeccak256 callKeccakF1600 words p) cOpen := by
  unfold Pi2H.pcsOpenWordsH
  split
  · exact qc_pure _ _
  · split
    · exact qc_pcsOpenKOH _ _ _ _ _ _
    · exact (UniKeccakComplete.Cost.qc_pcsOpenKH _ _ _ _ _ _).mono (by unfold cOpen; omega)

theorem cc_nextNarrow : CC (nextNarrow (m := OracleComp KeccakCalls)) 0 0 fun _ ↦ True := by
  unfold nextNarrow
  exact cc_mono (cc_bind (UniKeccakComplete.Cost.cc_takeBytes 20) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0)
    (by omega) (Nat.zero_le _) fun _ _ ↦ trivial

/-- **π2's walk on the calldata**: `10` blocks beyond the channel's potential (five challenges). -/
theorem cc_reduceWithH2 (s : Spec) (stmt : List E) (frameAt : ℕ → List UInt8) :
    CC (Pi2H.reduceWithH callKeccak256 s stmt frameAt) 10 0 fun _ ↦ True := by
  unfold Pi2H.reduceWithH
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun rd pubs ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun pubs _ ↦ ?_
  · rcases rd with b | _ | _ | _ | p
    · exact cc_free (cc_nextInteger b) fun _ _ ↦ cc_pure trivial 0
    · exact cc_free cc_nextRoot fun _ _ ↦ cc_pure trivial 0
    · exact cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ cc_pure trivial 0
    · exact cc_free cc_nextNarrow fun _ _ ↦ cc_pure trivial 0
    · exact cc_pure trivial 0
  · refine cc_free cc_nextRoot fun _ _ ↦
      cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦
      cc_seq cc_sampleH (fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦
      cc_seq cc_sampleH (fun _ _ ↦ cc_free cc_nextRoot fun _ _ ↦
      cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦
      cc_free (cc_nextScalars _) fun _ _ ↦ cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h)
      fun _ _ ↦ cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h)
      fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦ cc_pure trivial _) (by omega)) (by omega)) (by omega)) (by omega))
      (by omega)

/-- Budget can only help a cost whose postcondition is monotone in the budget left. -/
theorem costP_budget_mono {α : Type} {X : OracleComp KeccakCalls α} {n n' : ℕ} {Q : α → ℕ → Prop}
    (hQ : ∀ a r r', r ≤ r' → Q a r → Q a r') (h : CostP X n Q) (hn : n ≤ n') : CostP X n' Q := by
  induction X using OracleComp.inductionOn generalizing n n' with
  | pure a => exact hQ a n n' hn h
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun u ↦ ih u (h.2 u) (by omega)⟩

/-- **The contract's run on the calldata**: the seed (`80` bytes and the frame's words), the walk; `m` blocks left on
success. -/
theorem costP_runWithH2 (s : Spec) (iv input : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8)
    (hiv : iv.length = 32) (hin : input.length = 32) (m : ℕ) :
    CostP (Pi2H.runWithH callKeccak256 s iv input frameAt stream)
      ((80 + ((frameReads s.reads).flatMap frameAt).length) / 136 + 1 + (10 + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → m ≤ rem := by
  unfold Pi2H.runWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (RecStatement.name ++ iv ++ input ++ (frameReads s.reads).flatMap frameAt).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length, hiv, hin]
    omega
  · rw [show (80 + ((frameReads s.reads).flatMap frameAt).length) / 136 + 1 + (10 + 3 * stream.size + m) -
        hashBlocks (Sum.inl (RecStatement.name ++ iv ++ input ++ (frameReads s.reads).flatMap frameAt)) =
        10 + pot (Chan.start seed stream) + m by
      show _ - ((RecStatement.name ++ iv ++ input ++ (frameReads s.reads).flatMap frameAt).length / 136 + 1) = _
      simp only [List.length_append, name_length, hiv, hin, pot, Chan.start]
      omega]
    have hw : CC (do
        let r ← Pi2H.reduceWithH callKeccak256 s (UniStatement.publicWordsOf input) frameAt
        UniStatement.finish (m := OracleComp KeccakCalls)
        return r : UniKeccakComplete.Cost.CM Reduced) 10 0 fun _ ↦ True :=
      cc_mono (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithH2 s _ frameAt) fun _ _ ↦ cc_free cc_finish fun _ _ ↦
        cc_pure (P := fun _ : Reduced ↦ True) trivial 0) (by omega) le_rfl fun _ h ↦ h
    refine UniKeccakComplete.Cost.CostP.bind (hw (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m) fun z rem hz ↦ ?_
    obtain ⟨res, ch⟩ := z
    show ∀ r, res = .ok r → m ≤ rem
    intro r hr
    have := (hz r hr).2.2
    omega

/-- The contract's run and seven openings, on a stream of at most `S` bytes. -/
noncomputable def contractC (S : ℕ) : ℕ := ivC + (2 + (10 + 3 * S + 7 * cOpen))

/-- **The contract**: π2's IV, the run on the calldata (its seed with the frame's three words), its seven openings. -/
theorem qc_contractWithH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) {S : ℕ} (hS : proof.stream.size ≤ S) :
    QC (Pi2H.contractWithH callKeccak256 callKeccakF1600 D roots input proof) (contractC S) := by
  refine UniKeccakComplete.Cost.CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold Pi2H.contractWithH contractC
  refine UniKeccakComplete.Cost.CostP.bind (cp_ivOfH hD roots _) fun iv rem hiv ↦ ?_
  refine UniKeccakComplete.Cost.CostP.weaken (n := 2 + (10 + 3 * proof.stream.size + 7 * cOpen)) ?_
    (by have := hiv.2; omega)
  have hF := frame_len hD roots.pi1 proof.pi1Claims
  have hrun := costP_runWithH2 (Spec.of (D.circuitAt roots.pi1).circuit) iv input.toList (frameOf proof.pi1Claims)
    proof.stream hiv.1 (by simp) (7 * cOpen)
  refine UniKeccakComplete.Cost.CostP.bind (costP_budget_mono (fun o r r' hr h x hx ↦ (h x hx).trans hr) hrun
    (by omega)) fun o rem' ho ↦ ?_
  split
  · trivial
  · rename_i r hr
    have hm := ho r hr
    split
    · trivial
    · dsimp only
      split
      · trivial
      · try dsimp only
        split
        · trivial
        · rename_i hl
          refine UniKeccakComplete.Cost.CostP.weaken
            (UniKeccakComplete.Cost.CostP.mono (costP_of_qc ?_ 0) fun _ _ _ ↦ trivial) (by omega)
          refine (qc_forIn_mem _ _ _ (c := cOpen) fun x hx s ↦ ?_).bind_le (fun _ ↦ qc_pure _ 0) ?_
          · obtain ⟨words, pp⟩ := x
            exact (qc_pcsOpenWordsH words pp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
          · rw [List.length_zip, Nat.add_zero]
            refine Nat.mul_le_mul_right _ ?_
            simp only [ne_eq, not_not] at hl
            exact (min_le_left _ _).trans (le_of_eq hl)

theorem qc_verifierWithH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) {S : ℕ} (hS : proof.stream.size ≤ S) :
    QC (Pi2H.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) (contractC S + 0) := by
  unfold Pi2H.verifierWithH
  exact (qc_contractWithH hD roots input proof hS).bind (fun _ ↦ qc_pure _ 0)

/-! ## The stages -/

/-- The prover's openings' common part: WHIR's prover at height `26`, `nonceFuel` nonces a proof of work. -/
noncomputable def openP2 : ℕ := 3 + (4 + (2 + whirBound)) * blockFactor costHeight PcsQuotient.nonceFuel

/-- After `ρ`: the four openings (claims of `24`, `25`, `28`, `28` coordinates: their seeds' `5`, `6`, `6`, `6`
blocks), the contract on `1216` bytes. -/
noncomputable def costR : ℕ :=
  (5 + openP2) + ((6 + openP2) + ((6 + openP2) + ((6 + openP2) + (contractC 1216 + 0))))

/-- Stage C: `ρ`'s `4` blocks, then `costR`. -/
noncomputable def costC : ℕ := 4 + costR

theorem qc_restC {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB)
    (p1 : UniKeccak.KeccakProof) (out : Pi2Out) (hs : out.stream.size ≤ 1216) :
    QC (restC callKeccak256 callKeccakF1600 D C input b p1 out) costR := by
  unfold restC costR
  have hc : (D.circuitAt b.a.roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
  obtain ⟨lW, lS, lQ, lP⟩ := Pi2K.run_points_length (Spec.of (D.circuitAt b.a.roots.pi1).circuit).core
    (by rw [hc]; rfl) (by rw [hc]; rfl) out.inputs
  refine E2ECompleteness.Cost.QC.bind_le
    (b := (6 + openP2) + ((6 + openP2) + ((6 + openP2) + (contractC 1216 + 0))))
    (PcsZ.cost_pcsProveZH _ _ _ _ _ _ _ (w := 24) (by simp [lW])) (fun pW ↦ ?_)
    (by unfold openP2; omega)
  refine E2ECompleteness.Cost.QC.bind_le (b := (6 + openP2) + ((6 + openP2) + (contractC 1216 + 0)))
    (PcsZ.cost_pcsProveZH _ _ _ _ _ _ _ (w := 25) (by simp [lS])) (fun pS ↦ ?_)
    (by unfold openP2; omega)
  refine E2ECompleteness.Cost.QC.bind_le (b := (6 + openP2) + (contractC 1216 + 0))
    (PcsZ.cost_pcsProveZH _ _ _ _ _ _ _ (w := 28) (by simp [lQ])) (fun pQ1 ↦ ?_)
    (by unfold openP2; omega)
  refine E2ECompleteness.Cost.QC.bind_le (b := contractC 1216 + 0)
    (PcsZ.cost_pcsProveZH _ _ _ _ _ _ _ (w := 28) (by simp [lP])) (fun pQ2 ↦ ?_)
    (by unfold openP2; omega)
  split
  · exact (qc_verifierWithH hD _ input _ (S := 1216) hs).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
  · exact qc_pure _ _

theorem qc_stageC {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)
    (b : StB) (st : Digest) (hb : b.wr.stream.size ≤ 784) :
    QC (stageC callKeccak256 callKeccakF1600 D C input b st) costC := by
  unfold stageC
  split
  · exact qc_pure _ _
  · refine CP.toQC (P := fun _ ↦ True) (CP.bind_le (c₂ := costR)
      (cp_post2 (C.G b.a.roots) (Fa.logW b.a.roots) _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ rfl) (fun z hz ↦ cp_of_qc ?_) (by unfold costC; omega))
    obtain ⟨out, _⟩ := z
    dsimp only at hz ⊢
    refine (qc_restC hD C input b _ out ?_).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
    rw [hz]
    show b.wr.stream.size + 432 ≤ 1216
    omega

theorem cp_stageB {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) (ha : a.wr.stream.size ≤ 728) :
    CP (stageB callKeccak256 D C input a s₁ s₂ s₃) (treeCost 28 + 28) fun b ↦
      b.wr.absorbed + 56 = b.wr.stream.size ∧ b.wr.stream.size ≤ 784 := by
  unfold stageB
  dsimp only
  refine CP.bind_le (c₂ := 0) (cp_mid2 _ (Fa.logN a.roots) _ _ _ _ _ _ _) (fun z hz ↦ ?_) (by simp)
  obtain ⟨qs, wr⟩ := z
  refine cp_pure _ ⟨?_, ?_⟩
  · show wr.absorbed + 56 = wr.stream.size
    rw [hz.1, hz.2]
    rfl
  · show wr.stream.size ≤ 784
    rw [hz.2]
    show a.wr.stream.size + 56 ≤ 784
    omega

/-- Stage A: the setup twice, π1-rec4's prover, the graph, π2's IV, the seed, `W`'s tree and point. -/
noncomputable def costA (S : ℕ) : ℕ := S + (2 ^ 47 + (3 * gOpen + (S + (ivC + (2 + ((treeCost 24 + 24) + 0))))))

theorem cp_stageA {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (hP : QC P1k (2 ^ 47)) (input : Vector UInt8 32) :
    CP (stageA callKeccak256 callKeccakF1600 D C Fa P1k input) (costA (setup2 D)) fun a ↦ a.wr.stream.size ≤ 728 := by
  unfold stageA costA
  refine CP.bind (cp_of_qc (qc_setupTreesWithH2 hD)) fun trees _ ↦ CP.bind (cp_of_qc hP) fun o _ ↦ ?_
  cases o with
  | none => exact (cp_pure _ (by simp [UniComplete.Wr.start])).mono (Nat.zero_le _) fun _ h ↦ h
  | some p1 =>
    dsimp only
    refine CP.bind (cp_of_qc (qc_pi1GraphVerifierWithH D _ input p1)) fun a1 _ ↦
      CP.bind (cp_of_qc (qc_setupTreesWithH2 hD)) fun tr _ ↦ CP.bind (cp_ivOfH hD tr.roots) fun iv hiv ↦
      CP.bind (cp_H_le (k := 2) ?_) fun seed _ ↦ ?_
    · have := frameWords_choice_le hD C Fa tr.roots input p1.stream (Pi2E.pi1ClaimsOf D tr.roots.pi1 input p1.stream)
      simp only [List.length_append, name_length, hiv, Vector.length_toList]
      omega
    · have hr : (D.circuitAt tr.roots.pi1).circuit.reads = Data.reads := by
        rw [RecDeployment.circuitAt, hD.1]
        rfl
      refine CP.bind (cp_pre2 _ (Fa.logN tr.roots) _ _ _ _) fun z hz ↦ ?_
      obtain ⟨ws, wr⟩ := z
      refine cp_pure _ ?_
      show wr.stream.size ≤ 728
      rw [hz.2, hr]
      have := length_publicWire_data (Pi2E.pi2Choice D C.G Fa.pubOf tr.roots input p1.stream
        (Pi2E.pi1ClaimsOf D tr.roots.pi1 input p1.stream)).1
      show 0 + _ + 56 ≤ 728
      omega

/-! ## The staged run -/

/-- The setup's blocks at the reference shape: at most `2^27` for π1's (`treeCost 23 = 5 · 2^18`), π2's setup tree. -/
noncomputable def setupR : ℕ := 2 ^ 27 + treeCost 25

theorem setup2_le {D : RecDeployment} (hD : D.Real) : setup2 D ≤ setupR := by
  unfold setup2 setupR
  rw [hD.2.2.1, show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
    UniKeccakSound.setupVars_ref]
  unfold treeCost
  norm_num

/-- **The staged run's block count.** -/
noncomputable def pi2RunN : ℕ := costA setupR + (1 + (1 + (1 + (((treeCost 28 + 28) + (1 + (costC + 0))) + 0))))

theorem qc_pi2Staged {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (hP : QC P1k (2 ^ 47)) (input : Vector UInt8 32) :
    QC (pi2Staged D C Fa P1k input).run pi2RunN := by
  have h : CP (pi2Staged D C Fa P1k input).run
      (costA (setup2 D) + (1 + (1 + (1 + (((treeCost 28 + 28) + (1 + (costC + 0))) + 0))))) fun _ ↦ True := by
    unfold Pi2P.Pi2Staged.run Pi2P.staged3 Pi2P.Pi2Staged.tail
    refine CP.bind (cp_stageA hD C Fa P1k hP input) fun a ha ↦ CP.bind (cp_H_le (k := 1) ?_) fun s₁ _ ↦
      CP.bind (cp_H_le (k := 1) ?_) fun s₂ _ ↦ CP.bind (cp_H_le (k := 1) ?_) fun s₃ _ ↦
      CP.bind (CP.bind (cp_stageB C Fa input a s₁ s₂ s₃ ha) fun b hb ↦ CP.bind (cp_H_le (k := 1) ?_) fun st _ ↦
        CP.bind (cp_of_qc (qc_stageC hD C Fa input b st hb.2)) fun _ _ ↦ cp_pure (P := fun _ ↦ True) _ trivial)
        fun _ _ ↦ cp_pure (P := fun _ ↦ True) _ trivial
    · show (fixLen 88 _).length < 136 * 1
      rw [fixLen_length]
      norm_num
    · rw [len_digestBytes]
      norm_num
    · rw [len_digestBytes]
      norm_num
    · show (UniKeccakComplete.Prob.tInput b.wr).length < 136 * 1
      simp only [UniKeccakComplete.Prob.tInput, List.length_append, len_digestBytes, Array.length_toList,
        Array.size_extract]
      have := hb.1
      omega
  refine (h.mono ?_ fun _ _ ↦ trivial).toQC
  unfold pi2RunN costA
  have := setup2_le hD
  omega

theorem pi2RunN_le : pi2RunN ≤ 2 ^ 50 := by
  unfold pi2RunN costA setupR costC costR openP2 contractC cOpen gOpen ivC UniKeccakComplete.Cost.openCost
  norm_num [treeCost, vOpen, whirBound, costHeight, blockFactor, PcsQuotient.nonceFuel]

end Cost2

open Cost2 in
/-- **`Pi2RunCost` for a π1 prover of at most `2^47` block calls** (`Pi1Cost`, named): at most `pi2RunN ≤ 2^50` block
calls (`pi2RunN_le`), at the real deployment. -/
theorem pi2RunCost_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    {P1k : Pi1ProverK D} (hP1 : Pi1Cost D P1k) : Pi2RunCost D C Fa P1k pi2RunN := fun input rows q hfit hrel ↦
  qc_pi2Staged hD C Fa _ (hP1 input rows q hfit hrel) input

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.pi2RunCost_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2RunCost_of

/-- info: 'RecCompose.Pi2G.Cost2.pi2RunN_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.Cost2.pi2RunN_le
