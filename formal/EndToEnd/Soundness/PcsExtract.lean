-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Soundness/Extract.lean` (`extractFrom_spec`, `extractor_of_mem`)
-- and `formal/EndToEnd/Soundness/Replay.lean` (`witnessWord_eq_committed`) at commit abe22812, to the witness table
-- of the EIP's PCS claims (committed as itself, its root the first two scalars' digest), and from
-- `formal/Compose/Compose/Rpm.lean` (`adversaryExtractor_congr`).
import Soundness.PcsF1
import Soundness.MerkleWord
import Soundness.Replay
import Soundness.Extract

/-!
# What the extractors read of a transcript

The event the transfer carries (`EvK`, an event on a transcript of Keccak-256 evaluations) is that the verifier
accepts while **the witness root's word, read off the transcript, lists no stack spelling a secret**
(`ExtractsT`: mumbai's list decoder `decodeStacks` on the Merkle word `wordT`). Here:

* `ExtractsT` reads the transcript through its answers (`lookInv_EvK`), and only at the lengths the witness tree
  hashes (`merkleWord_filter`: a node's `64` bytes, a leaf's `512`);
* **`extracts_of_mem`** (`SoundPcs`'s side): if `SoundPcs`'s extractor list on a transcript (`adversaryExtractor2`,
  the deployed table code `colCode` of the witness table) holds a message satisfying F1's relation for the
  statement, `ExtractsT` holds of that transcript (`StackRel`);
* **`extractor_of_extracts`** (the Statement's side): if `ExtractsT` holds of the setup tree's log, any entries of
  other lengths (the out-of-domain point's) and the Keccak-256 evaluations of the adversary's transcript, the
  Statement's extractor returns a secret of the statement: its word is mumbai's `committedLeaves` on those
  evaluations (`witnessWord_eq_committed`), which agrees with `wordT` on every column (`wordOfMerkle_merkleWord_eq`),
  so its list decoder, tried last, lists the stack (`mem_decodeStacks_congr`), and what it returns satisfies the
  relation (`extractFrom_spec`).
-/

set_option linter.unusedSectionVars false

attribute [local irreducible] PcsQuotient.membershipBuilder PcsQuotient.secretOfStack
set_option simprocs false

open OracleSpec OracleComp

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## The event -/

/-- **The witness word a transcript commits to under a root**: the Merkle word of the witness table (`24`
variables, rate `1/2`: height `19`, leaves of `512` bytes), read as words. -/
def wordT (tr : Transcript) (r : Digest) : Word :=
  wordOfMerkle (WhirBridge.rootHeight 24 WhirBridge.logInvRate) (2 ^ WhirBridge.laneFold)
    (merkleWord (histOfTr tr) (tableOfTr tr) (WhirBridge.rootHeight 24 WhirBridge.logInvRate) leafBytes (toB r))

/-- **The extraction succeeds on a transcript**: the proof names a witness root, and mumbai's list decoder on its
word lists a stack spelling a secret of the statement. -/
def ExtractsT (a : PcsQuotient.Statement × PcsQuotient.Proof) (tr : Transcript) : Prop :=
  ∃ r, PcsQuotient.rootOfHalves a.2.reduction.witness.root = some r ∧
    ∃ st ∈ LeanVM.Extraction.decodeStacks 24 WhirBridge.logInvRate (wordT tr r),
      PcsQuotient.Relation a.1 (PcsQuotient.secretOfStack (PcsQuotient.membership PcsQuotient.logRows) st)

/-- **The event**: the verifier accepts while the extraction fails on the transcript. -/
def EvK {σ₀ : Type} (_ : σ₀) (a : PcsQuotient.Statement × PcsQuotient.Proof) (v : Bool) (tr : Transcript) :
    Prop :=
  v = true ∧ ¬ ExtractsT a tr

theorem hist_table_congr {tr tr' : Transcript} (h : ∀ x, lookTr tr x = lookTr tr' x) :
    histOfTr tr = histOfTr tr' ∧ tableOfTr tr = tableOfTr tr' := by
  have hs : ∀ x, (tr.find? fun e => decide (e.1 = x)).map Prod.snd =
      (tr'.find? fun e => decide (e.1 = x)).map Prod.snd := fun x => by
    have := h x
    rw [lookTr_eq_map, lookTr_eq_map] at this
    exact Option.map_injective (LeanVM.Rpm.digestEquiv.symm.injective) this
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_histOfTr_iff, mem_histOfTr_iff, hs x]
  · funext x
    simp only [tableOfTr, hs x]

theorem wordT_congr {tr tr' : Transcript} (h : ∀ x, lookTr tr x = lookTr tr' x) (r : Digest) :
    wordT tr r = wordT tr' r := by
  obtain ⟨h1, h2⟩ := hist_table_congr h
  simp only [wordT, h1, h2]

/-- **The event reads the transcript through its answers.** -/
theorem lookInv_EvK {σ₀ : Type} : PcsKS.LookInv (EvK (σ₀ := σ₀)) := by
  intro s a v tr tr' h hv
  refine ⟨hv.1, fun ⟨r, hr, st, hst, hrel⟩ => hv.2 ⟨r, hr, st, ?_, hrel⟩⟩
  rwa [wordT_congr h r]

/-! ## `SoundPcs`'s side -/

variable {P : Kc3.Params E} (readW : Column 24 → P.Msg₁) (hrel : StackRel P readW)

/-- The witness table's code of `SoundPcs`: the extractor's decoder, each column read by `readW`. -/
abbrev cWK : TableCode P.Msg₁ := SoundPcs.colCode 24 SoundPcs.adm24 readW

include hrel in
/-- **If `SoundPcs`'s extractor list holds a witness, the extraction succeeds** on the same transcript. -/
theorem extracts_of_mem (a : PcsQuotient.Statement × PcsQuotient.Proof) (index : PcsQuotient.Commitment)
    (tA : Transcript) (rW : Digest) (hW : PcsQuotient.rootOfHalves a.2.reduction.witness.root = some rW)
    (g : P.Msg₁)
    (hg : g ∈ adversaryExtractor2 (cWK readW) tA (rootProofOf2 index a.1 a.2.reduction))
    (hs : P.Sat ((pcsWire2 P).decode (rootProofOf2 index a.1 a.2.reduction).stmt) (P.cells g.1)) :
    ExtractsT a tA := by
  have hr : (rootProofOf2 index a.1 a.2.reduction).rW = toB rW := by
    simp [rootProofOf2, hW]
  unfold adversaryExtractor2 cWK at hg
  rw [hr] at hg
  dsimp only [SoundPcs.colCode] at hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  unfold decodeColumns at hq
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hq
  exact ⟨rW, hW, st, hst, hrel a.1 st hs⟩

/-! ## The lengths the witness tree hashes -/

/-- An entry of a node's `64` bytes or a leaf's `ℓ`. -/
def keepLen (ℓ : ℕ) (e : List UInt8 × QuotientRpm.Bytes32) : Bool :=
  decide (e.1.length = 64) || decide (e.1.length = ℓ)

theorem mem_hist_filter (tr : Transcript) (ℓ : ℕ) (z : List UInt8) :
    z ∈ histOfTr (tr.filter (keepLen ℓ)) ↔ z ∈ histOfTr tr ∧ (z.length = 64 ∨ z.length = ℓ) := by
  simp only [histOfTr, List.mem_toFinset, List.mem_map, List.mem_filter, keepLen, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hk⟩, rfl⟩
    exact ⟨⟨e, he, rfl⟩, hk⟩
  · rintro ⟨⟨e, he, rfl⟩, hk⟩
    exact ⟨e, ⟨he, hk⟩, rfl⟩

theorem table_filter (tr : Transcript) (ℓ : ℕ) (z : List UInt8) (hz : z.length = 64 ∨ z.length = ℓ) :
    tableOfTr (tr.filter (keepLen ℓ)) z = tableOfTr tr z := by
  unfold tableOfTr
  congr 2
  rw [List.find?_filter]
  congr 1
  funext e
  by_cases he : e.1 = z
  · subst he
    simp [keepLen, hz]
  · simp [he]

theorem below_filter (tr : Transcript) (ℓ : ℕ) (d : List UInt8) (n : ℕ) (hn : n = 64 ∨ n = ℓ) :
    below (histOfTr (tr.filter (keepLen ℓ))) (tableOfTr (tr.filter (keepLen ℓ))) d n =
      below (histOfTr tr) (tableOfTr tr) d n := by
  unfold below
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, ht, hl⟩
    rw [table_filter tr ℓ z (hl ▸ hn)] at ht
    exact ⟨((mem_hist_filter tr ℓ z).mp hz).1, ht, hl⟩
  · rintro ⟨hz, ht, hl⟩
    refine ⟨(mem_hist_filter tr ℓ z).mpr ⟨hz, hl ▸ hn⟩, ?_, hl⟩
    rw [table_filter tr ℓ z (hl ▸ hn)]
    exact ht

theorem leafAt_filter (tr : Transcript) (ℓ : ℕ) :
    ∀ (k : ℕ) (d : List UInt8) (bs : List Bool),
      Compose.leafAt (histOfTr (tr.filter (keepLen ℓ))) (tableOfTr (tr.filter (keepLen ℓ))) ℓ k d bs =
        Compose.leafAt (histOfTr tr) (tableOfTr tr) ℓ k d bs
  | 0, d, _ => below_filter tr ℓ d ℓ (Or.inr rfl)
  | _ + 1, _, [] => rfl
  | k + 1, d, b :: bs => by
    simp only [Compose.leafAt, below_filter tr ℓ d 64 (Or.inl rfl)]
    congr 1
    funext y
    exact leafAt_filter tr ℓ k _ bs

/-- **The Merkle word reads only the entries of a node's and a leaf's lengths.** -/
theorem merkleWord_filter (tr : Transcript) (ht ℓ : ℕ) (r : QuotientRpm.Bytes32) :
    merkleWord (histOfTr (tr.filter (keepLen ℓ))) (tableOfTr (tr.filter (keepLen ℓ))) ht ℓ r =
      merkleWord (histOfTr tr) (tableOfTr tr) ht ℓ r := by
  funext p
  exact leafAt_filter tr ℓ ht _ _

theorem wordT_filter (tr : Transcript) (r : Digest) :
    wordT (tr.filter (keepLen leafBytes)) r = wordT tr r := by
  simp only [wordT, merkleWord_filter]

/-- **Entries of another length change no word.** -/
theorem wordT_drop (A L B : Transcript) (hL : ∀ e ∈ L, e.1.length = 46) (r : Digest) :
    wordT (A ++ L ++ B) r = wordT (A ++ B) r := by
  rw [← wordT_filter (A ++ L ++ B), ← wordT_filter (A ++ B)]
  have hf : L.filter (keepLen leafBytes) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [keepLen, hL e he, leafBytes, WhirBridge.laneFold]
    decide
  simp only [List.filter_append, hf, List.append_nil]

/-! ## The Statement's side -/

/-- **The Statement's extractor returns a secret** when its word is `W` and the list decoder lists a stack spelling
a secret of the statement: any circuit of `2^n` rows. The fast path's and the unique decoder's candidates are tried
first; whatever they return satisfies the relation. -/
theorem extractFrom_spec (n : ℕ) (circuit : PcsQuotient.Circuit) (hlog : circuit.logRows = n)
    (stmt : PcsQuotient.Statement) (pre : Digest → ℕ → Option (List UInt8))
    (proof : PcsQuotient.Proof) (W : ℕ → List K)
    (hw : PcsQuotient.witnessWord n pre proof = some W)
    (st : Vector K (2 ^ PcsQuotient.cellVars n))
    (hst : st ∈ LeanVM.Extraction.decodeStacks (PcsQuotient.cellVars n)
      PcsQuotient.logInvRate W)
    (hrel : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st)) :
    ∃ w, PcsQuotient.extractFrom circuit stmt pre proof = some w ∧
      PcsQuotient.Relation stmt w := by
  unfold PcsQuotient.extractFrom
  rw [hlog, hw, Option.bind_eq_bind, Option.bind_some]
  have hf : ∀ (a : Vector K (2 ^ PcsQuotient.cellVars n)) b,
      (let w := PcsQuotient.secretOfStack circuit a
        if PcsQuotient.Relation stmt w then some w else none) = some b →
        PcsQuotient.Relation stmt b := fun a b hab => by
    by_cases hr : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit a)
    · simp only [ite_eq_left hr] at hab
      cases hab
      exact hr
    · simp only [ite_eq_right hr] at hab
      cases hab
  refine Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
    (Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
    (Soundness.findSome_spec _ _ _ hf ⟨st, hst, ?_⟩))
  show (if PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st) then
    some (PcsQuotient.secretOfStack circuit st) else none).isSome = true
  rw [ite_eq_left hrel]
  rfl

/-- **The Statement's witness word is mumbai's `committedLeaves`** on the setup's evaluations and the
transcript's, at a proof naming the witness root `d`. -/
theorem witnessWord_eq_committed (setupEvals : List (List UInt8 × Digest)) (T : Common.OracleQueryLog)
    (proof : PcsQuotient.Proof) (d : Digest)
    (hd : PcsQuotient.rootOfHalves proof.reduction.witness.root = some d) :
    PcsQuotient.witnessWord 22 (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (setupEvals ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) proof =
      some (LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
        ((setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1)) d 19
          (2 ^ WhirBridge.laneFold)) 19 (2 ^ WhirBridge.laneFold)) := by
  unfold PcsQuotient.witnessWord PcsQuotient.witnessRootOf
  rw [hd, Option.map_some]
  congr 1
  show LeanVM.Extraction.leafAt (PcsQuotient.Replay.leavesUnder _ 64 19 d) 19 64 =
    LeanVM.Extraction.leafAt (LeanVM.Extraction.subtreeLeaves _ 64 19 d) 19 64
  rw [← Soundness.Replay.leavesUnder_preimage]
  congr 1
  refine Soundness.Replay.leavesUnder_congr _ _ 64 (fun d' ↦ ?_) (fun d' ↦ ?_) 19 d
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' 64 (by decide)
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' (8 * 64) (by decide)

theorem trOf_append_eval (t : LeanVM.Prover.Tree) (T : Common.OracleQueryLog) :
    Soundness.trOf (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)) =
      Soundness.treeTr t ++ evalTr (permutationQueries T) := by
  simp only [Soundness.trOf, Soundness.treeTr, evalTr, List.map_append]

/-- **If the extraction succeeds on the setup tree's log, entries of another length, and the Keccak-256
evaluations of the adversary's transcript, the Statement's extractor returns a secret of the statement.** -/
theorem extractor_of_extracts (t : LeanVM.Prover.Tree) (L : Transcript) (hL : ∀ e ∈ L, e.1.length = 46)
    (T : Common.OracleQueryLog) (a : PcsQuotient.Statement × PcsQuotient.Proof)
    (h : ExtractsT a (Soundness.treeTr t ++ L ++ evalTr (permutationQueries T))) :
    ∃ w, PcsQuotient.extractor a.1 (PcsQuotient.Tree.evaluations t) T a.2 = some w ∧
      PcsQuotient.Relation a.1 w := by
  obtain ⟨r, hr, st, hst, hrel⟩ := h
  set paths := PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)
    with hpaths
  rw [wordT_drop _ L _ hL, ← trOf_append_eval] at hst
  have hadm : Whir.Admissible 24 WhirBridge.logInvRate := SoundPcs.adm24
  have hst' : st ∈ LeanVM.Extraction.decodeStacks 24 1
      (LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (lookupEvaluation paths) (paths.map (·.1)) r 19 (2 ^ WhirBridge.laneFold)) 19
          (2 ^ WhirBridge.laneFold)) := by
    refine Soundness.mem_decodeStacks_congr hadm (fun v hv => ?_) st hst
    have hv' : v < 2 ^ 19 := lt_of_lt_of_eq hv rfl
    exact Soundness.wordOfMerkle_merkleWord_eq paths r 19 (2 ^ WhirBridge.laneFold) hv'
  unfold PcsQuotient.extractor PcsQuotient.transcriptExtractorFor
  exact extractFrom_spec 22 _ rfl a.1 _ a.2 _
    (witnessWord_eq_committed (PcsQuotient.Tree.evaluations t) T a.2 r hr) st hst' hrel

end PcsKS
