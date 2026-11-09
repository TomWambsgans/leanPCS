-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsFinal.lean`'s `uniGameLeV_holds` and
-- `UniSound/FsFinal128.lean`'s `fsLayer128_holds` for the Keccak verifier, and the reference Keccak shape's numbers.
import UniKeccakSound.Fs.GameK
import UniKeccakSound.Fs.ExtractK
import UniKeccakSound.Fs.VerifierK
import UniKeccakSound.Code.Numbers

/-!
# The Keccak verifier's Fiat–Shamir layer at `≥ 128` bits, proved

* **`uniGameLeVK_holds`**: the coupling `UniGameLeVK` (`GameK.lean`) for every Keccak deployment whose `C1` and setup
  stacks have fewer than `256` variables (`LayoutVarsSmallK`) and every code-level link whose result names the
  transcript's roots (`UniOutRootsK`, `Code/Link.lean`), from its three bridge facts, each proved: the setup's
  (`uniSetupBridgeK`), the verifier's (`uniVerifierBridgeK_of_walk` with `uniWalkK`, `uniWalkRejectK`) and the
  extractor's (`uniExtractBridgeK`).
* **`fsLayer128K_holds`**: **`FsLayer128K F D Fl nV V C`** (`FsK.lean`) for every such link `C`, from the deployment's
  numbers only: `UniShapesK` (the three layout words name `23 … 28` variables, `C1`'s and `C2`'s at least `24`),
  `LayoutVarsSmallK`, `UniIvK` (the program IV's length), the chain's `≤ 2^10` queries and rounds of `≤ 2^30`
  scalars; **`fsLayer128K_holds'`** with the last two from Flock's rounds (`nSteps Fl.prog.rounds + V ≤ 1014`, each
  of Flock's rounds and `nV` at most `2^30` scalars).
* **The reference Keccak shape** (`keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]`, 128 signatures:
  `C1` `2^27` words, `C2` `2^26`, the setup `2^23`, by kernel evaluation after `stackLayout_vars` and, for `C2`,
  the heap's sort replaced by its result, `c2Vars_ref`): `uniShapesK_ref`, `layoutVarsSmallK_ref`, and `uniIvK_programIv`
  (leanVM's program IV, `32` bytes); **`fsLayer128K_ref`**: the layer at a deployment of that
  shape and IV, for every link `C` with `UniOutRootsK` and every Flock phase with `nSteps Fl.prog.rounds + V ≤ 1014`
  and rounds of `≤ 2^30` scalars (the code-level link's numbers are `nV = 118`, `V = 27` here).
-/

namespace UniKeccakSound

open Compose LeanVM.Parameters LeanVM.Protocol UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **The coupling, proved**, from `LayoutVarsSmallK` and `UniOutRootsK`. -/
theorem uniGameLeVK_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D) (hsmall : LayoutVarsSmallK D)
    (hO : UniOutRootsK D Fl C) : UniGameLeVK D Fl nV V C hs :=
  uniGameLeVK_of D Fl nV V C hs (uniSetupBridgeK D hs hsmall.setup)
    (uniVerifierBridgeK_of_walk D Fl nV V C hs (uniWalkK D Fl nV V C) (uniWalkRejectK D Fl nV V C) hO)
    (uniExtractBridgeK D Fl nV V hs hsmall.c1)

/-- **The Keccak verifier's Fiat–Shamir layer at `≥ 128` bits, proved**, for every code-level link naming the
transcript's roots, from the deployment's numbers. -/
theorem fsLayer128K_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hnQ : (uSpecK Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK Fl nV V, r.nv ≤ 2 ^ 30) (hO : UniOutRootsK D Fl C) :
    FsLayer128K F D Fl nV V C :=
  fsLayer128K_of_gameV' D Fl nV V C hs hnQ hnv hI (uniGameLeVK_holds D Fl nV V C hs hsmall hO)

/-! ## The chain's numbers from Flock's rounds -/

theorem nSteps_append : ∀ (a b : List RoundSpec), nSteps (a ++ b) = nSteps a + nSteps b
  | [], b => by simp [nSteps]
  | s :: a, b => by
    simp only [List.cons_append, nSteps, nSteps_append a b]
    ring

theorem nSteps_replicate (r : RoundSpec) : ∀ n, nSteps (List.replicate n r) = n * (r.ns + 1)
  | 0 => by simp [nSteps]
  | n + 1 => by
    rw [List.replicate_succ, nSteps, nSteps_replicate r n]
    ring

/-- **The main line's chain queries**: `nSteps` of Flock's rounds, `V`, and `10`. -/
theorem nQ_uSpecK {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ) :
    (uSpecK Fl nV V).K.nQ = nSteps Fl.prog.rounds + V + 10 := by
  show nSteps (uniRounds Fl.prog.rounds nV V) + 1 = _
  simp only [uniRounds, nSteps_append, nSteps_replicate, nSteps]
  ring

/-- **The Fiat–Shamir layer, proved**, its chain's numbers from Flock's rounds: at most `1014 − V` of Flock's steps,
and every one of Flock's rounds and the values' round at most `2^30` scalars. -/
theorem fsLayer128K_holds' (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hFl : nSteps Fl.prog.rounds + V ≤ 1014)
    (hFlv : ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30) (hnV : nV ≤ 2 ^ 30) (hO : UniOutRootsK D Fl C) :
    FsLayer128K F D Fl nV V C := by
  refine fsLayer128K_holds D Fl nV V C hs hsmall hI ?_ ?_ hO
  · rw [nQ_uSpecK]
    omega
  · intro r hr
    simp only [uRoundsK, uniRounds, List.mem_append, List.mem_cons,
      List.mem_replicate, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | hr) | rfl | rfl) | ⟨-, rfl⟩
    · show 0 ≤ 2 ^ 30
      exact Nat.zero_le _
    · exact hFlv r hr
    · show 0 ≤ 2 ^ 30
      exact Nat.zero_le _
    · exact hnV
    · show 2 ≤ 2 ^ 30
      norm_num

/-! ## The reference Keccak shape -/

/-- The reference Keccak shape (`EndK.lean`'s `keccakRef`, `Code/Numbers.lean`'s `keccak128`): 128 signatures. -/
abbrev keccakRefShape : UniStatement.Shape := keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]

/-- The pieces' words of a stack layout's columns (each `E`-valued column three limbs). -/
def piecesSum (cols : List (UniStatement.Column × ℕ × Bool)) : ℕ :=
  ((cols.flatMap fun x => (List.range (if x.2.2 then 3 else 1)).map fun limb => (x.1, limb, x.2.1)).map
    fun x => 2 ^ x.2.2).sum

theorem foldl_snd_sum {α β : Type} (f : β × ℕ → α → β × ℕ) (g : α → ℕ)
    (hf : ∀ acc x, (f acc x).2 = acc.2 + g x) :
    ∀ (l : List α) (init : β × ℕ), (l.foldl f init).2 = init.2 + (l.map g).sum
  | [], init => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_snd_sum f g hf l, hf, List.map_cons, List.sum_cons]
    ring

/-- **A stack layout's variables** do not depend on its blocks' order (`StackLayout.new` sorts them by
`List.mergeSort`, which the kernel does not evaluate): `⌈log₂⌉` of its pieces' words, at least `15`. -/
theorem stackLayout_vars (cols : List (UniStatement.Column × ℕ × Bool)) :
    (StackLayout.new cols).vars = max (log2Ceil (max (piecesSum cols) 2)) 15 := by
  unfold StackLayout.new
  show max (log2Ceil (max (List.foldl _ ((#[] : Array (UniStatement.Column × ℕ × ℕ × ℕ)), 0) _).2 2)) 15 = _
  rw [foldl_snd_sum _ (fun x : UniStatement.Column × ℕ × ℕ => 2 ^ x.2.2)
    (fun acc x => by obtain ⟨c, l, v⟩ := x; rfl), ((List.mergeSort_perm _ _).map _).sum_eq, Nat.zero_add]
  rfl

/-- The reference shape's setup stack has `23` variables (kernel evaluation). -/
theorem setupVars_ref : (setupLayout keccakRefShape).vars = 23 := by
  rw [show setupLayout keccakRefShape = StackLayout.new _ from rfl, stackLayout_vars]
  decide +kernel

/-- The reference shape's `C1` stack has `27` variables (kernel evaluation). -/
theorem c1Vars_ref : (c1LayoutK keccakRefShape).vars = 27 := by
  rw [show c1LayoutK keccakRefShape = StackLayout.new _ from rfl, stackLayout_vars]
  decide +kernel

theorem mergeSort_eq_of {α : Type} (le : α → α → Bool) (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b || le b a) {l L : List α} (hp : l.Perm L) (hs : L.Pairwise fun a b => le a b)
    (hanti : ∀ a ∈ L, ∀ b ∈ L, le a b = true → le b a = true → a = b) : l.mergeSort le = L :=
  List.Perm.eq_of_pairwise (le := fun a b => le a b = true)
    (fun a b ha hb h1 h2 => hanti a (((List.mergeSort_perm l le).trans hp).subset ha) b hb h1 h2)
    (List.pairwise_mergeSort htrans htotal l) hs ((List.mergeSort_perm l le).trans hp)

/-- The heap's order (`HeapLayout.new`'s comparator: larger first, ties by `Leaves.order`). -/
abbrev heapLe (a b : Leaves × ℕ) : Bool := b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)

theorem heapLe_trans : ∀ a b c, heapLe a b → heapLe b c → heapLe a c := by
  intro a b c h1 h2
  simp only [heapLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2 ⊢
  omega

theorem heapLe_total : ∀ a b, heapLe a b || heapLe b a := by
  intro a b
  simp only [heapLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- The reference shape's heap blocks, sorted (`HeapLayout.new`'s `sorted`). -/
def heapRefL : List (Leaves × ℕ) :=
  [(.memory, 20), (.bytecode, 18), (.table 1, 16), (.table 3, 16), (.table 0, 15), (.table 2, 15),
    (.table 5, 15), (.table 4, 14)]

/-- **The reference shape's `C2` stack has `26` variables**: the heap's sort replaced by its result
(`mergeSort_eq_of`: a permutation, sorted, the order antisymmetric on it), the `for` loops by `List.forIn`
(`Std.Legacy.Range.forIn_eq_forIn_range'`), then kernel evaluation. -/
theorem c2Vars_ref : (StackLayout.new (Shape.c2ColumnsK keccakRefShape)).vars = 26 := by
  rw [stackLayout_vars]
  simp only [Shape.c2ColumnsK, Shape.heap, HeapLayout.new, unusedBlocks, chunks,
    Std.Legacy.Range.forIn_eq_forIn_range']
  rw [mergeSort_eq_of heapLe heapLe_trans heapLe_total (L := heapRefL) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

/-- `layoutWordsK`'s `C2` word is `C2`'s layout's (`layoutsOfK`'s `C2` entry). -/
theorem layoutWordsK_c2 (s : UniStatement.Shape) :
    (layoutWordsK s).getD 1 [] = layoutWord s (layoutCode .c2) (StackLayout.new (Shape.c2ColumnsK s)).vars
      (StackLayout.new (Shape.c2ColumnsK s)).words := rfl

/-- **`LayoutVarsSmallK` at the reference shape.** -/
theorem layoutVarsSmallK_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : LayoutVarsSmallK D := by
  refine ⟨?_, ?_⟩
  · rw [hD, c1Vars_ref]; norm_num
  · rw [hD, setupVars_ref]; norm_num

/-- **`UniShapesK` at the reference shape**: `C1` `2^27` words, `C2` `2^26`, the setup `2^23`. -/
theorem uniShapesK_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : UniShapesK D := by
  have hs := layoutVarsSmallK_ref D hD
  have h0 : wvK D 0 = 27 := by rw [wvK_zero D hs.c1, hD, c1Vars_ref]
  have h2 : wvK D 2 = 23 := by rw [wvK_two D hs.setup, hD, setupVars_ref]
  have h1 : wvK D 1 = 26 := by
    unfold wvK
    rw [hD, layoutWordsK_c2, layoutWordVars_layoutWordK _ _ _ _ (by rw [c2Vars_ref]; norm_num), c2Vars_ref]
  refine ⟨fun k hk => ?_, fun k hk => ?_, by omega, by omega⟩
  · interval_cases k <;> omega
  · interval_cases k <;> omega

/-- **`UniIvK` at leanVM's program IV** (`32` bytes). -/
theorem uniIvK_programIv (D : KDeployment) (hI : D.programIv = UniStatement.programIv) : UniIvK D := by
  have h : UniStatement.programIv.length = 32 := by decide +kernel
  refine ⟨?_, ?_⟩ <;> rw [hI, h] <;> norm_num

/-- **The Keccak verifier's Fiat–Shamir layer at the reference deployment**: the 128-signature shape, leanVM's
program IV, any `A0`, `B0` constants; for every code-level link naming the transcript's roots (`UniOutRootsK`, which
`Code/Link.lean`'s `uniCodeKAt` has) at `nV ≤ 2^30` values and `V` batch rounds, and every Flock phase with
`nSteps Fl.prog.rounds + V ≤ 1014` and rounds of `≤ 2^30` scalars. -/
theorem fsLayer128K_ref (D : KDeployment) (hD : D.shape = keccakRefShape) (hIv : D.programIv = UniStatement.programIv)
    {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
    (C : UniCodeK D Fl nV V) (hFl : nSteps Fl.prog.rounds + V ≤ 1014) (hFlv : ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30)
    (hnV : nV ≤ 2 ^ 30) (hO : UniOutRootsK D Fl C) : FsLayer128K F D Fl nV V C :=
  fsLayer128K_holds' D Fl nV V C (uniShapesK_ref D hD) (layoutVarsSmallK_ref D hD) (uniIvK_programIv D hIv)
    hFl hFlv hnV hO

/-! ## At the code-level link `uniCodeKAt` -/

/-- **The Fiat–Shamir layer at `Code/Link.lean`'s code-level link** (`uniCodeKAt`, `nV = valsCountK = 118`,
`V = varsOf (layoutsOfK D.shape)`), from the deployment's numbers and Flock's rounds. -/
theorem fsLayer128K_codeAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (nV V : ℕ)
    (hnV : nV = valsCountK) (hV : V = varsOf (layoutsOfK D.shape)) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hFl : nSteps Fl.prog.rounds + V ≤ 1014)
    (hFlv : ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30) :
    FsLayer128K F D Fl nV V (uniCodeKAt D Fl hκ nV V hnV hV) :=
  fsLayer128K_holds' D Fl nV V _ hs hsmall hI hFl hFlv (by rw [hnV, valsCountK_eq]; norm_num)
    (uniOutRootsK_uniCodeKAt D Fl hκ nV V hnV hV)

/-- **The Fiat–Shamir layer at the reference deployment and `Code/Link.lean`'s code-level link.** -/
theorem fsLayer128K_refCodeAt (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (nV V : ℕ)
    (hnV : nV = valsCountK) (hV : V = varsOf (layoutsOfK D.shape)) (hFl : nSteps Fl.prog.rounds + V ≤ 1014)
    (hFlv : ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30) :
    FsLayer128K F D Fl nV V (uniCodeKAt D Fl hκ nV V hnV hV) :=
  fsLayer128K_codeAt D Fl hκ nV V hnV hV (uniShapesK_ref D hD) (layoutVarsSmallK_ref D hD)
    (uniIvK_programIv D hIv) hFl hFlv

end UniKeccakSound

/-- info: 'UniKeccakSound.fsLayer128K_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K_holds

/-- info: 'UniKeccakSound.fsLayer128K_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K_ref

/-- info: 'UniKeccakSound.fsLayer128K_refCodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K_refCodeAt
