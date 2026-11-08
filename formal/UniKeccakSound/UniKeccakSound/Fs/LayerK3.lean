-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/LayerK.lean` at π1-rec3's
-- shape, as `UniSound/Rec3/FsFinal128_3.lean`.
import UniKeccakSound.Fs.GameK3
import UniKeccakSound.Fs.ExtractK3
import UniKeccakSound.Fs.VerifierK3
import UniKeccakSound.Fs.LayerK

/-!
# The Keccak verifier's Fiat–Shamir layer at π1-rec3's shape, proved

* **`uniGameLeVK3_holds`**, **`fsLayer128K3_holds`**: the coupling and **`FsLayer128K3 F D F3 nV np C`** (`FinalK3.lean`)
  for every code-level link `C` with `UniOutRootsK3` (`Code/Link3.lean`), from the deployment's numbers
  (`UniShapesK`, `LayoutVarsSmallK`, `UniIvK`: the main line's) and the chain's; **`fsLayer128K3_holds'`** with the
  chain's numbers from Flock's rounds (`nSteps F3.prog.rounds + np ≤ 1016`, Flock's rounds and `nV` at most `2^30`
  scalars; `nQ_uSpecK3`: `nQ = nSteps F3.prog.rounds + np + 8`).
* **`fsLayer128K3_codeAt`**: at `Code/Link3.lean`'s link `uniCodeK3At` (`nV = valsCountK`,
  `varsOf (layoutsOfK D.shape) = 2 np + 1`); **`fsLayer128K3_ref`**, **`fsLayer128K3_refCodeAt`**: at the reference
  deployment (the 128-signature shape, leanVM's program IV; the shape's numbers are `LayerK.lean`'s
  `uniShapesK_ref`, `layoutVarsSmallK_ref`, `uniIvK_programIv`; `np = 13` there).
-/

namespace UniKeccakSound

open Compose LeanVM.Parameters LeanVM.Protocol UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **The coupling, proved**, from `LayoutVarsSmallK` and `UniOutRootsK3`. -/
theorem uniGameLeVK3_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D) (hsmall : LayoutVarsSmallK D)
    (hO : UniOutRootsK3 D F3 C) : UniGameLeVK3 D F3 nV np C hs :=
  uniGameLeVK3_of D F3 nV np C hs (uniSetupBridgeK D hs hsmall.setup)
    (uniVerifierBridgeK3_of_walk D F3 nV np C hs (uniWalkK3 D F3 nV np C) (uniWalkRejectK3 D F3 nV np C) hO)
    (uniExtractBridgeK3 D F3 nV np hs hsmall.c1)

/-- **The Keccak verifier's Fiat–Shamir layer at π1-rec3's shape, at `≥ 128` bits, proved**, for every code-level link naming the
transcript's roots, from the deployment's numbers. -/
theorem fsLayer128K3_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hnQ : (uSpecK3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK3 F3 nV np, r.nv ≤ 2 ^ 30) (hO : UniOutRootsK3 D F3 C) :
    FsLayer128K3 F D F3 nV np C :=
  fsLayer128K3_of_gameV' D F3 nV np C hs hnQ hnv hI (uniGameLeVK3_holds D F3 nV np C hs hsmall hO)

/-! ## The chain's numbers from Flock's rounds -/

/-- **π1-rec3's chain queries**: `nSteps` of Flock's rounds, `np`, and `8`. -/
theorem nQ_uSpecK3 {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) :
    (uSpecK3 F3 nV np).K.nQ = nSteps F3.prog.rounds + np + 8 := by
  show nSteps (rec3Rounds F3.prog.rounds nV np) + 1 = _
  simp only [rec3Rounds, nSteps_append, nSteps_replicate, nSteps]
  ring

/-- **The Fiat–Shamir layer at π1-rec3's shape, proved**, its chain's numbers from Flock's rounds: at most
`1016 − np` of Flock's steps, and every one of Flock's rounds and the values' round at most `2^30` scalars. -/
theorem fsLayer128K3_holds' (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hFl : nSteps F3.prog.rounds + np ≤ 1016)
    (hFlv : ∀ r ∈ F3.prog.rounds, r.nv ≤ 2 ^ 30) (hnV : nV ≤ 2 ^ 30) (hO : UniOutRootsK3 D F3 C) :
    FsLayer128K3 F D F3 nV np C := by
  refine fsLayer128K3_holds D F3 nV np C hs hsmall hI ?_ ?_ hO
  · rw [nQ_uSpecK3]
    omega
  · intro r hr
    simp only [uRoundsK3, rec3Rounds, List.mem_append, List.mem_cons,
      List.mem_replicate, List.not_mem_nil, or_false] at hr
    rcases hr with (((rfl | hr) | rfl | rfl) | ⟨-, rfl⟩) | rfl
    · show 0 ≤ 2 ^ 30
      exact Nat.zero_le _
    · exact hFlv r hr
    · show 0 ≤ 2 ^ 30
      exact Nat.zero_le _
    · exact hnV
    · show 8 ≤ 2 ^ 30
      norm_num
    · show 2 ≤ 2 ^ 30
      norm_num

/-! ## The reference Keccak shape -/

/-- **The Keccak verifier's Fiat–Shamir layer at π1-rec3's shape at the reference deployment**: the 128-signature
shape, leanVM's program IV, any `A0`, `B0` constants; for every code-level link naming the transcript's roots
(`UniOutRootsK3`) at `nV ≤ 2^30` values and `np` pair rounds, and every Flock phase with
`nSteps F3.prog.rounds + np ≤ 1016` and rounds of `≤ 2^30` scalars. -/
theorem fsLayer128K3_ref (D : KDeployment) (hD : D.shape = keccakRefShape) (hIv : D.programIv = UniStatement.programIv)
    {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
    (C : UniCodeK3 D F3 nV np) (hFl : nSteps F3.prog.rounds + np ≤ 1016) (hFlv : ∀ r ∈ F3.prog.rounds, r.nv ≤ 2 ^ 30)
    (hnV : nV ≤ 2 ^ 30) (hO : UniOutRootsK3 D F3 C) : FsLayer128K3 F D F3 nV np C :=
  fsLayer128K3_holds' D F3 nV np C (uniShapesK_ref D hD) (layoutVarsSmallK_ref D hD) (uniIvK_programIv D hIv)
    hFl hFlv hnV hO

/-! ## At the code-level link `uniCodeK3At` -/

/-- **The Fiat–Shamir layer at π1-rec3's shape at `Code/Link3.lean`'s code-level link** (`uniCodeK3At`,
`nV = valsCountK = 118`, `varsOf (layoutsOfK D.shape) = 2 np + 1`), from the deployment's numbers and Flock's
rounds. -/
theorem fsLayer128K3_codeAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ)
    (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (hs : UniShapesK D)
    (hsmall : LayoutVarsSmallK D) (hI : UniIvK D) (hFl : nSteps F3.prog.rounds + np ≤ 1016)
    (hFlv : ∀ r ∈ F3.prog.rounds, r.nv ≤ 2 ^ 30) :
    FsLayer128K3 F D F3 nV np (uniCodeK3At D F3 hκ nV np hnV hV) :=
  fsLayer128K3_holds' D F3 nV np _ hs hsmall hI hFl hFlv (by rw [hnV, valsCountK_eq]; norm_num)
    (uniOutRootsK3_uniCodeK3At D F3 hκ nV np hnV hV)

/-- **The Fiat–Shamir layer at π1-rec3's shape at the reference deployment and `Code/Link3.lean`'s link.** -/
theorem fsLayer128K3_refCodeAt (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ)
    (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hFl : nSteps F3.prog.rounds + np ≤ 1016) (hFlv : ∀ r ∈ F3.prog.rounds, r.nv ≤ 2 ^ 30) :
    FsLayer128K3 F D F3 nV np (uniCodeK3At D F3 hκ nV np hnV hV) :=
  fsLayer128K3_codeAt D F3 hκ nV np hnV hV (uniShapesK_ref D hD) (layoutVarsSmallK_ref D hD)
    (uniIvK_programIv D hIv) hFl hFlv

end UniKeccakSound

/-- info: 'UniKeccakSound.fsLayer128K3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K3_holds

/-- info: 'UniKeccakSound.fsLayer128K3_refCodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.fsLayer128K3_refCodeAt
