-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakSound.EndK
import UniKeccakSound.Fs.LayerK

/-!
# The Keccak verifier's knowledge soundness at the reference shape (main line), the code-level link and the
Fiat–Shamir layer proved

`EndK.lean`'s `uniKnowledgeSoundnessKeccak_of` with the code-level link (`Code/Link.lean`'s `uniCodeKAt`) and the
Fiat–Shamir layer (`Fs/LayerK.lean`'s `fsLayer128K_refCodeAt`, at the reference shape `keccakRef` with leanVM's
program IV) in place. What remains are two named `Prop`s:

* `KFlockRefP D`: Flock on the Keccak-f block at `κ = h_SHA3`, every round's error at most `2^32/|E|`, and its rounds'
  numbers as the Fiat–Shamir layer's chain needs them (at most `1014` steps with the batch, every round at most
  `2^30` scalars);
* `KIdsP F D Fl`: for such a Flock interface, the identity model `I` at the code link's numbers (`valsCountK`
  values at `t`, `varsOf (layoutsOfK D.shape)` batch rounds), the last link for `uniCodeKAt`, and the identity
  model's numbers.
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **Remaining: Flock on the Keccak-f block** at the deployment's `κ = h_SHA3`, main line: an interface whose rounds
err at most `2^32/|E|`, with at most `1014` chain steps together with the batch's rounds and at most `2^30` scalars a
round. -/
def KFlockRefP (D : KDeployment) : Prop :=
  ∃ Fl : KFlockSound KeccakFlock.keccakFlockSpec (D.shape.heights.getD opBlake2s 0) keccakMain,
    (∀ j, Fl.err j ≤ e32) ∧ Compose.nSteps Fl.prog.rounds + varsOf (layoutsOfK D.shape) ≤ 1014 ∧
      ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30

/-- **Remaining: the identity model and the last link** for the Flock interface `Fl`: an identity model at the code
link's numbers whose last link holds for `uniCodeKAt`, with its numbers. -/
def KIdsP (F : KeccakVm.KeccakFlockSpec) (D : KDeployment)
    (Fl : KFlockSound F (D.shape.heights.getD opBlake2s 0) keccakMain) : Prop :=
  ∃ (I : UniIdsK F D Fl) (hnV : I.nV = valsCountK) (hV : I.V = varsOf (layoutsOfK D.shape)),
    UniFinalK D Fl I (uniCodeKAt D Fl rfl I.nV I.V hnV hV) ∧
      I.errMain ≤ e32 ∧ I.degSum + I.degBad ≤ 2 ^ 32 ∧ I.nRel + 2 ≤ 2 ^ 32

/-- **Knowledge soundness of the Keccak verifier (main line) at the reference shape**, for the Keccak-f block and
the explicit extractor `uniExtractorK`, error `uniBound128 (2^32/|E|) Q ≤ 2^-64` for `Q ≤ 2^64`; the code-level link
and the Fiat–Shamir layer proved, from the named `KFlockRefP` and `KIdsP`. -/
theorem uniKnowledgeSoundnessKeccak_ref (D : KDeployment) (hD : D.shape = keccakRef)
    (hIv : D.programIv = UniStatement.programIv) (hFl : KFlockRefP D)
    (hI : ∀ Fl, KIdsP KeccakFlock.keccakFlockSpec D Fl) :
    UniKnowledgeSoundnessKeccak KeccakFlock.keccakFlockSpec D (uniBound128 e32) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 e32 Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  obtain ⟨Fl, hFle, hsteps, hnv⟩ := hFl
  obtain ⟨I, hnV, hV, hFin, hMain, hdeg, hrel⟩ := hI Fl
  have hFs := fsLayer128K_refCodeAt D (hD.trans rfl) hIv Fl rfl I.nV I.V hnV hV
    (by rw [hV]; exact hsteps) hnv
  exact uniKnowledgeSoundnessK_bits Fl I _ hFin hFs hMain hFle hdeg hrel

end UniKeccakSound
