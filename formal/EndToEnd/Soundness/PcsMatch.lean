-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: `SoundPcs.ClaimsMatch` from `PcsBridge.Kc3.accepts_of_claims`.
import Soundness.PcsFinal
import PcsBridge.Kc3Accepts

/-!
# The claims match F1's verifier

For F1's parameters `P` that match the statement's constants with the Statement's wiring table as `σ`'s polynomial
(`PcsBridge.Kc3.Matches P (colFn wcol)`), the witness table read as its four row polynomials (`readWK`) and the
quotient table as its four polynomials (`readTK`) make `SoundPcs.ClaimsMatch (pcsWire2 P) wcol` (**`claimsMatchK`**):
the deployed claims, where they hold of the tables, make F1's verifier accept.
-/

set_option linter.unusedSectionVars false

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters WhirBridge WhirBridge.Pcs SoundPcs
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd
open PcsBridge.Kc3

variable (P : _root_.Kc3.Params E)

/-- The witness table's four row polynomials, as F1's first message. -/
noncomputable def readWK (hcard : P.T.card = 2 ^ 22) (q : Column 24) : P.Msg₁ :=
  ⟨witnessOfTable (k := 22) (colFn q), fun j => by
    rw [hcard]
    exact natDegree_witnessOfTable_lt _ j⟩

theorem readWK_fst (hcard : P.T.card = 2 ^ 22) (q : Column 24) :
    (readWK P hcard q).1 = witnessOfTable (k := 22) (colFn q) := by simp only [readWK]

/-- The quotient table's four polynomials, as F1's second message. -/
noncomputable def readTK (hn : P.nCells = 2 ^ 24) (q : Column 28) : P.Msg₂ :=
  ⟨readTM (colFn q), by
    rw [hn, readTM_A₀, readTM_A₁, readTM_B₀, readTM_B₁]
    exact ⟨natDegree_limbPoly_lt _ _ _ _, natDegree_limbPoly_lt _ _ _ _, natDegree_limbPoly_lt _ _ _ _,
      natDegree_limbPoly_lt _ _ _ _⟩⟩

theorem readTK_fst (hn : P.nCells = 2 ^ 24) (q : Column 28) : (readTK P hn q).1 = readTM (colFn q) := by
  simp only [readTK]

theorem nCells_of_card (hcard : P.T.card = 2 ^ 22) : P.nCells = 2 ^ 24 := by
  rw [_root_.Kc3.Params.nCells_eq, hcard]; norm_num

/-- **The claims match F1's verifier** for parameters matching the statement's constants. -/
noncomputable def claimsMatchK (hM : Matches P (colFn wcol)) : ClaimsMatch (pcsWire2 P) wcol where
  readW := readWK P hM.card
  readT := readTK P (nCells_of_card P hM.card)
  accepts a cl qW qT h hlw hls hlc hw hs hc := by
    unfold claimsD at h
    rw [colEval_eq_mle _ _ hlw] at hw
    rw [colEval_eq_mle _ _ hls] at hs
    rw [colEval_eq_mle _ _ hlc] at hc
    rw [readWK_fst, readTK_fst]
    exact accepts_of_claims P hM h (colFn qW) (colFn qT) hw hs hc

end PcsKS

/-- info: 'PcsKS.claimsMatchK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsKS.claimsMatchK
