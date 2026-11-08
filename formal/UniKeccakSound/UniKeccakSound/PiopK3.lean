-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The round-by-round form is `UniSound/Rec3/Piop3.lean`'s
-- (π1-rec3's rounds `rec3Rounds`, the batch `PairBatch`), for the Keccak verifier at `keccakRec3`.
import UniSound.Rec3.Piop3
import UniKeccakSound.PiopK

/-!
# The Keccak verifier's PIOP at π1-rec3's shape (`keccakRec3`): identity model, states, errors

The rounds are π1-rec3's (`UniSound.rec3Rounds`: `C1` and `c, β, γ`; Flock's; `C2` and `t`; the values and `ρ, λ`;
`np` pair rounds; the last plain round), the batch's rounds abstract (`UniSound.PairBatch`).

**The identity model** (`UniIdsK3`) is `UniSound.UniIds3` for the Keccak VM, as `UniIdsK` is `UniIds`'s: the relation
`RelK F D`, Flock's predicate `KFlockHolds F κ` on `2^(11 + κ)` cells, three commitments, no pending term. Where
π1-rec3's states carry the pending claim from `C2`'s round on, these carry Flock's zeros (the structured terminal,
`F3.prog.ZerosVanish fd []`); the batch's start may assume them.
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open scoped ENNReal

/-! ## The identity model -/

/-- **The Keccak verifier's identity model at π1-rec3's shape**: `UniIdsK` at π1-rec3's transcripts, for the Flock
phase `F3` on the Keccak-f block: round `0`'s three challenges, Flock's ring claim on its result, the batch over
`2 np + 1` variables, its start where Flock's zeros vanish. -/
structure UniIdsK3 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) where
  nV : ℕ
  qf : Stk → LeanVM.Protocol.Column (KeccakVm.kWords + κ)
  MainHolds : USt → Stk → Prop
  rel_of : ∀ s c, MainHolds s c → KFlockHolds F κ (qf c) → RelK F D s c
  MainOK : USt → Stk → List E → Prop
  errMain : ℝ≥0∞
  mainSound : ∀ s c, Pr{let ch ← Compose.draws E 3}[¬ MainHolds s c ∧ MainOK s c ch] ≤ errMain
  polys : USt → Stk → List E → Done → Stk → List (Polynomial E)
  degSum : ℕ
  deg_le : ∀ s c1 ch fd c2, ((polys s c1 ch fd c2).map Polynomial.natDegree).sum ≤ degSum
  main_of_polys : ∀ s c1 ch fd c2, (∀ P ∈ polys s c1 ch fd c2, P = 0) → MainOK s c1 ch
  zb : Done → Polynomial E
  zb_ne : ∀ fd, zb fd ≠ 0
  degBad : ℕ
  zb_deg : ∀ fd, (zb fd).natDegree ≤ degBad
  diffs : USt → Stk → List E → Done → Stk → E → List E → List (List E)
  nRel : ℕ
  diffs_len : ∀ s c1 ch fd c2 t vals, ∀ d ∈ diffs s c1 ch fd c2 t vals, d.length ≤ nRel
  diffs_count : ∀ s c1 ch fd c2 t vals, (diffs s c1 ch fd c2 t vals).length ≤ 3
  diffs_eval : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polys s c1 ch fd c2, P.eval t = 0
  diffs_flock : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHoldsK (qf c1) (F3.prog.out fd [])
  prod : USt → Stk → List E → Done → Stk → E → List E → E → E → ProdSum
  prod_vars : ∀ s c1 ch fd c2 t vals ρ l, (prod s c1 ch fd c2 t vals ρ l).vars = 2 * np + 1
  target : USt → Stk → List E → Done → Stk → E → List E → E → E → E
  batch_start : ∀ s c1 ch fd c2 t vals ρ l, F3.prog.ZerosVanish fd [] →
    (prod s c1 ch fd c2 t vals ρ l).T [] + target s c1 ch fd c2 t vals ρ l =
      powComb ((diffs s c1 ch fd c2 t vals).map fun d => powComb d ρ) l

/-! ## The states -/

section States

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) {np : ℕ}
  (I : UniIdsK3 F D F3 np) (BR : PairBatch np)

/-- **Flock's end**: its rounds completed. -/
def FlockDoneK3 (fd : Done) : Prop := DoneFits F3.prog.rounds fd

/-- **The state after the completed rounds `q`** (`q` nonempty). -/
def uniSK3 (s : USt) (q : Op Stk) : Prop :=
  ∃ c1, (rd q 0).1.1 = some c1 ∧
    if q.length ≤ F3.prog.rounds.length + 1 then
      I.MainOK s c1 (rd q 0).2 ∧
        DoneFits (F3.prog.rounds.take (q.length - 1)) (fdOf F3.prog.rounds.length q) ∧
          F3.S (I.qf c1) (fdOf F3.prog.rounds.length q)
    else ∃ c2, (rd q (F3.prog.rounds.length + 1)).1.1 = some c2 ∧
      FlockDoneK3 F3 (fdOf F3.prog.rounds.length q) ∧
      F3.prog.ZerosVanish (fdOf F3.prog.rounds.length q) [] ∧
      ((I.zb (fdOf F3.prog.rounds.length q)).eval ((rd q (F3.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      if q.length = F3.prog.rounds.length + 2 then
        ∃ vals, ∀ d ∈ I.diffs s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
          ((rd q (F3.prog.rounds.length + 1)).2.headD 0) vals, ∀ x ∈ d, x = 0
      else
        BR.St (I.prod s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
            ((rd q (F3.prog.rounds.length + 1)).2.headD 0)
            (rd q (F3.prog.rounds.length + 2)).1.2
            ((rd q (F3.prog.rounds.length + 2)).2.headD 0)
            ((rd q (F3.prog.rounds.length + 2)).2.getD 1 0))
          (I.target s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
            ((rd q (F3.prog.rounds.length + 1)).2.headD 0)
            (rd q (F3.prog.rounds.length + 2)).1.2
            ((rd q (F3.prog.rounds.length + 2)).2.headD 0)
            ((rd q (F3.prog.rounds.length + 2)).2.getD 1 0))
          (brOf F3.prog.rounds.length q))

/-- **The state before a round's challenges**: before round `0`, the relation of `C1`'s candidate; before `t`,
the identities as polynomials for `C2`'s candidate, Flock's end and its pending claim; else the state after the
rounds before. -/
def uniPreK3 (s : USt) (p : Op Stk) (m : Option Stk × List E) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ RelK F D s c
  else if p.length = F3.prog.rounds.length + 1 then
    ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHoldsK (I.qf c1) (F3.prog.out (fdOf F3.prog.rounds.length p) []) ∧
      F3.prog.ZerosVanish (fdOf F3.prog.rounds.length p) [] ∧
      FlockDoneK3 F3 (fdOf F3.prog.rounds.length p)
  else uniSK3 F3 I BR s p

/-- **The state after a round's challenges.** -/
def uniPostK3 (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E) : Prop :=
  uniSK3 F3 I BR s (p ++ [(m, c)])

/-- **The rounds' errors.** -/
noncomputable def uniErrK3 (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then I.errMain
  else if j ≤ F3.prog.rounds.length then F3.err (j - 1)
  else if j = F3.prog.rounds.length + 1 then
    ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j = F3.prog.rounds.length + 2 then
    ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j < F3.prog.rounds.length + 3 + np then BR.errPair
  else BR.errLast

end States

end UniKeccakSound
