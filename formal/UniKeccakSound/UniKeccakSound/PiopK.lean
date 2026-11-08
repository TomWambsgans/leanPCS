-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The round-by-round form is `UniSound.Piop`'s
-- (`formal/UniSound/UniSound/Piop.lean`), for the Keccak verifier's main line.
import UniSound.Piop
import UniKeccakSound.FlockInterfaceK

/-!
# The Keccak verifier's PIOP (main line), round by round: identity model, states, errors

The rounds are the main line's (`UniSound.uniRounds`):

| round | message | challenges |
|---|---|---|
| `0` | `C1`'s root | `α ∈ E^4`, `β`, `γ` |
| `1 … nF` | Flock's rounds on the Keccak-f block (`KFlockSound.prog.rounds`, the structured terminal's zero) | Flock's |
| `nF + 1` | `C2`'s root | `t` |
| `nF + 2` | the `nV` values at `t` | `ρ`, `λ` |
| `nF + 3 …` | the batching sumcheck's `V` rounds, `c0, c2` each | one each |

then the three stacks' values at the batch's point (the tail) and three openings (`C1`, `C2`, the setup).

**The identity model** (`UniIdsK F D Fl`) is `UniSound.UniIds` for the Keccak VM: the relation before round `0` is
`KvHolds F` of `C1`'s Keccak VM stack (`RelK`: `kvStack`), Flock's predicate is `KFlockHolds F κ` on `q_flock` of
`2^(11 + κ)` cells, there are three commitments and **no pending matrices' term** (the batch is
`Σ_{k<3} λ^k W_k C_k`): the Keccak verifier checks the Flock lincheck's terminal itself (the structured terminal).

**The states** (`uniSK`, `uniPreK`, `uniPostK`) are the main line's (`uniS`), but from `C2`'s round on Flock's
transcript has its **zeros vanishing** (`FlockDoneZ`: the structured terminal, a function of Flock's transcript,
given at the end by the verifier's checks), which Flock's `finish` needs.
-/

namespace UniKeccakSound

open LeanVM.Parameters LeanVM.Protocol UniStatement UniSound UniKeccak Finset
open scoped ENNReal

/-- **The Keccak VM's relation** of a `C1` candidate: its Keccak VM stack (`kvStack`) at the row counts satisfies
`KvHolds F` for the public input. -/
def RelK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (s : USt) (c : Stk) : Prop :=
  D.Relation F s.2 s.1 (kvStack D.prog (D.sizes s.2) D.shape c)

/-- **The identity model of the Keccak verifier's main line**: `UniSound.UniIds` for the Keccak VM's relation, Flock
on the Keccak-f block (`Fl`, `q_flock` of `2^(11 + κ)` cells), three commitments, no pending term. The fields are
`UniIds`' (see `UniSound/Piop.lean`); `diffs_flock` gives the ring claim `FlockEndHoldsK`. -/
structure UniIdsK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) where
  nV : ℕ
  V : ℕ
  qf : Stk → Column (KeccakVm.kWords + κ)
  MainHolds : USt → Stk → Prop
  rel_of : ∀ s c, MainHolds s c → KFlockHolds F κ (qf c) → RelK F D s c
  MainOK : USt → Stk → List E → Prop
  errMain : ℝ≥0∞
  mainSound : ∀ s c, Pr{let ch ← Compose.draws E 6}[¬ MainHolds s c ∧ MainOK s c ch] ≤ errMain
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
    FlockEndHoldsK (qf c1) (Fl.prog.out fd [])
  prod : USt → Stk → List E → Done → Stk → E → List E → E → E → ProdSum
  prod_vars : ∀ s c1 ch fd c2 t vals ρ l, (prod s c1 ch fd c2 t vals ρ l).vars = V
  target : USt → Stk → List E → Done → Stk → E → List E → E → E → E
  batch_start : ∀ s c1 ch fd c2 t vals ρ l,
    (prod s c1 ch fd c2 t vals ρ l).T [] + target s c1 ch fd c2 t vals ρ l =
      powComb ((diffs s c1 ch fd c2 t vals).map fun d => powComb d ρ) l

/-! ## The states -/

section States

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)
  (I : UniIdsK F D Fl)

/-- **Flock's end**: its rounds completed, its zeros (the structured terminal) vanishing. -/
def FlockDoneZ (fd : Done) : Prop := DoneFits Fl.prog.rounds fd ∧ Fl.prog.ZerosVanish fd []

/-- **The state after the completed rounds `q`** (`q` nonempty): `uniS` with `FlockDoneZ` from `C2` on. -/
def uniSK (s : USt) (q : Op Stk) : Prop :=
  ∃ c1, (rd q 0).1.1 = some c1 ∧
    if q.length ≤ Fl.prog.rounds.length + 1 then
      I.MainOK s c1 (rd q 0).2 ∧
        DoneFits (Fl.prog.rounds.take (q.length - 1)) (fdOf Fl.prog.rounds.length q) ∧
          Fl.S (I.qf c1) (fdOf Fl.prog.rounds.length q)
    else ∃ c2, (rd q (Fl.prog.rounds.length + 1)).1.1 = some c2 ∧
      FlockDoneZ Fl (fdOf Fl.prog.rounds.length q) ∧
      ((I.zb (fdOf Fl.prog.rounds.length q)).eval ((rd q (Fl.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      if q.length = Fl.prog.rounds.length + 2 then
        ∃ vals, ∀ d ∈ I.diffs s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
          ((rd q (Fl.prog.rounds.length + 1)).2.headD 0) vals, ∀ x ∈ d, x = 0
      else
        SumState (I.prod s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
            ((rd q (Fl.prog.rounds.length + 1)).2.headD 0)
            (rd q (Fl.prog.rounds.length + 2)).1.2
            ((rd q (Fl.prog.rounds.length + 2)).2.headD 0)
            ((rd q (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle
          (I.target s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
            ((rd q (Fl.prog.rounds.length + 1)).2.headD 0)
            (rd q (Fl.prog.rounds.length + 2)).1.2
            ((rd q (Fl.prog.rounds.length + 2)).2.headD 0)
            ((rd q (Fl.prog.rounds.length + 2)).2.getD 1 0))
          (brOf Fl.prog.rounds.length q))

/-- **The state before a round's challenges**: before round `0`, the Keccak VM's relation of `C1`'s candidate;
before `t`, the identities as polynomials for `C2`'s candidate, Flock's ring claim and its end; else the state after
the rounds before. -/
def uniPreK (s : USt) (p : Op Stk) (m : Option Stk × List E) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ RelK F D s c
  else if p.length = Fl.prog.rounds.length + 1 then
    ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHoldsK (I.qf c1) (Fl.prog.out (fdOf Fl.prog.rounds.length p) []) ∧
      FlockDoneZ Fl (fdOf Fl.prog.rounds.length p)
  else uniSK Fl I s p

/-- **The state after a round's challenges.** -/
def uniPostK (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E) : Prop :=
  uniSK Fl I s (p ++ [(m, c)])

/-- **The rounds' errors**: `UniSound.uniErr`'s, the two combinations over at most three commitments. -/
noncomputable def uniErrK (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then I.errMain
  else if j ≤ Fl.prog.rounds.length then Fl.err (j - 1)
  else if j = Fl.prog.rounds.length + 1 then
    ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j = Fl.prog.rounds.length + 2 then
    ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

end States

end UniKeccakSound
