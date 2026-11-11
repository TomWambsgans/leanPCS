-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The states are `PiopK3.lean`'s (`uniSK3`) read on
-- π1-rec4's transcript as π1-rec3's, with `C2`'s round and the values' round re-cut for the ring map drawn after
-- `C2`'s commitment; the round errors are `PiopSoundK3.lean`'s and Flock's bad family's (`Flock/Rec3.lean`).
import UniKeccakSound.PiopSoundK3
import UniKeccakSound.Flock.Instance
import UniKeccakSound.Rec4.Prog4
import UniKeccakSound.Rec4.Draws

/-!
# π1-rec4's PIOP, round by round

π1-rec4's rounds (`rec4Rounds κ nV np`) are π1-rec3's re-cut: round `0` draws `c, β, γ` and Flock's first challenge
`c'` together; Flock's rounds between are π1-rec3's; `C2`'s round draws `t` and the ring map's `f_0 … f_3` (its message
the slices, `C2`'s root, its answer); the values' round draws `ρ, λ, f_4, f_5`; the batch is π1-rec3's.

**The states** (`uniSK4`) are π1-rec3's (`uniSK3`, for Flock's phase on the Keccak-f block `kFlockSoundRec3 F hT κ` and
the identity model `I : UniIdsK3`) on the transcript read as π1-rec3's (`opT`: round `0` split in two, `C2`'s and the
values' rounds split into Flock's last round and π1-rec3's two), but after `C2`'s round, where no π1-rec3 state
exists (the map half drawn), the state (`c2St`) is: Flock's front done and its structured terminal zero, and either `t`
a root of the merge polynomial, or Flock's state with `f_0 … f_3` and the identities vanishing at `t` for some values
and some `f_4, f_5`. **The errors** (`uniErrK4`): round `0` the bus's and Flock's first round's; `C2`'s the identities'
Schwartz–Zippel and the bad sets of `f_0 … f_3`; the values' the combinations' and the bad sets of `f_4, f_5`; Flock's
and the batch's π1-rec3's.

The identity model's merge polynomial and identities are read off Flock's front only (`hzb`, `hpolys`: they read Flock's
point, which its last round, the map, does not change).
-/

namespace UniKeccakSound.Rec4

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open UniKeccakSound.KF (stateOfK kBad3 HitInK HitRoundK dBound3K)
open scoped ENNReal

/-! ## π1-rec4's opened transcript as π1-rec3's -/

section Op

variable (κ : ℕ)

/-- Round `0` as π1-rec3's: `c, β, γ`. -/
def r0Op (q : Op Stk) : (Option Stk × List E) × List E := ((rd q 0).1, (rd q 0).2.take 3)

/-- Flock's first round: `c'`. -/
def vr0Op (q : Op Stk) : (Option Stk × List E) × List E := ((none, []), [(rd q 0).2.getD 3 0])

/-- Flock's last round: the slices, the map. -/
def lastOp (q : Op Stk) : (Option Stk × List E) × List E :=
  ((none, (rd q (28 + κ)).1.2.take 64), (rd q (28 + κ)).2.drop 1 ++ (rd q (29 + κ)).2.drop 2)

/-- **π1-rec4's opened transcript as π1-rec3's.** -/
def opT (q : Op Stk) : Op Stk :=
  if q.length ≤ 28 + κ then [r0Op q, vr0Op q] ++ q.drop 1
  else [r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ) ++
    [lastOp κ q, (((rd q (28 + κ)).1.1, (rd q (28 + κ)).1.2.drop 64), (rd q (28 + κ)).2.take 1),
      ((rd q (29 + κ)).1, (rd q (29 + κ)).2.take 2)] ++ q.drop (30 + κ)

/-- **Flock's front in π1-rec4's opened transcript**: its first round, then the rounds `1 … 27 + κ`. -/
def vFrontO (q : Op Stk) : Done :=
  ((none, []), [(rd q 0).2.getD 3 0]) :: ((q.drop 1).take (27 + κ)).map fun x => ((none, x.1.2), x.2)

variable {κ}

theorem rd_opT_zero (q : Op Stk) : rd (opT κ q) 0 = r0Op q := by
  unfold opT
  split_ifs <;> rfl

theorem length_opT_le (q : Op Stk) (h1 : 1 ≤ q.length) (h2 : q.length ≤ 28 + κ) :
    (opT κ q).length = q.length + 1 := by
  rw [opT, ite_eq_left h2]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop]
  omega

theorem opT_append_le (p : Op Stk) (x : (Option Stk × List E) × List E) (h1 : 1 ≤ p.length)
    (h2 : p.length + 1 ≤ 28 + κ) : opT κ (p ++ [x]) = opT κ p ++ [x] := by
  have hr : rd (p ++ [x]) 0 = rd p 0 := rd_append_lt _ _ 0 (by omega)
  rw [opT, ite_eq_left (by simp; omega), opT, ite_eq_left (by omega)]
  simp only [r0Op, vr0Op, hr, List.drop_append_of_le_length h1, List.append_assoc]

theorem fdOf_opT_le (q : Op Stk) (_h1 : 1 ≤ q.length) (h2 : q.length ≤ 28 + κ) :
    fdOf (29 + κ) (opT κ q) = vFrontO κ q := by
  rw [opT, ite_eq_left h2, vFrontO, fdOf]
  have ht : (q.drop 1).take (27 + κ) = q.drop 1 := List.take_of_length_le (by simp; omega)
  have ht2 : (q.drop 1).take (28 + κ) = q.drop 1 := List.take_of_length_le (by simp; omega)
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, ht,
    show 29 + κ = (28 + κ) + 1 by omega, List.take_succ_cons, ht2, List.map_cons, vr0Op]

theorem length_vFrontO (q : Op Stk) (h : 28 + κ ≤ q.length) : (vFrontO κ q).length = 28 + κ := by
  simp only [vFrontO, List.length_cons, List.length_map, List.length_take, List.length_drop]
  omega

theorem length_opT_ge (q : Op Stk) (h : 30 + κ ≤ q.length) : (opT κ q).length = q.length + 2 := by
  rw [opT, ite_eq_right (by omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]
  omega

theorem rd_opT_c2 (q : Op Stk) (h : 30 + κ ≤ q.length) :
    rd (opT κ q) (30 + κ) = (((rd q (28 + κ)).1.1, (rd q (28 + κ)).1.2.drop 64), (rd q (28 + κ)).2.take 1) := by
  rw [opT, ite_eq_right (by omega)]
  have hl : ([r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ)).length = 29 + κ := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]
    omega
  unfold rd
  rw [List.getD_eq_getElem?_getD, List.append_assoc ([r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ)),
    List.getElem?_append_right (by omega), hl, show 30 + κ - (29 + κ) = 1 by omega]
  rfl

theorem rd_opT_v (q : Op Stk) (h : 30 + κ ≤ q.length) :
    rd (opT κ q) (31 + κ) = ((rd q (29 + κ)).1, (rd q (29 + κ)).2.take 2) := by
  rw [opT, ite_eq_right (by omega)]
  have hl : ([r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ)).length = 29 + κ := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]
    omega
  unfold rd
  rw [List.getD_eq_getElem?_getD, List.append_assoc ([r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ)),
    List.getElem?_append_right (by omega), hl, show 31 + κ - (29 + κ) = 2 by omega]
  rfl

theorem fdOf_opT_ge (q : Op Stk) (h : 30 + κ ≤ q.length) :
    fdOf (29 + κ) (opT κ q) = vFrontO κ q ++ [((none, (lastOp κ q).1.2), (lastOp κ q).2)] := by
  have hl : ((q.drop 1).take (27 + κ)).length = 27 + κ := by simp; omega
  rw [opT, ite_eq_right (by omega), vFrontO, fdOf]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.append_assoc,
    show 29 + κ = (28 + κ) + 1 by omega, List.take_succ_cons, List.map_cons, vr0Op, List.take_append, hl,
    List.take_of_length_le (show ((q.drop 1).take (27 + κ)).length ≤ 28 + κ by omega),
    show 28 + κ - (27 + κ) = 1 by omega, List.take_succ_cons, List.take_zero, List.map_append, List.map_cons,
    List.map_nil]

theorem brOf_opT (q : Op Stk) (h : 30 + κ ≤ q.length) : brOf (29 + κ) (opT κ q) = brOf (27 + κ) q := by
  rw [opT, ite_eq_right (by omega), brOf, brOf]
  have hl : ([r0Op q, vr0Op q] ++ (q.drop 1).take (27 + κ) ++
      [lastOp κ q, (((rd q (28 + κ)).1.1, (rd q (28 + κ)).1.2.drop 64), (rd q (28 + κ)).2.take 1),
        ((rd q (29 + κ)).1, (rd q (29 + κ)).2.take 2)]).length = 29 + κ + 3 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]
    omega
  rw [List.drop_left' hl, show 27 + κ + 3 = 30 + κ by omega]

theorem opT_append_ge (p : Op Stk) (x : (Option Stk × List E) × List E) (h : 30 + κ ≤ p.length) :
    opT κ (p ++ [x]) = opT κ p ++ [x] := by
  have hr : ∀ j, j < p.length → rd (p ++ [x]) j = rd p j := fun j hj => rd_append_lt _ _ j hj
  rw [opT, ite_eq_right (by simp; omega), opT, ite_eq_right (by omega)]
  simp only [r0Op, vr0Op, lastOp, hr 0 (by omega), hr (28 + κ) (by omega), hr (29 + κ) (by omega),
    List.drop_append_of_le_length (by omega : 1 ≤ p.length),
    List.drop_append_of_le_length (by omega : 30 + κ ≤ p.length),
    List.take_append_of_le_length (by simp; omega : 27 + κ ≤ (p.drop 1).length), List.append_assoc]

end Op

end UniKeccakSound.Rec4
