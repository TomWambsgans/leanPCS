-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniStatement`'s `reduceWithFs`
-- at `.rec3` with the walk (`Rec.lean`); the proof follows `CodeLink.lean`'s (the main line's), Flock's phase cited
-- through `FlockSound3.link`.
import UniSound.Rec3.CodeBatch3

/-!
# The code-level link at π1-rec3: `reduceWithFs … .rec3 true` is a chain program (`UniCode3`)

**`uniCode3 D F3 hκ np hV : UniCode3 D F3 valsCount np`** (and `uniCode3At` at any `nV = valsCount`): after the row
counts, `reduceWithFs` at the deployment's shape, π1-rec3 (`.rec3`, the walk, point claims) is the chain program
`main3Prog` on `rec3Rounds F3.prog.rounds valsCount np`, with a tail of three, up to `obsOf3`, for every deployment
whose batch has `2 np + 1` variables (`hV`). Its rounds:

* `C1`'s root and **three** challenges `c, β, γ` (`drawRun .rec3 4` is one draw and `squares c 4`);
* Flock's rounds (`F3.link`: `Flock.verifyWalkedFs` is Flock's chain program; its zeros, the walk's, are the main
  program's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`; the `valsCount` values at `t` (as the main line's) and `ρ, λ`;
* the batch's `np` pair rounds (`8` scalars, one draw) and its last plain round (`2` scalars, one draw): **the chain
  draws `x`, the program reads `narrowE x`** (`batchPureW narrowE`), where the verifier draws `narrowE x` itself
  (`sampleNarrow`); the two agree up to the channel's record of the challenges (`chEq_readRoundsN`), which `obsOf3`
  does not keep;

then the three stacks' values, the terminal zero `sum + last` collected (`batchPureW`), and the result (`main3Out`:
no matrices' claim). **`uniCode3_roots`**: the result names the roots of rounds `0` and `nF + 1` (`rfl`), the form
the Fiat–Shamir layer's `UniOutRoots` takes.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The program -/

/-- **Flock's claim at π1-rec3** (step 7: the walked Flock's point and end), as the main line's `flockClaim` reads
it (no pending reduction). -/
def flockClaim3 (rels : Array Relation) (fl : List E × Flock.End) :
    Array Relation × List Relation × Option (List E) :=
  flockClaim rels (fl.1, some fl.2, default)

/-- **The zeros after a round**: the Flock program's in its rounds, its tail zeros in `C2`'s round. -/
def zeros3 {β : Type} (Pf : ChainProg β) (done : Done) (msg : UMsg) : List E :=
  if 1 ≤ done.length ∧ done.length ≤ Pf.rounds.length then Pf.zeros (done.drop 1) msg
  else if done.length = Pf.rounds.length + 1 then Pf.tailZeros (done.drop 1) []
  else []

/-! ## The zeros -/

section Zeros

variable {β : Type} (Pf : ChainProg β)

theorem zeros3_nil (msg : UMsg) : zeros3 Pf [] msg = [] := by
  simp [zeros3]

theorem zeros3_flock (x : UMsg × List E) (e : Done) (msg : UMsg) (h : e.length < Pf.rounds.length) :
    zeros3 Pf ([] ++ [x] ++ e) msg = Pf.zeros e msg := by
  simp only [zeros3, List.nil_append, List.length_cons, List.singleton_append]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  simp

theorem zeros3_c2 (x : UMsg × List E) (G : Done) (hG : G.length = Pf.rounds.length) (msg : UMsg) :
    zeros3 Pf ([x] ++ G) msg = Pf.tailZeros G [] := by
  have h1 : ([x] ++ G).length = Pf.rounds.length + 1 := by simp [hG]
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_left h1]
  simp

theorem zeros3_vals (x x2 : UMsg × List E) (G : Done) (hG : G.length = Pf.rounds.length) (msg : UMsg) :
    zeros3 Pf ([x] ++ G ++ [x2]) msg = [] := by
  have h1 : ([x] ++ G ++ [x2]).length = Pf.rounds.length + 2 := by simp [hG]
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem zeros3_batch (d : Done) (msg : UMsg) (h : Pf.rounds.length + 3 ≤ d.length) : zeros3 Pf d msg = [] := by
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end Zeros

/-! ## The link -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem samples_three (F : KeccakState → m KeccakState) : samples F 3 = (do
    let a ← sample F
    let b ← sample F
    let c ← sample F
    pure [a, b, c]) := by
  simp [samples_eq, FlockSound.Uni.repeatM]

/-- **`bind` through a reading, observationally**: `ChEq.bind_map`, then `obsOf3`. -/
theorem ObsEq3.bind_chEq {α β γ : Type} {x : ChanM m β} {y : ChanM m γ} {φ : γ → β} {f : β → ChanM m α}
    {g : γ → ChanM m α} (hx : ChEq x (φ <$> y)) (hf : ∀ b, ChEq (f (φ b)) (g b)) (hff : ∀ b, ChObl (f b))
    (hgg : ∀ b, ChObl (g b)) (hy : ChObl y) : ObsEq3 (x >>= f) (y >>= g) :=
  (ChEq.bind_map hx hf hff hgg hy).obsEq3

/-- **The batch's narrow rounds are the chain's**, the records narrowed. -/
theorem chEq_batchRounds (F : KeccakState → m KeccakState) (np : ℕ) :
    ChEq (readRoundsN F (List.replicate np 8 ++ [2]))
      ((List.map narrowRec) <$> readRounds F (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) := by
  have e : (List.replicate np 8 ++ [2]).map (fun nv => (⟨false, nv, 0⟩ : Compose.RoundSpec)) =
      List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩] := by
    simp [List.map_replicate]
  have h := chEq_readRoundsN F (List.replicate np 8 ++ [2])
  rwa [e] at h

end Monad

/-! ## The code-level link -/

end UniSound

