-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The verifier (`Flock.verifyWalkedFs` at `.rec3`) is
-- `formal/UniStatement`'s `Rec.lean`, transcribed from `crates/leanvm/statement/src/flock_min.rs` (`verify_walked`).
import FlockSoundUni.Link
import UniStatement.Rec

/-!
# π1-rec3's Flock front as a chain program, and its code-level link

`Flock.verifyWalkedFs F (14 + κ) flockMain .rec3` (skip `3`, the slices sent, the ring map in tower order, the
zerocheck's coordinates after the seven fixed ones the squares of one challenge, the lincheck's terminal walked) is
the chain program `flockProg3 κ` (no root, no tail), whose `23 + κ` rounds are the main line's but the first:

* `⟨false, 0, 0⟩`: **one** challenge `c`; the zerocheck point's `4 + κ` sampled coordinates are `squares c (4 + κ)`;
* `⟨false, 8, 0⟩`, `11 + κ` zerocheck rounds, `v_a, v_b` then `α`, `8` lincheck rounds: the main line's;
* `⟨false, 64, 5⟩`: the `64` slices, **the walk's zero** (`walkOf`: `walkedTerminal … + r_lc`, required before the
  ring map's challenges), then the ring map's six challenges.

The result (`outOf3`) is the code's, the point and the ring switch's end. **The main line's reading** of a
transcript is `outOf κ (expandFd κ d)`: the first round's challenge written out as its squares (`expandFd`), read by
the main line's `outOf` (point, end, pending); its point and end are `outOf3`'s (`outOf_expandFd`). **`flock_link3`**
is the equation of channel programs, for every lawful monad and permutation.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

/-- **π1-rec3's Flock rounds before the slices**: the squares' one challenge, the coset values, the zerocheck's
rounds, `v_a, v_b`, the lincheck's rounds. -/
def flockRounds3Pre (κ : ℕ) : List Compose.RoundSpec :=
  [⟨false, 0, 0⟩, ⟨false, 8, 0⟩] ++ List.replicate (11 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++
    List.replicate 8 ⟨false, 2, 0⟩

/-- **π1-rec3's Flock rounds**, `κ` the table's batch bits. -/
def flockRounds3 (κ : ℕ) : List Compose.RoundSpec := flockRounds3Pre κ ++ [⟨false, 64, 5⟩]

theorem length_flockRounds3Pre (κ : ℕ) : (flockRounds3Pre κ).length = 22 + κ := by
  simp only [flockRounds3Pre, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem length_flockRounds3 (κ : ℕ) : (flockRounds3 κ).length = 23 + κ := by
  rw [flockRounds3, List.length_append, length_flockRounds3Pre, List.length_singleton]
  omega

theorem length_squares : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by simp [squares, length_squares (c * c) n]

/-! ## The main line's reading -/

/-- **The transcript as the main line's**: the first round's challenge written out as its `4 + κ` squares. -/
def expandFd (κ : ℕ) : Done → Done
  | [] => []
  | (m, c) :: d => (m, squares (c.headD 0) (4 + κ)) :: d

theorem rd_expandFd_succ (κ : ℕ) (d : Done) (a : ℕ) : rd (expandFd κ d) (a + 1) = rd d (a + 1) := by
  cases d <;> rfl

theorem drop_expandFd (κ : ℕ) (d : Done) (a : ℕ) : (expandFd κ d).drop (a + 1) = d.drop (a + 1) := by
  cases d <;> rfl

theorem rd_expandFd_zero (κ : ℕ) (d : Done) (h : d ≠ []) :
    (rd (expandFd κ d) 0).2 = squares ((rd d 0).2.headD 0) (4 + κ) := by
  cases d with
  | nil => exact absurd rfl h
  | cons x d => rfl

/-! ## The link -/

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem runRounds_append {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (a b : List Compose.RoundSpec) (done : Done),
      P.runRounds F (a ++ b) done = (P.runRounds F a done >>= fun d ↦ P.runRounds F b d)
  | [], b, done => by simp [ChainProg.runRounds]
  | s :: a, b, done => by
    cases h : s.root <;> simp [ChainProg.runRounds, h, bind_assoc, runRounds_append P F a b]

/-- **A chain program's rounds without roots, before its first zero, are their reads and draws.** -/
theorem runRounds_eq_of {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) (n : ℕ)
    (hz : ∀ done msg, done.length < n → P.zeros done msg = []) :
    ∀ (rs : List Compose.RoundSpec), (∀ s ∈ rs, s.root = false) → ∀ done : Done, done.length + rs.length ≤ n →
      P.runRounds F rs done = (fun d ↦ done ++ d) <$> readRounds F rs
  | [], _, done, _ => by simp [ChainProg.runRounds, readRounds]
  | s :: rs, hr, done, hl => by
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    have hlt : done.length < n := by simp at hl; omega
    simp only [ChainProg.runRounds, hs, Bool.false_eq_true, ite_false, pure_bind, hz done _ hlt,
      ChainProg.requireZeros, readRounds, readRound, bind_assoc, map_bind]
    congr 1
    funext vals
    congr 1
    funext chs
    rw [runRounds_eq_of P F n hz rs (fun s hs ↦ hr s (List.mem_cons_of_mem _ hs)) _
      (by simp at hl ⊢; omega)]
    simp

end Link

end FlockSound.Uni
