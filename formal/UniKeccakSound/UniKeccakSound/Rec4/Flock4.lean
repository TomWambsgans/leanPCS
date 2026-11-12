-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The verifier (`UniKeccak.verifyWalkedK4`) is
-- `formal/UniKeccak`'s (`Verifier4.lean`, transcribed from `crates/leanvm/statement/src/flock_min.rs`'s
-- `verify_walked` with `eq_first`); the proof follows `Flock/Link.lean`'s (`kflock_link3`).
import UniKeccakSound.Rec4.Prog4

/-!
# Flock's front at π1-rec4 as π1-rec3's Flock rounds

`UniKeccak.verifyWalkedK4 F (17 + κ) keccakRec4 c` (the zerocheck's coordinates after the seven fixed ones the
squares of the caller's `c`, the slices sent, the structured terminal required, no ring map drawn) reads the rounds
`kRoundsMid κ` (π1-rec3's Flock rounds without its first and its last), the `64` slices, and requires the zero of
π1-rec3's Flock program on the transcript whose first round is `((none, []), [c])` (`kflock_link4`): its result is
π1-rec3's Flock result's point (`KF.kOutT`, whose point does not read the last round: `kOutT_rec3_append`).
-/

namespace UniKeccakSound.KF

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-- **π1-rec3's Flock result on a transcript of `28 + κ` rounds and the slices' round**: the point does not read the
last round's challenges, the end is the ring switch's at them. -/
theorem kOutT_rec3_append (κ : ℕ) (d : Done) (hd : d.length = 28 + κ) (s mp : List E) :
    kOutT κ (sampRec3 κ) (d ++ [((none, s), mp)]) =
      ((kOutT κ (sampRec3 κ) (d ++ [((none, s), [])])).1, .ring mp (Flock.towerTarget s mp)) := by
  have e0 : ∀ x : UMsg × List E,
      sampRec3 κ (d ++ [x]) = squares ((FlockSound.Uni.rd d 0).2.headD 0) (7 + κ) := fun x => by
    rw [sampRec3, FlockSound.Uni.rd_append_left (by omega)]
  have e1 : ∀ x : UMsg × List E, FlockSound.Uni.rd (d ++ [x]) 1 = FlockSound.Uni.rd d 1 := fun x =>
    FlockSound.Uni.rd_append_left (by omega)
  have e2 : ∀ x : UMsg × List E, ((d ++ [x]).drop 2).take (14 + κ) = (d.drop 2).take (14 + κ) := fun x => by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  have e3 : ∀ x : UMsg × List E, FlockSound.Uni.rd ((d ++ [x]).drop (16 + κ)) 0 =
      FlockSound.Uni.rd (d.drop (16 + κ)) 0 := fun x => by
    rw [FlockSound.Uni.rd_drop, FlockSound.Uni.rd_drop, FlockSound.Uni.rd_append_left (by omega)]
  have e4 : ∀ x : UMsg × List E, ((d ++ [x]).drop (17 + κ)).take 11 = (d.drop (17 + κ)).take 11 := fun x => by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  have e5 : ∀ x : UMsg × List E, FlockSound.Uni.rd ((d ++ [x]).drop (28 + κ)) 0 = x := fun x => by
    rw [List.drop_left' hd]
    rfl
  simp only [kOutT, kOutOf, e0, e1, e2, e3, e4, e5]

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `kflock_link4` with the rounds' records as read. -/
theorem kflock_link4_raw (κ : ℕ) (F : KeccakState → m KeccakState) (c : E) :
    UniKeccak.verifyWalkedK4 F (keccakR1csLogSize + κ) UniKeccak.keccakRec4 c = (do
      let d ← readRounds F (kRoundsMid κ)
      let vals ← nextScalars (m := m) 64
      ChainProg.requireZeros [kTerm κ (sampRec3 κ) (((none, []), [c]) :: d) vals]
      pure ((kOutT κ (sampRec3 κ) ((((none, []), [c]) :: d) ++ [((none, vals), [])])).1, vals)) := by
  have h7 : keccakR1csLogSize + κ - 3 - Flock.nFixed = 7 + κ := by
    simp only [keccakR1csLogSize, Flock.nFixed]; omega
  have h14 : Flock.fixedChallenges.length + (7 + κ) = 14 + κ := by
    rw [length_fixedChallenges]; omega
  have h11 : UniKeccak.lincheckRoundsK = 11 := rfl
  have hp : Flock.packing - 3 = 3 := rfl
  have hk : Flock.kBits = 64 := rfl
  have h23 : (2 : ℕ) ^ 3 = 8 := rfl
  have h24 : (2 : ℕ) ^ (3 + 1) = 16 := rfl
  simp only [UniKeccak.verifyWalkedK4, UniKeccak.frontK4, Flock.zerocheckFirst, UniKeccak.keccakRec4, h7,
    show (3 : ℕ) > 0 from by decide, ite_true, h11, hp, hk, h23, h24]
  simp only [sumcheck_eq, sumcheckR_eq, List.length_map, List.length_append, length_squares, h14,
    List.length_replicate, bind_map_left, bind_assoc, pure_bind]
  conv_rhs => simp only [kRoundsMid, readRounds_append, readRounds, readRound, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append, bind_assoc, pure_bind, map_bind,
    bind_map_left, map_pure, UniSound.nextScalars_two, Nat.zero_add, FlockSound.Uni.samples_one, ChainProg.requireZeros]
  rw [readRounds_fit_replicate F (14 + κ), readRounds_fit_replicate F 11]
  simp only [bind_map_left, kOutT_shape, kTerm_shape, sampRec3_cons, length_fitN, List.headD_cons,
    List.getD_cons_zero, List.getD_cons_succ, kOutOf, kTermOf, Option.getD_some]

/-- **Flock's front at π1-rec4** (`verifyWalkedK4` at `17 + κ` variables, `KECCAK_REC4`, the zerocheck's first
coordinate `c` given): the rounds `kRoundsMid κ`, the `64` slices, the structured terminal's zero of π1-rec3's Flock
program on the transcript whose first round is `((none, []), [c])`; the slices' point is that program's, for every
lawful monad and permutation. -/
theorem kflock_link4 (κ : ℕ) (F : KeccakState → m KeccakState) (c : E) :
    UniKeccak.verifyWalkedK4 F (keccakR1csLogSize + κ) UniKeccak.keccakRec4 c = (do
      let d ← readRounds F (kRoundsMid κ)
      let vals ← nextScalars (m := m) 64
      ChainProg.requireZeros [kTerm κ (sampRec3 κ) (((none, []), [c]) :: fitN (27 + κ) d) vals]
      pure ((kOutT κ (sampRec3 κ) ((((none, []), [c]) :: fitN (27 + κ) d) ++ [((none, vals), [])])).1, vals)) := by
  rw [kflock_link4_raw]
  conv_lhs => rw [readRounds_fit F (kRoundsMid κ)]
  simp only [bind_map_left, length_kRoundsMid]

end Link

end UniKeccakSound.KF
