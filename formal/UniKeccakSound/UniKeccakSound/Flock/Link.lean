-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The verifier (`UniKeccak.verifyWalkedK`) is
-- `formal/UniKeccak`'s, transcribed from `crates/leanvm_flock_gas/src/flock_min.rs` (`verify_walked_with::<S, Keccak>`);
-- the proof follows `formal/FlockSound/FlockSoundUni/{Link,Rec3Link}.lean` (BLAKE2s's).
import FlockSoundUni.Rec3Link
import UniKeccakSound.FlockInterfaceK

/-!
# The Keccak verifier's Flock phase as a chain program, and its code-level link

`UniKeccak.verifyWalkedK F (17 + κ) v` (skip `3`, the slices sent, the structured terminal, the ring map in tower
order) is the chain program `kProgWith κ r0 samp` (no root, no tail), whose `29 + κ` rounds are:

* `r0`: the zerocheck point's sampled coordinates: at the main line `⟨false, 0, 6 + κ⟩` (`7 + κ` challenges), at
  π1-rec3 `⟨false, 0, 0⟩` (one challenge `c`, the coordinates `squares c (7 + κ)`); `samp` reads them off the round;
* `⟨false, 8, 0⟩`: the skip's `8` coset values, then `z`;
* `14 + κ` × `⟨false, 2, 0⟩`: the zerocheck's rounds;
* `⟨false, 2, 0⟩`: `v_a`, `v_b`, then `α`;
* `11` × `⟨false, 2, 0⟩`: the lincheck's rounds (`17 − 6`);
* `⟨false, 64, 5⟩`: the `64` slices, **the structured terminal's zero** (`kTerm`: `structuredTerminal … + r_lc`,
  required before the ring map's challenges), then the ring map's six challenges.

The result (`kOutT`) is the code's: the slices' point and the ring switch's end. **`kflock_link`** (main line) and
**`kflock_link3`** (π1-rec3) are the equations of channel programs, for every lawful monad and permutation.
-/

namespace UniKeccakSound.KF

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The rounds -/

/-- **The Keccak verifier's Flock rounds before the slices**, the first `r0`. -/
def kRoundsPre (κ : ℕ) (r0 : Compose.RoundSpec) : List Compose.RoundSpec :=
  [r0, ⟨false, 8, 0⟩] ++ List.replicate (14 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++
    List.replicate 11 ⟨false, 2, 0⟩

/-- **The Keccak verifier's Flock rounds.** -/
def kRounds (κ : ℕ) (r0 : Compose.RoundSpec) : List Compose.RoundSpec := kRoundsPre κ r0 ++ [⟨false, 64, 5⟩]

/-- The main line's first round: the `7 + κ` sampled coordinates. -/
abbrev r0Main (κ : ℕ) : Compose.RoundSpec := ⟨false, 0, 6 + κ⟩

/-- π1-rec3's first round: one challenge. -/
abbrev r0Rec3 : Compose.RoundSpec := ⟨false, 0, 0⟩

theorem length_kRoundsPre (κ : ℕ) (r0 : Compose.RoundSpec) : (kRoundsPre κ r0).length = 28 + κ := by
  simp only [kRoundsPre, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem length_kRounds (κ : ℕ) (r0 : Compose.RoundSpec) : (kRounds κ r0).length = 29 + κ := by
  rw [kRounds, List.length_append, length_kRoundsPre, List.length_singleton]
  omega

/-! ## The zero and the result from the rounds' reads -/

/-- **The structured terminal's zero from the rounds' reads**: the zerocheck's and the lincheck's sumchecks decoded,
then `structuredTerminal` at the front's skip point, row point (`3` coordinates), lincheck points (`11`), `α` and
slices, plus `r_lc`. -/
def kTermOf (sampled coset : List E) (z : E) (zc : Done) (vA vB alpha : E) (lc : Done) (slices : List E) : E :=
  let zr := decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
    ((Flock.fixedChallenges ++ sampled).map some) zc
  let lr := decodeSC (vA + alpha * vB + epow alpha 2 * (zr.2 + vA * vB) + epow alpha 3)
    (List.replicate 11 none) lc
  UniKeccak.structuredTerminal (some z) (zr.1.take 3) ((zr.1.drop 3).take 11) lr.1.reverse slices alpha + lr.2

/-- **The code's result from the rounds' reads**: the slices' point (the lincheck's challenges reversed, then the
instance coordinates) and the ring switch's end in tower order. -/
def kOutOf (sampled coset : List E) (z : E) (zc : Done) (vA vB alpha : E) (lc : Done) (slices map : List E) :
    List E × Flock.End :=
  let zr := decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
    ((Flock.fixedChallenges ++ sampled).map some) zc
  let lr := decodeSC (vA + alpha * vB + epow alpha 2 * (zr.2 + vA * vB) + epow alpha 3)
    (List.replicate 11 none) lc
  (lr.1.reverse ++ (zr.1.drop 3).drop 11, .ring map (Flock.towerTarget slices map))

/-- **The zero from the transcript** before the slices' round (its sampled coordinates read by `samp`), and the
slices. -/
def kTerm (κ : ℕ) (samp : Done → List E) (d : Done) (slices : List E) : E :=
  kTermOf (samp d) (rd d 1).1.2 ((rd d 1).2.headD 0) ((d.drop 2).take (14 + κ))
    ((rd (d.drop (16 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (16 + κ)) 0).1.2.getD 1 0)
    ((rd (d.drop (16 + κ)) 0).2.headD 0) ((d.drop (17 + κ)).take 11) slices

/-- **The result from the transcript.** -/
def kOutT (κ : ℕ) (samp : Done → List E) (d : Done) : List E × Flock.End :=
  kOutOf (samp d) (rd d 1).1.2 ((rd d 1).2.headD 0) ((d.drop 2).take (14 + κ))
    ((rd (d.drop (16 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (16 + κ)) 0).1.2.getD 1 0)
    ((rd (d.drop (16 + κ)) 0).2.headD 0) ((d.drop (17 + κ)).take 11) (rd (d.drop (28 + κ)) 0).1.2
    (rd (d.drop (28 + κ)) 0).2

/-- **The Keccak verifier's Flock phase as a chain program**, its first round `r0`, its sampled coordinates read by
`samp`: its one zero the structured terminal's, in the slices' round. -/
def kProgWith (κ : ℕ) (r0 : Compose.RoundSpec) (samp : Done → List E) : ChainProg (List E × Flock.End) where
  rounds := kRounds κ r0
  zeros d msg := if d.length = 28 + κ then [kTerm κ samp d msg.2] else []
  tail := 0
  tailZeros _ _ := []
  out d _ := kOutT κ samp d

/-- The main line's sampled coordinates: round `0`'s challenges. -/
def sampMain (d : Done) : List E := (rd d 0).2

/-- π1-rec3's sampled coordinates: the `7 + κ` squares of round `0`'s challenge. -/
def sampRec3 (κ : ℕ) (d : Done) : List E := squares ((rd d 0).2.headD 0) (7 + κ)

/-- **The main line's Flock program** (`KECCAK_MAIN`). -/
def kProg (κ : ℕ) : ChainProg (List E × Flock.End) := kProgWith κ (r0Main κ) sampMain

/-- **π1-rec3's Flock program** (`KECCAK_REC3`). -/
def kProg3 (κ : ℕ) : ChainProg (List E × Flock.End) := kProgWith κ r0Rec3 (sampRec3 κ)

theorem kProgWith_root (κ : ℕ) (r0 : Compose.RoundSpec) (h0 : r0.root = false) (samp : Done → List E) :
    ∀ s ∈ (kProgWith κ r0 samp).rounds, s.root = false := by
  intro s hs
  simp only [kProgWith, kRounds, kRoundsPre, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((((h | h) | ⟨-, h⟩) | h) | ⟨-, h⟩) | h <;> subst h <;> first | exact h0 | rfl

theorem kProgWith_tail (κ : ℕ) (r0 : Compose.RoundSpec) (samp : Done → List E) :
    (kProgWith κ r0 samp).tail = 0 := rfl

/-! ## The link -/

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The program runs its reads before the slices, the slices, the structured terminal's zero, the ring map's
draws**, then reads off the result. -/
theorem kProgWith_run (κ : ℕ) (r0 : Compose.RoundSpec) (h0 : r0.root = false) (samp : Done → List E)
    (F : KeccakState → m KeccakState) :
    (kProgWith κ r0 samp).run F = (do
      let d ← readRounds F (kRoundsPre κ r0)
      let vals ← nextScalars (m := m) 64
      requireZero (m := m) (kTerm κ samp d vals)
      let chs ← samples F 6
      pure (kOutT κ samp (d ++ [((none, vals), chs)]))) := by
  have hpre := runRounds_eq_of (kProgWith κ r0 samp) F (28 + κ)
    (fun done msg h ↦ by simp only [kProgWith]; rw [ite_eq_right (by omega)]) (kRoundsPre κ r0)
    (fun s hs ↦ kProgWith_root κ r0 h0 samp s (List.mem_append_left _ hs)) []
    (by simp [length_kRoundsPre])
  rw [ChainProg.run, show (kProgWith κ r0 samp).rounds = kRoundsPre κ r0 ++ [⟨false, 64, 5⟩] from rfl,
    runRounds_append, hpre]
  conv_lhs => rw [readRounds_fit F (kRoundsPre κ r0)]
  conv_rhs => rw [readRounds_fit F (kRoundsPre κ r0)]
  simp only [bind_map_left, bind_assoc, List.nil_append]
  congr 1
  funext d
  simp [ChainProg.runRounds, ChainProg.requireZeros, kProgWith, length_fitN, length_kRoundsPre,
    nextScalars_zero]

theorem kTerm_shape {κ : ℕ} (samp : Done → List E) (r0 r1 r4 : UMsg × List E) (zc lc : Done)
    (hzc : zc.length = 14 + κ) (hlc : lc.length = 11) (slices : List E) :
    kTerm κ samp (r0 :: r1 :: (zc ++ r4 :: lc)) slices =
      kTermOf (samp (r0 :: r1 :: (zc ++ r4 :: lc))) r1.1.2 (r1.2.headD 0) zc (r4.1.2.getD 0 0)
        (r4.1.2.getD 1 0) (r4.2.headD 0) lc slices := by
  have h16 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop (16 + κ) = r4 :: lc := by
    rw [show 16 + κ = 2 + (14 + κ) by omega, ← List.drop_drop]
    exact List.drop_left' hzc
  have h17 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop (17 + κ) = lc := by
    rw [show 17 + κ = (16 + κ) + 1 by omega, ← List.drop_drop, h16]
    rfl
  have h2 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop 2 = zc ++ r4 :: lc := rfl
  rw [kTerm, h2, h16, h17, List.take_left' hzc, List.take_of_length_le (l := lc) (by omega)]
  rfl

theorem kOutT_shape {κ : ℕ} (samp : Done → List E) (r0 r1 r4 r6 : UMsg × List E) (zc lc : Done)
    (hzc : zc.length = 14 + κ) (hlc : lc.length = 11) :
    kOutT κ samp (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))) =
      kOutOf (samp (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6])))) r1.1.2 (r1.2.headD 0) zc (r4.1.2.getD 0 0)
        (r4.1.2.getD 1 0) (r4.2.headD 0) lc r6.1.2 r6.2 := by
  have h16 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (16 + κ) = r4 :: (lc ++ [r6]) := by
    rw [show 16 + κ = 2 + (14 + κ) by omega, ← List.drop_drop]
    exact List.drop_left' hzc
  have h17 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (17 + κ) = lc ++ [r6] := by
    rw [show 17 + κ = (16 + κ) + 1 by omega, ← List.drop_drop, h16]
    rfl
  have h28 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (28 + κ) = [r6] := by
    rw [show 28 + κ = (17 + κ) + 11 by omega, ← List.drop_drop, h17]
    exact List.drop_left' hlc
  have h2 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop 2 = zc ++ r4 :: (lc ++ [r6]) := rfl
  rw [kOutT, h2, h16, h17, h28, List.take_left' hzc, List.take_left' hlc]
  rfl

theorem sampMain_cons (r0 : UMsg × List E) (d : Done) : sampMain (r0 :: d) = r0.2 := rfl

theorem sampRec3_cons (κ : ℕ) (r0 : UMsg × List E) (d : Done) :
    sampRec3 κ (r0 :: d) = squares (r0.2.headD 0) (7 + κ) := rfl

/-- **The code-level link, main line**: `verifyWalkedK` at `17 + κ` variables, `KECCAK_MAIN`, is the chain program
`kProg κ`, for every lawful monad and permutation. -/
theorem kflock_link (κ : ℕ) (F : KeccakState → m KeccakState) :
    UniKeccak.verifyWalkedK F (keccakR1csLogSize + κ) UniKeccak.keccakMain = (kProg κ).run F := by
  rw [kProg, kProgWith_run κ (r0Main κ) rfl]
  have h7 : keccakR1csLogSize + κ - 3 - Flock.nFixed = 7 + κ := by
    simp only [keccakR1csLogSize, Flock.nFixed]; omega
  have h14 : Flock.fixedChallenges.length + (7 + κ) = 14 + κ := by
    rw [length_fixedChallenges]; omega
  have h6 : 6 + κ + 1 = 7 + κ := by omega
  have h11 : UniKeccak.lincheckRoundsK = 11 := rfl
  have hp : Flock.packing - 3 = 3 := rfl
  have hk : Flock.kBits = 64 := rfl
  have hr : Flock.ringMapShifts.length = 6 := rfl
  have h23 : (2 : ℕ) ^ 3 = 8 := rfl
  have h24 : (2 : ℕ) ^ (3 + 1) = 16 := rfl
  have h51 : 5 + 1 = 6 := rfl
  simp only [UniKeccak.verifyWalkedK, UniKeccak.frontK, Flock.zerocheckFs, drawRun, Flock.ringEnd,
    UniKeccak.keccakMain, UniKeccak.KeccakVariant.flock, h7, show (3 : ℕ) > 0 from by decide, ite_true, h11, hp,
    hk, hr, h23, h24]
  conv_lhs => rw [samples_fit F (7 + κ)]
  simp only [sumcheck_eq, sumcheckR_eq, List.length_map, List.length_append, length_fitL, h14,
    List.length_replicate, bind_map_left, bind_assoc, pure_bind]
  conv_rhs => simp only [kRoundsPre, readRounds_append, readRounds, readRound, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append, bind_assoc, pure_bind, map_bind,
    bind_map_left, map_pure, nextScalars_zero, nextScalars_two, Nat.zero_add, h51, h6, samples_one]
  conv_rhs => rw [samples_fit F (7 + κ)]
  rw [readRounds_fit_replicate F (14 + κ), readRounds_fit_replicate F 11]
  simp only [bind_map_left, kOutT_shape, kTerm_shape, sampMain_cons, length_fitN, List.headD_cons,
    List.getD_cons_zero, List.getD_cons_succ, kOutOf, kTermOf, Option.getD_some]

/-- **The code-level link, π1-rec3**: `verifyWalkedK` at `17 + κ` variables, `KECCAK_REC3`, is the chain program
`kProg3 κ`, for every lawful monad and permutation. -/
theorem kflock_link3 (κ : ℕ) (F : KeccakState → m KeccakState) :
    UniKeccak.verifyWalkedK F (keccakR1csLogSize + κ) UniKeccak.keccakRec3 = (kProg3 κ).run F := by
  rw [kProg3, kProgWith_run κ r0Rec3 rfl]
  have h7 : keccakR1csLogSize + κ - 3 - Flock.nFixed = 7 + κ := by
    simp only [keccakR1csLogSize, Flock.nFixed]; omega
  have h0 : (7 + κ = 0) = False := by simp
  have h14 : Flock.fixedChallenges.length + (7 + κ) = 14 + κ := by
    rw [length_fixedChallenges]; omega
  have h11 : UniKeccak.lincheckRoundsK = 11 := rfl
  have hp : Flock.packing - 3 = 3 := rfl
  have hk : Flock.kBits = 64 := rfl
  have hr : Flock.ringMapShifts.length = 6 := rfl
  have h23 : (2 : ℕ) ^ 3 = 8 := rfl
  have h24 : (2 : ℕ) ^ (3 + 1) = 16 := rfl
  have h51 : 5 + 1 = 6 := rfl
  simp only [UniKeccak.verifyWalkedK, UniKeccak.frontK, Flock.zerocheckFs, drawRun, Flock.ringEnd,
    UniKeccak.keccakRec3, UniKeccak.KeccakVariant.flock, h7, h0, ite_false, show (3 : ℕ) > 0 from by decide,
    ite_true, h11, hp, hk, hr, h23, h24]
  simp only [sumcheck_eq, sumcheckR_eq, List.length_map, List.length_append, length_squares, h14,
    List.length_replicate, bind_map_left, bind_assoc, pure_bind]
  conv_rhs => simp only [kRoundsPre, readRounds_append, readRounds, readRound, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append, bind_assoc, pure_bind, map_bind,
    bind_map_left, map_pure, nextScalars_zero, nextScalars_two, Nat.zero_add, h51, samples_one]
  rw [readRounds_fit_replicate F (14 + κ), readRounds_fit_replicate F 11]
  simp only [bind_map_left, kOutT_shape, kTerm_shape, sampRec3_cons, length_fitN, List.headD_cons,
    List.getD_cons_zero, List.getD_cons_succ, kOutOf, kTermOf, Option.getD_some]

end Link

end UniKeccakSound.KF
