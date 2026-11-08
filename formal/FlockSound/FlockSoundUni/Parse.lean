-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import FlockSoundUni.Link
import FlockSoundUni.RoundByRound

/-!
# The transcript as Flock's run, and its bad family

`parse κ d` reads a transcript of `flockProg κ`'s rounds as `FlockSound`'s run
(`Front E 3 3 8 κ (4 + κ) 6`): `τ`'s sampled coordinates, the coset values, `z`, the zerocheck's
rounds (each message decoded from the claim before it, `msgPoly ∘ decodeMsg`, as the code decodes
it), `v_a`, `v_b`, `α`, the lincheck's rounds, the slices and the ring map. Every field reads the
rounds by position (`rd`), past the end `noRound`'s zeros, so a prefix of a transcript parses too.

**The bad family** (`flockBad κ`): the bad set of challenge `i` of round `j` is `Front.Bad`'s set at
that position (`badAt`) of the parse of the rounds so far, this round's message and its challenges
so far. Its sizes (`dBound`, from `card_bad`): `1` for each of `τ`'s `4 + κ` coordinates, `15` for
`z`, `2` for each zerocheck round, `3` for `α`, `2` for each lincheck round, `1` for each of the
ring map's six stages; round `j`'s error is the sum over its challenges: `4 + κ`, `15`, `2`
(`11 + κ` times), `3`, `2` (`8` times), `6`, over `|E|`.

**The prefix property** (`badAt_congr`): the bad set at `(j, i)` reads only the rounds before `j`,
round `j`'s message and its challenges before `i` (`AgreeAt`), by the `_congr` lemmas of
`FlockSound` (`pointBad_congr`, `sumBad_congr`, `ringBad_congr`) and their extensions here
(`trueAt_congr`, `sumBad_congr'`, `zcBad_congr`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

/-! ## Congruence of the bad sets -/

section Congr

variable {F : Type*} [Field F]

theorem trueAt_congr : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F) (χ χ' : Fin m → F)
    (j : Fin (m + 1)), (∀ i : Fin m, i.val < j.val → χ i = χ' i) →
    trueAt m w Φ χ j = trueAt m w Φ χ' j
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, w, Φ, χ, χ', j, h => by
    refine Fin.cases (fun _ ↦ rfl) (fun j h ↦ ?_) j h
    rw [trueAt_succ, trueAt_succ, h 0 (Nat.succ_pos _)]
    exact trueAt_congr m _ _ _ _ j fun i hi ↦ h i.succ (by simpa using hi)

theorem claimAt_castSucc_congr {m : ℕ} (c₀ : F) (q q' : Fin m → F[X]) (χ χ' : Fin m → F) (j : Fin m)
    (hq : ∀ i : Fin m, i.val < j.val → q i = q' i) (hχ : ∀ i : Fin m, i.val < j.val → χ i = χ' i) :
    claimAt c₀ q χ j.castSucc = claimAt c₀ q' χ' j.castSucc := by
  obtain ⟨_ | k, hk⟩ := j
  · rfl
  · have e : (Fin.castSucc ⟨k + 1, hk⟩ : Fin (m + 1)) = (⟨k, by omega⟩ : Fin m).succ :=
      Fin.ext rfl
    rw [e]
    show (q _).eval (χ _) = (q' _).eval (χ' _)
    rw [hq _ (by simp), hχ _ (by simp)]

variable [Fintype F] [DecidableEq F]

/-- Round `j`'s bad challenges read its message and the challenges before it only. -/
theorem sumBad_congr' (d : ℕ) : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F)
    (q q' : Fin m → F[X]) (χ χ' : Fin m → F) (j : Fin m), q j = q' j →
    (∀ i : Fin m, i.val < j.val → χ i = χ' i) →
    sumBad d m w Φ q χ j = sumBad d m w Φ q' χ' j
  | 0, _, _, _, _, _, _, j, _, _ => j.elim0
  | m + 1, w, Φ, q, q', χ, χ', j, hq, h => by
    refine Fin.cases (fun hq _ ↦ ?_) (fun j hq h ↦ ?_) j hq h
    · simp only [sumBad, Fin.cases_zero, hq]
    · rw [sumBad_succ, sumBad_succ, h 0 (Nat.succ_pos _)]
      exact sumBad_congr' d m _ _ _ _ _ _ j hq fun i hi ↦ h i.succ (by simpa using hi)

/-- **A zerocheck round's bad challenges** read the messages up to it and the challenges before
it only. -/
theorem zcBad_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (node : Bool × ι → F)
    (A B Z : ι → Cube n → F) (pin : Cube n → F) (τ : Fin n → F) (z c₀ : F) (q q' : Fin n → F[X])
    (χ χ' : Fin n → F) (j : Fin n) (hq : ∀ i : Fin n, i.val ≤ j.val → q i = q' i)
    (hχ : ∀ i : Fin n, i.val < j.val → χ i = χ' i) :
    zcBad node A B Z pin τ z c₀ q χ j = zcBad node A B Z pin τ z c₀ q' χ' j := by
  unfold zcBad
  rw [claimAt_castSucc_congr c₀ q q' χ χ' j (fun i hi ↦ hq i hi.le) hχ,
    trueAt_congr n _ _ χ χ' j.castSucc (fun i hi ↦ hχ i (by simpa using hi)),
    pointBad_congr n _ χ χ' j hχ, sumBad_congr' 2 n _ _ q q' χ χ' j (hq j le_rfl) hχ]

end Congr

/-! ## The main line's constants -/

/-- The ring map's stages in tower order (`towerRingMap`: stage `j` of shift `2^j`). -/
abbrev towerShifts : List ℕ := [1, 2, 4, 8, 16, 32]

/-- The column's bits on the cube. -/
abbrev zOf {κ : ℕ} (qf : Column (8 + κ)) : Cube (3 + 3) → Cube 8 → Cube κ → E :=
  colBits (k := 3) (l := 3) rfl qf

/-! ## The parse -/

/-- `τ`'s sampled coordinates. -/
def pSampled (d : Done) : List E := (rd d 0).2

/-- The coset values. -/
def pCoset (d : Done) : List E := (rd d 1).1.2

/-- `z`. -/
def pZ (d : Done) : E := (rd d 1).2.headD 0

/-- The zerocheck rounds' `eq` factors: the fixed coordinates, then the sampled. -/
def pEs (d : Done) : List (Option E) := (Flock.fixedChallenges ++ pSampled d).map some

/-- The zerocheck's starting claim, as the code computes it. -/
def pC0 (d : Done) : E := Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ pCoset d) (pZ d)

/-- The zerocheck's last claim. -/
def pRunning (κ : ℕ) (d : Done) : E := scClaim (pC0 d) (pEs d) (d.drop 2) (11 + κ)

/-- `v_a`. -/
def pVa (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).1.2.getD 0 0

/-- `v_b`. -/
def pVb (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).1.2.getD 1 0

/-- `α`. -/
def pAlpha (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).2.headD 0

/-- The lincheck's starting claim, as the code computes it. -/
def pLc0 (κ : ℕ) (d : Done) : E :=
  pVa κ d + pAlpha κ d * pVb κ d + epow (pAlpha κ d) 2 * (pRunning κ d + pVa κ d * pVb κ d) +
    epow (pAlpha κ d) 3

/-- **The transcript as Flock's run.** -/
noncomputable def parse (κ : ℕ) (d : Done) : Front E 3 3 8 κ (4 + κ) 6 where
  τs a := (pSampled d).getD a 0
  cv b := (pCoset d).getD (cubeFin 3 b) 0
  z := pZ d
  zq t := msgPoly (decodeMsg (scClaim (pC0 d) (pEs d) (d.drop 2) t) ((pEs d).getD t none)
    (rd (d.drop 2) t).1.2)
  zχ t := (rd (d.drop 2) t).2.headD 0
  va := pVa κ d
  vb := pVb κ d
  α := pAlpha κ d
  lq t := msgPoly (decodeMsg (scClaim (pLc0 κ d) (List.replicate 8 none) (d.drop (14 + κ)) t) none
    (rd (d.drop (14 + κ)) t).1.2)
  lχ t := (rd (d.drop (14 + κ)) t).2.headD 0
  s cy := (rd d (22 + κ)).1.2.getD (cubeFin (3 + 3) cy) 0
  f a := (rd d (22 + κ)).2.getD a 0

/-! ## The bad family -/

/-- **The bad sets' sizes** (`card_bad`), by position. -/
def dBound (κ : ℕ) (j _i : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then 15 else if j < 13 + κ then 2 else if j = 13 + κ then 3
  else if j < 22 + κ then 2 else 1

end FlockSound.Uni
