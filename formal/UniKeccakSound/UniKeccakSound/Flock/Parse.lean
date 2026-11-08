-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `formal/FlockSound/FlockSoundUni/Parse.lean` and
-- `Prefix.lean` (BLAKE2s's main line) at the Keccak verifier's sizes (`11` lincheck rounds, `7 + κ` sampled
-- coordinates).
import UniKeccakSound.Flock.Link
import UniKeccakSound.Flock.Setup
import UniKeccakSound.Flock.RoundByRound
import FlockSoundUni.Prefix

/-!
# The Keccak verifier's Flock transcript as Flock's run, and its bad family

`parseK κ d` reads a transcript of the main line's Flock rounds (`kRounds κ (r0Main κ)`) as `FlockSound`'s run
(`Front E 3 3 11 κ (7 + κ) 6`): `τ`'s sampled coordinates (round `0`), the coset values and `z` (round `1`), the
zerocheck's `14 + κ` rounds (each message decoded from the claim before it, as the code decodes it), `v_a`, `v_b`, `α`
(round `16 + κ`), the lincheck's `11` rounds, the slices and the ring map (round `28 + κ`). Every field reads the
rounds by position (`rd`), so a prefix of a transcript parses too.

**The bad family** (`kBad F κ`): the bad set of challenge `i` of round `j` is `Front.Bad`'s set at that position
(`badAtK`) of the parse of the rounds so far, this round's message and its challenges so far, at the setup
`kSetup F κ`. Its sizes (`dBoundK`, from `card_badM`): `1` for each of `τ`'s `7 + κ` coordinates, `15` for `z`, `2`
for each zerocheck round, `3` for `α`, `2` for each lincheck round, `1` for each of the ring map's six stages.

**The prefix property** (`badAtK_congr`): the bad set at `(j, i)` reads only the rounds before `j`, round `j`'s
message and its challenges before `i` (`AgreeAt`); hence `hitInK_of_mem`.
-/

namespace UniKeccakSound.KF

open UniSound hiding rd
open UniStatement LeanVM.Parameters LeanVM.Semantics Finset Polynomial FlockSound FlockSound.Uni
open LeanVM.Protocol (Column)

/-! ## The parse -/

/-- `τ`'s sampled coordinates. -/
def kSampled (d : Done) : List E := (rd d 0).2

/-- The coset values. -/
def kCoset (d : Done) : List E := (rd d 1).1.2

/-- `z`. -/
def kZ (d : Done) : E := (rd d 1).2.headD 0

/-- The zerocheck rounds' `eq` factors: the fixed coordinates, then the sampled. -/
def kEs (d : Done) : List (Option E) := (Flock.fixedChallenges ++ kSampled d).map some

/-- The zerocheck's starting claim, as the code computes it. -/
def kC0 (d : Done) : E := Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ kCoset d) (kZ d)

/-- The zerocheck's last claim. -/
def kRunning (κ : ℕ) (d : Done) : E := scClaim (kC0 d) (kEs d) (d.drop 2) (14 + κ)

/-- `v_a`. -/
def kVa (κ : ℕ) (d : Done) : E := (rd d (16 + κ)).1.2.getD 0 0

/-- `v_b`. -/
def kVb (κ : ℕ) (d : Done) : E := (rd d (16 + κ)).1.2.getD 1 0

/-- `α`. -/
def kAlpha (κ : ℕ) (d : Done) : E := (rd d (16 + κ)).2.headD 0

/-- The lincheck's starting claim, as the code computes it. -/
def kLc0 (κ : ℕ) (d : Done) : E :=
  kVa κ d + kAlpha κ d * kVb κ d + epow (kAlpha κ d) 2 * (kRunning κ d + kVa κ d * kVb κ d) + epow (kAlpha κ d) 3

/-- **The transcript as Flock's run.** -/
noncomputable def parseK (κ : ℕ) (d : Done) : Front E 3 3 11 κ (7 + κ) 6 where
  τs a := (kSampled d).getD a 0
  cv b := (kCoset d).getD (cubeFin 3 b) 0
  z := kZ d
  zq t := msgPoly (decodeMsg (scClaim (kC0 d) (kEs d) (d.drop 2) t) ((kEs d).getD t none) (rd (d.drop 2) t).1.2)
  zχ t := (rd (d.drop 2) t).2.headD 0
  va := kVa κ d
  vb := kVb κ d
  α := kAlpha κ d
  lq t := msgPoly (decodeMsg (scClaim (kLc0 κ d) (List.replicate 11 none) (d.drop (17 + κ)) t) none
    (rd (d.drop (17 + κ)) t).1.2)
  lχ t := (rd (d.drop (17 + κ)) t).2.headD 0
  s cy := (rd d (28 + κ)).1.2.getD (cubeFin (3 + 3) cy) 0
  f a := (rd d (28 + κ)).2.getD a 0

/-! ## The bad family -/

section Bad

variable (F : KeccakVm.KeccakFlockSpec) {κ : ℕ}

/-- **The bad set of challenge `i` of round `j`**, for the column `qf` and the run `R`: `Front.Bad`'s set at that
position. -/
noncomputable def badAtK (qf : Column (KeccakVm.kWords + κ)) (R : Front E 3 3 11 κ (7 + κ) 6) (j i : ℕ) :
    Finset E :=
  if j = 0 then
    if h : i < 7 + κ then
      pointBad (7 + κ) (sampledTables (kSetup F κ).hsize (kSetup F κ).fixed
        (Front.zRes (kSetup F κ) (zOfK qf))) R.τs ⟨i, h⟩
    else ∅
  else if j = 1 then
    if i = 0 then
      skipBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) (Front.zB (kSetup F κ) (zOfK qf))
        (Front.zZ (zOfK qf)) (Front.τ (kSetup F κ) R) R.cv
    else ∅
  else if h : j < 16 + κ then
    if i = 0 then
      zcBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) (Front.zB (kSetup F κ) (zOfK qf))
        (Front.zZ (zOfK qf)) (pinTab (zOfK qf) (kSetup F κ).cpos) (Front.τ (kSetup F κ) R) R.z
        (Front.c₀ (kSetup F κ) R) R.zq R.zχ ⟨j - 2, by omega⟩
    else ∅
  else if j = 16 + κ then
    if i = 0 then
      alphaBad R.va R.vb (Front.vc (kSetup F κ) R)
        (skipVal (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) R.z R.zχ)
        (skipVal (kSetup F κ).node (Front.zB (kSetup F κ) (zOfK qf)) R.z R.zχ)
        (skipVal (kSetup F κ).node (Front.zZ (zOfK qf)) R.z R.zχ)
        (zhat (zOfK qf) (Front.rt (kSetup F κ) R) (kSetup F κ).cpos)
    else ∅
  else if h : j < 28 + κ then
    if i = 0 then
      sumBad 2 11 (fun _ ↦ none)
        (linRev (linFun (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos (kSetup F κ).node
          R.z (Front.rl (kSetup F κ) R) (Front.rh (kSetup F κ) R) (Front.rt (kSetup F κ) R) R.α))
        R.lq R.lχ ⟨j - (17 + κ), by omega⟩
    else ∅
  else if j = 28 + κ then
    if h : i < 6 then
      ringBad univ (kSetup F κ).w (kSetup F κ).sh
        (fun cy ↦ R.s cy - strue (zOfK qf) (Front.rt (kSetup F κ) R) (Front.χ' (kSetup F κ) R) cy) R.f
        ⟨i, h⟩
    else ∅
  else ∅

/-- **The Keccak verifier's Flock bad family**: the bad set of the next challenge, at its position, of the parse of
the rounds so far, this round's message and its challenges so far. -/
noncomputable def kBad (κ : ℕ) : KBadFamily κ := fun qf done msg pre ↦
  badAtK F qf (parseK κ (done ++ [(msg, pre)])) done.length pre.length

/-- **The bad sets' sizes** (`card_badM`), by position. -/
def dBoundK (κ : ℕ) (j _i : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then 15 else if j < 16 + κ then 2 else if j = 16 + κ then 3
  else if j < 28 + κ then 2 else 1

theorem card_badAtK (qf : Column (KeccakVm.kWords + κ)) (R : Front E 3 3 11 κ (7 + κ) 6) (j i : ℕ) :
    (badAtK F qf R j i).card ≤ dBoundK κ j i := by
  obtain ⟨hτ, hz, hzc, hα, hlin, hring⟩ := card_badK F κ qf R
  unfold badAtK
  by_cases h0 : j = 0
  · rw [ite_eq_left h0, show dBoundK κ j i = 1 by unfold dBoundK; split_ifs; omega]
    split_ifs
    · exact hτ _
    · simp
  rw [ite_eq_right h0]
  by_cases h1 : j = 1
  · rw [ite_eq_left h1, show dBoundK κ j i = 15 by unfold dBoundK; split_ifs; omega]
    split_ifs
    · exact hz.trans (by norm_num)
    · simp
  rw [ite_eq_right h1]
  by_cases h2 : j < 16 + κ
  · rw [dite_eq_left h2, show dBoundK κ j i = 2 by unfold dBoundK; split_ifs; omega]
    split_ifs
    · exact hzc _
    · simp
  rw [dite_eq_right h2]
  by_cases h3 : j = 16 + κ
  · rw [ite_eq_left h3, show dBoundK κ j i = 3 by unfold dBoundK; split_ifs; omega]
    split_ifs
    · exact hα
    · simp
  rw [ite_eq_right h3]
  by_cases h4 : j < 28 + κ
  · rw [dite_eq_left h4, show dBoundK κ j i = 2 by unfold dBoundK; split_ifs; omega]
    split_ifs
    · exact hlin _
    · simp
  rw [dite_eq_right h4, show dBoundK κ j i = 1 by unfold dBoundK; split_ifs; omega]
  split_ifs
  · exact hring _
  · simp
  · simp

theorem card_kBad (κ : ℕ) : ∀ qf done msg pre,
    (kBad F κ qf done msg pre).card ≤ dBoundK κ done.length pre.length :=
  fun qf _ _ _ ↦ card_badAtK F qf _ _ _

end Bad

/-! ## The parse's fields read their rounds -/

section Fields

variable {κ : ℕ} {d d' : Done}

theorem parseK_τs (h : rd d 0 = rd d' 0) : (parseK κ d).τs = (parseK κ d').τs := by
  funext a
  show (rd d 0).2.getD a 0 = (rd d' 0).2.getD a 0
  rw [h]

theorem parseK_cv (h : (rd d 1).1 = (rd d' 1).1) : (parseK κ d).cv = (parseK κ d').cv := by
  funext b
  show (rd d 1).1.2.getD _ 0 = (rd d' 1).1.2.getD _ 0
  rw [h]

theorem parseK_z (h : rd d 1 = rd d' 1) : (parseK κ d).z = (parseK κ d').z := by
  show (rd d 1).2.headD 0 = (rd d' 1).2.headD 0
  rw [h]

theorem kEs_congr (h : rd d 0 = rd d' 0) : kEs d = kEs d' := by
  simp only [kEs, kSampled, h]

theorem kC0_congr (h : rd d 1 = rd d' 1) : kC0 d = kC0 d' := by
  simp only [kC0, kCoset, kZ, h]

theorem parseK_zq (t : Fin (3 + 11 + κ)) (h : ∀ a < 2 + t.val, rd d a = rd d' a)
    (h1 : (rd d (2 + t.val)).1 = (rd d' (2 + t.val)).1) : (parseK κ d).zq t = (parseK κ d').zq t := by
  show msgPoly (decodeMsg (scClaim (kC0 d) (kEs d) (d.drop 2) t) ((kEs d).getD t none)
      (rd (d.drop 2) t).1.2) =
    msgPoly (decodeMsg (scClaim (kC0 d') (kEs d') (d'.drop 2) t) ((kEs d').getD t none)
      (rd (d'.drop 2) t).1.2)
  rw [kC0_congr (h 1 (by omega)), kEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parseK_zχ (t : Fin (3 + 11 + κ)) (h : rd d (2 + t.val) = rd d' (2 + t.val)) :
    (parseK κ d).zχ t = (parseK κ d').zχ t := by
  show (rd (d.drop 2) t).2.headD 0 = (rd (d'.drop 2) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parseK_zq_eq (h : ∀ a < 16 + κ, rd d a = rd d' a) : (parseK κ d).zq = (parseK κ d').zq := by
  funext t
  have := t.isLt
  exact parseK_zq t (fun a ha ↦ h a (by omega)) (by rw [h _ (by omega)])

theorem parseK_zχ_eq (h : ∀ a < 16 + κ, rd d a = rd d' a) : (parseK κ d).zχ = (parseK κ d').zχ := by
  funext t
  have := t.isLt
  exact parseK_zχ t (h _ (by omega))

theorem parseK_va (h : (rd d (16 + κ)).1 = (rd d' (16 + κ)).1) : (parseK κ d).va = (parseK κ d').va := by
  show (rd d (16 + κ)).1.2.getD 0 0 = (rd d' (16 + κ)).1.2.getD 0 0
  rw [h]

theorem parseK_vb (h : (rd d (16 + κ)).1 = (rd d' (16 + κ)).1) : (parseK κ d).vb = (parseK κ d').vb := by
  show (rd d (16 + κ)).1.2.getD 1 0 = (rd d' (16 + κ)).1.2.getD 1 0
  rw [h]

theorem parseK_α (h : rd d (16 + κ) = rd d' (16 + κ)) : (parseK κ d).α = (parseK κ d').α := by
  show (rd d (16 + κ)).2.headD 0 = (rd d' (16 + κ)).2.headD 0
  rw [h]

theorem kRunning_congr (h : ∀ a < 16 + κ, rd d a = rd d' a) : kRunning κ d = kRunning κ d' := by
  unfold kRunning
  rw [kC0_congr (h 1 (by omega)), kEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ _ fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega)]

theorem kLc0_congr (h : ∀ a < 17 + κ, rd d a = rd d' a) : kLc0 κ d = kLc0 κ d' := by
  unfold kLc0 kVa kVb kAlpha
  rw [kRunning_congr fun a ha ↦ h a (by omega), h (16 + κ) (by omega)]

theorem parseK_lq (t : Fin 11) (h : ∀ a < 17 + κ + t.val, rd d a = rd d' a)
    (h1 : (rd d (17 + κ + t.val)).1 = (rd d' (17 + κ + t.val)).1) :
    (parseK κ d).lq t = (parseK κ d').lq t := by
  show msgPoly (decodeMsg (scClaim (kLc0 κ d) (List.replicate 11 none) (d.drop (17 + κ)) t) none
      (rd (d.drop (17 + κ)) t).1.2) =
    msgPoly (decodeMsg (scClaim (kLc0 κ d') (List.replicate 11 none) (d'.drop (17 + κ)) t) none
      (rd (d'.drop (17 + κ)) t).1.2)
  rw [kLc0_congr fun a ha ↦ h a (by omega),
    scClaim_congr (d := d.drop (17 + κ)) (d' := d'.drop (17 + κ)) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parseK_lχ (t : Fin 11) (h : rd d (17 + κ + t.val) = rd d' (17 + κ + t.val)) :
    (parseK κ d).lχ t = (parseK κ d').lχ t := by
  show (rd (d.drop (17 + κ)) t).2.headD 0 = (rd (d'.drop (17 + κ)) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parseK_lχ_eq (h : ∀ a < 28 + κ, rd d a = rd d' a) : (parseK κ d).lχ = (parseK κ d').lχ := by
  funext t
  have := t.isLt
  exact parseK_lχ t (h _ (by omega))

theorem parseK_s (h : (rd d (28 + κ)).1 = (rd d' (28 + κ)).1) : (parseK κ d).s = (parseK κ d').s := by
  funext cy
  show (rd d (28 + κ)).1.2.getD _ 0 = (rd d' (28 + κ)).1.2.getD _ 0
  rw [h]

variable (F : KeccakVm.KeccakFlockSpec)

theorem τK_congr (h : rd d 0 = rd d' 0) :
    Front.τ (kSetup F κ) (parseK κ d) = Front.τ (kSetup F κ) (parseK κ d') := by
  show fullPoint _ _ (parseK κ d).τs = fullPoint _ _ (parseK κ d').τs
  rw [parseK_τs h]

theorem c₀K_congr (h : rd d 1 = rd d' 1) :
    Front.c₀ (kSetup F κ) (parseK κ d) = Front.c₀ (kSetup F κ) (parseK κ d') := by
  show (FlockSound.interp _ (parseK κ d).cv).eval (parseK κ d).z =
    (FlockSound.interp _ (parseK κ d').cv).eval (parseK κ d').z
  rw [parseK_cv (congrArg Prod.fst h), parseK_z h]

theorem vcK_congr (h : ∀ a < 16 + κ, rd d a = rd d' a) (h1 : (rd d (16 + κ)).1 = (rd d' (16 + κ)).1) :
    Front.vc (kSetup F κ) (parseK κ d) = Front.vc (kSetup F κ) (parseK κ d') := by
  show claimAt (Front.c₀ (kSetup F κ) (parseK κ d)) (parseK κ d).zq (parseK κ d).zχ (Fin.last _) +
      (parseK κ d).va * (parseK κ d).vb =
    claimAt (Front.c₀ (kSetup F κ) (parseK κ d')) (parseK κ d').zq (parseK κ d').zχ (Fin.last _) +
      (parseK κ d').va * (parseK κ d').vb
  rw [c₀K_congr F (h 1 (by omega)), parseK_zq_eq h, parseK_zχ_eq h, parseK_va h1, parseK_vb h1]

theorem rlK_congr (h : ∀ a < 16 + κ, rd d a = rd d' a) :
    Front.rl (kSetup F κ) (parseK κ d) = Front.rl (kSetup F κ) (parseK κ d') := by
  show lowPart (lowPart (parseK κ d).zχ) = lowPart (lowPart (parseK κ d').zχ)
  rw [parseK_zχ_eq h]

theorem rhK_congr (h : ∀ a < 16 + κ, rd d a = rd d' a) :
    Front.rh (kSetup F κ) (parseK κ d) = Front.rh (kSetup F κ) (parseK κ d') := by
  show highPart (lowPart (parseK κ d).zχ) = highPart (lowPart (parseK κ d').zχ)
  rw [parseK_zχ_eq h]

theorem rtK_congr (h : ∀ a < 16 + κ, rd d a = rd d' a) :
    Front.rt (kSetup F κ) (parseK κ d) = Front.rt (kSetup F κ) (parseK κ d') := by
  show highPart (parseK κ d).zχ = highPart (parseK κ d').zχ
  rw [parseK_zχ_eq h]

theorem χ'K_congr (h : ∀ a < 28 + κ, rd d a = rd d' a) :
    Front.χ' (kSetup F κ) (parseK κ d) = Front.χ' (kSetup F κ) (parseK κ d') := by
  show (fun j ↦ (parseK κ d).lχ (Fin.rev j)) = fun j ↦ (parseK κ d').lχ (Fin.rev j)
  rw [parseK_lχ_eq h]

end Fields

/-! ## The prefix property -/

variable (F : KeccakVm.KeccakFlockSpec) {κ : ℕ}

/-- **The bad set at `(j, i)` reads the transcript before `(j, i)` only.** -/
theorem badAtK_congr (qf : Column (KeccakVm.kWords + κ)) {d d' : Done} {j i : ℕ} (hA : AgreeAt d d' j i) :
    badAtK F qf (parseK κ d) j i = badAtK F qf (parseK κ d') j i := by
  obtain ⟨hlt, hmsg, hch⟩ := hA
  unfold badAtK
  by_cases h0 : j = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    subst h0
    split_ifs with hi
    · exact pointBad_congr _ _ _ _ _ fun a ha ↦ hch a (by simpa using ha)
    · rfl
  simp only [ite_eq_right h0]
  by_cases h1 : j = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    subst h1
    split_ifs
    · rw [τK_congr F (hlt 0 (by omega)), parseK_cv hmsg]
    · rfl
  simp only [ite_eq_right h1]
  by_cases h2 : j < 16 + κ
  · simp only [dite_eq_left h2]
    split_ifs
    · rw [τK_congr F (hlt 0 (by omega)), c₀K_congr F (hlt 1 (by omega)), parseK_z (hlt 1 (by omega))]
      refine zcBad_congr _ _ _ _ _ _ _ _ _ _ _ _ _ (fun u hu ↦ ?_) (fun u hu ↦ ?_)
      · simp only at hu
        refine parseK_zq u (fun a ha ↦ hlt a (by omega)) ?_
        rcases Nat.lt_or_ge (2 + u.val) j with hl | hl
        · rw [hlt _ hl]
        · rw [show 2 + u.val = j by omega]
          exact hmsg
      · simp only at hu
        exact parseK_zχ u (hlt _ (by omega))
    · rfl
  simp only [dite_eq_right h2]
  by_cases h3 : j = 16 + κ
  · rw [ite_eq_left h3, ite_eq_left h3]
    subst h3
    split_ifs
    · rw [vcK_congr F hlt hmsg, rtK_congr F hlt, parseK_va hmsg, parseK_vb hmsg, parseK_z (hlt 1 (by omega)),
        parseK_zχ_eq hlt]
    · rfl
  simp only [ite_eq_right h3]
  by_cases h4 : j < 28 + κ
  · simp only [dite_eq_left h4]
    split_ifs
    · have h16 : ∀ a < 16 + κ, rd d a = rd d' a := fun a ha ↦ hlt a (by omega)
      rw [rlK_congr F h16, rhK_congr F h16, rtK_congr F h16, parseK_z (hlt 1 (by omega)),
        parseK_α (hlt (16 + κ) (by omega))]
      refine sumBad_congr' 2 11 _ _ _ _ _ _ _ ?_ fun u hu ↦ ?_
      · refine parseK_lq _ (fun a ha ↦ hlt a (by simp only at ha; omega)) ?_
        simp only
        rw [show 17 + κ + (j - (17 + κ)) = j by omega]
        exact hmsg
      · simp only at hu
        exact parseK_lχ u (hlt _ (by omega))
    · rfl
  simp only [dite_eq_right h4]
  by_cases h5 : j = 28 + κ
  · rw [ite_eq_left h5, ite_eq_left h5]
    subst h5
    split_ifs
    · rw [rtK_congr F fun a ha ↦ hlt a (by omega), χ'K_congr F hlt, parseK_s hmsg]
      exact ringBad_congr _ _ _ _ _ _ _ fun a ha ↦ hch a (by simpa using ha)
    · rfl
  simp only [ite_eq_right h5]

/-- **A challenge in its own parse's bad set is a hit of `kBad`.** -/
theorem hitInK_of_mem (qf : Column (KeccakVm.kWords + κ)) {done : Done} {j i : ℕ} (hj : j < done.length)
    (hi : i < (rd done j).2.length)
    (hmem : (rd done j).2.getD i 0 ∈ badAtK F qf (parseK κ done) j i) : HitInK (kBad F κ) qf done := by
  obtain ⟨r, ds, rfl⟩ : ∃ r ds, done = r :: ds :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega))
  have hr := rd_eq_getElem hj
  refine ⟨j, hj, i, by rw [← hr]; exact hi, ?_⟩
  show _ ∈ kBad F κ qf ((r :: ds).take j) ((r :: ds)[j]).1 (((r :: ds)[j]).2.take i)
  rw [← hr]
  unfold kBad
  rw [List.length_take, min_eq_left hj.le, List.length_take, min_eq_left hi.le,
    badAtK_congr F qf (agree_pfx hj i)]
  exact hmem

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.badAtK_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.badAtK_congr
