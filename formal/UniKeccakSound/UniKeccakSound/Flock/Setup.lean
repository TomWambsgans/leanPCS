-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Generalises `formal/FlockSound/FlockSound/Leanvm.lean`
-- and `Main.lean`'s `card_bad` (leanVM's Flock at `m = 8` slot bits) to any number `m` of slot bits.
import FlockSoundUni.Catch
import FlockSoundUni.Transcription
import FlockSound.FlockSq
import UniKeccakSound.FlockInterfaceK
import KeccakFlock

/-!
# Flock at leanVM's constants with `m` slot bits, and the Keccak-f block's setup

`FlockSound.Leanvm` instantiates the generic theorems (`FlockSound.Flock`) at leanVM's constants with BLAKE2s's
`m = 8` slot bits. The constants' facts (`Setup.Valid`: the skip nodes, the fixed coordinates, ring switching) do not
read `m`, so the same holds for any `m`; here at `m` slot bits:

* `posFinM`, `wordFinM`, `colBitsM`, `cubeMatM`, `colWordM`: a block position, a column word, the column's bits, the
  matrices and the words on the cube (Lv42's indices `jsk + 64 jin`, `jin + 2^m t`);
* `leanvmSetupM`, **`leanvmSetupM_valid`**: the constants and their facts;
* **`r1csHoldsM_iff`**: the generic relation on the column's bits is Lv42's `BatchHolds`; `colPackM`: packing;
* **`card_badM`**: every bad set's size, as `FlockSound.card_bad`.

At `m = 11` (`KeccakVm.kWords`), skip `3`, `7 + κ` sampled coordinates and the ring map in tower order, with the
Keccak-f block's R1CS and constant position, this is **`kSetup F κ`**, the setup of the Keccak verifier's Flock.
-/

namespace UniKeccakSound.KF

open Finset LeanVM.Parameters LeanVM.Protocol Lv42.Protocol FlockSound

/-! ## The constants at `m` slot bits -/

/-- **leanVM's Flock constants** at a skip of `k` bits, `m` slot bits, `κ` batch bits, the ring map's shifts `sh`
and the R1CS of a block: the generic `Setup` with `f₀ = 7`. -/
def leanvmSetupM (k l m κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + m + κ = 7 + ns)
    (sh : List ℕ) (A B : Pos k l m → Pos k l m → Bool) (cpos : Pos k l m) : Setup E k l m κ 7 ns where
  A := A
  B := B
  cpos := cpos
  node := skipNodes k hk
  fixed := fixedPt
  hsize := hsize
  sh := sh
  w := packW hkl
  twists := range 64

/-- **The constants' facts** for both orders of the ring map, at any number of slot bits. -/
theorem leanvmSetupM_valid (k l m κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6)
    (hsize : l + m + κ = 7 + ns) (sh : List ℕ)
    (hsh : sh = [32, 16, 8, 4, 2, 1] ∨ sh = [1, 2, 4, 8, 16, 32])
    (A B : Pos k l m → Pos k l m → Bool) (cpos : Pos k l m) :
    (leanvmSetupM k l m κ ns hkl hk hsize sh A B cpos).Valid where
  node_injective := skipNodes_injective k hk
  fixed := hfixed_leanvm
  ring_injective := ringInjective_leanvm hkl
  twists_covered := by
    rcases hsh with rfl | rfl
    · exact range_subset_rel_leanvm
    · exact range_subset_rel_tower

/-! ## Lv42's relation at `m` slot bits -/

/-- A position of a block as Lv42's index `jsk + 64 jin`. -/
def posFinM {k l : ℕ} (m : ℕ) (hkl : k + l = 6) : Pos k l m ≃ Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m)) :=
  (Equiv.prodCongr (cube64 hkl) (cubeFin m)).trans (cubeSplit 6 m)

/-- A word of the column as its index `jin + 2^m t`. -/
def wordFinM (m κ : ℕ) : Cube m × Cube κ ≃ Fin (2 ^ (m + κ)) :=
  (Equiv.prodCongr (cubeFin m) (cubeFin κ)).trans (cubeSplit m κ)

/-- **The column's bits** on the cube: packing bits `y`, slot bits `ch`, block `t`. -/
def colBitsM {k l m κ : ℕ} (hkl : k + l = 6) (c : Column (m + κ)) (y : Cube (k + l)) (ch : Cube m)
    (t : Cube κ) : E :=
  Lv42.Protocol.cellBit (c.values.get (wordFinM m κ (ch, t))) (cube64 hkl y).val

theorem colBitsM_bool {k l m κ : ℕ} (hkl : k + l = 6) (c : Column (m + κ)) (y : Cube (k + l))
    (ch : Cube m) (t : Cube κ) : colBitsM hkl c y ch t = 0 ∨ colBitsM hkl c y ch t = 1 := by
  unfold colBitsM Lv42.Protocol.cellBit
  split <;> simp

/-- The matrices on the cube. -/
def cubeMatM {k l m : ℕ} (hkl : k + l = 6) (M : Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m)) →
    Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m)) → Bool) (r c : Pos k l m) : Bool :=
  M (posFinM m hkl r) (posFinM m hkl c)

theorem batchBlock_posFinM {k l m κ : ℕ} (hkl : k + l = 6) (c : Column (m + κ)) (t : Cube κ)
    (row : Pos k l m) :
    (BlockR1CS.batchBlock (s := Lv42.Parameters.Flock.kSkip) (m := m) (Lv42.Protocol.bitTable c) (cubeFin κ t))[posFinM m hkl row] =
      colBitsM hkl c row.1 row.2 t := by
  have h := BlockR1CS.batchBlock_cubeIndex (s := Lv42.Parameters.Flock.kSkip) (m := m) (Lv42.Protocol.bitTable c)
    (cubeFin κ t) (cube64 hkl row.1) (cubeFin m row.2)
  simp only [posFinM, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, cubeSplit_apply]
  rw [h]
  simp only [Lv42.Protocol.bitTable, colBitsM, wordFinM, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    cubeSplit_apply]
  rw [Fin.getElem_fin, Vector.getElem_ofFn]

/-- **Lv42's relation is the generic one**: the column's blocks satisfy `BatchHolds` exactly when its bits satisfy
`R1CSHolds` on the cube. -/
theorem r1csHoldsM_iff {k l m κ : ℕ} (hkl : k + l = 6) (C : BlockR1CS E (Lv42.Parameters.Flock.kSkip + m))
    (cpos : Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m))) (c : Column (m + κ)) :
    R1CSHolds (cubeMatM hkl C.A) (cubeMatM hkl C.B) (colBitsM hkl c) ((posFinM m hkl).symm cpos) ↔
      BlockR1CS.BatchHolds C cpos (Lv42.Protocol.bitTable c) := by
  have hrow : ∀ (M : Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m)) →
      Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m)) → Bool) (t : Cube κ) (row : Pos k l m),
      (∑ j, if M (posFinM m hkl row) j then
        (BlockR1CS.batchBlock (s := Lv42.Parameters.Flock.kSkip) (m := m) (Lv42.Protocol.bitTable c) (cubeFin κ t))[j] else 0) =
        rowProd (cubeMatM hkl M) (colBitsM hkl c) row t := by
    intro M t row
    rw [rowProd]
    refine (Fintype.sum_equiv (posFinM m hkl).symm _ _ fun j ↦ ?_)
    obtain ⟨col, rfl⟩ := (posFinM m hkl).surjective j
    simp only [cubeMatM, Equiv.symm_apply_apply, batchBlock_posFinM]
  constructor
  · rintro ⟨hc, hp⟩ t
    obtain ⟨t, rfl⟩ := (cubeFin κ).surjective t
    refine ⟨fun j ↦ ?_, ?_⟩
    · obtain ⟨row, rfl⟩ := (posFinM m hkl).surjective j
      rw [C.rows_fst, C.rows_snd, hrow, hrow, batchBlock_posFinM]
      exact hc row t
    · have := hp t
      rw [← Equiv.apply_symm_apply (posFinM m hkl) cpos, batchBlock_posFinM]
      exact this
  · intro h
    refine ⟨fun row t ↦ ?_, fun t ↦ ?_⟩
    · have := (h (cubeFin κ t)).1 (posFinM m hkl row)
      rw [C.rows_fst, C.rows_snd, hrow, hrow, batchBlock_posFinM] at this
      exact this
    · have := (h (cubeFin κ t)).2
      rw [← Equiv.apply_symm_apply (posFinM m hkl) cpos, batchBlock_posFinM] at this
      exact this

/-- A word of the column, on the cube of its `m + κ` coordinates. -/
def colWordM {m κ : ℕ} (c : Column (m + κ)) (u : Cube (m + κ)) : E :=
  ofK (c.values.get (wordFinM m κ (lowPart u, highPart u)))

/-- **Packing**: a word is its bits weighted by `x^cy`. -/
theorem colPackM {k l m κ : ℕ} (hkl : k + l = 6) (c : Column (m + κ)) (u : Cube (m + κ)) :
    colWordM c u = ∑ cy, packW hkl cy * wordBits (colBitsM hkl c) cy u := by
  rw [colWordM, ofK_eq_sum_cellBit]
  refine (Fintype.sum_equiv (cube64 hkl).symm _ _ fun i ↦ ?_)
  simp only [packW, wordBits, colBitsM, Equiv.apply_symm_apply]

/-! ## The setup of a block, and the bad sets' sizes -/

/-- leanVM's Flock at a skip of `k` bits and `m` slot bits, its R1CS and constant position a block's. -/
abbrev setupOfM (k l m κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + m + κ = 7 + ns)
    (sh : List ℕ) (C : BlockR1CS E (Lv42.Parameters.Flock.kSkip + m))
    (cpos : Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m))) : Setup E k l m κ 7 ns :=
  leanvmSetupM k l m κ ns hkl hk hsize sh (cubeMatM hkl C.A) (cubeMatM hkl C.B) ((posFinM m hkl).symm cpos)

/-- **Every bad set's size** at `m` slot bits (`FlockSound.card_bad`'s): `1` for a sampled coordinate,
`2^(k+1) − 1` for the skip challenge, `2` for a zerocheck round, `3` for `α`, `2` for a lincheck round, `1` for a
ring stage. -/
theorem card_badM (k l m κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + m + κ = 7 + ns)
    (sh : List ℕ) (C : BlockR1CS E (Lv42.Parameters.Flock.kSkip + m))
    (cpos : Fin (2 ^ (Lv42.Parameters.Flock.kSkip + m))) (c : Column (m + κ))
    (R : Front E k l m κ ns sh.length) :
    let S := setupOfM k l m κ ns hkl hk hsize sh C cpos
    let Z := colBitsM hkl c
    (∀ j, (pointBad ns (sampledTables S.hsize S.fixed (Front.zRes S Z)) R.τs j).card ≤ 1) ∧
    (skipBad S.node (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (Front.τ S R) R.cv).card ≤
      2 ^ (k + 1) - 1 ∧
    (∀ j, (zcBad S.node (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (pinTab Z S.cpos) (Front.τ S R) R.z
      (Front.c₀ S R) R.zq R.zχ j).card ≤ 2) ∧
    (alphaBad R.va R.vb (Front.vc S R) (skipVal S.node (Front.zA S Z) R.z R.zχ)
      (skipVal S.node (Front.zB S Z) R.z R.zχ) (skipVal S.node (Front.zZ Z) R.z R.zχ)
      (zhat Z (Front.rt S R) S.cpos)).card ≤ 3 ∧
    (∀ j, (sumBad 2 m (fun _ ↦ none)
      (linRev (linFun S.A S.B Z S.cpos S.node R.z (Front.rl S R) (Front.rh S R) (Front.rt S R) R.α))
        R.lq R.lχ j).card ≤ 2) ∧
    (∀ j, (ringBad univ S.w S.sh (fun cy ↦ R.s cy - strue Z (Front.rt S R) (Front.χ' S R) cy) R.f j).card
      ≤ 1) := by
  intro S Z
  refine ⟨fun j ↦ card_pointBad_le _ _ _ j, ?_, fun j ↦ card_zcBad_le _ _ _ _ _ _ _ _ _ _ j,
    card_alphaBad_le _ _ _ _ _ _ _, fun j ↦ card_sumBad_le 2 m _ _ _ _
      ((indDeg_linFun _ _ _ _ _ _ _ _ _ _).linRev) j, fun j ↦ card_ringBad_le _ _ _ _ _ j⟩
  have h := card_skipBad_le (node := S.node) (skipNodes_injective k hk : Function.Injective S.node)
    (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (Front.τ S R) R.cv
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  rw [pow_succ]
  omega

/-! ## The Keccak-f block -/

/-- The ring map's stages in tower order (`towerRingMap`: stage `j` of shift `2^j`). -/
abbrev towerShiftsK : List ℕ := [1, 2, 4, 8, 16, 32]

/-- **The Keccak verifier's Flock setup**: skip `3` (`l = 3`), `11` slot bits, `7 + κ` sampled coordinates, the
ring map in tower order, the R1CS and constant position of the block `F`. -/
abbrev kSetup (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) : Setup E 3 3 11 κ 7 (7 + κ) :=
  setupOfM 3 3 11 κ (7 + κ) rfl (by decide) (by omega) towerShiftsK F.r1cs F.constPos

/-- The column's bits on the cube. -/
abbrev zOfK {κ : ℕ} (qf : Column (KeccakVm.kWords + κ)) : Cube (3 + 3) → Cube 11 → Cube κ → E :=
  colBitsM (k := 3) (l := 3) (m := 11) rfl qf

theorem kSetup_valid (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) : (kSetup F κ).Valid :=
  leanvmSetupM_valid 3 3 11 κ (7 + κ) rfl (by decide) (by omega) towerShiftsK (Or.inr rfl) _ _ _

/-- **The block's predicate is the generic relation** on the column's bits. -/
theorem kFlockHolds_iff (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) (qf : Column (KeccakVm.kWords + κ)) :
    R1CSHolds (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos ↔ KFlockHolds F κ qf :=
  r1csHoldsM_iff (k := 3) (l := 3) rfl F.r1cs F.constPos qf

/-- **Every bad set's size** at the Keccak verifier's setup (`card_badM` at `kSetup F κ`). -/
theorem card_badK (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) (qf : Column (KeccakVm.kWords + κ))
    (R : Front E 3 3 11 κ (7 + κ) 6) :
    (∀ j, (pointBad (7 + κ) (sampledTables (kSetup F κ).hsize (kSetup F κ).fixed
      (Front.zRes (kSetup F κ) (zOfK qf))) R.τs j).card ≤ 1) ∧
    (skipBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) (Front.zB (kSetup F κ) (zOfK qf))
      (Front.zZ (zOfK qf)) (Front.τ (kSetup F κ) R) R.cv).card ≤ 2 ^ (3 + 1) - 1 ∧
    (∀ j, (zcBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) (Front.zB (kSetup F κ) (zOfK qf))
      (Front.zZ (zOfK qf)) (pinTab (zOfK qf) (kSetup F κ).cpos) (Front.τ (kSetup F κ) R) R.z
      (Front.c₀ (kSetup F κ) R) R.zq R.zχ j).card ≤ 2) ∧
    (alphaBad R.va R.vb (Front.vc (kSetup F κ) R) (skipVal (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) R.z R.zχ)
      (skipVal (kSetup F κ).node (Front.zB (kSetup F κ) (zOfK qf)) R.z R.zχ)
      (skipVal (kSetup F κ).node (Front.zZ (zOfK qf)) R.z R.zχ)
      (zhat (zOfK qf) (Front.rt (kSetup F κ) R) (kSetup F κ).cpos)).card ≤ 3 ∧
    (∀ j, (sumBad 2 11 (fun _ ↦ none)
      (linRev (linFun (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos (kSetup F κ).node R.z
        (Front.rl (kSetup F κ) R) (Front.rh (kSetup F κ) R) (Front.rt (kSetup F κ) R) R.α))
        R.lq R.lχ j).card ≤ 2) ∧
    (∀ j, (ringBad univ (kSetup F κ).w (kSetup F κ).sh
      (fun cy ↦ R.s cy - strue (zOfK qf) (Front.rt (kSetup F κ) R) (Front.χ' (kSetup F κ) R) cy) R.f j).card
      ≤ 1) :=
  card_badM 3 3 11 κ (7 + κ) rfl (by decide) (by omega) towerShiftsK F.r1cs F.constPos qf R

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.r1csHoldsM_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.r1csHoldsM_iff

/-- info: 'UniKeccakSound.KF.card_badM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.card_badM
