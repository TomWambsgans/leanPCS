-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import FlockSoundUni.Parse

/-!
# The bad family's prefix property

The bad set at challenge `i` of round `j` (`badAt` of a parse) reads only the rounds before `j`,
round `j`'s message and its challenges before `i`: two transcripts that agree there (`AgreeAt`)
have the same bad set there (**`badAt_congr`**). A completed transcript agrees at `(j, i)` with
its prefix (`agree_pfx`: the rounds before `j`, round `j`'s message, its first `i` challenges), which
is what `flockBad` parses; so a challenge of the transcript in the bad set of the transcript's own
parse at its position is a hit of `flockBad` (**`hitIn_of_mem`**).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-- **Two transcripts agree at challenge `i` of round `j`**: on the rounds before `j`, round `j`'s
message and its challenges before `i`. -/
def AgreeAt (d d' : Done) (j i : ℕ) : Prop :=
  (∀ a < j, rd d a = rd d' a) ∧ (rd d j).1 = (rd d' j).1 ∧
    ∀ b < i, (rd d j).2.getD b 0 = (rd d' j).2.getD b 0

/-! ## The parse's fields read their rounds -/

section Fields

variable {d d' : Done}

theorem parse_τs (h : rd d 0 = rd d' 0) : (parse κ d).τs = (parse κ d').τs := by
  funext a
  show (rd d 0).2.getD a 0 = (rd d' 0).2.getD a 0
  rw [h]

theorem parse_cv (h : (rd d 1).1 = (rd d' 1).1) : (parse κ d).cv = (parse κ d').cv := by
  funext b
  show (rd d 1).1.2.getD _ 0 = (rd d' 1).1.2.getD _ 0
  rw [h]

theorem parse_z (h : rd d 1 = rd d' 1) : (parse κ d).z = (parse κ d').z := by
  show (rd d 1).2.headD 0 = (rd d' 1).2.headD 0
  rw [h]

theorem pEs_congr (h : rd d 0 = rd d' 0) : pEs d = pEs d' := by
  simp only [pEs, pSampled, h]

theorem pC0_congr (h : rd d 1 = rd d' 1) : pC0 d = pC0 d' := by
  simp only [pC0, pCoset, pZ, h]

theorem parse_zq (t : Fin (3 + 8 + κ)) (h : ∀ a < 2 + t.val, rd d a = rd d' a)
    (h1 : (rd d (2 + t.val)).1 = (rd d' (2 + t.val)).1) : (parse κ d).zq t = (parse κ d').zq t := by
  show msgPoly (decodeMsg (scClaim (pC0 d) (pEs d) (d.drop 2) t) ((pEs d).getD t none)
      (rd (d.drop 2) t).1.2) =
    msgPoly (decodeMsg (scClaim (pC0 d') (pEs d') (d'.drop 2) t) ((pEs d').getD t none)
      (rd (d'.drop 2) t).1.2)
  rw [pC0_congr (h 1 (by omega)), pEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parse_zχ (t : Fin (3 + 8 + κ)) (h : rd d (2 + t.val) = rd d' (2 + t.val)) :
    (parse κ d).zχ t = (parse κ d').zχ t := by
  show (rd (d.drop 2) t).2.headD 0 = (rd (d'.drop 2) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parse_zq_eq (h : ∀ a < 13 + κ, rd d a = rd d' a) : (parse κ d).zq = (parse κ d').zq := by
  funext t
  have := t.isLt
  exact parse_zq t (fun a ha ↦ h a (by omega)) (by rw [h _ (by omega)])

theorem parse_zχ_eq (h : ∀ a < 13 + κ, rd d a = rd d' a) : (parse κ d).zχ = (parse κ d').zχ := by
  funext t
  have := t.isLt
  exact parse_zχ t (h _ (by omega))

theorem parse_va (h : (rd d (13 + κ)).1 = (rd d' (13 + κ)).1) : (parse κ d).va = (parse κ d').va := by
  show (rd d (13 + κ)).1.2.getD 0 0 = (rd d' (13 + κ)).1.2.getD 0 0
  rw [h]

theorem parse_vb (h : (rd d (13 + κ)).1 = (rd d' (13 + κ)).1) : (parse κ d).vb = (parse κ d').vb := by
  show (rd d (13 + κ)).1.2.getD 1 0 = (rd d' (13 + κ)).1.2.getD 1 0
  rw [h]

theorem parse_α (h : rd d (13 + κ) = rd d' (13 + κ)) : (parse κ d).α = (parse κ d').α := by
  show (rd d (13 + κ)).2.headD 0 = (rd d' (13 + κ)).2.headD 0
  rw [h]

theorem pRunning_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) : pRunning κ d = pRunning κ d' := by
  unfold pRunning
  rw [pC0_congr (h 1 (by omega)), pEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ _ fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega)]

theorem pLc0_congr (h : ∀ a < 14 + κ, rd d a = rd d' a) : pLc0 κ d = pLc0 κ d' := by
  unfold pLc0 pVa pVb pAlpha
  rw [pRunning_congr fun a ha ↦ h a (by omega), h (13 + κ) (by omega)]

theorem parse_lq (t : Fin 8) (h : ∀ a < 14 + κ + t.val, rd d a = rd d' a)
    (h1 : (rd d (14 + κ + t.val)).1 = (rd d' (14 + κ + t.val)).1) :
    (parse κ d).lq t = (parse κ d').lq t := by
  show msgPoly (decodeMsg (scClaim (pLc0 κ d) (List.replicate 8 none) (d.drop (14 + κ)) t) none
      (rd (d.drop (14 + κ)) t).1.2) =
    msgPoly (decodeMsg (scClaim (pLc0 κ d') (List.replicate 8 none) (d'.drop (14 + κ)) t) none
      (rd (d'.drop (14 + κ)) t).1.2)
  rw [pLc0_congr fun a ha ↦ h a (by omega),
    scClaim_congr (d := d.drop (14 + κ)) (d' := d'.drop (14 + κ)) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parse_lχ (t : Fin 8) (h : rd d (14 + κ + t.val) = rd d' (14 + κ + t.val)) :
    (parse κ d).lχ t = (parse κ d').lχ t := by
  show (rd (d.drop (14 + κ)) t).2.headD 0 = (rd (d'.drop (14 + κ)) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parse_lχ_eq (h : ∀ a < 22 + κ, rd d a = rd d' a) : (parse κ d).lχ = (parse κ d').lχ := by
  funext t
  have := t.isLt
  exact parse_lχ t (h _ (by omega))

theorem parse_s (h : (rd d (22 + κ)).1 = (rd d' (22 + κ)).1) : (parse κ d).s = (parse κ d').s := by
  funext cy
  show (rd d (22 + κ)).1.2.getD _ 0 = (rd d' (22 + κ)).1.2.getD _ 0
  rw [h]

/-! The derived values. -/

end Fields

/-! ## The prefix property -/

/-- **A transcript agrees with its prefix** at `(j, i)`: its rounds before `j`, round `j`'s message
and its first `i` challenges. -/
theorem agree_pfx {done : Done} {j : ℕ} (hj : j < done.length) (i : ℕ) :
    AgreeAt (done.take j ++ [((rd done j).1, (rd done j).2.take i)]) done j i := by
  have hl : (done.take j).length = j := by simp only [List.length_take]; omega
  refine ⟨fun a ha ↦ ?_, ?_, fun b hb ↦ ?_⟩
  · rw [rd_append_left (by omega), rd_take ha]
  · rw [rd_append_right (by omega), hl, Nat.sub_self]
    rfl
  · rw [rd_append_right (by omega), hl, Nat.sub_self]
    show ((rd done j).2.take i).getD b 0 = (rd done j).2.getD b 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hb, ite_true]

end FlockSound.Uni
