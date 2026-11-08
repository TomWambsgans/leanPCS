-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import FlockSoundUni.Prefix

/-!
# The bad family catches, given the code's evaluators

`Catches (flockProg κ) (flockBad κ)` is `FlockSound`'s deterministic theorem (`flock_front`) on the
transcript: a completed transcript whose ring claim holds of the column and whose pending claim is
its sum has a satisfied relation, or one of its challenges is in its bad set.

**What it needs of the code** (`Tx`, from the evaluator transcription, another branch): the
evaluators the verifier calls equal the cube forms of `FlockSound`:

* `fixed`: `fixed_challenges` are leanVM's fixed coordinates (`fixedPt`);
* `epow`: `E::pow` is the power;
* `interp`: the skip's `lagrange_interpolate` at `z` is `interp` over `skipNodes 3`;
* `target`: the ring switch's target in tower order is `Σ_cy x^cy Φ_tower(s_cy)`;
* `ring`: the ring claim's weight (`towerCoefficients` on the 64 twists) is `Φ_tower(eq(p, ·))`
  against the column;
* `claim`: `Pending::new`'s claim is `r_lc` plus the terminal's two known terms;
* `sum`: the pending sum (`Pending.G`, `Pending.L` on the setup stacks) is the matrices' part against
  the slices.

Each is stated for every input (the lists the code reads being `List.ofFn` of the cube forms'
functions). **`catches_of_tx`** proves `Catches` from them; **`flockSound_of_tx`** is then the
interface's `FlockSound κ`.

The rest is here: the transcript's shape (`Fits`, from `DoneFits`), the decoded rounds' consistency
(`sc_consistent`, from `decode_consistent`), the code's result as the run's (`outOf_parse`: the
point, the map, the slices, `r_lc`), and each bad event of `Front.Bad` as a hit of `flockBad`
(`hit_of_bad`, by the prefix property).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The transcript's shape -/

theorem doneFits_rd : ∀ {rs : List Compose.RoundSpec} {done : Done}, DoneFits rs done →
    done.length = rs.length ∧ ∀ a (h : a < rs.length),
      (rd done a).1.2.length = rs[a].nv ∧ (rd done a).2.length = rs[a].ns + 1
  | [], [], _ => ⟨rfl, fun _ h ↦ absurd h (by simp)⟩
  | _ :: _, (_, _) :: _, h => by
    obtain ⟨hm, hc, hd⟩ := h
    obtain ⟨hl, hr⟩ := doneFits_rd hd
    refine ⟨by simp [hl], fun a ha ↦ ?_⟩
    cases a with
    | zero => exact ⟨hm.2, hc⟩
    | succ a => exact hr a (by simpa using ha)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem flockRounds_length (κ : ℕ) : (flockRounds κ).length = 23 + κ := by
  simp only [flockRounds, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

theorem flockRounds_getElem (κ a : ℕ) (h : a < (flockRounds κ).length) :
    (flockRounds κ)[a] = if a = 0 then ⟨false, 0, 3 + κ⟩ else if a = 1 then ⟨false, 8, 0⟩
      else if a < 22 + κ then ⟨false, 2, 0⟩ else ⟨false, 64, 5⟩ := by
  have h' : a < 23 + κ := flockRounds_length κ ▸ h
  simp only [flockRounds, List.getElem_append, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil, List.getElem_replicate, List.getElem_cons]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **The transcript's shape**: `23 + κ` rounds, each of its round's reads and draws. -/
structure Fits (κ : ℕ) (done : Done) : Prop where
  len : done.length = 23 + κ
  r0 : (rd done 0).2.length = 4 + κ
  r1v : (rd done 1).1.2.length = 8
  r1c : (rd done 1).2.length = 1
  mid : ∀ a, 2 ≤ a → a < 22 + κ → (rd done a).1.2.length = 2 ∧ (rd done a).2.length = 1
  r6v : (rd done (22 + κ)).1.2.length = 64
  r6c : (rd done (22 + κ)).2.length = 6

theorem fits_of_doneFits {done : Done} (h : DoneFits (flockRounds κ) done) : Fits κ done := by
  obtain ⟨hl, hr⟩ := doneFits_rd h
  have hL := flockRounds_length κ
  have at_ : ∀ a (ha : a < 23 + κ), (rd done a).1.2.length = ((flockRounds κ)[a]'(by omega)).nv ∧
      (rd done a).2.length = ((flockRounds κ)[a]'(by omega)).ns + 1 :=
    fun a ha ↦ hr a (by omega)
  refine ⟨by omega, ?_, ?_, ?_, fun a h2 h22 ↦ ?_, ?_, ?_⟩
  · have := (at_ 0 (by omega)).2
    rw [flockRounds_getElem] at this
    simp only [ite_true] at this
    omega
  · have := (at_ 1 (by omega)).1
    rw [flockRounds_getElem] at this
    simpa using this
  · have := (at_ 1 (by omega)).2
    rw [flockRounds_getElem] at this
    simpa using this
  · have := at_ a (by omega)
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬a = 0), ite_eq_right (by omega : ¬a = 1),
      ite_eq_left h22] at this
    exact this
  · have := (at_ (22 + κ) (by omega)).1
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬22 + κ = 0), ite_eq_right (by omega : ¬22 + κ = 1),
      ite_eq_right (by omega : ¬22 + κ < 22 + κ)] at this
    exact this
  · have := (at_ (22 + κ) (by omega)).2
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬22 + κ = 0), ite_eq_right (by omega : ¬22 + κ = 1),
      ite_eq_right (by omega : ¬22 + κ < 22 + κ)] at this
    exact this

/-! ## The decoded rounds are consistent -/

/-- **A decoded sumcheck is consistent** (`decode_consistent`): from the claim `c₀ = c`, rounds of
two scalars decoded from the claim before them, with the `eq` factors `w`. Its claims are the
decoding's (`scClaim`). -/
theorem sc_consistent {n : ℕ} (c c₀ : E) (hc : c = c₀) (es : List (Option E)) (d : Done)
    (w : Fin n → Option E) (q : Fin n → E[X]) (χ : Fin n → E)
    (hq : ∀ t : Fin n, q t = msgPoly (decodeMsg (scClaim c es d t) (es.getD t none) (rd d t).1.2))
    (hχ : ∀ t : Fin n, χ t = (rd d t).2.headD 0) (hw : ∀ t : Fin n, es.getD t none = w t)
    (h2 : ∀ t : Fin n, (rd d t).1.2.length = 2) :
    (∀ t : Fin (n + 1), claimAt c₀ q χ t = scClaim c es d t) ∧ Consistent 2 w c₀ q χ := by
  have hclaim : ∀ t : Fin (n + 1), claimAt c₀ q χ t = scClaim c es d t := by
    intro t
    refine Fin.cases ?_ (fun s ↦ ?_) t
    · exact hc.symm
    · show (q s).eval (χ s) = scClaim c es d (s.val + 1)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 s)
      rw [scClaim_succ, hq, hχ, hab, (decode_consistent _ _ a b).2.2]
  refine ⟨hclaim, fun s ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 s)
  obtain ⟨hdeg, hL, -⟩ := decode_consistent (scClaim c es d s) (es.getD s none) a b
  rw [hq s, hab]
  refine ⟨hdeg, ?_⟩
  rw [← hw s, hL, hclaim]
  rfl

/-! ## Lists and their functions -/

theorem fin_append_cast {α : Type} {n m : ℕ} (h : n = 7 + m) (a : Fin 7 → α) (b : Fin m → α)
    (t : Fin n) :
    Fin.append a b (Fin.cast h t) = if ht : t.val < 7 then a ⟨t, ht⟩ else b ⟨t - 7, by omega⟩ := by
  split_ifs with ht
  · have e : Fin.cast h t = Fin.castAdd m ⟨t, ht⟩ := Fin.ext rfl
    rw [e, Fin.append_left]
  · have e : Fin.cast h t = Fin.natAdd 7 ⟨t - 7, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, Fin.append_right]

theorem ofFn_three_parts {α : Type} {a b c : ℕ} (x : Fin (a + b + c) → α) :
    (List.ofFn x).take a = List.ofFn (lowPart (lowPart x)) ∧
      ((List.ofFn x).drop a).take b = List.ofFn (highPart (lowPart x)) ∧
      ((List.ofFn x).drop a).drop b = List.ofFn (highPart x) := by
  have e : List.ofFn x =
      List.ofFn (lowPart (lowPart x)) ++ (List.ofFn (highPart (lowPart x)) ++ List.ofFn (highPart x)) := by
    rw [← List.append_assoc, ← List.ofFn_fin_append, append_lowPart_highPart, ← List.ofFn_fin_append,
      append_lowPart_highPart]
  rw [e]
  refine ⟨List.take_left' (by simp), ?_, ?_⟩
  · rw [List.drop_left' (by simp)]
    exact List.take_left' (by simp)
  · rw [List.drop_left' (by simp)]
    exact List.drop_left' (by simp)

/-- The 64 slices as the code reads them: slice `i` at the cube point of `i`'s bits. -/
def sliceList (s : Cube (3 + 3) → E) : List E :=
  List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)

theorem eq_sliceList {l : List E} (h : l.length = 64) :
    l = sliceList fun cy ↦ l.getD (cubeFin (3 + 3) cy) 0 := by
  conv_lhs => rw [eq_ofFn_getD h 0]
  rw [sliceList]
  congr 1
  funext i
  simp only [Equiv.apply_symm_apply]

/-! ## What the code's evaluators must be -/

/-! ## The code's result is the run's -/

theorem outOf_eq (d : Done) :
    outOf κ d = flockOut (pSampled d) (pCoset d) (pZ d) ((d.drop 2).take (11 + κ)) (pVa κ d)
      (pVb κ d) (pAlpha κ d) ((d.drop (14 + κ)).take 8) (rd d (22 + κ)).1.2 (rd d (22 + κ)).2 := by
  simp only [outOf, rd_drop, Nat.add_zero]
  rfl

theorem flockOut_of (sampled coset : List E) (z : E) (zc : Done) (vA vB α : E) (lc : Done)
    (slices map zs ls : List E) (running rLc : E)
    (hzr : decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
      ((Flock.fixedChallenges ++ sampled).map some) zc = (zs, running))
    (hlr : decodeSC (vA + α * vB + epow α 2 * (running + vA * vB) + epow α 3) (List.replicate 8 none) lc =
      (ls, rLc)) :
    flockOut sampled coset z zc vA vB α lc slices map =
      (ls.reverse ++ (zs.drop 3).drop 8, some (.ring map (Flock.towerTarget slices map)),
        Flock.Pending.new (some z) (zs.take 3) ((zs.drop 3).take 8) ls.reverse α rLc (some slices)) := by
  simp only [flockOut, hzr, hlr]

theorem getD_replicate_none (t : Fin 8) : (List.replicate 8 (none : Option E)).getD t none = none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, t.isLt, ite_true, Option.getD_some]

section Run

variable {done : Done} (hF : Fits κ done)
include hF

theorem decode_zc :
    decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ pCoset done) (pZ done))
        ((Flock.fixedChallenges ++ pSampled done).map some) ((done.drop 2).take (11 + κ)) =
      (List.ofFn (parse κ done).zχ, pRunning κ done) := by
  have hl : ((done.drop 2).take (11 + κ)).length = 11 + κ := by
    simp only [List.length_take, List.length_drop, hF.len]
    omega
  have hes : ((Flock.fixedChallenges ++ pSampled done).map some).length = 11 + κ := by
    simp only [List.length_map, List.length_append, length_fixedChallenges, pSampled, hF.r0]
    omega
  rw [decodeSC_eq _ _ _ (hl.trans hes.symm), hes, map_eq_ofFn hl noRound]
  congr 1
  · congr 1
    funext t
    show (rd ((done.drop 2).take (11 + κ)) t).2.headD 0 = (rd (done.drop 2) t).2.headD 0
    rw [rd_take t.isLt]
  · exact scClaim_congr _ _ _ fun v hv ↦ rd_take hv

end Run

/-! ## Each bad event is a hit -/

/-! ## The catch, and the interface -/

/-! ## The rounds' errors -/

/-- **Round `j`'s error, times `|E|`**: `4 + κ` for `τ` (one value per coordinate), `15` for `z`,
`2` for each zerocheck round, `3` for `α`, `2` for each lincheck round, `6` for the ring map. -/
def roundErr (κ j : ℕ) : ℕ :=
  if j = 0 then 4 + κ else if j = 1 then 15 else if j < 13 + κ then 2 else if j = 13 + κ then 3
  else if j < 22 + κ then 2 else 6

theorem roundErr_zc {j : ℕ} (h1 : 2 ≤ j) (h2 : j < 13 + κ) : roundErr κ j = 2 := by
  unfold roundErr
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

theorem roundErr_lin {j : ℕ} (h1 : 14 + κ ≤ j) (h2 : j < 22 + κ) : roundErr κ j = 2 := by
  unfold roundErr
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left h2]

theorem sum_roundErr (κ : ℕ) : ∑ j ∈ range (23 + κ), roundErr κ j = 66 + 3 * κ := by
  rw [show 23 + κ = 2 + ((11 + κ) + (1 + (8 + 1))) by omega,
    Finset.sum_range_add (roundErr κ) 2, Finset.sum_range_add _ (11 + κ), Finset.sum_range_add _ 1,
    Finset.sum_range_add _ 8]
  have e2 : ∑ x ∈ range 2, roundErr κ x = 19 + κ := by
    have h0 : roundErr κ 0 = 4 + κ := by unfold roundErr; rw [ite_eq_left rfl]
    have h1 : roundErr κ 1 = 15 := by unfold roundErr; rw [ite_eq_right (by omega), ite_eq_left rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    omega
  have hzc : ∀ x ∈ range (11 + κ), roundErr κ (2 + x) = 2 := fun x hx ↦
    roundErr_zc (by omega) (by have := Finset.mem_range.mp hx; omega)
  have hlin : ∀ x ∈ range 8, roundErr κ (2 + (11 + κ + (1 + x))) = 2 := fun x hx ↦
    roundErr_lin (by omega) (by have := Finset.mem_range.mp hx; omega)
  have eα : roundErr κ (2 + (11 + κ + 0)) = 3 := by
    unfold roundErr
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  have er : roundErr κ (2 + (11 + κ + (1 + (8 + 0)))) = 6 := by
    unfold roundErr
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [e2, Finset.sum_congr rfl hzc, Finset.sum_congr rfl hlin, Finset.sum_range_one,
    Finset.sum_range_one, eα, er]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

end FlockSound.Uni
