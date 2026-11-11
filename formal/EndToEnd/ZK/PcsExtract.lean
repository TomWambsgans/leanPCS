-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. Byte lemmas from leanerVM `mumbai` (6175f1a0, MIT OR Apache-2.0: `common/Common/Lanes.lean`).
import ZK.PcsPhaseF
import ZK.PcsRoot
import VCVio.OracleComp.Constructions.UniformFinMeasure

/-!
# A challenge from a uniform state is uniform

A challenge of the chain (`challengeOf`) and a coordinate of an out-of-domain point (`elementOf` of the digest's
last 24 bytes) are the same function of a state's lanes `1, 2, 3`, byte-reversed (`challengeOf_digestOf`,
`elementOf_digestOf`). A state is a uniform element of `E` placed in those lanes and 22 uniform words in the others
(`mk`, a bijection), so a uniform state is that pair (`uState_eq_mkDist`), and its challenge is the element.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- A word with its bytes reversed. -/
def bsw (w : UInt64) : UInt64 := LeanVM.Rpm.bytesLane (wordBytes w).reverse

theorem wordBytes_bytesLane_of_length {b : List UInt8} (hb : b.length = 8) : wordBytes (LeanVM.Rpm.bytesLane b) = b := by
  rw [LeanVM.Rpm.wordBytes_bytesLane]
  match b, hb with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem bsw_bsw (w : UInt64) : bsw (bsw w) = w := by
  unfold bsw
  rw [wordBytes_bytesLane_of_length (by simp [LeanVM.Rpm.wordBytes_len]), List.reverse_reverse]
  simpa using LeanVM.Rpm.bytesLane_wordBytes_append w []

theorem bsw_injective : Function.Injective bsw := fun a b h ↦ by
  rw [← bsw_bsw a, h, bsw_bsw]

theorem beWord_lanesBytes (l : List UInt64) (i k : ℕ) (hk : k = 8 * i) (hi : i < l.length) :
    beWord (LeanVM.Rpm.lanesBytes l) k = bsw l[i] := by
  subst hk
  rw [beWord_eq_bytesLane, bsw]
  congr 2
  have : ∀ j ∈ List.range 8, (LeanVM.Rpm.lanesBytes l).getD (8 * i + j) 0 = (l[i] >>> (8 * j).toUInt64).toUInt8 := by
    intro j hj
    have hj' : j < 8 := List.mem_range.1 hj
    rw [LeanVM.Rpm.getD_lanesBytes _ _ (by omega)]
    have h1 : (8 * i + j) / 8 = i := by omega
    have h2 : (8 * i + j) % 8 = j := by omega
    simp only [h1, h2]
    rw [LeanVM.Rpm.wordBytes_getD _ _ hj']
  rw [List.map_congr_left this]
  rfl

/-- The common form of a challenge and an out-of-domain coordinate: lanes `3, 2, 1` byte-reversed, as limbs. -/
def laneE (d : Digest) : E := E.ofLimbs (K.ofLane (bsw d[3])) (K.ofLane (bsw d[2])) (K.ofLane (bsw d[1]))

theorem challengeOf_eq (d : Digest) : challengeOf d = laneE d := by
  have hb : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  simp only [challengeOf, laneE, hb]
  rw [beWord_lanesBytes _ 3 24 rfl (by simp), beWord_lanesBytes _ 2 16 rfl (by simp),
    beWord_lanesBytes _ 1 8 rfl (by simp)]
  simp

theorem elementOf_eq (d : Digest) : elementOf ((digestBytes d).drop 8) = laneE d := by
  have hb : (digestBytes d).drop 8 = LeanVM.Rpm.lanesBytes (d.toList.drop 1) := by
    rw [show digestBytes d = LeanVM.Rpm.lanesBytes d.toList from rfl, show (8 : ℕ) = 8 * 1 from rfl,
      LeanVM.Rpm.drop_lanesBytes]
  simp only [elementOf, laneE, hb]
  rw [beWord_lanesBytes _ 2 16 rfl (by simp), beWord_lanesBytes _ 1 8 rfl (by simp),
    beWord_lanesBytes _ 0 0 rfl (by simp)]
  simp

/-- **A state from an element of `E` and 22 words**: the element's limbs `2, 1, 0` byte-reversed in lanes `1, 2, 3`,
the words in lanes `0, 4, …, 24`. -/
def mk (e : E) (w : Vector UInt64 22) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦
    if i.val = 1 then bsw (e.limb 2).lane else if i.val = 2 then bsw (e.limb 1).lane
    else if i.val = 3 then bsw (e.limb 0).lane else w.toList.getD (if i.val = 0 then 0 else i.val - 3) 0

/-- The element and the words of a state. -/
def unmk (y : KeccakState) : E × Vector UInt64 22 :=
  (E.ofLimbs (K.ofLane (bsw y[3])) (K.ofLane (bsw y[2])) (K.ofLane (bsw y[1])),
    Vector.ofFn fun j : Fin 22 ↦ if j.val = 0 then y[0] else y.toList.getD (j.val + 3) 0)

theorem mk_get (e : E) (w : Vector UInt64 22) (i : ℕ) (hi : i < 25) :
    (mk e w)[i] = if i = 1 then bsw (e.limb 2).lane else if i = 2 then bsw (e.limb 1).lane
      else if i = 3 then bsw (e.limb 0).lane else w.toList.getD (if i = 0 then 0 else i - 3) 0 := by
  simp only [mk, Vector.getElem_ofFn]

theorem digestOf_get1 (y : KeccakState) : (digestOf y)[1] = Keccak.lane y 1 := rfl
theorem digestOf_get2 (y : KeccakState) : (digestOf y)[2] = Keccak.lane y 2 := rfl
theorem digestOf_get3 (y : KeccakState) : (digestOf y)[3] = Keccak.lane y 3 := rfl

theorem lane_mk1 (e : E) (w : Vector UInt64 22) : Keccak.lane (mk e w) 1 = bsw (e.limb 2).lane := by
  rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega), mk_get _ _ _ (by omega), ite_eq_left rfl]

theorem lane_mk2 (e : E) (w : Vector UInt64 22) : Keccak.lane (mk e w) 2 = bsw (e.limb 1).lane := by
  rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega), mk_get _ _ _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem lane_mk3 (e : E) (w : Vector UInt64 22) : Keccak.lane (mk e w) 3 = bsw (e.limb 0).lane := by
  rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega), mk_get _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left rfl]

theorem laneE_digestOf_mk (e : E) (w : Vector UInt64 22) : laneE (digestOf (mk e w)) = e := by
  rw [laneE, digestOf_get1, digestOf_get2, digestOf_get3, lane_mk1, lane_mk2, lane_mk3, bsw_bsw, bsw_bsw,
    bsw_bsw]
  exact ofLimbs_limb e

theorem toList_ofFn_getD {n : ℕ} (f : Fin n → UInt64) (j : ℕ) (hj : j < n) :
    (Vector.ofFn f).toList.getD j 0 = f ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem toList_getD {n : ℕ} (v : Vector UInt64 n) (j : ℕ) (hj : j < n) : v.toList.getD j 0 = v[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem mk_unmk (y : KeccakState) : mk (unmk y).1 (unmk y).2 = y := by
  apply Vector.ext
  intro i hi
  rw [mk_get _ _ _ hi]
  simp only [unmk]
  have l0 : ∀ a b c : K, (E.ofLimbs a b c).limb 0 = a := fun _ _ _ ↦ rfl
  have l1 : ∀ a b c : K, (E.ofLimbs a b c).limb 1 = b := fun _ _ _ ↦ rfl
  have l2 : ∀ a b c : K, (E.ofLimbs a b c).limb 2 = c := fun _ _ _ ↦ rfl
  have hl : ∀ w : UInt64, (K.ofLane w).lane = w := fun _ ↦ rfl
  rw [l0, l1, l2, hl, hl, hl, bsw_bsw, bsw_bsw, bsw_bsw]
  by_cases h1 : i = 1
  · subst h1; rfl
  by_cases h2 : i = 2
  · subst h2; rfl
  by_cases h3 : i = 3
  · subst h3; rfl
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  by_cases h0 : i = 0
  · subst h0
    rw [ite_eq_left rfl, toList_ofFn_getD _ 0 (by omega)]
    simp
  · have h4 : i - 3 ≠ 0 := by omega
    rw [ite_eq_right h0, toList_ofFn_getD _ (i - 3) (by omega)]
    simp only [h4, ↓reduceIte]
    rw [show i - 3 + 3 = i by omega, toList_getD _ _ hi]

theorem unmk_mk (e : E) (w : Vector UInt64 22) : unmk (mk e w) = (e, w) := by
  have h1 : (mk e w)[1] = bsw (e.limb 2).lane := by rw [mk_get _ _ _ (by omega), ite_eq_left rfl]
  have h2 : (mk e w)[2] = bsw (e.limb 1).lane := by rw [mk_get _ _ _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  have h3 : (mk e w)[3] = bsw (e.limb 0).lane := by
    rw [mk_get _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  have hol : ∀ a : K, K.ofLane a.lane = a := fun _ ↦ rfl
  simp only [unmk, h1, h2, h3, bsw_bsw, hol, ofLimbs_limb, Prod.mk.injEq, true_and]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn]
  by_cases h0 : j = 0
  · subst h0
    rw [ite_eq_left rfl, mk_get _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left rfl, toList_getD _ _ (by omega)]
  · have a1 : j + 3 ≠ 1 := by omega
    have a2 : j + 3 ≠ 2 := by omega
    have a3 : j + 3 ≠ 3 := by omega
    have a0 : j + 3 ≠ 0 := by omega
    rw [ite_eq_right h0, toList_getD _ _ (by omega), mk_get _ _ _ (by omega)]
    simp only [a1, a2, a3, a0, ↓reduceIte]
    rw [show j + 3 - 3 = j by omega, toList_getD _ _ hj]

theorem mk_injective : Function.Injective fun p : E × Vector UInt64 22 ↦ mk p.1 p.2 := fun a b h ↦ by
  have := congrArg unmk h
  simp only [unmk_mk] at this
  exact this

/-! ### Uniform words, elements, states -/

/-- A uniform word, as `ProbComp` runs the model's coin. -/
noncomputable def cwDist : ProbComp UInt64 := simulateQ coinsOf coinWord

/-- The mass of a word. -/
noncomputable def c64 : ℝ≥0∞ := (((2 ^ 64 - 1 : ℕ) : ℝ≥0∞) + 1)⁻¹

theorem cwDist_eq : cwDist = (fun n : Fin (2 ^ 64 - 1 + 1) ↦ UInt64.ofNat n.val) <$> ProbComp.uniformFin (2 ^ 64 - 1) := by
  simp only [cwDist, coinWord, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, coinsOf]
  rw [map_eq_bind_pure_comp]
  rfl

theorem prEvent_cwDist (w : UInt64) : Pr{let x ← cwDist}[x = w] = c64 := by
  have hinj : Function.Injective fun n : Fin (2 ^ 64 - 1 + 1) ↦ UInt64.ofNat n.val := fun a b h ↦ by
    have ha := a.isLt; have hb := b.isLt
    have := congrArg UInt64.toNat h
    simp only at this
    rw [UInt64.toNat_ofNat_of_lt' (by simp at ha ⊢), UInt64.toNat_ofNat_of_lt' (by simp at hb ⊢)] at this
    exact Fin.ext this
  have hw : w = UInt64.ofNat (⟨w.toNat, by have := w.toNat_lt; omega⟩ : Fin (2 ^ 64 - 1 + 1)).val := by simp
  rw [cwDist_eq, hw, prEvent_map_injective _ hinj, c64]
  classical
  rw [ProbComp.prEvent_uniformFin]
  rw [Finset.filter_eq', ite_eq_left (Finset.mem_univ _), Finset.card_singleton, Nat.cast_one, one_div]

theorem prEvent_pair {α β : Type} (X : ProbComp α) (Y : ProbComp β) (a : α) (b : β) :
    Pr{let p ← (do let x ← X; let y ← Y; pure (x, y))}[p = (a, b)] = Pr{let x ← X}[x = a] * Pr{let y ← Y}[y = b] := by
  classical
  rw [prEvent_bind_eq_tsum]
  have h : ∀ x, Pr{let z ← X}[z = x] * Pr{let p ← (do let y ← Y; pure (x, y))}[p = (a, b)] =
      if x = a then Pr{let z ← X}[z = a] * Pr{let y ← Y}[y = b] else 0 := by
    intro x
    split_ifs with hx
    · subst hx
      congr 1
      rw [show (Y >>= fun y ↦ pure (x, y)) = Prod.mk x <$> Y by rw [map_eq_bind_pure_comp]; rfl]
      exact prEvent_map_injective Y (fun u v h ↦ (Prod.mk.inj h).2) b
    · rw [(prEvent_eq_zero_iff (do let y ← Y; pure (x, y)) (· = (a, b))).2 fun p hp h ↦ ?_, mul_zero]
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
      obtain ⟨y, -, rfl⟩ := hp
      exact hx (Prod.mk.inj h).1
  rw [tsum_congr h, tsum_ite_eq]

/-- A uniform element of `E`, as `ProbComp` runs the model's coins. -/
theorem eDist_eq : eDist = (fun t : UInt64 × UInt64 × UInt64 ↦ E.ofLimbs (K.ofLane t.1) (K.ofLane t.2.1) (K.ofLane t.2.2))
    <$> (do let a ← cwDist; let t ← (do let b ← cwDist; let c ← cwDist; pure (b, c)); pure (a, t)) := by
  simp only [eDist, coinE, simulateQ_bind, simulateQ_pure, map_bind, bind_assoc, pure_bind, map_pure]
  rfl

theorem prEvent_eDist (e : E) : Pr{let x ← eDist}[x = e] = c64 * (c64 * c64) := by
  have hinj : Function.Injective fun t : UInt64 × UInt64 × UInt64 ↦
      E.ofLimbs (K.ofLane t.1) (K.ofLane t.2.1) (K.ofLane t.2.2) := fun a b h ↦ by
    have h0 := congrArg (fun x : E ↦ (x.limb 0).lane) h
    have h1 := congrArg (fun x : E ↦ (x.limb 1).lane) h
    have h2 := congrArg (fun x : E ↦ (x.limb 2).lane) h
    exact Prod.ext h0 (Prod.ext h1 h2)
  have he : e = E.ofLimbs (K.ofLane ((e.limb 0).lane, (e.limb 1).lane, (e.limb 2).lane).1)
      (K.ofLane ((e.limb 0).lane, (e.limb 1).lane, (e.limb 2).lane).2.1)
      (K.ofLane ((e.limb 0).lane, (e.limb 1).lane, (e.limb 2).lane).2.2) := (ofLimbs_limb e).symm
  rw [eDist_eq, he, prEvent_map_injective _ hinj, prEvent_pair, prEvent_pair, prEvent_cwDist, prEvent_cwDist,
    prEvent_cwDist]

/-- Uniform words for the other lanes. -/
noncomputable def wDist : ProbComp (Vector UInt64 22) := $ᵗ (Vector UInt64 22)

/-- **A uniform state, as an element and words.** -/
noncomputable def mkDist : ProbComp KeccakState := do
  let e ← eDist
  let w ← wDist
  pure (mk e w)

theorem prEvent_mkDist (y : KeccakState) :
    Pr{let x ← mkDist}[x = y] = c64 * (c64 * c64) * (Fintype.card (Vector UInt64 22) : ℝ≥0∞)⁻¹ := by
  have h : mkDist = (fun p : E × Vector UInt64 22 ↦ mk p.1 p.2) <$> (do let e ← eDist; let w ← wDist; pure (e, w)) := by
    simp only [mkDist, map_bind, map_pure]
  rw [h, ← mk_unmk y, prEvent_map_injective _ mk_injective, prEvent_pair, prEvent_eDist, wDist,
    SampleableType.prEvent_uniformSample_eq_singleton]

theorem evalDistEq_of_const {T : Type} [Fintype T] [Nonempty T] (X Y : ProbComp T) (k k' : ℝ≥0∞)
    (hX : ∀ y, Pr{let x ← X}[x = y] = k) (hY : ∀ y, Pr{let x ← Y}[x = y] = k') : X =ᵈ Y := by
  have hc : (Fintype.card T : ℝ≥0∞) ≠ 0 := by simp
  have h1 : (Fintype.card T : ℝ≥0∞) * k = 1 := by
    rw [← tsum_prEvent_eq_one X, tsum_fintype, Finset.sum_congr rfl fun y _ ↦ hX y, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have h2 : (Fintype.card T : ℝ≥0∞) * k' = 1 := by
    rw [← tsum_prEvent_eq_one Y, tsum_fintype, Finset.sum_congr rfl fun y _ ↦ hY y, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hk : k = k' := (ENNReal.mul_right_inj hc (ENNReal.natCast_ne_top _)).1 (h1.trans h2.symm)
  exact (evalDistEq_iff_forall_prEvent_eq_output).2 fun y ↦ by rw [hX, hY, hk]

/-- **A uniform state is a uniform element and uniform words.** -/
theorem uState_eq_mkDist : uState =ᵈ mkDist :=
  evalDistEq_of_const _ _ _ _ prEvent_uState prEvent_mkDist

end PcsQuotient.EndToEnd
