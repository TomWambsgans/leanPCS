-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The split of the bad challenges (a
-- vanishing denominator, the log-derivative sum, the fingerprints in `γ`) follows
-- `formal/QuotientSecurity/Counting.lean` (crates/membership/quotient's copy argument).
import RecPiop.Circuit
import RecPiop.LogUp

/-!
# π2's copy argument and the ports (π2v2)

`PI2.md` §1, §7: on `V_m`, the identity `h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T = 0` with
`d_pull = α + w + βx`, `d_push = α + P + κ + βσ` (`P = P_v` there: the internal pushes, a hole's own value at a
hole), and `T` the ports' term, `E_p + F_J` at the hole of port `J` and zero elsewhere; and `Σ_V h = 0`.

* **The copy argument over the internal positions**: a non-hole `i` pulls `(w_i, ω_i)` and pushes
  `(P_i, ω_{σ_i})` (`entries`, `entryVal`); `σ` is a bijection of the non-holes, so every tag of the family is one
  pull and one push (`copy_of_even`): if the family is even, every non-hole's pull is the push meant for it.
* **The holes**: at a hole `x₀` of port `j` the identity is `h d_pull d_push = T(x₀)`, `d_pull = α + w(x₀) + β x₀`
  (the pole `a_j`) and `d_push = α + w(x₀) + β τ_j` (the pole `b_j`, to the outside tag): `h(x₀) = c_j/(d(a_j)
  d(b_j))`, `c_j = E_p(x₀) + F_j` (`tVal`). No other fraction has the pole `a_j` (no pull's tag is a hole, no push
  targets one) or `b_j`.
* **The sum** (`logSum_of_copyOK`): where no denominator vanishes, `Σ_V h` is the family's log-derivative sum plus
  `Σ_j c_j/(d(a_j) d(b_j))`; LogUp with poles (`RecPiop.card_poles_eq_zero_le`) bounds the points where it is zero
  unless the family is even and every `c_j` zero, that is unless the copy constraints hold and every port's
  fingerprint is its public one.
* **`card_copyOK_le`**: if the witness does not satisfy the circuit, at most `(4N − 1 + Σ_j d_j)·|F|²` triples
  `(α, β, γ)` reach `CopyOK`: `(N + nP)|F|²` where a denominator vanishes (a pull's, a hole's push), `(2N − 1)|F|²`
  where the sum with poles is zero but not as a rational function, and `d_j |F|²` where port `j`'s limbs differ from
  the public ones but their fingerprints agree at `γ` (`hbind`; `RecPiop.Ports`). **`prob_copyOK_le`**: probability
  at most `(4N − 1 + Σ_j d_j)/|F|` at a uniform `(α, β, γ)`.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset

/-- **An entry of the copy argument**: an internal position's pull or push. -/
inductive Entry where
  | pull (i : ℕ)
  | push (i : ℕ)
deriving DecidableEq

namespace Circuit

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F] (G : Circuit F)

/-! ## The family -/

/-- **The internal positions**: the non-holes of `[0, N)`. -/
def internal : Finset ℕ := (range G.N).filter fun i => ¬ G.IsHole i

/-- **The copy argument's entries**: a pull and a push at every internal position. -/
def entries : Finset Entry := G.internal.image Entry.pull ∪ G.internal.image Entry.push

/-- **An entry's (value, tag) pair**, the tags the points `ω`. A non-hole's push does not read `γ`
(`push_gamma`): it is taken at `0`. -/
def entryVal (ω : ℕ → F) (w : ℕ → F) : Entry → F × F
  | .pull i => (w i, ω i)
  | .push i => (G.push w 0 i, ω (G.sigma i))

theorem mem_internal {i : ℕ} : i ∈ G.internal ↔ i < G.N ∧ ¬ G.IsHole i := by
  simp [internal]

theorem mem_entries (z : Entry) : z ∈ G.entries ↔
    (∃ i < G.N, ¬ G.IsHole i ∧ z = .pull i) ∨ (∃ i < G.N, ¬ G.IsHole i ∧ z = .push i) := by
  simp only [entries, Finset.mem_union, Finset.mem_image, mem_internal]
  constructor
  · rintro (⟨i, ⟨hi, hh⟩, rfl⟩ | ⟨i, ⟨hi, hh⟩, rfl⟩)
    · exact Or.inl ⟨i, hi, hh, rfl⟩
    · exact Or.inr ⟨i, hi, hh, rfl⟩
  · rintro (⟨i, hi, hh, rfl⟩ | ⟨i, hi, hh, rfl⟩)
    · exact Or.inl ⟨i, ⟨hi, hh⟩, rfl⟩
    · exact Or.inr ⟨i, ⟨hi, hh⟩, rfl⟩

variable {G}

/-! ## Ports and holes -/

theorem port_eq_getElem {j : ℕ} (hj : j < G.nP) : G.port j = G.ports[j] := by
  unfold port
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem port_lt (hV : G.Valid) {j : ℕ} (hj : j < G.nP) : G.port j < G.N ∧ G.IsHole (G.port j) := by
  rw [port_eq_getElem hj]
  exact (hV.ports_holes _).mp (List.getElem_mem _)

theorem port_inj (hV : G.Valid) {j j' : ℕ} (hj : j < G.nP) (hj' : j' < G.nP)
    (h : G.port j = G.port j') : j = j' := by
  rw [port_eq_getElem hj, port_eq_getElem hj'] at h
  exact (hV.ports_nodup.getElem_inj_iff).mp h

theorem exists_port_of_hole (hV : G.Valid) {i : ℕ} (hi : i < G.N) (hh : G.IsHole i) :
    ∃ j < G.nP, G.port j = i := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem ((hV.ports_holes i).mpr ⟨hi, hh⟩)
  exact ⟨j, hj, by rw [port_eq_getElem hj, he]⟩

/-- **There are as many holes as ports.** -/
theorem card_holes (hV : G.Valid) : ((range G.N).filter G.IsHole).card = G.nP := by
  have : (range G.N).filter G.IsHole = G.ports.toFinset := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, hV.ports_holes]
  rw [this, List.toFinset_card_of_nodup hV.ports_nodup]
  rfl

theorem nP_le (hV : G.Valid) : G.nP ≤ G.N := by
  rw [← card_holes hV]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem N_pos : 0 < G.N := Nat.two_pow_pos _

theorem card_internal (hV : G.Valid) : G.internal.card = G.N - G.nP := by
  have := Finset.card_filter_add_card_filter_not (s := range G.N) G.IsHole
  rw [card_holes hV, Finset.card_range] at this
  unfold internal
  omega

/-- **The family has `2(N − nP)` entries.** -/
theorem card_entries_le (hV : G.Valid) : G.entries.card ≤ 2 * (G.N - G.nP) := by
  unfold entries
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := G.internal) (f := Entry.pull)
  have h2 := Finset.card_image_le (s := G.internal) (f := Entry.push)
  rw [card_internal hV] at h1 h2
  omega

/-- **A sum over the holes is a sum over the ports.** -/
theorem sum_holes (hV : G.Valid) {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ (range G.N).filter G.IsHole, f i = ∑ j ∈ range G.nP, f (G.port j) := by
  symm
  refine Finset.sum_nbij G.port (fun j hj => ?_) (fun j hj j' hj' h => ?_) (fun i hi => ?_) (fun _ _ => rfl)
  · have := port_lt hV (Finset.mem_range.mp hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr this.1, this.2⟩
  · exact port_inj hV (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') h
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨j, hj, he⟩ := exists_port_of_hole hV hi.1 hi.2
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr hj), he⟩

/-! ## The values on `V_m` -/

variable (G)

/-- **A position's push value on `V_m`** in π2v2's `d_push`: `P_v + κ`, the push at a non-hole and the hole's own
value at a hole (`κ` is zero there). -/
def pushV (w : ℕ → F) (i : ℕ) : F := if G.IsHole i then w i else G.push w 0 i

/-- **The ports' term on `V_m`**: `E_p(x₀) + F_j` at the hole `x₀` of port `j`, zero elsewhere. -/
def tVal (pub : ℕ → List F) (w : ℕ → F) (γ : F) (i : ℕ) : F :=
  ∑ j ∈ range G.nP, if G.port j = i then G.push w γ i + G.pubFp γ pub j else 0

variable (ω : ℕ → F)

/-- A pull's denominator `α + w_i + β ω_i`. -/
def _root_.RecPiop.dPull (w : ℕ → F) (α β : F) (i : ℕ) : F := den α β (w i, ω i)

/-- **A push's denominator** `α + P_i + β ω_{σ_i}` (π2v2: `P_i` the push value `pushV`). -/
def dPushV (w : ℕ → F) (α β : F) (i : ℕ) : F := den α β (G.pushV w i, ω (G.sigma i))

/-- **The holes' indicator** `1_S` on positions. -/
def holeInd (i : ℕ) : F := if G.IsHole i then 1 else 0

/-- **The identity at position `i`**, for a value `h_i` of `h`:
`h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T = 0` (`q Z_V` vanishes on `V_m`). -/
def PointId (pub : ℕ → List F) (w : ℕ → F) (α β γ hv : F) (i : ℕ) : Prop :=
  hv * dPull ω w α β i * G.dPushV ω w α β i + (1 + G.holeInd i) * (G.dPushV ω w α β i + dPull ω w α β i) +
    G.tVal pub w γ i = 0

/-- **The state after `α, β, γ`**: some values of `h` on `V_m` meet the identity at every position and sum to
zero. -/
def CopyOK (pub : ℕ → List F) (w : ℕ → F) (α β γ : F) : Prop :=
  ∃ hv : ℕ → F, (∀ i < G.N, G.PointId ω pub w α β γ (hv i) i) ∧ ∑ i ∈ range G.N, hv i = 0

/-- The poles of port `j`'s term: its hole's pull pair `a_j` and push pair `b_j`. -/
def poleA (w : ℕ → F) (j : ℕ) : F × F := (w (G.port j), ω (G.port j))
def poleB (w : ℕ → F) (j : ℕ) : F × F := (w (G.port j), ω (G.N + j))

/-- Port `j`'s term on `V_m`, `c_j = E_p(x₀) + F_j`. -/
def portC (pub : ℕ → List F) (w : ℕ → F) (γ : F) (j : ℕ) : F := G.push w γ (G.port j) + G.pubFp γ pub j

variable {G}

theorem tVal_port (hV : G.Valid) (pub : ℕ → List F) (w : ℕ → F) (γ : F) {j : ℕ} (hj : j < G.nP) :
    G.tVal pub w γ (G.port j) = G.push w γ (G.port j) + G.pubFp γ pub j := by
  unfold tVal
  rw [Finset.sum_eq_single j (fun j' hj' hne => by
      rw [ite_eq_right fun h => hne (port_inj hV (Finset.mem_range.mp hj') hj h)])
    (fun h => absurd (Finset.mem_range.mpr hj) h), ite_eq_left rfl]

theorem tVal_internal (hV : G.Valid) (pub : ℕ → List F) (w : ℕ → F) (γ : F) {i : ℕ} (hh : ¬ G.IsHole i) :
    G.tVal pub w γ i = 0 :=
  Finset.sum_eq_zero fun j hj => by
    rw [ite_eq_right fun h => hh (by rw [← h]; exact (port_lt hV (Finset.mem_range.mp hj)).2)]

theorem dPushV_port (hV : G.Valid) (w : ℕ → F) (α β : F) {j : ℕ} (hj : j < G.nP) :
    G.dPushV ω w α β (G.port j) = den α β (w (G.port j), ω (G.N + j)) := by
  unfold dPushV pushV
  rw [ite_eq_left (port_lt hV hj).2, hV.sigma_port j hj]

/-- **The identity at a non-hole, solved**: where the pull's denominator is not zero, the push's is not either,
and `h_i = 1/d_pull + 1/d_push`. -/
theorem hv_internal (hV : G.Valid) {pub : ℕ → List F} {w : ℕ → F} {α β γ hv : F} {i : ℕ}
    (hh : ¬ G.IsHole i) (h : G.PointId ω pub w α β γ hv i) (hp : dPull ω w α β i ≠ 0) :
    G.dPushV ω w α β i ≠ 0 ∧ hv = (dPull ω w α β i)⁻¹ + (G.dPushV ω w α β i)⁻¹ := by
  unfold PointId holeInd at h
  rw [ite_eq_right hh, tVal_internal hV pub w γ hh, add_zero, add_zero, one_mul] at h
  set a := dPull ω w α β i
  set b := G.dPushV ω w α β i
  have h1 : hv * a * b = b + a := CharTwo.add_eq_zero.mp (by rw [← h]; try ring)
  have hb : b ≠ 0 := fun h0 => by
    rw [h0, mul_zero, zero_add] at h1
    exact hp h1.symm
  refine ⟨hb, ?_⟩
  field_simp
  linear_combination h1

/-- **The identity at a hole, solved**: where both denominators are nonzero, `h(x₀) = T(x₀)/(d_pull d_push)`. -/
theorem hv_hole {pub : ℕ → List F} {w : ℕ → F} {α β γ hv : F} {i : ℕ} (hh : G.IsHole i)
    (h : G.PointId ω pub w α β γ hv i) (hp : dPull ω w α β i ≠ 0) (hq : G.dPushV ω w α β i ≠ 0) :
    hv = G.tVal pub w γ i * (dPull ω w α β i * G.dPushV ω w α β i)⁻¹ := by
  unfold PointId holeInd at h
  rw [ite_eq_left hh, CharTwo.add_self_eq_zero, zero_mul, add_zero] at h
  rw [eq_mul_inv_iff_mul_eq₀ (mul_ne_zero hp hq), ← mul_assoc]
  exact CharTwo.add_eq_zero.mp h

/-! ## Every tag twice -/

/-- **The copy argument's conclusion from the family zero mod 2**: every non-hole's pull is the push meant for
it. -/
theorem copy_of_even (hV : G.Valid) (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b) (w : ℕ → F)
    (hev : EvenAll G.entries (G.entryVal ω w)) :
    ∀ i < G.N, ¬ G.IsHole i → w (G.sigma i) = G.push w 0 i := by
  intro i hi hh
  obtain ⟨hj, hjh⟩ := hV.sigma_inside i hi hh
  have hx : Entry.pull (G.sigma i) ∈ G.entries := (mem_entries G _).mpr (Or.inl ⟨_, hj, hjh, rfl⟩)
  have h := eq_of_even_of_pair G.entries (G.entryVal ω w) hev (y := Entry.push i) hx
    (fun z hz ht => by
      rcases (mem_entries G z).mp hz with ⟨a, ha, -, rfl⟩ | ⟨a, ha, hah, rfl⟩
      · exact Or.inl (by rw [hω a (by omega) _ (by omega) ht])
      · have := hω _ (by have := (hV.sigma_inside a ha hah).1; omega) _ (by omega) ht
        exact Or.inr (by rw [hV.sigma_inj a ha i hi this]))
  simp only [entryVal, Prod.mk.injEq] at h
  exact h.1

/-! ## The identities give the sum -/

/-- **The identities give the sum with poles.** In the state after `α, β, γ`, if no pull's denominator and no
hole's push denominator vanishes, every denominator of the family is nonzero and the log-derivative sum plus the
holes' terms is zero. -/
theorem logSum_of_copyOK (hV : G.Valid) {pub : ℕ → List F} {w : ℕ → F} {α β γ : F}
    (h : G.CopyOK ω pub w α β γ) (hpull : ∀ i < G.N, dPull ω w α β i ≠ 0)
    (hpush : ∀ j < G.nP, den α β (G.poleB ω w j) ≠ 0) :
    (∀ x ∈ G.entries, den α β (G.entryVal ω w x) ≠ 0) ∧
      logSum G.entries (G.entryVal ω w) α β +
        ∑ j ∈ range G.nP, G.portC pub w γ j * (den α β (G.poleA ω w j) * den α β (G.poleB ω w j))⁻¹ = 0 := by
  obtain ⟨hv, hid, hsum⟩ := h
  have hint := fun i (hi : i < G.N) (hh : ¬ G.IsHole i) => hv_internal ω hV hh (hid i hi) (hpull i hi)
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases (mem_entries G x).mp hx with ⟨i, hi, -, rfl⟩ | ⟨i, hi, hh, rfl⟩
    · exact hpull i hi
    · have := (hint i hi hh).1
      unfold dPushV pushV at this
      rwa [ite_eq_right hh] at this
  · have hd : Disjoint (G.internal.image Entry.pull) (G.internal.image Entry.push) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_, -, he⟩ := Finset.mem_image.mp hz'
      cases he
    have hlog : logSum G.entries (G.entryVal ω w) α β =
        ∑ i ∈ G.internal, hv i := by
      unfold logSum entries
      rw [Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => Entry.pull.inj h),
        Finset.sum_image (fun a _ b _ h => Entry.push.inj h), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨hi, hh⟩ := (G.mem_internal).mp hi
      rw [(hint i hi hh).2]
      unfold dPushV pushV
      rw [ite_eq_right hh]
      rfl
    have hholes : ∑ i ∈ (range G.N).filter G.IsHole, hv i =
        ∑ j ∈ range G.nP, G.portC pub w γ j * (den α β (G.poleA ω w j) * den α β (G.poleB ω w j))⁻¹ := by
      rw [sum_holes hV]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      obtain ⟨hpj, hph⟩ := port_lt hV hj'
      have hq : G.dPushV ω w α β (G.port j) ≠ 0 := by rw [dPushV_port ω hV w α β hj']; exact hpush j hj'
      rw [hv_hole ω hph (hid _ hpj) (hpull _ hpj) hq, tVal_port hV pub w γ hj', dPushV_port ω hV w α β hj']
      rfl
    rw [hlog, ← hholes]
    unfold internal
    rw [Finset.sum_filter_not_add_sum_filter]
    exact hsum

/-! ## Counting the bad challenges -/

variable [Fintype F]

omit [CharP F 2] [DecidableEq F] in
/-- Triples counted by their last coordinate. -/
theorem card_triple_le (P : F × F × F → Prop) [DecidablePred P] (c : ℕ)
    (h : ∀ γ : F, (univ.filter fun ab : F × F => P (ab.1, ab.2, γ)).card ≤ c) :
    (univ.filter P).card ≤ c * Fintype.card F := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : F × F × F => v.2.2) (t := univ)
    fun _ _ => Finset.mem_univ _]
  calc ∑ γ : F, ((univ.filter P).filter fun v => v.2.2 = γ).card ≤ ∑ _γ : F, c := by
        refine Finset.sum_le_sum fun γ _ => ?_
        have hsub : ((univ.filter P).filter fun v => v.2.2 = γ) ⊆
            (univ.filter fun ab : F × F => P (ab.1, ab.2, γ)).image fun ab => (ab.1, ab.2, γ) := by
          intro v hv
          rw [Finset.mem_filter, Finset.mem_filter] at hv
          refine Finset.mem_image.mpr ⟨(v.1, v.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
            ?_⟩
          · rw [← hv.2]; exact hv.1.2
          · rw [← hv.2]
        exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (h γ))
    _ = c * Fintype.card F := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

omit [CharP F 2] [DecidableEq F] in
/-- An event on the last coordinate of a triple. -/
theorem card_filter_last (Q : F → Prop) [DecidablePred Q] :
    (univ.filter fun v : F × F × F => Q v.2.2).card = (univ.filter Q).card * Fintype.card F ^ 2 := by
  have : (univ.filter fun v : F × F × F => Q v.2.2) = univ ×ˢ (univ ×ˢ univ.filter Q) := by
    ext v
    simp
  rw [this, Finset.card_product, Finset.card_product, Finset.card_univ]
  ring

/-- A pair's denominator vanishes at `|F|²` triples. -/
theorem card_den_eq_zero_le (q : F × F) :
    (univ.filter fun v : F × F × F => den v.1 v.2.1 q = 0).card ≤ Fintype.card F ^ 2 := by
  classical
  refine (Finset.card_le_card (t := univ.image fun p : F × F => (q.1 + p.1 * q.2, p.1, p.2))
    fun v hv => ?_).trans (Finset.card_image_le.trans (by simp [sq]))
  rw [Finset.mem_filter] at hv
  refine Finset.mem_image.mpr ⟨(v.2.1, v.2.2), Finset.mem_univ _, ?_⟩
  have h := hv.2
  unfold den at h
  have : v.1 = q.1 + v.2.1 * q.2 := CharTwo.add_eq_zero.mp (by rw [← h]; ring)
  rw [← this]

/-- Triples where one of `n` pairs' denominators vanishes. -/
theorem card_exists_den_eq_zero_le (n : ℕ) (q : ℕ → F × F) :
    (univ.filter fun v : F × F × F => ∃ i < n, den v.1 v.2.1 (q i) = 0).card ≤ n * Fintype.card F ^ 2 := by
  classical
  have : (univ.filter fun v : F × F × F => ∃ i < n, den v.1 v.2.1 (q i) = 0) ⊆
      (range n).biUnion fun i => univ.filter fun v : F × F × F => den v.1 v.2.1 (q i) = 0 := by
    intro v hv
    obtain ⟨i, hi, h0⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
  refine (Finset.card_le_card this).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ i ∈ range n, (univ.filter fun v : F × F × F => den v.1 v.2.1 (q i) = 0).card
      ≤ ∑ _i ∈ range n, Fintype.card F ^ 2 := Finset.sum_le_sum fun i _ => card_den_eq_zero_le (q i)
    _ = n * Fintype.card F ^ 2 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

open Classical in
/-- **The copy argument's soundness, counting form.** If the witness `w` does not satisfy the circuit for the
public limbs `pub`, at most `(4N − 1 + Σ_j d_j)·|F|²` triples `(α, β, γ)` reach the state `CopyOK`, `d_j`
bounding the `γ` at which port `j`'s fingerprints of different limbs agree (`hbind`). -/
theorem card_copyOK_le (hV : G.Valid) (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b)
    (pub : ℕ → List F) (w : ℕ → F) (d : ℕ → ℕ)
    (hbind : ∀ j < G.nP, G.limbVals w j ≠ pub j →
      (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ d j)
    (hns : ¬ G.Satisfies pub w) :
    (univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2).card ≤
      (4 * G.N - 1 + ∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 := by
  have hP := nP_le hV
  set A1 := univ.filter fun v : F × F × F => ∃ i < G.N, den v.1 v.2.1 (w i, ω i) = 0
  set A2 := univ.filter fun v : F × F × F => ∃ j < G.nP, den v.1 v.2.1 (G.poleB ω w j) = 0
  set B := univ.filter fun v : F × F × F =>
    (∀ x ∈ G.entries, den v.1 v.2.1 (G.entryVal ω w x) ≠ 0) ∧
      (∀ j ∈ range G.nP, den v.1 v.2.1 (G.poleA ω w j) ≠ 0 ∧ den v.1 v.2.1 (G.poleB ω w j) ≠ 0) ∧
      (¬ EvenAll G.entries (G.entryVal ω w) ∨ ∃ j ∈ range G.nP, G.portC pub w v.2.2 j ≠ 0) ∧
      logSum G.entries (G.entryVal ω w) v.1 v.2.1 +
        ∑ j ∈ range G.nP, G.portC pub w v.2.2 j * (den v.1 v.2.1 (G.poleA ω w j) * den v.1 v.2.1 (G.poleB ω w j))⁻¹ = 0
  set Cj := fun j => univ.filter fun v : F × F × F =>
    G.limbVals w j ≠ pub j ∧ G.push w v.2.2 (G.port j) = G.pubFp v.2.2 pub j
  -- The bad triples are in `A1 ∪ A2 ∪ B ∪ ⋃ Cj`.
  have hsub : (univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2) ⊆
      A1 ∪ (A2 ∪ (B ∪ (range G.nP).biUnion Cj)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    by_cases hA : ∃ i < G.N, den v.1 v.2.1 (w i, ω i) = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
    by_cases hA' : ∃ j < G.nP, den v.1 v.2.1 (G.poleB ω w j) = 0
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA'⟩))
    push Not at hA hA'
    obtain ⟨hden, hlog⟩ := logSum_of_copyOK ω hV hv.2 hA hA'
    refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
    by_cases hE : EvenAll G.entries (G.entryVal ω w) ∧ ∀ j ∈ range G.nP, G.portC pub w v.2.2 j = 0
    · refine Finset.mem_union_right _ ?_
      have hcopy := copy_of_even ω hV hω w hE.1
      by_contra hC
      apply hns
      refine ⟨fun i hi hh => hcopy i hi hh, fun j hj => ?_⟩
      by_contra hne
      have hc := hE.2 j (Finset.mem_range.mpr hj)
      exact hC (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, CharTwo.add_eq_zero.mp hc⟩⟩)
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hden,
        fun j hj => ⟨hA _ (port_lt hV (Finset.mem_range.mp hj)).1, hA' j (Finset.mem_range.mp hj)⟩, ?_, hlog⟩)
      rw [not_and_or] at hE
      rcases hE with hE | hE
      · exact Or.inl hE
      · push Not at hE
        exact Or.inr hE
  -- The counts.
  have hA1c : A1.card ≤ G.N * Fintype.card F ^ 2 := card_exists_den_eq_zero_le G.N fun i => (w i, ω i)
  have hA2c : A2.card ≤ G.nP * Fintype.card F ^ 2 := card_exists_den_eq_zero_le G.nP (G.poleB ω w)
  have hBc : B.card ≤ (2 * G.N - 1) * Fintype.card F ^ 2 := by
    refine (card_triple_le _ ((2 * G.N - 1) * Fintype.card F) fun γ => ?_).trans (le_of_eq (by ring))
    by_cases hE : ¬ EvenAll G.entries (G.entryVal ω w) ∨ ∃ j ∈ range G.nP, G.portC pub w γ j ≠ 0
    · refine (Finset.card_le_card fun ab hab => ?_).trans
        ((card_poles_eq_zero_le G.entries (G.entryVal ω w) (range G.nP) (G.poleA ω w) (G.poleB ω w)
          (G.portC pub w γ) ?_ ?_ ?_ ?_ hE).trans (Nat.mul_le_mul_right _ ?_))
      · rw [Finset.mem_filter] at hab ⊢
        exact ⟨hab.1, hab.2.1, hab.2.2.1, hab.2.2.2.2⟩
      · intro x hx j hj h
        have hpj := port_lt hV (Finset.mem_range.mp hj)
        rcases (mem_entries G x).mp hx with ⟨i, hi, hh, rfl⟩ | ⟨i, hi, hh, rfl⟩
        · have := hω _ (by omega) _ (by omega) (congrArg Prod.snd h)
          exact hh (this ▸ hpj.2)
        · have hs := hV.sigma_inside i hi hh
          have := hω _ (by omega) _ (by omega) (congrArg Prod.snd h)
          exact hs.2 (this ▸ hpj.2)
      · intro x hx j hj h
        have hj' := Finset.mem_range.mp hj
        rcases (mem_entries G x).mp hx with ⟨i, hi, hh, rfl⟩ | ⟨i, hi, hh, rfl⟩
        · have := hω _ (by omega) _ (by omega) (congrArg Prod.snd h)
          omega
        · have hs := (hV.sigma_inside i hi hh).1
          have := hω _ (by omega) _ (by omega) (congrArg Prod.snd h)
          omega
      · intro j hj j' hj' h
        have hpj := port_lt hV (Finset.mem_range.mp hj)
        have hj'' := Finset.mem_range.mp hj'
        have := hω _ (by omega) _ (by omega) (congrArg Prod.snd h)
        omega
      · intro j hj j' hj' h
        have hpj := port_lt hV (Finset.mem_range.mp hj)
        have hpj' := port_lt hV (Finset.mem_range.mp hj')
        exact port_inj hV (Finset.mem_range.mp hj) (Finset.mem_range.mp hj')
          (hω _ (by omega) _ (by omega) (congrArg Prod.snd h))
      · have := card_entries_le hV
        rw [Finset.card_range]
        omega
    · rw [Finset.filter_false_of_mem fun ab _ h => hE h.2.2.1, Finset.card_empty]
      exact Nat.zero_le _
  have hCc : ((range G.nP).biUnion Cj).card ≤ (∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 := by
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hne : G.limbVals w j ≠ pub j
    · have : Cj j = univ.filter fun v : F × F × F =>
          G.push w v.2.2 (G.port j) = G.pubFp v.2.2 pub j := by
        ext v
        simp [Cj, hne]
      rw [this]
      refine le_of_eq_of_le
        (card_filter_last (fun γ => G.push w γ (G.port j) = G.pubFp γ pub j)) ?_
      exact Nat.mul_le_mul_right _ (hbind j (Finset.mem_range.mp hj) hne)
    · have : Cj j = ∅ := Finset.filter_false_of_mem fun v _ h => hne h.1
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
  have hN := N_pos (G := G)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  refine (Nat.add_le_add hA1c ((Finset.card_union_le _ _).trans (Nat.add_le_add hA2c
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hBc hCc))))).trans ?_
  rw [← add_mul, ← add_mul, ← add_mul]
  refine Nat.mul_le_mul_right _ ?_
  omega

open Classical OracleComp in
/-- **The copy argument's soundness.** If the witness does not satisfy the circuit, a uniform
`(α, β, γ)` reaches `CopyOK` with probability at most `(4N − 1 + Σ_j d_j)/|F|`. -/
theorem prob_copyOK_le [SampleableType F] (hV : G.Valid)
    (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b)
    (pub : ℕ → List F) (w : ℕ → F) (d : ℕ → ℕ)
    (hbind : ∀ j < G.nP, G.limbVals w j ≠ pub j →
      (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ d j)
    (hns : ¬ G.Satisfies pub w) :
    Pr{let v ← $ᵗ (F × F × F)}[G.CopyOK ω pub w v.1 v.2.1 v.2.2] ≤
      ((4 * G.N - 1 + ∑ j ∈ range G.nP, d j : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_prod, Fintype.card_prod]
  calc ((univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2).card : ENNReal) /
        ((Fintype.card F * (Fintype.card F * Fintype.card F) : ℕ) : ENNReal)
      ≤ (((4 * G.N - 1 + ∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 : ℕ) : ENNReal) /
          ((Fintype.card F * (Fintype.card F * Fintype.card F) : ℕ) : ENNReal) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_copyOK_le ω hV hω pub w d hbind hns)) _
    _ = _ := by
        rw [show Fintype.card F * (Fintype.card F * Fintype.card F) =
          Fintype.card F * Fintype.card F ^ 2 by ring, Nat.cast_mul, Nat.cast_mul,
          ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
            (ENNReal.natCast_ne_top _)]

end Circuit

end RecPiop
