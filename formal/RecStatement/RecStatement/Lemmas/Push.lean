-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Lemmas.SpecOf

/-!
# The push side at `t`: the indicators, the groups, the ports

Under `SpecOf`, at a `t` outside `V_m` (`w_m(t) ≠ 0`), what the verifier's push side computes
(`PI2.md` §2 steps 3–5):

* each pair's denominator `Ẑ_s(t) + Ẑ_s(c_p)` is nonzero and `I_p(t) = w_m(t)/d_p` (`pairDen_ind`, from
  `ind_eval_closed`);
* each port role's `Φ` denominators `w_r(t) + ω_y` are nonzero (`phiDen_ne_zero`: `w_{m−r}` sends `ω_y` to zero and
  `w_r(t)` to `w_m(t)`);
* the internal pushes are `RecPiop`'s: `P_v(t) = v_0 + w_m A/B`, `B ≠ 0` (`push_side`);
* the ports' fraction is the holes' indicator times `Δ` plus the ports' term: `1_S(t) Δ + T(t) = w_m R_n/R_d`,
  `R_d ≠ 0`, for any `Φ` taking the verifier's values `phiAt` at `t` (`push_side`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-! ## Lists -/

theorem le_foldl_max : ∀ (L : List ℕ) (init : ℕ), init ≤ L.foldl max init
  | [], _ => le_refl _
  | x :: L, init => (le_max_left init x).trans (le_foldl_max L _)

theorem mem_le_foldl_max : ∀ (L : List ℕ) (init : ℕ), ∀ x ∈ L, x ≤ L.foldl max init
  | [], _, _, h => absurd h List.not_mem_nil
  | y :: L, init, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right init x).trans (le_foldl_max L _)
    · exact mem_le_foldl_max L _ x h

theorem zip_map_self {α β : Type} (f : α → β) : ∀ L : List α, L.zip (L.map f) = L.map fun a ↦ (a, f a)
  | [] => rfl
  | a :: L => by simp [zip_map_self f L]

theorem sum_flatMap_map {α : Type} (f : α → List ℕ) (h : ℕ → F) :
    ∀ L : List α, ((L.flatMap f).map h).sum = (L.map fun g ↦ ((f g).map h).sum).sum
  | [] => rfl
  | g :: L => by simp [List.flatMap_cons, sum_flatMap_map f h L]

theorem sum_filter_map {α : Type} (P : α → Bool) (f : α → F) :
    ∀ L : List α, ((L.filter P).map f).sum = (L.map fun x ↦ if P x then f x else 0).sum
  | [] => rfl
  | x :: L => by
    by_cases hx : P x <;> simp [hx, sum_filter_map P f L]

theorem prod_filter_ne_zero {α : Type} (P : α → Bool) (f : α → F) (L : List α) (h : ∀ x ∈ L, f x ≠ 0) :
    ((L.filter P).map f).prod ≠ 0 :=
  List.prod_ne_zero fun h0 ↦ by
    obtain ⟨x, hx, hfx⟩ := List.mem_map.mp h0
    exact h x (List.mem_filter.mp hx).1 hfx

/-- **A fraction, empty or not**: its denominator the product, its numerator the product times the sum of the
inverses. -/
theorem fraction_spec (xs : List F) (hx : ∀ x ∈ xs, x ≠ 0) :
    (fraction xs).2 = xs.prod ∧ (fraction xs).1 = xs.prod * (xs.map (·⁻¹)).sum := by
  cases xs with
  | nil => exact ⟨rfl, by simp [fraction]⟩
  | cons x xs => exact ⟨fraction_snd _ (List.cons_ne_nil _ _), fraction_fst _ (List.cons_ne_nil _ _) hx⟩

/-- **An accumulated fraction, empty or not.** -/
theorem accFold_getD (xs : List (F × F)) (hd : ∀ xd ∈ xs, xd.2 ≠ 0) :
    ((xs.foldl accStep none).map (·.2)).getD 1 = (xs.map (·.2)).prod ∧
      ((xs.foldl accStep none).map (·.1)).getD 0 =
        (xs.map (·.2)).prod * (xs.map fun xd ↦ xd.1 / xd.2).sum := by
  cases xs with
  | nil => exact ⟨rfl, by simp⟩
  | cons xd xs =>
    obtain ⟨a, b, h1, h2, h3⟩ := accFold_none (xd :: xs) (List.cons_ne_nil _ _) hd
    rw [h1]
    exact ⟨h2, by rw [Option.map_some, Option.getD_some, h3, h2]⟩

/-! ## The pairs -/

section Pairs

variable {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : QuotientSecurity.CantorBasis F n}
  {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {pubOf : List F → ℕ → List F}

/-- A pair's denominator `Ẑ_s(t) + Ẑ_s(c_p)`, `Ẑ_s(t)` read from `zt`. -/
def pairDen (S : CoreSpec F) (zt : List F) (i : ℕ) : F := zt.getD (S.pairs.getD i (0, 0)).1 0 + (S.pairs.getD i (0, 0)).2

theorem groupDens_eq (S : CoreSpec F) (zt : List F) (g : GroupF F) : groupDens S zt g = g.pairs.map (pairDen S zt) := rfl

/-- `Ẑ_s(t)` for every block. -/
def ztOf (S : CoreSpec F) (t : F) : List F := (List.range (S.maxLogRows + 1)).map fun s ↦ zHat S.c s t

theorem ztOf_getD (S : CoreSpec F) (t : F) {s : ℕ} (hs : s ≤ S.maxLogRows) : (ztOf S t).getD s 0 = zHat S.c s t := by
  simp [ztOf, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hs]

theorem logRows_le (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) : p.1.logRows ≤ G.logN - G.logW := by
  have hb := (Circuit.mem_pairs.mp hp).1
  have hr := hV.in_range _ hb
  have h2 : 2 ^ p.1.logRows ≤ 2 ^ (G.logN - G.logW) := by unfold Circuit.rows at hr; omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem logRows_le_max (S : CoreSpec F) {i : ℕ} (hi : i < S.pairs.length) :
    (S.pairs.getD i (0, 0)).1 ≤ S.maxLogRows := by
  unfold CoreSpec.maxLogRows
  refine mem_le_foldl_max _ _ _ (List.mem_map.mpr ⟨S.pairs.getD i (0, 0), ?_, rfl⟩)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- **A pair's indicator at `t`**: its denominator nonzero, `I_p(t) = w_m(t)/d_p`. -/
theorem pairDen_ind (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) {t : F}
    (ht : QuotientSecurity.sq^[G.logN] t ≠ 0) {i : ℕ} (hi : i < S.pairs.length) :
    pairDen S (ztOf S t) i ≠ 0 ∧
      (G.ind (Heap.omega B) (pairOf i)).eval t = QuotientSecurity.sq^[G.logN] t / pairDen S (ztOf S t) i := by
  have hp := hS.pair_mem i hi
  have hs := hS.pair_s i hi
  have hle : (S.pairs.getD i (0, 0)).1 ≤ S.maxLogRows := logRows_le_max S hi
  have hzt : (ztOf S t).getD (S.pairs.getD i (0, 0)).1 0 = zHat S.c (S.pairs.getD i (0, 0)).1 t :=
    ztOf_getD S t hle
  have hc : NormConsts (blockBasis (Heap.omega B) G.logW) S.c (pairOf i).1.logRows :=
    fun s hs' ↦ hS.c s (lt_of_lt_of_le hs' (logRows_le hV hp))
  obtain ⟨h1, h2⟩ := ind_eval_closed B hS.hn hV hp hc ht
  have e : pairDen S (ztOf S t) i = zHat S.c (pairOf i).1.logRows t +
      zHat S.c (pairOf i).1.logRows (Heap.omega B (G.pairBase (pairOf i))) := by
    unfold pairDen
    rw [hzt, hS.pair_z i hi, hs]
  rw [e]
  exact ⟨h1, h2⟩

theorem mul_mul_div_cancel (X P Q : F) (hP : P ≠ 0) : X * (P * Q) / P = X * Q := by
  field_simp

/-- `ω_{2k+1} = ω_{2k} + 1` on a Cantor basis (`β_0 = 1`). -/
theorem omega_odd (hn : 1 ≤ n) (k : ℕ) : Heap.omega B (2 * k + 1) = Heap.omega B (2 * k) + 1 := by
  rw [add_eq_xor_of_dvd (m := 1) (by rw [pow_one]; exact Dvd.intro k rfl) (by norm_num)]
  exact Heap.omega_xor_one B hn (2 * k)

/-- The run's row cells are `cellsOf`. -/
theorem run_cells (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) {x : ℕ}
    (hx : x < 2 ^ G.logW) :
    (S.run inp).cells.getD x 0 = cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t x := by
  have h1n : 1 ≤ n := by have := hV.logW_lt; have := hS.hn; omega
  show (cellsList S.ω (digitsList inp.t (S.logN + 1)) S.logRow inp.a).getD x 0 = _
  rw [hS.omega, hS.logRow]
  refine cellsList_eq_cellsOf (Heap.omega B) (omega_odd h1n) inp.t _ (fun l hl ↦ digitsList_getD inp.t ?_) inp.a hx
  have := hV.logW_lt; rw [hS.logN]; omega

/-- The groups' pairs are pairs. -/
theorem mem_groups_lt (hS : SpecOf S G B pairOf portOf pubOf) {g : GroupF F} (hg : g ∈ S.groups) {i : ℕ}
    (hi : i ∈ g.pairs) : i < S.pairs.length :=
  List.mem_range.mp (hS.groups_perm.mem_iff.mp (List.mem_flatMap.mpr ⟨g, hg, hi⟩))

/-- **The verifier's `Φ_k(t)`**: `w_m G_n/G_d` of role `k`'s fraction, zero for a role of no port of nonzero
value. -/
def phiAt (S : CoreSpec F) (gs pubs : List F) (t : F) (k : ℕ) : F :=
  match S.phi.find? (·.1 = k) with
  | some kt => QuotientSecurity.sq^[S.logN] t * (phiFrac S.ω gs pubs (QuotientSecurity.sq^[S.logRow] t) kt.2).1 /
      (phiFrac S.ω gs pubs (QuotientSecurity.sq^[S.logRow] t) kt.2).2
  | none => 0

theorem mem_phiTerms {S : CoreSpec F} {kt : ℕ × List (ℕ × LinF F)} (hkt : kt ∈ S.phi) {yl : ℕ × LinF F}
    (hyl : yl ∈ kt.2) : (kt.1, yl) ∈ phiTerms S :=
  List.mem_flatMap.mpr ⟨kt, hkt, List.mem_map.mpr ⟨yl, hyl, rfl⟩⟩

/-- A `Φ` term's row is below `2^(m − r)`. -/
theorem phiTerm_row_lt (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) {x : ℕ × ℕ × LinF F}
    (hx : x ∈ phiTerms S) : x.2.1 < 2 ^ (G.logN - G.logW) := by
  obtain ⟨J, hJ, rfl⟩ := List.getElem_of_mem hx
  have e : (phiTerms S)[J] = (phiTerms S).getD J noPhi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, Option.getD_some]
  rw [e, hS.phi_row J hJ]
  have hp := (G.port_lt hV (hS.phi_port_lt J hJ)).1
  have hW : 0 < G.W := Nat.two_pow_pos _
  rw [Nat.div_lt_iff_lt_mul hW]
  have : G.N = 2 ^ (G.logN - G.logW) * G.W := by
    unfold Circuit.N Circuit.W
    rw [← pow_add, Nat.sub_add_cancel hV.logW_lt.le]
  omega

/-- **A `Φ` denominator at `t` off `V_m` is nonzero**: `w_r(t) + ω_y ≠ 0` for `y < 2^(m − r)`. -/
theorem phiDen_ne_zero (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) {t : F}
    (ht : QuotientSecurity.sq^[G.logN] t ≠ 0) {y : ℕ} (hy : y < 2 ^ (G.logN - G.logW)) :
    QuotientSecurity.sq^[G.logW] t + Heap.omega B y ≠ 0 := by
  intro h0
  have he : QuotientSecurity.sq^[G.logW] t = Heap.omega B y := CharTwo.add_eq_zero.mp h0
  apply ht
  have hn := hS.hn
  have hy' : y < 2 ^ n := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [show G.logN = (G.logN - G.logW) + G.logW by have := hV.logW_lt; omega, Function.iterate_add_apply, he,
    Heap.sq_iterate_omega B _ hy', Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hy, Heap.omega_zero]

/-- The run's `Φ` lookup is `phiAt`'s, scaled by `w_m`. -/
theorem find_wPhi (S : CoreSpec F) (gs pubs : List F) (wm wr : F) (k : ℕ) :
    ((S.phi.map fun kt ↦ (kt.1, phiFrac S.ω gs pubs wr kt.2)).map fun knd ↦ (knd.1, wm * knd.2.1, knd.2.2)).find?
        (·.1 = k) =
      (S.phi.find? (·.1 = k)).map fun kt ↦ (kt.1, wm * (phiFrac S.ω gs pubs wr kt.2).1,
        (phiFrac S.ω gs pubs wr kt.2).2) := by
  rw [List.map_map, List.find?_map]
  rfl

/-- **The push side at `t`** (`PI2.md` §2 steps 3–5): `B ≠ 0`, `R_d ≠ 0`, the internal pushes
`P_v(t) = v_0 + w_m A/B`, and the ports' fraction `1_S(t) Δ + T(t) = w_m R_n/R_d`, for any `Φ` taking the verifier's
`Φ_k(t)` (`phiAt`). -/
theorem push_side (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) (Φ : ℕ → Polynomial F)
    (hΦ : ∀ k, (Φ k).eval inp.t = phiAt S (powersList inp.γ (S.maxGamma + 1)) inp.scalars inp.t k) :
    (S.run inp).den ≠ 0 ∧ (S.run inp).rDen ≠ 0 ∧
      G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t =
        cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t 0 +
          QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).num / (S.run inp).den ∧
      (G.holePoly (Heap.omega B)).eval inp.t * (S.run inp).delta +
          G.tAt (Heap.omega B) Φ (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t =
        QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).rNum / (S.run inp).rDen := by
  set v := cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t with hv
  set wm := QuotientSecurity.sq^[G.logN] inp.t with hwm
  set zt := ztOf S inp.t with hzt
  set gs := powersList inp.γ (S.maxGamma + 1) with hgs
  set cells := (S.run inp).cells with hcells
  set d := pairDen S zt with hd
  set delta := (S.run inp).delta with hdelta
  have hW : 0 < 2 ^ G.logW := Nat.two_pow_pos _
  have hcell : ∀ x < 2 ^ G.logW, cells.getD x 0 = v x := fun x hx ↦ run_cells hS hV inp hx
  -- the digits the run reads
  have hwmR : (digitsList inp.t (S.logN + 1)).getD S.logN 0 = wm := by
    rw [digitsList_getD inp.t (by omega), hS.logN]
  have hwrR : (digitsList inp.t (S.logN + 1)).getD S.logRow 0 = QuotientSecurity.sq^[G.logW] inp.t := by
    rw [digitsList_getD inp.t (by rw [hS.logRow, hS.logN]; have := hV.logW_lt; omega), hS.logRow]
  -- the pairs' denominators and indicators
  have hdi : ∀ i < S.pairs.length, d i ≠ 0 ∧ (G.ind (Heap.omega B) (pairOf i)).eval inp.t = wm / d i :=
    fun i hi ↦ pairDen_ind hS hV ht hi
  -- the groups' fractions
  set fr : GroupF F → F × F := fun g ↦ fraction (groupDens S zt g) with hfr
  have hgr : ∀ g ∈ S.groups, (fr g).2 = (g.pairs.map d).prod ∧
      (fr g).1 = (g.pairs.map d).prod * ((g.pairs.map d).map (·⁻¹)).sum ∧ (g.pairs.map d).prod ≠ 0 := by
    intro g hg
    have hne : ∀ x ∈ g.pairs.map d, x ≠ 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact (hdi i (mem_groups_lt hS hg hi)).1
    obtain ⟨h1, h2⟩ := fraction_spec (g.pairs.map d) hne
    exact ⟨h1, h2, List.prod_ne_zero fun h0 ↦ hne 0 h0 rfl⟩
  -- one-pair groups' numerators are one
  have hsingle : SingleOne (S.groups.zip (S.groups.map fr)) := by
    rw [zip_map_self]
    intro gf hgf hlen
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hgf
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlen
    show (fraction (groupDens S zt g)).1 = 1
    rw [groupDens_eq, hi]
    rfl
  -- the `Φ` fractions
  set wPhi := ((S.phi.map fun kt ↦ (kt.1, phiFrac S.ω gs inp.scalars
    ((digitsList inp.t (S.logN + 1)).getD S.logRow 0) kt.2)).map fun knd ↦
      (knd.1, (digitsList inp.t (S.logN + 1)).getD S.logN 0 * knd.2.1, knd.2.2)) with hwPhi
  have hphiDen : ∀ kt ∈ S.phi, ∀ yl ∈ kt.2, (digitsList inp.t (S.logN + 1)).getD S.logRow 0 + S.ω yl.1 ≠ 0 := by
    intro kt hkt yl hyl
    rw [hwrR, hS.omega]
    exact phiDen_ne_zero hS hV ht (phiTerm_row_lt hS hV (mem_phiTerms hkt hyl))
  -- each port group's value over its denominator
  have hpv : ∀ g ∈ S.groups, ∀ nd : F × F, nd.2 ≠ 0 →
      (portVD gs cells delta wPhi (g, nd)).2 ≠ 0 ∧
        (portVD gs cells delta wPhi (g, nd)).1 / (portVD gs cells delta wPhi (g, nd)).2 =
          (g.formula.eval gs (fun c ↦ cells.getD (c ^^^ g.role) 0) + delta + phiAt S gs inp.scalars inp.t g.role) /
            nd.2 := by
    intro g hg nd hnd
    unfold portVD
    rw [hwPhi, find_wPhi]
    unfold phiAt
    cases hf : S.phi.find? (·.1 = g.role) with
    | none => simp [hnd]
    | some kt =>
      have hkt := List.mem_of_find?_eq_some hf
      have hpf := phiFrac_spec S.ω gs inp.scalars _ kt.2 (hphiDen kt hkt)
      have hd0 : (phiFrac S.ω gs inp.scalars ((digitsList inp.t (S.logN + 1)).getD S.logRow 0) kt.2).2 ≠ 0 := by
        rw [hpf.1]
        exact List.prod_ne_zero fun h0 ↦ by
          obtain ⟨yl, hyl, he⟩ := List.mem_map.mp h0
          exact hphiDen kt hkt yl hyl he
      simp only [Option.map_some]
      refine ⟨mul_ne_zero hnd hd0, ?_⟩
      rw [hwmR, hwrR] at *
      rw [hS.logN, hS.logRow]
      rw [← hwrR] at hd0 ⊢
      field_simp
      rw [hwm]
      ring
  -- the run's sums
  have hps : pushSums S gs cells (cells.getD 0 0) delta wPhi (S.groups.map fr) = ((S.run inp).num,
      (S.run inp).den, (S.run inp).rNum, (S.run inp).rDen) := rfl
  rw [pushSums_eq S gs cells _ _ _ _ hsingle, zip_map_self] at hps
  simp only [Prod.mk.injEq] at hps
  obtain ⟨hnum, hden, hrnum, hrden⟩ := hps
  set L := S.groups.map fun g ↦ (g, fr g) with hL
  have hLd : ∀ xd ∈ (L.filter fun gf ↦ gf.1.pulls).map (intTerm gs cells (cells.getD 0 0)), xd.2 ≠ 0 := by
    intro xd hxd
    obtain ⟨gf, hgf, rfl⟩ := List.mem_map.mp hxd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hgf).1
    rw [show (intTerm gs cells (cells.getD 0 0) (g, fr g)).2 = (fr g).2 from rfl, (hgr g hg).1]
    exact (hgr g hg).2.2
  have hLp : ∀ xd ∈ (L.filter fun gf ↦ !gf.1.pulls).map (portTerm gs cells delta wPhi), xd.2 ≠ 0 := by
    intro xd hxd
    obtain ⟨gf, hgf, rfl⟩ := List.mem_map.mp hxd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hgf).1
    have := (hpv g hg (fr g) (by rw [(hgr g hg).1]; exact (hgr g hg).2.2)).1
    exact this
  obtain ⟨hA2, hA1⟩ := accFold_getD _ hLd
  obtain ⟨hR2, hR1⟩ := accFold_getD _ hLp
  rw [hden] at hA2
  rw [hnum, ← hA2] at hA1
  rw [hrden] at hR2
  rw [hrnum, ← hR2] at hR1
  have hden0 : (S.run inp).den ≠ 0 := by
    rw [hA2]
    exact List.prod_ne_zero fun h0 ↦ by
      obtain ⟨xd, hxd, he⟩ := List.mem_map.mp h0
      exact hLd xd hxd he
  have hrden0 : (S.run inp).rDen ≠ 0 := by
    rw [hR2]
    exact List.prod_ne_zero fun h0 ↦ by
      obtain ⟨xd, hxd, he⟩ := List.mem_map.mp h0
      exact hLp xd hxd he
  have hv0 : cells.getD 0 0 = v 0 := hcell 0 hW
  refine ⟨hden0, hrden0, ?_, ?_⟩
  · -- the internal pushes, over the pairs' indices
    set h : ℕ → F := fun i ↦ if (G.regionRole (pairOf i).1 (pairOf i).2).isPort then 0 else
      ((G.regionRole (pairOf i).1 (pairOf i).2).value inp.γ (v 0) (fun c ↦ v ((pairOf i).2 ^^^ c)) + v 0) *
        (d i)⁻¹ with hh
    have hsum : ((((L.filter fun gf ↦ gf.1.pulls).map (intTerm gs cells (cells.getD 0 0)))).map
        fun xd ↦ xd.1 / xd.2).sum = ∑ i ∈ range S.pairs.length, h i := by
      rw [List.map_map, sum_filter_map, hL, List.map_map]
      calc _ = (S.groups.map fun g ↦ (g.pairs.map h).sum).sum := congrArg List.sum (List.map_congr_left fun g hg ↦ by
            obtain ⟨h1, h2, h3⟩ := hgr g hg
            simp only [Function.comp]
            by_cases hp : g.pulls
            · simp only [hp, ite_true, intTerm]
              rw [h2, h1, mul_comm _ (_ + _), mul_mul_div_cancel _ _ _ h3, List.map_map, ← List.sum_map_mul_left]
              refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
              have hpi := hS.group_pulls g hg i hi
              rw [hp] at hpi
              simp only [Function.comp, hh]
              rw [ite_eq_right (by simpa using hpi)]
              congr 1
              rw [hS.group_formula g hg i hi inp.γ (fun x ↦ cells.getD x 0), hv0]
              congr 1
              refine Role.value_congr _ _ (fun _ ↦ rfl) fun c hc ↦ ?_
              have hp' := hS.pair_mem i (mem_groups_lt hS hg hi)
              exact hcell _ (Nat.xor_lt_two_pow (Circuit.mem_pairs.mp hp').2.1 (Circuit.regionRole_reads_lt hV hp' hc))
            · have hpf : g.pulls = false := by simpa using hp
              simp only [hp, Bool.false_eq_true, ite_false]
              symm
              refine List.sum_eq_zero fun x hx ↦ ?_
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
              have hpi := hS.group_pulls g hg i hi
              rw [hpf] at hpi
              simp only [hh]
              rw [ite_eq_left (by simpa using hpi.symm)])
        _ = ∑ i ∈ range S.pairs.length, h i := by
            rw [← sum_flatMap_map, (hS.groups_perm.map h).sum_eq, list_range_sum]
    have hbij : ∑ p ∈ G.intPairs, (G.ind (Heap.omega B) p).eval inp.t *
        ((G.regionRole p.1 p.2).value inp.γ (v 0) (fun c ↦ v (p.2 ^^^ c)) + v 0) =
        ∑ i ∈ range S.pairs.length, wm * h i := by
      unfold Circuit.intPairs
      rw [Finset.sum_filter]
      symm
      refine Finset.sum_nbij pairOf (fun i hi ↦ hS.pair_mem i (Finset.mem_range.mp hi))
        (fun i hi j hj hij ↦ hS.pair_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij)
        (fun p hp ↦ ?_) (fun i hi ↦ ?_)
      · obtain ⟨i, hi, rfl⟩ := hS.pair_surj p hp
        exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
      · simp only [hh]
        by_cases hc : (G.regionRole (pairOf i).1 (pairOf i).2).isPort = true
        · simp [hc]
        · have hc' : (G.regionRole (pairOf i).1 (pairOf i).2).isPort = false := by simpa using hc
          rw [ite_eq_right hc, ite_eq_left hc', (hdi i (Finset.mem_range.mp hi)).2]
          ring
    unfold Circuit.pvAt
    rw [hbij, ← Finset.mul_sum, ← hsum, hA1]
    field_simp
  · -- the ports
    set h : ℕ → F := fun i ↦ if (G.regionRole (pairOf i).1 (pairOf i).2).isPort then
      ((G.regionRole (pairOf i).1 (pairOf i).2).value inp.γ (v 0) (fun c ↦ v ((pairOf i).2 ^^^ c)) + delta +
        phiAt S gs inp.scalars inp.t (pairOf i).2) * (d i)⁻¹ else 0 with hh
    have hsum : ((((L.filter fun gf ↦ !gf.1.pulls).map (portTerm gs cells delta wPhi))).map
        fun xd ↦ xd.1 / xd.2).sum = ∑ i ∈ range S.pairs.length, h i := by
      rw [List.map_map, sum_filter_map, hL, List.map_map]
      calc _ = (S.groups.map fun g ↦ (g.pairs.map h).sum).sum := congrArg List.sum (List.map_congr_left fun g hg ↦ by
            obtain ⟨h1, h2, h3⟩ := hgr g hg
            simp only [Function.comp]
            by_cases hp : g.pulls
            · simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false]
              symm
              refine List.sum_eq_zero fun x hx ↦ ?_
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
              have hpi := hS.group_pulls g hg i hi
              rw [hp] at hpi
              simp only [hh]
              rw [ite_eq_right (by simpa using hpi)]
            · have hpf : g.pulls = false := by simpa using hp
              simp only [hp, Bool.not_false, ite_true]
              have hq := (hpv g hg (fr g) (by rw [h1]; exact h3)).2
              set V := g.formula.eval gs (fun c ↦ cells.getD (c ^^^ g.role) 0) + delta +
                phiAt S gs inp.scalars inp.t g.role with hV'
              have e : (portTerm gs cells delta wPhi (g, fr g)).1 / (portTerm gs cells delta wPhi (g, fr g)).2 =
                  V * ((g.pairs.map d).map (·⁻¹)).sum := by
                rw [show (portTerm gs cells delta wPhi (g, fr g)).1 / (portTerm gs cells delta wPhi (g, fr g)).2 =
                  (fr g).1 * ((portVD gs cells delta wPhi (g, fr g)).1 / (portVD gs cells delta wPhi (g, fr g)).2)
                  from by unfold portTerm; ring, hq, h2, h1]
                field_simp
              rw [e, List.map_map, ← List.sum_map_mul_left]
              refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
              have hpi := hS.group_pulls g hg i hi
              rw [hpf] at hpi
              simp only [Function.comp, hh]
              rw [ite_eq_left (by simpa using hpi.symm), hV']
              have hval : g.formula.eval gs (fun c ↦ cells.getD (c ^^^ g.role) 0) =
                  (G.regionRole (pairOf i).1 (pairOf i).2).value inp.γ (v 0) (fun c ↦ v ((pairOf i).2 ^^^ c)) := by
                rw [hS.group_formula g hg i hi inp.γ (fun x ↦ cells.getD x 0)]
                refine Role.value_congr _ _ (fun _ ↦ hv0) fun c hc ↦ ?_
                have hp' := hS.pair_mem i (mem_groups_lt hS hg hi)
                exact hcell _ (Nat.xor_lt_two_pow (Circuit.mem_pairs.mp hp').2.1
                  (Circuit.regionRole_reads_lt hV hp' hc))
              rw [hval, hS.group_role g hg i hi])
        _ = ∑ i ∈ range S.pairs.length, h i := by
            rw [← sum_flatMap_map, (hS.groups_perm.map h).sum_eq, list_range_sum]
    have hbij : ∑ p ∈ G.portPairs, (G.ind (Heap.omega B) p).eval inp.t *
        ((G.regionRole p.1 p.2).value inp.γ (v 0) (fun c ↦ v (p.2 ^^^ c)) + delta + (Φ p.2).eval inp.t) =
        ∑ i ∈ range S.pairs.length, wm * h i := by
      unfold Circuit.portPairs
      rw [Finset.sum_filter]
      symm
      refine Finset.sum_nbij pairOf (fun i hi ↦ hS.pair_mem i (Finset.mem_range.mp hi))
        (fun i hi j hj hij ↦ hS.pair_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij)
        (fun p hp ↦ ?_) (fun i hi ↦ ?_)
      · obtain ⟨i, hi, rfl⟩ := hS.pair_surj p hp
        exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
      · simp only [hh, hΦ]
        split_ifs
        · rw [(hdi i (Finset.mem_range.mp hi)).2]; ring
        · ring
    have hT : (G.holePoly (Heap.omega B)).eval inp.t * delta + G.tAt (Heap.omega B) Φ v inp.γ inp.t =
        ∑ p ∈ G.portPairs, (G.ind (Heap.omega B) p).eval inp.t *
          ((G.regionRole p.1 p.2).value inp.γ (v 0) (fun c ↦ v (p.2 ^^^ c)) + delta + (Φ p.2).eval inp.t) := by
      unfold Circuit.holePoly Circuit.tAt
      rw [Polynomial.eval_finsetSum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      ring
    rw [hT, hbij, ← Finset.mul_sum, ← hsum, hR1]
    field_simp

end Pairs

end RecStatement
