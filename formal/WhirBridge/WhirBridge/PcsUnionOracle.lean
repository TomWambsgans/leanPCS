/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

`PcsUnion.lean`'s `pcs_union_sound` with the out-of-domain point read off Keccak-256 by the verifier at some of the
sizes (as deployed, `crates/pcs_claim/src/lib.rs`, `ood_point`), by `PcsOracle.lean`'s split of the random oracle
generalized to the out-of-domain inputs of every size at once.
-/
import WhirBridge.PcsOracle
import WhirBridge.PcsUnion

/-!
# PCS openings of several sizes, charged once, the point read off Keccak-256

`pcs_union_sound` charges openings of several sizes once, each size's out-of-domain point a fixed function `zOf n` of
the root. `PcsOracle.lean`'s `pcs_sound_oracle` lets the verifier read the point off Keccak-256 (`pcsVerifierO`), at
one size. Here the two meet: at the sizes `S` the verifier reads the point off Keccak-256, at the others it takes the
fixed `zOf n` (`pUVerO`), and the union keeps `pcs_union_sound`'s bound `(QA + QV) (ε + 5 (QA + QV) / 2^256)`.

The proof splits the random oracle on the out-of-domain inputs of **every** size below `256` at once (`OodAll`: a
size, a root and a coordinate; their inputs `oodInput n root j` are distinct, since they name `n` and `j`): a table
`g` answers them all, and in each split world the run is `pcs_union_sound`'s experiment at the point `zOfGA g n` for
the sizes of `S` and `zOf n` for the others (`zMix`). The fixed-point verifier never asks a `46`-byte input (its
claim's bytes are `82 + 24 n` long, its other inputs multiples of eight), so the table leaves it unchanged
(`sim_pcsVerifier`). This file restates `PcsOracle.lean`'s split, coupling and transfer lemmas at `OodAll`, in the
namespace `WhirBridge.Pcs.UnionO` (the names are `PcsOracle.lean`'s).

* **`pcs_union_sound_oracle`**: the union at `S`, its doom `PcsDoomedO` (the point read off the final cache) at the
  sizes of `S`, `PcsDoomed (zOf n)` at the others;
* `Grows`, `verifierO_present_of`: an accepting `pcsVerifierO` asked its root's out-of-domain inputs, under any
  implementation that records its answers (the random oracle: `grows_randomOracle`);
* **`pcsVerifyWithHashO_pure`**, `pcsVerifyWithHashO_id`: over a hash function `h` (answers `pure (h x)`), the
  oracle verifier is `pcsVerifyWithHash` at the point `oodPointWith h n` (what an honest prover's out-of-domain
  answer must be computed at).
-/

namespace WhirBridge.Pcs.UnionO

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open WhirBridge.Pcs (KCache Agree8 run_congr runProof_congr extract_congr oodInput_length ro_run_none ro_run_some
  run_query_bind sim_query_bind cacheQuery_eq_none toList_oodPointWith pcsVerifierO pcsVerifyWithHashO oodPointM
  PcsDoomedO zOfCache)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The out-of-domain inputs of every size -/

/-- **The out-of-domain inputs of every size below `256`**: a size, a root, a coordinate. -/
abbrev OodAll : Type := Fin 256 × Digest × Fin 256

/-- Their bytes, `oodInput n root j`. -/
def oodEnc (d : OodAll) : Bytes := oodInput d.1 d.2.1 d.2.2

theorem toUInt8_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : a.toUInt8 = b.toUInt8) : a = b := by
  have h' := congrArg UInt8.toNat h
  simp only [Nat.toUInt8] at h'
  have e : ∀ x : ℕ, (UInt8.ofNat x).toNat = x % 256 := fun x ↦ UInt8.toNat_ofNat
  rw [e, e, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact h'

theorem oodEnc_injective : Function.Injective oodEnc := by
  rintro ⟨n, r, j⟩ ⟨n', r', j'⟩ h
  simp only [oodEnc, oodInput] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [digestBytes_length'])
  obtain ⟨h0, h3⟩ := List.append_inj h1 (by simp)
  have hr := digestBytes_injective h3
  have hn : (n : ℕ).toUInt8 = (n' : ℕ).toUInt8 := by simpa using h0
  have hj : (j : ℕ).toUInt8 = (j' : ℕ).toUInt8 := by simpa using h2
  have hn' := toUInt8_inj n.isLt n'.isLt hn
  have hj' := toUInt8_inj j.isLt j'.isLt hj
  exact Prod.ext (Fin.ext hn') (Prod.ext hr (Fin.ext hj'))

/-- The out-of-domain input an input is, if any (decided classically). -/
noncomputable def oodDecode (x : Bytes) : Option OodAll :=
  @dite _ (∃ d : OodAll, oodEnc d = x) (Classical.propDecidable _)
    (fun h ↦ some (Classical.choose h)) fun _ ↦ none

theorem oodEnc_of_decode {x : Bytes} {d : OodAll} (h : oodDecode x = some d) : oodEnc d = x := by
  unfold oodDecode at h
  split_ifs at h with hx
  cases h
  exact Classical.choose_spec hx

theorem oodDecode_enc (d : OodAll) : oodDecode (oodEnc d) = some d := by
  have hx : ∃ d', oodEnc d' = oodEnc d := ⟨d, rfl⟩
  unfold oodDecode
  split_ifs
  exact congrArg some (oodEnc_injective (Classical.choose_spec hx))

theorem oodEnc_length (d : OodAll) : (oodEnc d).length = 46 := by
  simp [oodEnc, oodInput, oodTag, digestBytes_length']

theorem oodDecode_of_length {x : Bytes} (hx : x.length ≠ 46) : oodDecode x = none := by
  unfold oodDecode
  split_ifs with h
  · obtain ⟨d, hd⟩ := h
    exact absurd (hd ▸ oodEnc_length d) hx
  · rfl

theorem oodDecode_of_mod {x : Bytes} (hx : x.length % 8 = 0) : oodDecode x = none :=
  oodDecode_of_length fun h ↦ by rw [h] at hx; exact absurd hx (by decide)

/-- Coordinate `j` of a root at `n < 256` variables is an out-of-domain input. -/
theorem oodInput_eq_enc {n j : ℕ} (hn : n < 256) (hj : j < n) (r : Digest) :
    oodInput n r j = oodEnc (⟨n, hn⟩, r, ⟨j, by omega⟩) := rfl

/-- The out-of-domain input a query is, if any. -/
noncomputable def ptOf : (Bytes ⊕ KeccakState) → Option OodAll
  | .inl x => oodDecode x
  | .inr _ => none

/-- The tables of the out-of-domain inputs. -/
abbrev Table : Type := OodAll → Digest

/-- The answer the table `g` gives a query, if it is an out-of-domain input. -/
noncomputable def pick (g : Table) : (t : Bytes ⊕ KeccakState) → Option (KeccakCalls.Range t)
  | .inl x => (oodDecode x).map g
  | .inr _ => none

theorem pick_eq_none_iff (g : Table) (t : Bytes ⊕ KeccakState) : pick g t = none ↔ ptOf t = none := by
  rcases t with x | s <;> simp [pick, ptOf]

theorem ptOf_eq_some {t : Bytes ⊕ KeccakState} {d : OodAll} (h : ptOf t = some d) : t = .inl (oodEnc d) := by
  rcases t with x | s
  · exact congrArg Sum.inl (oodEnc_of_decode h).symm
  · cases h

theorem pick_enc (g : Table) (d : OodAll) : pick g (.inl (oodEnc d)) = some (g d) := by
  simp [pick, oodDecode_enc d]

/-! ## The random oracle split on the out-of-domain inputs -/

/-- **The random oracle with the out-of-domain inputs answered by the table `g`.** -/
noncomputable def roG (g : Table) : QueryImpl KeccakCalls (StateT KCache ProbComp) :=
  fun t ↦ StateT.mk fun c ↦ match c t with
    | some u => pure (u, c)
    | none => match pick g t with
      | some u => pure (u, c.cacheQuery t u)
      | none => ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u)

theorem roG_run (g : Table) (t : Bytes ⊕ KeccakState) (c : KCache) :
    (roG g t).run c = match c t with
      | some u => pure (u, c)
      | none => match pick g t with
        | some u => pure (u, c.cacheQuery t u)
        | none => ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u) := rfl

theorem roG_run_some (g : Table) {t : Bytes ⊕ KeccakState} {c : KCache} {u : KeccakCalls.Range t}
    (hc : c t = some u) : (roG g t).run c = pure (u, c) := by
  rw [roG_run, hc]

theorem roG_run_none (g : Table) {t : Bytes ⊕ KeccakState} {c : KCache} (hc : c t = none)
    (hp : ptOf t = none) :
    (roG g t).run c = ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u) := by
  rw [roG_run, hc]
  simp only [(pick_eq_none_iff g t).2 hp]

/-- The uniform average over the tables. -/
noncomputable def avgG (f : Table → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ g, (Fintype.card Table : ℝ≥0∞)⁻¹ * f g

theorem card_table_ne_zero : (Fintype.card Table : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem avgG_const (a : ℝ≥0∞) : avgG (fun _ ↦ a) = a := by
  rw [avgG, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel card_table_ne_zero (ENNReal.natCast_ne_top _), one_mul]

theorem avgG_le {f : Table → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ g, f g ≤ a) : avgG f ≤ a :=
  (Finset.sum_le_sum fun g _ ↦ by gcongr; exact h g).trans_eq (avgG_const a)

/-- **The run reads the table only off the cache.** -/
theorem roG_congr {g g' : Table} {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ c : KCache, (∀ d, c (.inl (oodEnc d)) = none → g d = g' d) →
      (simulateQ (roG g) oa).run c = (simulateQ (roG g') oa).run c := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro c _; simp
  | query_bind t k ih =>
    intro c hc
    rw [run_query_bind, run_query_bind, roG_run, roG_run]
    rcases hct : c t with _ | u
    · have hp : pick g t = pick g' t := by
        rcases t with x | s
        · simp only [pick]
          rcases hd : oodDecode x with _ | d
          · rfl
          · have := oodEnc_of_decode hd
            subst this
            simp [hc d hct]
        · rfl
      rw [hp]
      rcases pick g' t with _ | u
      · simp only [bind_assoc, pure_bind]
        exact bind_congr fun u ↦ ih u _ fun d hd ↦ hc d (cacheQuery_eq_none hd)
      · simp only [pure_bind]
        exact ih u _ fun d hd ↦ hc d (cacheQuery_eq_none hd)
    · simp only [pure_bind]
      exact ih u c hc

/-- **One table entry is uniform and independent of the others.** -/
theorem avg_update (I : Fintype Digest) (d : OodAll) (Φ : Table → Digest → ℝ≥0∞)
    (hΦ : ∀ g u, Φ (Function.update g d u) u = Φ g u) :
    ∑ u, (@Fintype.card Digest I : ℝ≥0∞)⁻¹ * avgG (fun g ↦ Φ g u) = avgG fun g ↦ Φ g (g d) := by
  classical
  obtain rfl : I = instFintypeDigest := Subsingleton.elim _ _
  set e := Equiv.funSplitAt d Digest
  have hsymm : ∀ v r, (e.symm (v, r)) d = v := fun v r ↦ by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  have hupd : ∀ v r u, Function.update (e.symm (v, r)) d u = e.symm (u, r) := fun v r u ↦ by
    funext j
    by_cases hj : j = d
    · subst hj
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update, hj]
  set S : Digest → ℝ≥0∞ := fun u ↦ ∑ r, Φ (e.symm (u, r)) u
  have h1 : ∀ u, ∑ g, Φ g u = Fintype.card Digest * S u := by
    intro u
    calc ∑ g, Φ g u = ∑ g, Φ (Function.update g d u) u := by simp only [hΦ]
      _ = ∑ p : Digest × ({j // j ≠ d} → Digest), Φ (Function.update (e.symm p) d u) u :=
          (e.symm.sum_comp fun g ↦ Φ (Function.update g d u) u).symm
      _ = ∑ v : Digest, S u := by
          rw [Fintype.sum_prod_type]
          simp only [hupd, S]
      _ = Fintype.card Digest * S u := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ g, Φ g (g d) = ∑ u, S u := by
    calc ∑ g, Φ g (g d) = ∑ p : Digest × ({j // j ≠ d} → Digest), Φ (e.symm p) ((e.symm p) d) :=
          (e.symm.sum_comp fun g ↦ Φ g (g d)).symm
      _ = ∑ u, S u := by
          rw [Fintype.sum_prod_type]
          simp only [hsymm, S]
  have h3 : ∀ u, (Fintype.card Digest : ℝ≥0∞)⁻¹ * avgG (fun g ↦ Φ g u) =
      (Fintype.card Table : ℝ≥0∞)⁻¹ * S u := by
    intro u
    rw [avgG, ← Finset.mul_sum, h1, mul_left_comm, ← mul_assoc ((Fintype.card Digest : ℝ≥0∞)⁻¹),
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  rw [Finset.sum_congr rfl fun u _ ↦ h3 u, ← Finset.mul_sum, avgG, ← Finset.mul_sum, h2]

/-- The same through an equivalence with the answers. -/
theorem avg_update' {R : Type} [Fintype R] (e : R ≃ Digest) (d : OodAll)
    (Φ : Table → R → ℝ≥0∞) (hΦ : ∀ g u, Φ (Function.update g d (e u)) u = Φ g u) :
    ∑ u, (Fintype.card R : ℝ≥0∞)⁻¹ * avgG (fun g ↦ Φ g u) = avgG fun g ↦ Φ g (e.symm (g d)) := by
  have h := avg_update inferInstance d (fun g v ↦ Φ g (e.symm v)) fun g v ↦ by
    simpa using hΦ g (e.symm v)
  rw [← h, Fintype.card_congr e]
  exact Fintype.sum_equiv e _ _ fun u ↦ by rw [Equiv.symm_apply_apply]

/-- The answers at an out-of-domain input are digests. -/
def ptEquiv {t : Bytes ⊕ KeccakState} {d : OodAll} (h : ptOf t = some d) : KeccakCalls.Range t ≃ Digest :=
  Equiv.cast (by rw [ptOf_eq_some h]; rfl)

theorem pick_of_ptOf (g : Table) {t : Bytes ⊕ KeccakState} {d : OodAll} (h : ptOf t = some d) :
    pick g t = some ((ptEquiv h).symm (g d)) := by
  obtain rfl := ptOf_eq_some h
  simp only [ptOf] at h
  simp [pick, h, ptEquiv]

theorem roG_run_pt (g : Table) {t : Bytes ⊕ KeccakState} {c : KCache} {d : OodAll}
    (hc : c t = none) (h : ptOf t = some d) :
    (roG g t).run c = pure ((ptEquiv h).symm (g d), c.cacheQuery t ((ptEquiv h).symm (g d))) := by
  rw [roG_run, hc]
  simp only [pick_of_ptOf g h]

/-- **The lazy random oracle is the average, over the out-of-domain tables, of the oracle with those inputs
answered by the table.** -/
theorem split_eq {α : Type} (E : α × KCache → Prop) (oa : OracleComp KeccakCalls α) :
    ∀ c : KCache, Pr{let z ← (simulateQ randomOracle oa).run c}[E z] =
      avgG fun g : Table ↦ Pr{let z ← (simulateQ (roG g) oa).run c}[E z] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c
    simp only [simulateQ_pure, StateT.run_pure]
    rw [avgG_const]
  | query_bind t k ih =>
    intro c
    rw [run_query_bind, randomOracle.run_eq]
    simp only [run_query_bind]
    rcases hct : c t with _ | u
    · rcases hpt : ptOf t with _ | d
      · simp only [roG_run_none _ hct hpt, bind_assoc, pure_bind, prEvent_bind_eq_sum_fintype,
          SampleableType.prEvent_uniformSample_eq_singleton, ih]
        simp only [avgG, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
        exact mul_left_comm _ _ _
      · simp only [roG_run_pt _ hct hpt, bind_assoc, pure_bind, prEvent_bind_eq_sum_fintype,
          SampleableType.prEvent_uniformSample_eq_singleton, ih]
        refine avg_update' (ptEquiv hpt) d
          (fun g u ↦ Pr{let z ← ((simulateQ (roG g) (k u)).run (c.cacheQuery t u))}[E z])
          fun g u ↦ ?_
        have hc' : ∀ d' : OodAll, (c.cacheQuery t u) (.inl (oodEnc d')) = none →
            Function.update g d (ptEquiv hpt u) d' = g d' := fun d' hd' ↦ by
          have hne : d' ≠ d := by
            rintro rfl
            rw [← ptOf_eq_some hpt, QueryCache.cacheQuery_self] at hd'
            cases hd'
          exact Function.update_of_ne hne _ _
        exact congrArg (fun m ↦ Pr{let z ← m}[E z]) (roG_congr (k u) _ hc')
    · simp only [roG_run_some _ hct, pure_bind]
      exact ih u c

/-! ## The table's oracle is the random oracle of the computation the table answers -/

/-- The cache without its out-of-domain entries. -/
noncomputable def strip (c : KCache) : KCache :=
  QueryCache.ofFn fun t ↦ if (ptOf t).isSome then none else c t

theorem strip_apply (c : KCache) (t : Bytes ⊕ KeccakState) :
    strip c t = if (ptOf t).isSome then none else c t := rfl

theorem strip_of_none {c : KCache} {t : Bytes ⊕ KeccakState} (h : ptOf t = none) : strip c t = c t := by
  rw [strip_apply, h]
  rfl

theorem strip_of_some {c : KCache} {t : Bytes ⊕ KeccakState} {d : OodAll} (h : ptOf t = some d) :
    strip c t = none := by
  rw [strip_apply, h]
  rfl

theorem strip_empty : strip ∅ = ∅ :=
  QueryCache.ext fun t ↦ by
    rw [strip_apply]
    split <;> rfl

theorem strip_cacheQuery_pt (c : KCache) {t : Bytes ⊕ KeccakState} (u : KeccakCalls.Range t)
    {d : OodAll} (h : ptOf t = some d) : strip (c.cacheQuery t u) = strip c :=
  QueryCache.ext fun t' ↦ by
    by_cases ht : t' = t
    · subst ht
      rw [strip_of_some h, strip_of_some h]
    · rw [strip_apply, strip_apply, QueryCache.cacheQuery_of_ne _ _ ht]

theorem strip_cacheQuery_none (c : KCache) {t : Bytes ⊕ KeccakState} (u : KeccakCalls.Range t)
    (h : ptOf t = none) : strip (c.cacheQuery t u) = (strip c).cacheQuery t u :=
  QueryCache.ext fun t' ↦ by
    by_cases ht : t' = t
    · subst ht
      rw [QueryCache.cacheQuery_self, strip_of_none h, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ ht, strip_apply, strip_apply,
        QueryCache.cacheQuery_of_ne _ _ ht]

/-- **The table agrees with the cache** on the out-of-domain inputs it holds. -/
def Inv (g : Table) (c : KCache) : Prop :=
  ∀ t u v, pick g t = some u → c t = some v → v = u

theorem inv_empty (g : Table) : Inv g ∅ := fun _ _ _ _ h ↦ by cases h

theorem inv_cacheQuery {g : Table} {c : KCache} (hc : Inv g c) {t : Bytes ⊕ KeccakState}
    {u : KeccakCalls.Range t} (hu : ∀ u', pick g t = some u' → u = u') : Inv g (c.cacheQuery t u) := by
  intro t' u' v hp hv
  by_cases ht : t' = t
  · subst ht
    rw [QueryCache.cacheQuery_self] at hv
    cases hv
    exact hu _ hp
  · rw [QueryCache.cacheQuery_of_ne _ _ ht] at hv
    exact hc _ _ _ hp hv

theorem roG_run_pick (g : Table) {t : Bytes ⊕ KeccakState} {c : KCache} {u : KeccakCalls.Range t}
    (hc : c t = none) (hp : pick g t = some u) : (roG g t).run c = pure (u, c.cacheQuery t u) := by
  rw [roG_run, hc]
  simp only [hp]

/-- **The out-of-domain queries answered by the table `g`**, the others asked. -/
noncomputable def implG (g : Table) : QueryImpl KeccakCalls (OracleComp KeccakCalls) :=
  fun t ↦ match pick g t with
    | some u => pure u
    | none => liftM (KeccakCalls.query t)

theorem implG_some (g : Table) {t : Bytes ⊕ KeccakState} {u : KeccakCalls.Range t}
    (h : pick g t = some u) : implG g t = pure u := by
  simp only [implG, h]

theorem implG_none (g : Table) {t : Bytes ⊕ KeccakState} (h : pick g t = none) :
    implG g t = liftM (KeccakCalls.query t) := by
  simp only [implG, h]

/-- **Coupling**: the oracle answering the out-of-domain inputs by `g`, its cache stripped of them, is the random
oracle running the computation with those queries answered by `g`. -/
theorem couple (g : Table) {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ c : KCache, Inv g c →
      (fun z ↦ (z.1, strip z.2)) <$> (simulateQ (roG g) oa).run c =
        (simulateQ randomOracle (simulateQ (implG g) oa)).run (strip c) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro c _; simp
  | query_bind t k ih =>
    intro c hc
    rw [run_query_bind, sim_query_bind, simulateQ_bind, StateT.run_bind]
    rcases hp : pick g t with _ | u0
    · have hpt : ptOf t = none := (pick_eq_none_iff g t).1 hp
      rw [implG_none g hp, simulateQ_spec_query]
      rcases hct : c t with _ | v
      · have hst : strip c t = none := by rw [strip_of_none hpt, hct]
        rw [roG_run_none g hct hpt, ro_run_none hst]
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun u ↦ ?_
        rw [← strip_cacheQuery_none c u hpt]
        exact ih u _ (inv_cacheQuery hc fun u' h ↦ by rw [hp] at h; cases h)
      · have hst : strip c t = some v := by rw [strip_of_none hpt, hct]
        rw [roG_run_some g hct, ro_run_some hst]
        simp only [pure_bind]
        exact ih v c hc
    · rw [implG_some g hp, simulateQ_pure, StateT.run_pure, pure_bind]
      obtain ⟨d, hpt⟩ : ∃ d, ptOf t = some d := Option.ne_none_iff_exists'.1 fun h ↦ by
        rw [(pick_eq_none_iff g t).2 h] at hp
        cases hp
      rcases hct : c t with _ | v
      · rw [roG_run_pick g hct hp]
        simp only [pure_bind]
        rw [ih u0 _ (inv_cacheQuery hc fun u' h ↦ by rw [hp] at h; cases h; rfl),
          strip_cacheQuery_pt c u0 hpt]
      · obtain rfl := hc t u0 v hp hct
        rw [roG_run_some g hct]
        simp only [pure_bind]
        exact ih v c hc

/-! ## Implementations that record their answers -/

/-- **An implementation records its answers**: a query's run keeps the cache's entries and records its answer. -/
def Grows (impl : QueryImpl KeccakCalls (StateT KCache ProbComp)) : Prop :=
  ∀ (t : Bytes ⊕ KeccakState) (c : KCache) (p : KeccakCalls.Range t × KCache),
    p ∈ support ((impl t).run c) → c ≤ p.2 ∧ p.2 t = some p.1

theorem grows_roG (g : Table) : Grows (roG g) := by
  intro t c p hp
  rcases hct : c t with _ | v
  · rcases hpk : pick g t with _ | u
    · rw [roG_run_none g hct ((pick_eq_none_iff g t).1 hpk), mem_support_bind_iff] at hp
      obtain ⟨u, -, hp⟩ := hp
      rw [mem_support_pure_iff] at hp
      subst hp
      exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _⟩
    · rw [roG_run_pick g hct hpk, mem_support_pure_iff] at hp
      subst hp
      exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _⟩
  · rw [roG_run_some g hct, mem_support_pure_iff] at hp
    subst hp
    exact ⟨le_rfl, hct⟩

theorem grows_randomOracle : Grows randomOracle := by
  intro t c p hp
  rcases hct : c t with _ | v
  · rw [ro_run_none hct, mem_support_bind_iff] at hp
    obtain ⟨u, -, hp⟩ := hp
    rw [mem_support_pure_iff] at hp
    subst hp
    exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _⟩
  · rw [ro_run_some hct, mem_support_pure_iff] at hp
    subst hp
    exact ⟨le_rfl, hct⟩

/-- **The cache only grows.** -/
theorem support_le {impl : QueryImpl KeccakCalls (StateT KCache ProbComp)} (himpl : Grows impl) {α : Type}
    (oa : OracleComp KeccakCalls α) :
    ∀ (c : KCache) (z : α × KCache), z ∈ support ((simulateQ impl oa).run c) → c ≤ z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro c z hz
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact (himpl t c p hp).1.trans (ih p.1 p.2 z hz)

/-- The table's oracle keeps the table's agreement. -/
theorem roG_inv (g : Table) {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ (c : KCache) (z : α × KCache), z ∈ support ((simulateQ (roG g) oa).run c) → Inv g c → Inv g z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact id
  | query_bind t k ih =>
    intro c z hz hc
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine ih p.1 p.2 z hz ?_
    rcases hct : c t with _ | v
    · rcases hpk : pick g t with _ | u
      · rw [roG_run_none g hct ((pick_eq_none_iff g t).1 hpk), mem_support_bind_iff] at hp
        obtain ⟨u, -, hp⟩ := hp
        rw [mem_support_pure_iff] at hp
        subst hp
        exact inv_cacheQuery hc fun u' h ↦ by rw [hpk] at h; cases h
      · rw [roG_run_pick g hct hpk, mem_support_pure_iff] at hp
        subst hp
        exact inv_cacheQuery hc fun u' h ↦ by rw [hpk] at h; cases h; rfl
    · rw [roG_run_some g hct, mem_support_pure_iff] at hp
      subst hp
      exact hc

/-- After the out-of-domain point's queries, its inputs are in the cache. -/
theorem ood_present {impl : QueryImpl KeccakCalls (StateT KCache ProbComp)} (himpl : Grows impl) (n : ℕ)
    (r : Digest) : ∀ (js : List ℕ) (c : KCache) (z : List E × KCache),
    z ∈ support ((simulateQ impl (js.mapM fun j ↦ do
        return elemOf ((digestBytes (← callKeccak256 (oodInput n r j))).drop 8))).run c) →
      ∀ j ∈ js, z.2 (.inl (oodInput n r j)) ≠ none
  | [], _, _, _, j, hj => absurd hj List.not_mem_nil
  | j :: js, c, z, hz, j', hj' => by
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p1, hp1, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p2, hp2, hz⟩ := hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_queryH] at hp1
    obtain ⟨p0, hp0, hp1⟩ := hp1
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp1
    subst hp1
    have h0 := himpl _ _ _ hp0
    have h2 := support_le himpl _ _ _ hp2
    rcases List.mem_cons.1 hj' with rfl | hj'
    · intro hnone
      have := QueryCache.le_def.1 h2 h0.2
      rw [hnone] at this
      cases this
    · exact ood_present himpl n r js _ _ hp2 j' hj'

/-- **An accepting run of `pcsVerifierO` asked the out-of-domain point of the claim's root**, under any
implementation that records its answers. -/
theorem verifierO_present_of {impl : QueryImpl KeccakCalls (StateT KCache ProbComp)} (himpl : Grows impl)
    {n : ℕ} (w : Claim1 n × Proof) (c : KCache) (z : Bool × KCache)
    (hz : z ∈ support ((simulateQ impl (pcsVerifierO w)).run c)) (hacc : z.1 = true) :
    ∀ j < n, z.2 (.inl (oodInput n w.1.root j)) ≠ none := by
  intro j hj
  unfold pcsVerifierO pcsVerifyWithHashO at hz
  by_cases h : minVars ≤ n ∧ n ≤ maxVars
  swap
  · simp only [h, ↓reduceIte] at hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    cases hacc
  simp only [h, and_self, ↓reduceIte] at hz
  by_cases hr : rootOf w.2 = some w.1.root
  swap
  · simp only [hr, ↓reduceIte] at hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p1, -, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p2, -, hz⟩ := hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    cases hacc
  simp only [hr, ↓reduceIte] at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p1, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p2, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p3, hp3, hz⟩ := hz
  have h3 := ood_present himpl n w.1.root (List.range n) p2.2 p3 hp3 j (List.mem_range.2 hj)
  have hle := support_le himpl _ _ _ hz
  intro hnone
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h3
  have := QueryCache.le_def.1 hle hv
  rw [hnone] at this
  cases this

/-! ## The verifiers with the out-of-domain queries answered by a table -/

/-- The hash the table `g` answers at the out-of-domain inputs. -/
noncomputable def hG (g : Table) (x : Bytes) : Digest := ((oodDecode x).map g).getD default

/-- **The out-of-domain point of the table `g`** at `n` variables. -/
noncomputable def zOfGA (g : Table) (n : ℕ) : Digest → Vector E n := oodPointWith (hG g) n

theorem implH_implG_of_none (g : Table) {x : Bytes} (hx : oodDecode x = none) :
    implH (implG g) x = callKeccak256 x := by
  have hp : pick g (.inl x) = none := by simp only [pick, hx, Option.map_none]
  exact implG_none g hp

theorem implH_implG_enc (g : Table) (d : OodAll) : implH (implG g) (oodEnc d) = pure (g d) :=
  implG_some g (pick_enc g d)

theorem implF_implG (g : Table) : implF (implG g) = callKeccakF1600 := rfl

theorem agree8_implG (g : Table) : Agree8 (implH (implG g)) callKeccak256 :=
  fun _ hx ↦ implH_implG_of_none g (oodDecode_of_mod hx)

theorem hG_enc (g : Table) (d : OodAll) : hG g (oodEnc d) = g d := by
  simp [hG, oodDecode_enc d]

theorem sim_oodPoint {n : ℕ} (hn : n < 256) (g : Table) (r : Digest) : ∀ js : List ℕ, (∀ j ∈ js, j < n) →
    simulateQ (implG g) (js.mapM fun j ↦ do
        return elemOf ((digestBytes (← callKeccak256 (oodInput n r j))).drop 8)) =
      pure (js.map fun j ↦ elemOf ((digestBytes (hG g (oodInput n r j))).drop 8))
  | [], _ => by simp
  | j :: js, hjs => by
    have hj : j < n := hjs j List.mem_cons_self
    have ih := sim_oodPoint hn g r js fun j' h ↦ hjs j' (List.mem_cons_of_mem _ h)
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_queryH]
    rw [oodInput_eq_enc hn hj r, implH_implG_enc g]
    simp only [pure_bind, ih, List.map_cons]
    rw [oodInput_eq_enc hn hj r, hG_enc]

/-- **The oracle verifier with the out-of-domain queries answered by `g`** is `pcsVerifier` at the point
`zOfGA g n`. -/
theorem sim_verifierO {n : ℕ} (hn : n < 256) (g : Table) (w : Claim1 n × Proof) :
    simulateQ (implG g) (pcsVerifierO w) = pcsVerifier (zOfGA g n) w := by
  have hc : implH (implG g) (claimBytes w.1) = callKeccak256 (claimBytes w.1) :=
    implH_implG_of_none g (oodDecode_of_length (by rw [claimBytes_length]; omega))
  unfold pcsVerifierO pcsVerifyWithHashO pcsVerifier pcsVerifyWithHash
  split_ifs with h hr
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG]
    refine bind_congr fun iv ↦ bind_congr fun seed ↦ ?_
    rw [oodPointM, sim_oodPoint hn g _ _ fun j hj ↦ List.mem_range.1 hj, pure_bind,
      simulateQ_runProof, implF_implG, runProof_congr _ (agree8_implG g), zOfGA,
      toList_oodPointWith]
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG,
      simulateQ_pure]
  · rw [simulateQ_pure]

/-- **The fixed-point verifier with the out-of-domain queries answered by `g`** is itself: it asks no `46`-byte
input. -/
theorem sim_pcsVerifier {n : ℕ} (g : Table) (zOf : Digest → Vector E n) (w : Claim1 n × Proof) :
    simulateQ (implG g) (pcsVerifier zOf w) = pcsVerifier zOf w := by
  have hc : implH (implG g) (claimBytes w.1) = callKeccak256 (claimBytes w.1) :=
    implH_implG_of_none g (oodDecode_of_length (by rw [claimBytes_length]; omega))
  unfold pcsVerifier pcsVerifyWithHash
  split_ifs with h hr
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG]
    refine bind_congr fun iv ↦ bind_congr fun seed ↦ ?_
    rw [simulateQ_runProof, implF_implG, runProof_congr _ (agree8_implG g)]
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG,
      simulateQ_pure]
  · rw [simulateQ_pure]

theorem isTotalQueryBound_implG (g : Table) {α : Type} (A : OracleComp KeccakCalls α) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (simulateQ (implG g) A) QA := by
  have := IsTotalQueryBound.simulateQ_of_step_le (impl := implG g) (step := 1) hA fun t ↦ by
    unfold implG
    split
    · trivial
    · rw [← bind_pure (liftM (KeccakCalls.query t))]
      exact isTotalQueryBound_query_bind_iff.2 ⟨Nat.one_pos, fun _ ↦ trivial⟩
  simpa using this

/-! ## The events -/

theorem extract_strip (c : KCache) (r : Digest) (ht wd : ℕ) :
    extract (fun x ↦ strip c (.inl x)) r ht wd = extract (fun x ↦ c (.inl x)) r ht wd :=
  extract_congr (fun x hx ↦ strip_of_none (by simp only [ptOf]; exact oodDecode_of_mod hx)) r ht wd

/-- **The events agree**, the point read off the cache: on a cache the table agrees with and holding the
out-of-domain point of the claim's root, `PcsDoomedO` is `PcsDoomed` at the table's point on the stripped cache. -/
theorem doomed_transfer {n : ℕ} (hn : n < 256) (g : Table) (w : Claim1 n × Proof) (c : KCache)
    (hinv : Inv g c) (hpres : ∀ j < n, c (.inl (oodInput n w.1.root j)) ≠ none)
    (h : PcsDoomedO w c) : PcsDoomed (zOfGA g n) w (strip c) := by
  have hz : zOfCache c n w.1.root = zOfGA g n w.1.root := by
    unfold zOfCache zOfGA oodPointWith
    congr 1
    funext j
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hpres j j.isLt)
    have he := oodInput_eq_enc hn j.isLt w.1.root
    have hv' : v = g (⟨n, hn⟩, w.1.root, ⟨j, by omega⟩) :=
      hinv _ _ _ (by rw [he]; exact pick_enc g _) hv
    rw [hv, Option.getD_some, hv', he, hG_enc]
  intro q hq
  rw [extract_strip] at hq
  rw [← hz]
  exact h q hq

/-- **The events agree**, the point fixed: extraction reads no out-of-domain input. -/
theorem doomed_strip {n : ℕ} (zOf : Digest → Vector E n) (w : Claim1 n × Proof) (c : KCache)
    (h : PcsDoomed zOf w c) : PcsDoomed zOf w (strip c) := by
  intro q hq
  rw [extract_strip] at hq
  exact h q hq

/-! ## The union -/

section Union

variable {ε : ℝ≥0∞} (U : PcsShapes ε) (S : ℕ → Bool) (zOf : (n : ℕ) → Digest → Vector E n)

/-- **The union's verifier, the point read off Keccak-256 at the sizes of `S`**: the indexed size's
`pcsVerifierO` there, its `pcsVerifier` at `zOf n` elsewhere. -/
def pUVerO (w : PSt U × Proof) : OracleComp KeccakCalls Bool :=
  if S (U.shs.get w.1.1).n then pcsVerifierO (w.1.2, w.2) else pcsVerifier (zOf (U.shs.get w.1.1).n) (w.1.2, w.2)

/-- **The union's event**: at the sizes of `S`, `PcsDoomedO` (the point read off the cache); elsewhere
`PcsDoomed` at `zOf n`. -/
def PUDoomedO (w : PSt U × Proof) (c : KCache) : Prop :=
  if S (U.shs.get w.1.1).n then PcsDoomedO (w.1.2, w.2) c else PcsDoomed (zOf (U.shs.get w.1.1).n) (w.1.2, w.2) c

/-- The points of a split world: the table's at the sizes of `S`, `zOf n` elsewhere. -/
noncomputable def zMix (g : Table) (n : ℕ) : Digest → Vector E n := if S n then zOfGA g n else zOf n

theorem sim_pUVerO (g : Table) (w : PSt U × Proof) :
    simulateQ (implG g) (pUVerO U S zOf w) = pUVer U (zMix S zOf g) w := by
  have hn : (U.shs.get w.1.1).n < 256 := n_lt_256 _
  unfold pUVerO pUVer zMix
  by_cases hS : S (U.shs.get w.1.1).n
  · simp only [hS, ↓reduceIte]
    exact sim_verifierO hn g _
  · simp only [hS, Bool.false_eq_true, ↓reduceIte]
    exact sim_pcsVerifier g _ _

/-- **Fiat-Shamir soundness of PCS openings of several sizes, charged once, the out-of-domain point read off
Keccak-256 at the sizes of `S`**: an adversary of at most `QA` queries to Keccak-256 and Keccak-f[1600] that outputs a
size's index, a claim of that size and a proof makes the verifier accept while every candidate of the word extracted
for the claim's root violates `f(z) = ood` or `f(point) = value` (`z` read off the final cache at the sizes of `S`,
`zOf n root` elsewhere) with probability at most `(QA + QV) · (ε + 5 (QA + QV) / 2^256)`, `pcs_union_sound`'s
bound. -/
theorem pcs_union_sound_oracle (A : OracleComp KeccakCalls (PSt U × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV) :
    Pr{let z ← romExperiment A (pUVerO U S zOf)}[z.1.2 = true ∧ PUDoomedO U S zOf z.1.1 z.2] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set X : OracleComp KeccakCalls ((PSt U × Proof) × Bool) :=
    A >>= fun a ↦ (a, ·) <$> pUVerO U S zOf a with hX
  have hexp : romExperiment A (pUVerO U S zOf) = (simulateQ randomOracle X).run ∅ := rfl
  rw [hexp, split_eq _ X ∅]
  refine avgG_le fun g ↦ ?_
  have hsim : simulateQ (implG g) X =
      simulateQ (implG g) A >>= fun a ↦ (a, ·) <$> pUVer U (zMix S zOf g) a := by
    rw [hX, simulateQ_bind]
    refine bind_congr fun a ↦ ?_
    rw [simulateQ_map, sim_pUVerO U S zOf g a]
  calc Pr{let z ← (simulateQ (roG g) X).run ∅}[z.1.2 = true ∧ PUDoomedO U S zOf z.1.1 z.2]
      ≤ Pr{let z ← (simulateQ (roG g) X).run ∅}[
          z.1.2 = true ∧ PUDoomed U (zMix S zOf g) z.1.1 (strip z.2)] := by
        refine prEvent_mono_of_support _ _ _ fun z hz hE ↦ ⟨hE.1, ?_⟩
        rw [hX, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [simulateQ_map, StateT.run_map, support_map] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        have hinv := roG_inv g _ _ _ hr (roG_inv g _ _ _ hp (inv_empty g))
        have hn : (U.shs.get p.1.1.1).n < 256 := n_lt_256 _
        have hE2 := hE.2
        unfold PUDoomed zMix
        unfold PUDoomedO at hE2
        by_cases hS : S (U.shs.get p.1.1.1).n
        · simp only [hS, ↓reduceIte] at hE2 ⊢
          have hacc : r.1 = true := hE.1
          have hr' : r ∈ support ((simulateQ (roG g) (pcsVerifierO (p.1.1.2, p.1.2))).run p.2) := by
            unfold pUVerO at hr
            simpa only [hS, ↓reduceIte] using hr
          exact doomed_transfer hn g _ r.2 hinv (verifierO_present_of (grows_roG g) _ _ r hr' hacc) hE2
        · simp only [hS, Bool.false_eq_true, ↓reduceIte] at hE2 ⊢
          exact doomed_strip _ _ _ hE2
    _ = Pr{let z ← (fun z ↦ (z.1, strip z.2)) <$> (simulateQ (roG g) X).run ∅}[
          z.1.2 = true ∧ PUDoomed U (zMix S zOf g) z.1.1 z.2] := by rw [prEvent_map]
    _ = Pr{let z ← romExperiment (simulateQ (implG g) A) (pUVer U (zMix S zOf g))}[
          z.1.2 = true ∧ PUDoomed U (zMix S zOf g) z.1.1 z.2] := by
        rw [couple g X ∅ (inv_empty g), strip_empty, hsim]
        rfl
    _ ≤ _ := pcs_union_sound U (zMix S zOf g) _ QA (isTotalQueryBound_implG g A QA hA) QV hQV

end Union

/-! ## The oracle verifier over a hash function -/

section Pure

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem oodPointM_pure (h : Bytes → Digest) (n : ℕ) (r : Digest) :
    oodPointM (m := m) (fun x ↦ pure (h x)) n r = pure (oodPointWith h n r).toList := by
  rw [oodPointM, toList_oodPointWith]
  generalize List.range n = js
  induction js with
  | nil => simp
  | cons j js ih => simp [List.mapM_cons]

/-- **The oracle verifier over a hash function `h`** is `pcsVerifyWithHash` at the point `oodPointWith h n`: an
honest proof's out-of-domain answer is the stack's value there. -/
theorem pcsVerifyWithHashO_pure (h : Bytes → Digest) (F : KeccakState → m KeccakState) {n : ℕ} (x : Claim1 n)
    (π : Proof) :
    pcsVerifyWithHashO (fun y ↦ pure (h y)) F x π =
      pcsVerifyWithHash (fun y ↦ pure (h y)) F (oodPointWith h n) x π := by
  unfold pcsVerifyWithHashO pcsVerifyWithHash
  split_ifs
  · refine bind_congr fun _ ↦ bind_congr fun _ ↦ ?_
    rw [oodPointM_pure, pure_bind]
  · rfl
  · rfl

end Pure

/-- **The same in `Id`** (the form of `UniKeccakComplete`'s honest-prover lemmas). -/
theorem pcsVerifyWithHashO_id (H : Bytes → Digest) (F : KeccakState → KeccakState) {n : ℕ} (x : Claim1 n)
    (π : Proof) :
    pcsVerifyWithHashO (m := Id) H F x π = pcsVerifyWithHash (m := Id) H F (oodPointWith H n) x π :=
  pcsVerifyWithHashO_pure (m := Id) H F x π

/-- At the deployed Keccak-256 the point is `oodPoint`. -/
theorem oodPointWith_keccak256 (n : ℕ) : oodPointWith keccak256 n = oodPoint n := rfl

end WhirBridge.Pcs.UnionO

/-- info: 'WhirBridge.Pcs.UnionO.split_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.UnionO.split_eq

/-- info: 'WhirBridge.Pcs.UnionO.couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.UnionO.couple

/-- info: 'WhirBridge.Pcs.UnionO.pcs_union_sound_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.UnionO.pcs_union_sound_oracle

/-- info: 'WhirBridge.Pcs.UnionO.verifierO_present_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.UnionO.verifierO_present_of

/-- info: 'WhirBridge.Pcs.UnionO.pcsVerifyWithHashO_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.UnionO.pcsVerifyWithHashO_pure
