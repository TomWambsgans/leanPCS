/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

Version 1's opening with the out-of-domain point read off Keccak-256 by the verifier, as deployed
(`crates/pcs_claim/src/lib.rs`, `ood_point`; the Statement's `openingWith`), and its Fiat-Shamir
soundness from `pcs_sound` by splitting the random oracle on the out-of-domain inputs.
-/
import WhirBridge.PcsClaim

/-!
# The out-of-domain point read off Keccak-256

`pcs_sound` holds for every out-of-domain derivation `zOf : Digest → Vector E n` fixed in advance.
The deployed verifier (`pcs::verify_claim`, `ood_point`; the Statement's `openingWith`) computes the
point itself with `n` Keccak-256 queries `oodInput n root j` (`OOD_TAG ‖ 1 ‖ n ‖ root ‖ j`, `46`
bytes), after the root check, and the adversary may have asked them before (`pcsVerifierO`). Its
event reads the point off the final cache (`zOfCache`, `PcsDoomedO`).

The proof splits the lazily sampled random oracle on those inputs (`OodDom n`: a root and a
coordinate), which no other input of the opening is: the claim's bytes are `82 + 24 n` long, Merkle
nodes `64`, leaves `8` per word, and mumbai's `extract` reads only nodes and leaves
(`run_congr`, `extract_congr`).

* `split_eq`: the random oracle is the average, over the tables `g : OodDom n → Digest`, of the
  oracle `roG g` answering the out-of-domain inputs by `g` (one fresh entry at a time is uniform and
  independent of the rest of the table: `avg_update`);
* `couple`: `roG g`, its cache stripped of the out-of-domain inputs, is the random oracle running the
  computation with those queries answered by `g` (`implG g`);
* `sim_verifierO`: the verifier with its out-of-domain queries answered by `g` is `pcs_sound`'s
  `pcsVerifier` at the fixed point `zOfG g`; `isTotalQueryBound_implG`: the adversary with them
  answered by `g` asks at most as many queries;
* `verifierO_present`, `doomed_transfer`: an accepting run asked the point, which the table answers,
  so the events agree;
* **`pcs_sound_oracle`**: the bound of `pcs_sound`, `openingBound QA` (`≤ 2^-63` for `QA ≤ 2^64`),
  for the verifier reading the point off Keccak-256; **`pcs_sound_any_oracle`**: for claims of any
  `n`, `14 · openingBound QA`.
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The opening reads Keccak-256 at multiples of eight bytes -/

section Congr

variable {m : Type → Type} [Monad m] {H H' : Bytes → m Digest}

/-- `H` and `H'` agree on every input of a multiple of eight bytes. -/
def Agree8 (H H' : Bytes → m Digest) : Prop := ∀ x : Bytes, x.length % 8 = 0 → H x = H' x

theorem length_flatMap_kBytes : ∀ l : List K, (l.flatMap kBytes).length = 8 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, kBytes_length, length_flatMap_kBytes l,
      List.length_cons]
    ring

theorem pair_length_mod (a b : Digest) : (digestBytes a ++ digestBytes b).length % 8 = 0 := by
  simp [digestBytes_length']

theorem climb_congr (h : Agree8 H H') : ∀ (node : Digest) (q : ℕ) (path : List Digest),
    climbWithHash H node q path = climbWithHash H' node q path
  | _, _, [] => rfl
  | node, q, s :: ss => by
    simp only [climbWithHash]
    split <;>
    · rw [h _ (pair_length_mod _ _)]
      congr 1
      funext p
      exact climb_congr h p _ ss

theorem openOne_congr (h : Agree8 H H') (root : Digest) (ht w q : ℕ) (o : Opening) :
    openOneWithHash H root ht w q o = openOneWithHash H' root ht w q o := by
  unfold openOneWithHash
  split
  · rw [h _ (by rw [length_flatMap_kBytes]; omega)]
    congr 1
    funext ld
    rw [climb_congr h]
  · rfl

theorem openAll_congr (h : Agree8 H H') (root : Digest) (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening),
      openAllWithHash H root ht w ps os = openAllWithHash H' root ht w ps os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | q :: qs, o :: os => by
    simp only [openAllWithHash, openOne_congr h, openAll_congr h root ht w qs os]

variable (F : KeccakState → m KeccakState)

theorem run_congr (h : Agree8 H H') :
    ∀ (p : Prog Bool) (s : ProgState), runWithHash H F p s = runWithHash H' F p s
  | .ret a, s => rfl
  | .fail, s => rfl
  | .read k, s => by
    simp only [runWithHash]
    split
    · rfl
    · congr 1; funext sp; exact run_congr h _ _
  | .sample k, s => by
    simp only [runWithHash]
    congr 1; funext r; exact run_congr h _ _
  | .grind bits k, s => by
    simp only [runWithHash]
    split
    · rfl
    · congr 1; funext sp; congr 1; funext r
      split
      · exact run_congr h _ _
      · rfl
  | .commit ht w k, s => by
    simp only [runWithHash]
    split
    · congr 1; funext sp0; congr 1; funext sp1
      split
      · exact run_congr h _ _
      · rfl
    · rfl
  | .query i ps k, s => by
    simp only [runWithHash]
    split
    · rfl
    · rw [openAll_congr h]
      congr 1; funext o
      split
      · exact run_congr h _ _
      · rfl

theorem runProof_congr (h : Agree8 H H') (P : Prog Bool) (seed : KeccakState) (π : Proof) :
    runProofWithHash H F P seed π = runProofWithHash H' F P seed π := by
  simp only [runProofWithHash, run_congr F h]

end Congr

/-- **Extraction reads Keccak-256 at multiples of eight bytes** (leaves of words, nodes of two
digests). -/
theorem extract_congr {H H' : Bytes → Option Digest} (h : ∀ x : Bytes, x.length % 8 = 0 → H x = H' x)
    (r : Digest) (ht w : ℕ) : extract H r ht w = extract H' r ht w := by
  funext p
  unfold extract
  have : (fun o ↦ openOneWithHash (m := Option) H r ht w p o = some true) =
      fun o ↦ openOneWithHash (m := Option) H' r ht w p o = some true :=
    funext fun o ↦ by rw [openOne_congr h]
  rw [this]

/-! ## The out-of-domain inputs -/

/-- The out-of-domain inputs at `n` variables: a root and a coordinate. -/
abbrev OodDom (n : ℕ) : Type := Digest × Fin n

/-- Their bytes, `oodInput n root j`. -/
def oodEnc {n : ℕ} (d : OodDom n) : Bytes := oodInput n d.1 d.2

theorem oodInput_length (n : ℕ) (r : Digest) (j : ℕ) : (oodInput n r j).length = 46 := by
  simp [oodInput, oodTag, digestBytes_length']

theorem oodEnc_injective {n : ℕ} (hn : n ≤ 256) : Function.Injective (oodEnc (n := n)) := by
  rintro ⟨r, j⟩ ⟨r', j'⟩ h
  simp only [oodEnc, oodInput] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [digestBytes_length'])
  obtain ⟨-, h3⟩ := List.append_inj h1 (by simp)
  have hr := digestBytes_injective h3
  have hj : (j : ℕ).toUInt8 = (j' : ℕ).toUInt8 := by simpa using h2
  have hj' := congrArg UInt8.toNat hj
  simp only [Nat.toUInt8] at hj'
  have e : ∀ a : ℕ, (UInt8.ofNat a).toNat = a % 256 := fun a ↦ UInt8.toNat_ofNat
  rw [e, e] at hj'
  have := j.isLt
  have := j'.isLt
  refine Prod.ext hr (Fin.ext ?_)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hj'
  exact hj'

/-- The root and coordinate of an out-of-domain input (decided classically: the roots are `2^256`). -/
noncomputable def oodDecode {n : ℕ} (x : Bytes) : Option (OodDom n) :=
  @dite _ (∃ d : OodDom n, oodEnc d = x) (Classical.propDecidable _)
    (fun h ↦ some (Classical.choose h)) fun _ ↦ none

theorem oodEnc_of_decode {n : ℕ} {x : Bytes} {d : OodDom n} (h : oodDecode x = some d) :
    oodEnc d = x := by
  unfold oodDecode at h
  split_ifs at h with hx
  cases h
  exact Classical.choose_spec hx

theorem oodDecode_enc {n : ℕ} (hn : n ≤ 256) (d : OodDom n) : oodDecode (oodEnc d) = some d := by
  have hx : ∃ d', oodEnc d' = oodEnc d := ⟨d, rfl⟩
  unfold oodDecode
  split_ifs
  exact congrArg some (oodEnc_injective hn (Classical.choose_spec hx))

theorem oodDecode_of_length {n : ℕ} {x : Bytes} (hx : x.length ≠ 46) :
    oodDecode (n := n) x = none := by
  unfold oodDecode
  split_ifs with h
  · obtain ⟨d, hd⟩ := h
    exact absurd (hd ▸ oodInput_length _ _ _) hx
  · rfl

theorem oodDecode_of_mod {n : ℕ} {x : Bytes} (hx : x.length % 8 = 0) :
    oodDecode (n := n) x = none :=
  oodDecode_of_length fun h ↦ by rw [h] at hx; exact absurd hx (by decide)

variable {n : ℕ}

/-- The out-of-domain input a query is, if any. -/
noncomputable def ptOf : (Bytes ⊕ KeccakState) → Option (OodDom n)
  | .inl x => oodDecode x
  | .inr _ => none

/-- The answer the table `g` gives a query, if it is an out-of-domain input. -/
noncomputable def pick (g : OodDom n → Digest) : (t : Bytes ⊕ KeccakState) → Option (KeccakCalls.Range t)
  | .inl x => (oodDecode x).map g
  | .inr _ => none

theorem pick_eq_none_iff (g : OodDom n → Digest) (t : Bytes ⊕ KeccakState) :
    pick g t = none ↔ ptOf (n := n) t = none := by
  rcases t with x | s <;> simp [pick, ptOf]

theorem ptOf_eq_some {t : Bytes ⊕ KeccakState} {d : OodDom n} (h : ptOf t = some d) :
    t = .inl (oodEnc d) := by
  rcases t with x | s
  · exact congrArg Sum.inl (oodEnc_of_decode h).symm
  · cases h

theorem pick_enc (hn : n ≤ 256) (g : OodDom n → Digest) (d : OodDom n) :
    pick g (.inl (oodEnc d)) = some (g d) := by
  simp [pick, oodDecode_enc hn d]

/-! ## The random oracle split on the out-of-domain inputs -/

/-- The oracle's cache. -/
abbrev KCache : Type := KeccakCalls.QueryCache

/-- The tables of the out-of-domain inputs. -/
abbrev Table (n : ℕ) : Type := OodDom n → Digest

/-- **The random oracle with the out-of-domain inputs answered by the table `g`**: a cached answer
first; else `g`'s answer at an out-of-domain input and a uniform one elsewhere, recorded. -/
noncomputable def roG (g : Table n) : QueryImpl KeccakCalls (StateT KCache ProbComp) :=
  fun t ↦ StateT.mk fun c ↦ match c t with
    | some u => pure (u, c)
    | none => match pick g t with
      | some u => pure (u, c.cacheQuery t u)
      | none => ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u)

theorem roG_run (g : Table n) (t : Bytes ⊕ KeccakState) (c : KCache) :
    (roG g t).run c = match c t with
      | some u => pure (u, c)
      | none => match pick g t with
        | some u => pure (u, c.cacheQuery t u)
        | none => ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u) := rfl

theorem roG_run_some (g : Table n) {t : Bytes ⊕ KeccakState} {c : KCache} {u : KeccakCalls.Range t}
    (hc : c t = some u) : (roG g t).run c = pure (u, c) := by
  rw [roG_run, hc]

theorem roG_run_none (g : Table n) {t : Bytes ⊕ KeccakState} {c : KCache} (hc : c t = none)
    (hp : ptOf (n := n) t = none) :
    (roG g t).run c = ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u) := by
  rw [roG_run, hc]
  simp only [(pick_eq_none_iff g t).2 hp]

theorem run_query_bind {σ α : Type} (impl : QueryImpl KeccakCalls (StateT σ ProbComp))
    (t : Bytes ⊕ KeccakState) (k : KeccakCalls.Range t → OracleComp KeccakCalls α) (c : σ) :
    (simulateQ impl (liftM (KeccakCalls.query t) >>= k)).run c =
      (impl t).run c >>= fun p ↦ (simulateQ impl (k p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, monadLift_self]
  rfl

/-- The uniform average over the tables. -/
noncomputable def avgG (f : Table n → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ g, (Fintype.card (Table n) : ℝ≥0∞)⁻¹ * f g

theorem card_table_ne_zero : (Fintype.card (Table n) : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem avgG_const (a : ℝ≥0∞) : avgG (n := n) (fun _ ↦ a) = a := by
  rw [avgG, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel card_table_ne_zero (ENNReal.natCast_ne_top _), one_mul]

theorem avgG_le {f : Table n → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ g, f g ≤ a) : avgG f ≤ a :=
  (Finset.sum_le_sum fun g _ ↦ by gcongr; exact h g).trans_eq (avgG_const a)

theorem cacheQuery_eq_none {c : KCache} {t t' : Bytes ⊕ KeccakState} {u : KeccakCalls.Range t}
    (h : (c.cacheQuery t u) t' = none) : c t' = none := by
  by_cases ht : t' = t
  · subst ht
    rw [QueryCache.cacheQuery_self] at h
    cases h
  · rwa [QueryCache.cacheQuery_of_ne _ _ ht] at h

/-- **The run reads the table only off the cache.** -/
theorem roG_congr {g g' : Table n} {α : Type} (oa : OracleComp KeccakCalls α) :
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
          rcases hd : oodDecode (n := n) x with _ | d
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
theorem avg_update (I : Fintype Digest) (d : OodDom n) (Φ : Table n → Digest → ℝ≥0∞)
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
      (Fintype.card (Table n) : ℝ≥0∞)⁻¹ * S u := by
    intro u
    rw [avgG, ← Finset.mul_sum, h1, mul_left_comm, ← mul_assoc ((Fintype.card Digest : ℝ≥0∞)⁻¹),
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  rw [Finset.sum_congr rfl fun u _ ↦ h3 u, ← Finset.mul_sum, avgG, ← Finset.mul_sum, h2]


/-- The same through an equivalence with the answers. -/
theorem avg_update' {R : Type} [Fintype R] (e : R ≃ Digest) (d : OodDom n)
    (Φ : Table n → R → ℝ≥0∞) (hΦ : ∀ g u, Φ (Function.update g d (e u)) u = Φ g u) :
    ∑ u, (Fintype.card R : ℝ≥0∞)⁻¹ * avgG (fun g ↦ Φ g u) = avgG fun g ↦ Φ g (e.symm (g d)) := by
  have h := avg_update inferInstance d (fun g v ↦ Φ g (e.symm v)) fun g v ↦ by
    simpa using hΦ g (e.symm v)
  rw [← h, Fintype.card_congr e]
  exact Fintype.sum_equiv e _ _ fun u ↦ by rw [Equiv.symm_apply_apply]

/-- The answers at an out-of-domain input are digests. -/
def ptEquiv {t : Bytes ⊕ KeccakState} {d : OodDom n} (h : ptOf t = some d) :
    KeccakCalls.Range t ≃ Digest :=
  Equiv.cast (by rw [ptOf_eq_some h]; rfl)

theorem pick_of_ptOf (g : Table n) {t : Bytes ⊕ KeccakState} {d : OodDom n}
    (h : ptOf t = some d) : pick g t = some ((ptEquiv h).symm (g d)) := by
  obtain rfl := ptOf_eq_some h
  simp only [ptOf] at h
  simp [pick, h, ptEquiv]

theorem roG_run_pt (g : Table n) {t : Bytes ⊕ KeccakState} {c : KCache} {d : OodDom n}
    (hc : c t = none) (h : ptOf t = some d) :
    (roG g t).run c = pure ((ptEquiv h).symm (g d), c.cacheQuery t ((ptEquiv h).symm (g d))) := by
  rw [roG_run, hc]
  simp only [pick_of_ptOf g h]

/-- **The lazy random oracle is the average, over the out-of-domain tables, of the oracle with
those inputs answered by the table** (from any cache, for any event of the outcome and the final
cache). -/
theorem split_eq {α : Type} (E : α × KCache → Prop) (oa : OracleComp KeccakCalls α) :
    ∀ c : KCache, Pr{let z ← (simulateQ randomOracle oa).run c}[E z] =
      avgG fun g : Table n ↦ Pr{let z ← (simulateQ (roG g) oa).run c}[E z] := by
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
    · rcases hpt : ptOf (n := n) t with _ | d
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
        have hc' : ∀ d' : OodDom n, (c.cacheQuery t u) (.inl (oodEnc d')) = none →
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
  QueryCache.ofFn fun t ↦ if (ptOf (n := n) t).isSome then none else c t

theorem strip_apply (c : KCache) (t : Bytes ⊕ KeccakState) :
    strip (n := n) c t = if (ptOf (n := n) t).isSome then none else c t := rfl

theorem strip_of_none {c : KCache} {t : Bytes ⊕ KeccakState} (h : ptOf (n := n) t = none) :
    strip (n := n) c t = c t := by
  rw [strip_apply, h]
  rfl

theorem strip_of_some {c : KCache} {t : Bytes ⊕ KeccakState} {d : OodDom n} (h : ptOf t = some d) :
    strip (n := n) c t = none := by
  rw [strip_apply, h]
  rfl

theorem strip_empty : strip (n := n) ∅ = ∅ :=
  QueryCache.ext fun t ↦ by
    rw [strip_apply]
    split <;> rfl

theorem strip_cacheQuery_pt (c : KCache) {t : Bytes ⊕ KeccakState} (u : KeccakCalls.Range t)
    {d : OodDom n} (h : ptOf t = some d) : strip (n := n) (c.cacheQuery t u) = strip (n := n) c :=
  QueryCache.ext fun t' ↦ by
    by_cases ht : t' = t
    · subst ht
      rw [strip_of_some h, strip_of_some h]
    · rw [strip_apply, strip_apply, QueryCache.cacheQuery_of_ne _ _ ht]

theorem strip_cacheQuery_none (c : KCache) {t : Bytes ⊕ KeccakState} (u : KeccakCalls.Range t)
    (h : ptOf (n := n) t = none) :
    strip (n := n) (c.cacheQuery t u) = (strip (n := n) c).cacheQuery t u :=
  QueryCache.ext fun t' ↦ by
    by_cases ht : t' = t
    · subst ht
      rw [QueryCache.cacheQuery_self, strip_of_none h, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ ht, strip_apply, strip_apply,
        QueryCache.cacheQuery_of_ne _ _ ht]

/-- **The table agrees with the cache** on the out-of-domain inputs it holds. -/
def Inv (g : Table n) (c : KCache) : Prop :=
  ∀ t u v, pick g t = some u → c t = some v → v = u

theorem inv_empty (g : Table n) : Inv g ∅ := fun _ _ _ _ h ↦ by cases h

theorem inv_cacheQuery {g : Table n} {c : KCache} (hc : Inv g c) {t : Bytes ⊕ KeccakState}
    {u : KeccakCalls.Range t} (hu : ∀ u', pick g t = some u' → u = u') :
    Inv g (c.cacheQuery t u) := by
  intro t' u' v hp hv
  by_cases ht : t' = t
  · subst ht
    rw [QueryCache.cacheQuery_self] at hv
    cases hv
    exact hu _ hp
  · rw [QueryCache.cacheQuery_of_ne _ _ ht] at hv
    exact hc _ _ _ hp hv

theorem roG_run_pick (g : Table n) {t : Bytes ⊕ KeccakState} {c : KCache} {u : KeccakCalls.Range t}
    (hc : c t = none) (hp : pick g t = some u) : (roG g t).run c = pure (u, c.cacheQuery t u) := by
  rw [roG_run, hc]
  simp only [hp]

theorem ro_run_none {t : Bytes ⊕ KeccakState} {c : KCache} (hc : c t = none) :
    (randomOracle t).run c = ($ᵗ KeccakCalls.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u) := by
  rw [randomOracle.run_eq, hc]

theorem ro_run_some {t : Bytes ⊕ KeccakState} {c : KCache} {u : KeccakCalls.Range t}
    (hc : c t = some u) : (randomOracle t).run c = pure (u, c) := by
  rw [randomOracle.run_eq, hc]

/-- **The out-of-domain queries answered by the table `g`**, the others asked. -/
noncomputable def implG (g : Table n) : QueryImpl KeccakCalls (OracleComp KeccakCalls) :=
  fun t ↦ match pick g t with
    | some u => pure u
    | none => liftM (KeccakCalls.query t)

theorem implG_some (g : Table n) {t : Bytes ⊕ KeccakState} {u : KeccakCalls.Range t}
    (h : pick g t = some u) : implG g t = pure u := by
  simp only [implG, h]

theorem implG_none (g : Table n) {t : Bytes ⊕ KeccakState} (h : pick g t = none) :
    implG g t = liftM (KeccakCalls.query t) := by
  simp only [implG, h]

theorem sim_query_bind {α : Type} (impl : QueryImpl KeccakCalls (OracleComp KeccakCalls))
    (t : Bytes ⊕ KeccakState) (k : KeccakCalls.Range t → OracleComp KeccakCalls α) :
    simulateQ impl (liftM (KeccakCalls.query t) >>= k) = impl t >>= fun u ↦ simulateQ impl (k u) := by
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, monadLift_self]
  rfl

/-- **Coupling**: the oracle answering the out-of-domain inputs by `g`, its cache stripped of them,
is the random oracle running the computation with those queries answered by `g`. -/
theorem couple (g : Table n) {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ c : KCache, Inv g c →
      (fun z ↦ (z.1, strip (n := n) z.2)) <$> (simulateQ (roG g) oa).run c =
        (simulateQ randomOracle (simulateQ (implG g) oa)).run (strip (n := n) c) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro c _; simp
  | query_bind t k ih =>
    intro c hc
    rw [run_query_bind, sim_query_bind, simulateQ_bind, StateT.run_bind]
    rcases hp : pick g t with _ | u0
    · have hpt : ptOf (n := n) t = none := (pick_eq_none_iff g t).1 hp
      rw [implG_none g hp, simulateQ_spec_query]
      rcases hct : c t with _ | v
      · have hst : strip (n := n) c t = none := by rw [strip_of_none hpt, hct]
        rw [roG_run_none g hct hpt, ro_run_none hst]
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun u ↦ ?_
        rw [← strip_cacheQuery_none c u hpt]
        exact ih u _ (inv_cacheQuery hc fun u' h ↦ by rw [hp] at h; cases h)
      · have hst : strip (n := n) c t = some v := by rw [strip_of_none hpt, hct]
        rw [roG_run_some g hct, ro_run_some hst]
        simp only [pure_bind]
        exact ih v c hc
    · rw [implG_some g hp, simulateQ_pure, StateT.run_pure, pure_bind]
      obtain ⟨d, hpt⟩ : ∃ d, ptOf (n := n) t = some d := Option.ne_none_iff_exists'.1 fun h ↦ by
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

/-- One step of the table's oracle records its answer, keeps the cache's, and keeps the table's
agreement. -/
theorem roG_step (g : Table n) {t : Bytes ⊕ KeccakState} {c : KCache}
    {p : KeccakCalls.Range t × KCache} (hp : p ∈ support ((roG g t).run c)) :
    c ≤ p.2 ∧ p.2 t = some p.1 ∧ (Inv g c → Inv g p.2) := by
  rcases hct : c t with _ | v
  · rcases hpk : pick g t with _ | u
    · rw [roG_run_none g hct ((pick_eq_none_iff g t).1 hpk), mem_support_bind_iff] at hp
      obtain ⟨u, -, hp⟩ := hp
      rw [mem_support_pure_iff] at hp
      subst hp
      exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _,
        fun hc ↦ inv_cacheQuery hc fun u' h ↦ by rw [hpk] at h; cases h⟩
    · rw [roG_run_pick g hct hpk, mem_support_pure_iff] at hp
      subst hp
      exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _,
        fun hc ↦ inv_cacheQuery hc fun u' h ↦ by rw [hpk] at h; cases h; rfl⟩
  · rw [roG_run_some g hct, mem_support_pure_iff] at hp
    subst hp
    exact ⟨le_rfl, hct, id⟩

/-- **The table's oracle only adds to the cache**, and keeps the table's agreement. -/
theorem roG_support (g : Table n) {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ (c : KCache) (z : α × KCache), z ∈ support ((simulateQ (roG g) oa).run c) →
      c ≤ z.2 ∧ (Inv g c → Inv g z.2) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact ⟨le_rfl, id⟩
  | query_bind t k ih =>
    intro c z hz
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    obtain ⟨h1, -, h3⟩ := roG_step g hp
    obtain ⟨h1', h3'⟩ := ih p.1 p.2 z hz
    exact ⟨h1.trans h1', fun hc ↦ h3' (h3 hc)⟩

/-! ## The verifier reading the out-of-domain point off Keccak-256 -/

section RunO

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **`ood_point`** (`lib.rs`, the Statement's `oodPointWith`) over the hash `H`: coordinate `j` the
element the low `24` bytes of `H(oodInput n root j)` encode, `j = 0, …, n − 1`. -/
def oodPointM (n : ℕ) (r : Digest) : m (List E) :=
  (List.range n).mapM fun j ↦ do return elemOf ((digestBytes (← H (oodInput n r j))).drop 8)

/-- **`verify_claim`** over a hash `H` and a permutation `F`, the out-of-domain point computed by
the verifier with `n` calls of `H` after the root check (as the Statement's `openingWith`). -/
def pcsVerifyWithHashO {n : ℕ} (x : Claim1 n) (π : Proof) : m Bool :=
  if minVars ≤ n ∧ n ≤ maxVars then do
    let iv ← H (claimBytes x)
    let seed ← F (seedInput iv publicDigest)
    if rootOf π = some x.root then do
      let z ← oodPointM H n x.root
      runProofWithHash H F (prog n logInvRate z x) seed π
    else pure false
  else pure false

end RunO

/-- **`verify_claim` as an oracle computation**, the out-of-domain point read off Keccak-256. -/
def pcsVerifierO (w : Claim1 n × Proof) : OracleComp KeccakCalls Bool :=
  pcsVerifyWithHashO callKeccak256 callKeccakF1600 w.1 w.2

/-- **The out-of-domain point read off the cache**, the default answer at a coordinate it misses. -/
def zOfCache (c : KCache) (n : ℕ) (r : Digest) : Vector E n :=
  Vector.ofFn fun j ↦
    elemOf ((digestBytes ((c (.inl (oodInput n r j)) : Option Digest).getD default)).drop 8)

/-- **The event**: every candidate of the word extracted for the claim's root violates
`f(z) = ood` or `f(point) = value`, `z` the out-of-domain point read off the final cache. -/
def PcsDoomedO (w : Claim1 n × Proof) (cache : KCache) : Prop :=
  ∀ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
      (extract (fun x ↦ cache (.inl x)) w.1.root (rootHeight n logInvRate) (2 ^ laneFold)),
    colEval q (zOfCache cache n w.1.root).toList ≠ w.1.ood ∨ colEval q w.1.point ≠ w.1.value

/-- The hash the table `g` answers at the out-of-domain inputs. -/
noncomputable def hG (g : Table n) (x : Bytes) : Digest := ((oodDecode (n := n) x).map g).getD default

/-- The out-of-domain point of the table `g`. -/
noncomputable def zOfG (g : Table n) : Digest → Vector E n := oodPointWith (hG g) n

theorem implH_implG_of_none (g : Table n) {x : Bytes} (hx : oodDecode (n := n) x = none) :
    implH (implG g) x = callKeccak256 x := by
  have hp : pick g (.inl x) = none := by simp only [pick, hx, Option.map_none]
  exact implG_none g hp

theorem implH_implG_enc (hn : n ≤ 256) (g : Table n) (d : OodDom n) :
    implH (implG g) (oodEnc d) = pure (g d) :=
  implG_some g (pick_enc hn g d)

theorem implF_implG (g : Table n) : implF (implG g) = callKeccakF1600 := rfl

theorem agree8_implG (g : Table n) : Agree8 (implH (implG g)) callKeccak256 :=
  fun _ hx ↦ implH_implG_of_none g (oodDecode_of_mod hx)

theorem hG_enc (hn : n ≤ 256) (g : Table n) (d : OodDom n) : hG g (oodEnc d) = g d := by
  simp [hG, oodDecode_enc hn d]

theorem sim_oodPoint (hn : n ≤ 256) (g : Table n) (r : Digest) : ∀ js : List ℕ, (∀ j ∈ js, j < n) →
    simulateQ (implG g) (js.mapM fun j ↦ do
        return elemOf ((digestBytes (← callKeccak256 (oodInput n r j))).drop 8)) =
      pure (js.map fun j ↦ elemOf ((digestBytes (hG g (oodInput n r j))).drop 8))
  | [], _ => by simp
  | j :: js, hjs => by
    have hj : j < n := hjs j List.mem_cons_self
    have ih := sim_oodPoint hn g r js fun j' h ↦ hjs j' (List.mem_cons_of_mem _ h)
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_queryH]
    rw [show implH (implG g) (oodInput n r j) = pure (g (r, ⟨j, hj⟩)) from
      implH_implG_enc hn g (r, ⟨j, hj⟩)]
    simp only [pure_bind, ih, List.map_cons]
    rw [show hG g (oodInput n r j) = g (r, ⟨j, hj⟩) from hG_enc hn g (r, ⟨j, hj⟩)]

theorem toList_oodPointWith (h : Bytes → Digest) (n : ℕ) (r : Digest) :
    (oodPointWith h n r).toList =
      (List.range n).map fun j ↦ elemOf ((digestBytes (h (oodInput n r j))).drop 8) := by
  rw [oodPointWith, Vector.toList_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

/-- **The verifier with the out-of-domain queries answered by `g`** is `pcsVerifier` at the point
`zOfG g`: the opening's other Keccak-256 inputs are a multiple of eight bytes long, the claim's
`82 + 24 n`, the out-of-domain inputs `46`. -/
theorem sim_verifierO (hn : n ≤ 256) (g : Table n) (w : Claim1 n × Proof) :
    simulateQ (implG g) (pcsVerifierO w) = pcsVerifier (zOfG g) w := by
  have hc : implH (implG g) (claimBytes w.1) = callKeccak256 (claimBytes w.1) :=
    implH_implG_of_none g (oodDecode_of_length (by rw [claimBytes_length]; omega))
  unfold pcsVerifierO pcsVerifyWithHashO pcsVerifier pcsVerifyWithHash
  split_ifs with h hr
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG]
    refine bind_congr fun iv ↦ bind_congr fun seed ↦ ?_
    rw [oodPointM, sim_oodPoint hn g _ _ fun j hj ↦ List.mem_range.1 hj, pure_bind,
      simulateQ_runProof, implF_implG, runProof_congr _ (agree8_implG g), zOfG,
      toList_oodPointWith]
  · simp only [simulateQ_bind, simulateQ_queryH, hc, simulateQ_queryF, implF_implG,
      simulateQ_pure]
  · rw [simulateQ_pure]

theorem isTotalQueryBound_implG (g : Table n) {α : Type} (A : OracleComp KeccakCalls α) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (simulateQ (implG g) A) QA := by
  have := IsTotalQueryBound.simulateQ_of_step_le (impl := implG g) (step := 1) hA fun t ↦ by
    unfold implG
    split
    · trivial
    · rw [← bind_pure (liftM (KeccakCalls.query t))]
      exact isTotalQueryBound_query_bind_iff.2 ⟨Nat.one_pos, fun _ ↦ trivial⟩
  simpa using this

/-! ## The event read off the cache -/

/-- After the out-of-domain point's queries, its inputs are in the cache. -/
theorem ood_present (g : Table n) (r : Digest) : ∀ (js : List ℕ) (c : KCache) (z : List E × KCache),
    z ∈ support ((simulateQ (roG g) (js.mapM fun j ↦ do
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
    have h0 := roG_step g hp0
    have h2 := (roG_support g _ _ _ hp2).1
    rcases List.mem_cons.1 hj' with rfl | hj'
    · intro hnone
      have := QueryCache.le_def.1 h2 h0.2.1
      rw [hnone] at this
      cases this
    · exact ood_present g r js _ _ hp2 j' hj'

/-- **An accepting run asked the out-of-domain point of the claim's root.** -/
theorem verifierO_present (g : Table n) (w : Claim1 n × Proof) (c : KCache) (z : Bool × KCache)
    (hz : z ∈ support ((simulateQ (roG g) (pcsVerifierO w)).run c)) (hacc : z.1 = true) :
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
  have h3 := ood_present g w.1.root (List.range n) p2.2 p3 hp3 j (List.mem_range.2 hj)
  have hle := (roG_support g _ _ _ hz).1
  intro hnone
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h3
  have := QueryCache.le_def.1 hle hv
  rw [hnone] at this
  cases this

/-- **The events agree**: on a cache the table agrees with and holding the out-of-domain point of
the claim's root, the event read off the cache is `PcsDoomed` at the table's point, on the cache
stripped of the out-of-domain inputs (extraction reads none of them). -/
theorem doomed_transfer (hn : n ≤ 256) (g : Table n) (w : Claim1 n × Proof) (c : KCache)
    (hinv : Inv g c) (hpres : ∀ j < n, c (.inl (oodInput n w.1.root j)) ≠ none)
    (h : PcsDoomedO w c) : PcsDoomed (zOfG g) w (strip (n := n) c) := by
  have hx : ∀ r ht wd, extract (fun x ↦ strip (n := n) c (.inl x)) r ht wd =
      extract (fun x ↦ c (.inl x)) r ht wd := fun r ht wd ↦
    extract_congr (fun x hx ↦ strip_of_none (by simp only [ptOf]; exact oodDecode_of_mod hx)) r ht wd
  have hz : zOfCache c n w.1.root = zOfG g w.1.root := by
    unfold zOfCache zOfG oodPointWith
    congr 1
    funext j
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hpres j j.isLt)
    have hv' : v = g (w.1.root, j) := hinv _ _ _ (pick_enc hn g (w.1.root, j)) hv
    rw [show hG g (oodInput n w.1.root j) = g (w.1.root, j) from hG_enc hn g (w.1.root, j)]
    simp only [hv, hv', Option.getD_some]
  intro q hq
  rw [hx] at hq
  rw [← hz]
  exact h q hq

/-! ## Soundness -/

/-- **Fiat-Shamir soundness of version 1's opening with the out-of-domain point read off
Keccak-256** (`verify_claim` as deployed), in the two-oracle random-oracle model, at every supported
`15 ≤ n ≤ 28`: an adversary of at most `QA` queries to Keccak-256 and Keccak-f[1600] outputs a claim
and a proof; the verifier accepts while every candidate of the word extracted for the claim's root
violates `f(z) = ood` or `f(point) = value`, `z` the out-of-domain point in the final cache, with
probability at most `openingBound QA = (QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)`.

The random oracle is split on the out-of-domain inputs (`split_eq`): for each table `g` of their
answers the run is `pcs_sound`'s experiment for the adversary with its out-of-domain queries answered
by `g` (`couple`, `sim_verifierO`, `isTotalQueryBound_implG`) and the point `zOfG g`, and the events
agree (`verifierO_present`, `doomed_transfer`). -/
theorem pcs_sound_oracle (h1 : minVars ≤ n) (h2 : n ≤ maxVars)
    (A : OracleComp KeccakCalls (Claim1 n × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A pcsVerifierO}[z.1.2 = true ∧ PcsDoomedO z.1.1 z.2] ≤
      openingBound QA := by
  have hn : n ≤ 256 := by unfold maxVars at h2; omega
  set X : OracleComp KeccakCalls ((Claim1 n × Proof) × Bool) :=
    A >>= fun a ↦ (a, ·) <$> pcsVerifierO a with hX
  have hexp : romExperiment A pcsVerifierO = (simulateQ randomOracle X).run ∅ := rfl
  rw [hexp, split_eq (n := n) _ X ∅]
  refine avgG_le fun g ↦ ?_
  have hsim : simulateQ (implG g) X =
      simulateQ (implG g) A >>= fun a ↦ (a, ·) <$> pcsVerifier (zOfG g) a := by
    rw [hX, simulateQ_bind]
    refine bind_congr fun a ↦ ?_
    rw [simulateQ_map, sim_verifierO hn g a]
  calc Pr{let z ← (simulateQ (roG g) X).run ∅}[z.1.2 = true ∧ PcsDoomedO z.1.1 z.2]
      ≤ Pr{let z ← (simulateQ (roG g) X).run ∅}[
          z.1.2 = true ∧ PcsDoomed (zOfG g) z.1.1 (strip (n := n) z.2)] := by
        refine prEvent_mono_of_support _ _ _ fun z hz hE ↦ ⟨hE.1, ?_⟩
        rw [hX, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [simulateQ_map, StateT.run_map, support_map] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        have hinv := (roG_support g _ _ _ hr).2 ((roG_support g _ _ _ hp).2 (inv_empty g))
        exact doomed_transfer hn g p.1 r.2 hinv (verifierO_present g p.1 p.2 r hr hE.1) hE.2
    _ = Pr{let z ← (fun z ↦ (z.1, strip (n := n) z.2)) <$> (simulateQ (roG g) X).run ∅}[
          z.1.2 = true ∧ PcsDoomed (zOfG g) z.1.1 z.2] := by rw [prEvent_map]
    _ = Pr{let z ← romExperiment (simulateQ (implG g) A) (pcsVerifier (zOfG g))}[
          z.1.2 = true ∧ PcsDoomed (zOfG g) z.1.1 z.2] := by
        rw [couple g X ∅ (inv_empty g), strip_empty, hsim]
        rfl
    _ ≤ openingBound QA := pcs_sound h1 h2 (zOfG g) _ QA (isTotalQueryBound_implG g A QA hA)

/-- **The numbers**: against `2^64` queries the bound is at most `2^-63`. -/
theorem pcs_oracle_bound_le {QA : ℕ} (hQ : QA ≤ 2 ^ 64) : openingBound QA ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 :=
  opening_bound_le hQ

/-! ## Claims on any number of variables -/

/-- **`verify_claim` on a claim of any `n`**, the out-of-domain point read off Keccak-256. -/
def pcsVerifierAnyO (w : AnyClaim × Proof) : OracleComp KeccakCalls Bool :=
  pcsVerifierO (w.1.2, w.2)

/-- The event at the claim's own `n`. -/
def PcsDoomedAnyO (w : AnyClaim × Proof) (cache : KCache) : Prop :=
  PcsDoomedO (w.1.2, w.2) cache

/-- The verifier accepts only claims of `15 ≤ n ≤ 28`. -/
theorem vars_of_acceptO (A : OracleComp KeccakCalls (AnyClaim × Proof)) :
    ∀ z ∈ support (romExperiment A pcsVerifierAnyO), z.1.2 = true →
      minVars ≤ z.1.1.1.1 ∧ z.1.1.1.1 ≤ maxVars := by
  intro z hz hacc
  rw [romExperiment_eq, mem_support_bind_iff] at hz
  obtain ⟨p, -, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  by_contra hn
  have hV : pcsVerifierAnyO p.1 = pure false := by
    simp only [pcsVerifierAnyO, pcsVerifierO, pcsVerifyWithHashO, hn, ↓reduceIte]
  rw [hV, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  rw [hr] at hacc
  exact Bool.false_ne_true hacc

/-- At one `m`, the experiment of any `n` restricted to `n = m` is the experiment of `m`. -/
theorem prEvent_any_at_leO (A : OracleComp KeccakCalls (AnyClaim × Proof)) (m : ℕ) :
    Pr{let z ← romExperiment A pcsVerifierAnyO}[
        (z.1.2 = true ∧ PcsDoomedAnyO z.1.1 z.2) ∧ z.1.1.1.1 = m] ≤
      Pr{let z ← romExperiment (atVars m <$> A) pcsVerifierO}[
        z.1.2 = true ∧ PcsDoomedO z.1.1 z.2] := by
  rw [romExperiment_map, prEvent_map, romExperiment_eq, romExperiment_eq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  rw [prEvent_map, prEvent_map]
  obtain ⟨⟨⟨n, x⟩, π⟩, c⟩ := p
  by_cases hn : n = m
  · subst hn
    have hat : atVars n (⟨n, x⟩, π) = (x, π) := by simp [atVars]
    dsimp only
    rw [hat, show pcsVerifierAnyO (⟨n, x⟩, π) = pcsVerifierO (x, π) from rfl]
    apply prEvent_mono
    intro r hr
    exact hr.1
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hev ↦ ?_) bot_le
    exact hn hev.2

/-- **Fiat-Shamir soundness of version 1's opening with the out-of-domain point read off
Keccak-256, for claims of any `n`** (the adversary chooses `n`): a union over the `14` supported
values, `14 · openingBound QA` (`≤ 2^-59` for `QA ≤ 2^64`, `pcs_any_bound_le`). -/
theorem pcs_sound_any_oracle (A : OracleComp KeccakCalls (AnyClaim × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A pcsVerifierAnyO}[z.1.2 = true ∧ PcsDoomedAnyO z.1.1 z.2] ≤
      14 * openingBound QA := by
  have hmono : Pr{let z ← romExperiment A pcsVerifierAnyO}[
      z.1.2 = true ∧ PcsDoomedAnyO z.1.1 z.2] ≤
      Pr{let z ← romExperiment A pcsVerifierAnyO}[∃ m ∈ Finset.Icc minVars maxVars,
        (z.1.2 = true ∧ PcsDoomedAnyO z.1.1 z.2) ∧ z.1.1.1.1 = m] :=
    prEvent_mono_of_support _ _ _ fun z hz hev ↦
      ⟨z.1.1.1.1, Finset.mem_Icc.2 (vars_of_acceptO A z hz hev.1), hev, rfl⟩
  refine hmono.trans ((prEvent_exists_finset_le_card_mul (ε := openingBound QA) _ _ _
    fun m hm ↦ ?_).trans ?_)
  · have hm' := Finset.mem_Icc.1 hm
    refine (prEvent_any_at_leO A m).trans (pcs_sound_oracle hm'.1 hm'.2 _ QA ?_)
    exact (isQueryBound_map_iff A (atVars m) QA _ _).mpr hA
  · rw [show (Finset.Icc minVars maxVars).card = 14 from rfl]
    norm_num

end WhirBridge.Pcs
