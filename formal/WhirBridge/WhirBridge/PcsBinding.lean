/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

The binding of version 1's commitment `(root, ood)`: the out-of-domain answer singles out one member of
the root's Johnson list, so claims on one commitment, opened separately, are of one polynomial. Uses
leanerVM `mumbai`'s out-of-domain separation count (https://github.com/Verified-zkEVM/leanerVM, commit
6175f1a0, MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/ToArkLib/Whir/Ood.lean`,
`card_ood_collision_image_le`) and its random-oracle potential bound
(`lean_vm/LeanVM/Protocol/ToVCVio/Rom/Potential.lean`, `prEvent_run_randomOracle_le_of_freshStepBound`).
-/
import WhirBridge.PcsClaim
import LeanVM.Protocol.Whir.Sound.Escape
import LeanVM.Protocol.Whir.Sound.Start
import LeanVM.Protocol.ToVCVio.Rom.Potential

/-!
# The out-of-domain answer binds the commitment

WHIR at rate `1/2` takes no out-of-domain sample at its first level: a root binds the up to `L₀`
stacks of its word's Johnson list (`Candidates`, `candidates_count`: `L₀ ≤ listMax ≤ 2^18`), and an
opening that is not doomed (`pcs_sound`) has **a** member of the list satisfying its two claims.
Two openings on one root could so be of two members. Version 1's commitment carries `ood = f(z)` at
the point `z = zOf root`; both openings prove `f(z) = ood`, so their members agree at `z`; if no two
distinct members of the list agree at `z` (`SepAt`), they are one.

* `colEval_eq_evalMle`, `colTable_injective`: a stack's polynomial is CompPoly's multilinear
  extension of its table, the table determining the stack;
* `card_not_sepAt_le` (**Schwartz-Zippel over the list**, mumbai's `card_ood_collision_image_le`):
  at most `C(L, 2) · n · |E|^(n-1)` points `z ∈ E^n` leave two distinct members of a list of `L`
  stacks agreeing;
* **`one_stack_of_sepAt`**, **`two_openings_one_polynomial`**: two openings of one commitment
  `(root, ood)`, neither doomed, with the root's list separated at `z`, have **one** candidate
  satisfying both openings' claims;
* **`ood_binding`** (random-oracle model): the out-of-domain point a random oracle
  `Digest →ₒ E^n` (`OodSpec`), the lists any fixed function of the root (`Λ`, at most `L` stacks
  each), a computation of at most `Q` queries ends with an answered root whose list is not
  separated at its point with probability at most `Q · C(L, 2) · n / 2^192`;
  `ood_binding_candidates`: for the lists of the deployed code (any fixed Keccak-256 answers),
  `L = listMax`; `binding_bound_le`: at most `2^-152` per query for every `n ≤ 32` (`L ≤ 2^18`).

The model's assumption, beyond `pcs_sound`'s: the out-of-domain point of a root is a uniform point
of `E^n` drawn when the root is first asked about (the `n` Keccak-256 answers at the
domain-separated inputs `oodInput`, each one's low 24 bytes uniform in `E`), and the root's list
is fixed before (`Λ` does not depend on the out-of-domain answers: the root's Merkle preimages fix
its word; changing them afterwards is a Keccak-256 collision, which this file does not formalise).
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom
open CompPoly CMlPolynomialEval Finset
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

variable {n : ℕ}

/-! ## A stack's polynomial is its table's multilinear extension -/

/-- The stack's table in CompPoly's hypercube form, over `E`. -/
noncomputable def colTable (q : Column n) : CMlPolynomialEval E n :=
  LeanVM.Protocol.Whir.Sound.tableOf fun p ↦
    ofK (q.values.getD (LeanVM.Protocol.Whir.bitsEquiv n p : ℕ) 0)

/-- **`f(z)` is the multilinear extension of the stack's table at `z`.** -/
theorem colEval_eq_evalMle (q : Column n) (z : Vector E n) :
    colEval q z.toList = evalMle (colTable q) z := by
  rw [colEval, colTable, ← LeanVM.Protocol.Whir.Sound.sum_eqEval_vec,
    ← Equiv.sum_comp (LeanVM.Protocol.Whir.bitsEquiv n)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [LeanVM.Protocol.Whir.bitsEquiv_val, LeanVM.Protocol.Whir.Sound.boolPoint_bitsToNat]

/-- The table determines the stack. -/
theorem colTable_injective : Function.Injective (colTable (n := n)) := by
  intro q q' h
  have hG := LeanVM.Protocol.Whir.Sound.tableOf_injective h
  obtain ⟨v⟩ := q
  obtain ⟨v'⟩ := q'
  congr 1
  refine Vector.ext fun i hi ↦ ?_
  have := congrFun hG ((LeanVM.Protocol.Whir.bitsEquiv n).symm ⟨i, hi⟩)
  simp only [Equiv.apply_symm_apply] at this
  have hinj := (algebraMap K E).injective this
  simpa [Vector.getD, hi] using hinj

/-! ## Separation of a list at a point -/

/-- **The list `S` is separated at `z`**: no two distinct members have the same polynomial value
at `z`. -/
def SepAt (S : Set (Column n)) (z : Vector E n) : Prop :=
  ∀ q ∈ S, ∀ q' ∈ S, colEval q z.toList = colEval q' z.toList → q = q'

open Classical in
/-- **Schwartz-Zippel over a list** (mumbai's `card_ood_collision_image_le`): a finite list of at
most `L` stacks is not separated at at most `C(L, 2) · n · |E|^(n-1)` points. -/
theorem card_not_sepAt_le (S : Set (Column n)) (hS : S.Finite) {L : ℕ} (hL : S.ncard ≤ L) :
    (Finset.univ.filter fun z : Vector E n ↦ ¬ SepAt S z).card ≤
      L.choose 2 * (n * Fintype.card E ^ (n - 1)) := by
  classical
  set T := hS.toFinset
  have hT : T.card ≤ L := by rw [← Set.ncard_eq_toFinset_card S hS]; exact hL
  have hinj : Set.InjOn colTable (T : Set (Column n)) := fun q _ q' _ h ↦ colTable_injective h
  refine (Finset.card_le_card fun z hz ↦ ?_).trans
    ((LeanVM.Protocol.Whir.card_ood_collision_image_le T colTable hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hT)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SepAt, not_forall] at hz ⊢
  obtain ⟨q, hq, q', hq', heq, hne⟩ := hz
  refine ⟨q, by simpa [T] using hq, q', by simpa [T] using hq', hne, ?_⟩
  rw [← colEval_eq_evalMle, ← colEval_eq_evalMle, heq]

/-- **One stack**: two members of a list separated at `z` with the same value at `z` are equal. -/
theorem one_stack_of_sepAt {S : Set (Column n)} {z : Vector E n} (hsep : SepAt S z)
    {q q' : Column n} (hq : q ∈ S) (hq' : q' ∈ S) {ood : E} (h : colEval q z.toList = ood)
    (h' : colEval q' z.toList = ood) : q = q' :=
  hsep q hq q' hq' (h.trans h'.symm)

/-- The candidates of a root: the stacks of its extracted word's Johnson list at level 0. -/
def rootList (Hc : Bytes → Option Digest) (r : Digest) : Set (Column n) :=
  Candidates n logInvRate (code₀ n logInvRate).thr
    (extract Hc r (rootHeight n logInvRate) (2 ^ laneFold))

/-- **Two openings of one commitment are of one polynomial**: claims `x₁`, `x₂` on one commitment
`(root, ood)` whose openings are not doomed (`pcs_sound`'s event fails for both, against one cache)
and whose root's list is separated at the out-of-domain point have **one** candidate satisfying
`f(z) = ood`, `f(point₁) = value₁` and `f(point₂) = value₂`. -/
theorem two_openings_one_polynomial {zOf : Digest → Vector E n} {x₁ x₂ : Claim1 n}
    {π₁ π₂ : Proof} {cache : KeccakCalls.QueryCache} (hroot : x₁.root = x₂.root)
    (hood : x₁.ood = x₂.ood)
    (h₁ : ¬ PcsDoomed zOf (x₁, π₁) cache) (h₂ : ¬ PcsDoomed zOf (x₂, π₂) cache)
    (hsep : SepAt (rootList (n := n) (fun x ↦ cache (.inl x)) x₁.root) (zOf x₁.root)) :
    ∃ q ∈ rootList (n := n) (fun x ↦ cache (.inl x)) x₁.root,
      colEval q (zOf x₁.root).toList = x₁.ood ∧ colEval q x₁.point = x₁.value ∧
        colEval q x₂.point = x₂.value := by
  simp only [PcsDoomed, not_forall, not_or, not_not] at h₁ h₂
  obtain ⟨q₁, hq₁, hz₁, hv₁⟩ := h₁
  obtain ⟨q₂, hq₂, hz₂, hv₂⟩ := h₂
  rw [← hroot] at hq₂ hz₂
  rw [← hood] at hz₂
  obtain rfl := one_stack_of_sepAt hsep hq₁ hq₂ hz₁ hz₂
  exact ⟨q₁, hq₁, hz₁, hv₁, hv₂⟩

/-! ## The out-of-domain point as a random oracle -/

/-- The out-of-domain oracle: a root's point of `E^n`. -/
abbrev OodSpec (n : ℕ) : OracleSpec Digest := Digest →ₒ Vector E n

/-- Some answered root's list is not separated at its point. -/
def CacheSepFails (Λ : Digest → Set (Column n)) (c : (OodSpec n).QueryCache) : Prop :=
  ∃ r z, c r = some z ∧ ¬ SepAt (Λ r) z

open Classical in
/-- The potential: one once some answered root's list is not separated at its point. -/
noncomputable def sepPotential (Λ : Digest → Set (Column n)) (c : (OodSpec n).QueryCache) : ℝ≥0∞ :=
  if CacheSepFails Λ c then 1 else 0

theorem cacheSepFails_cacheQuery_iff (Λ : Digest → Set (Column n)) (c : (OodSpec n).QueryCache)
    (t : Digest) (u : Vector E n) (hc : c t = none) :
    CacheSepFails Λ (c.cacheQuery t u) ↔ CacheSepFails Λ c ∨ ¬ SepAt (Λ t) u := by
  constructor
  · rintro ⟨t', u', h, hu'⟩
    by_cases ht : t' = t
    · subst ht
      rw [QueryCache.cacheQuery_self, Option.some.injEq] at h
      exact Or.inr (h ▸ hu')
    · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h
      exact Or.inl ⟨t', u', h, hu'⟩
  · rintro (⟨t', u', h, hu'⟩ | hu)
    · have ht : t' ≠ t := fun ht ↦ by subst ht; simp [hc] at h
      exact ⟨t', u', by rw [QueryCache.cacheQuery_of_ne _ _ ht]; exact h, hu'⟩
    · exact ⟨t, u, QueryCache.cacheQuery_self _ _ _, hu⟩

open Classical in
/-- The count, as a probability: at most `C(L, 2) · n / |E|` of the points of `E^n` leave the list
not separated. -/
theorem card_not_sepAt_div_le (S : Set (Column n)) (hS : S.Finite) {L : ℕ} (hL : S.ncard ≤ L) :
    ((Finset.univ.filter fun z : Vector E n ↦ ¬ SepAt S z).card : ℝ≥0∞) /
        Fintype.card (Vector E n) ≤ (L.choose 2 * n : ℕ) / (2 : ℝ≥0∞) ^ 192 := by
  have hcount := card_not_sepAt_le S hS hL
  rw [LeanVM.Protocol.Whir.card_vector_eq_pow]
  have hE : (Fintype.card E : ℝ≥0∞) = 2 ^ 192 := card_E_ennreal
  have hE0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by rw [hE]; simp
  have hEt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := by rw [hE]; simp
  rcases n with _ | m
  · have h0 : (Finset.univ.filter fun z : Vector E 0 ↦ ¬ SepAt S z).card = 0 := by
      have := hcount
      simp only [Nat.zero_mul, Nat.mul_zero] at this
      omega
    rw [h0]
    simp
  · calc ((Finset.univ.filter fun z : Vector E (m + 1) ↦ ¬ SepAt S z).card : ℝ≥0∞) /
          ((Fintype.card E ^ (m + 1) : ℕ) : ℝ≥0∞)
        ≤ ((L.choose 2 * ((m + 1) * Fintype.card E ^ m) : ℕ) : ℝ≥0∞) /
          ((Fintype.card E ^ (m + 1) : ℕ) : ℝ≥0∞) := by
          gcongr
          simpa using hcount
      _ = ((L.choose 2 * (m + 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
          have e1 : L.choose 2 * ((m + 1) * Fintype.card E ^ m) =
              (L.choose 2 * (m + 1)) * Fintype.card E ^ m := by ring
          have e2 : Fintype.card E ^ (m + 1) = Fintype.card E * Fintype.card E ^ m := by ring
          rw [e1, e2, Nat.cast_mul (L.choose 2 * (m + 1)) (Fintype.card E ^ m),
            Nat.cast_mul (Fintype.card E) (Fintype.card E ^ m), ENNReal.mul_div_mul_right _ _
            (Nat.cast_ne_zero.2 (pow_ne_zero _ Fintype.card_ne_zero)) (ENNReal.natCast_ne_top _)]
      _ = ((L.choose 2 * (m + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by rw [hE]

/-- **The step**: a fresh query raises the potential in expectation by at most
`C(L, 2) · n / 2^192`. -/
theorem freshStepBound_sepPotential (Λ : Digest → Set (Column n))
    (hΛ : ∀ r, (Λ r).Finite) {L : ℕ} (hL : ∀ r, (Λ r).ncard ≤ L) :
    FreshStepBound (sepPotential Λ) ((L.choose 2 * n : ℕ) / (2 : ℝ≥0∞) ^ 192) := by
  classical
  intro c t hc
  have hcard : (Fintype.card (Vector E n) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hf : CacheSepFails Λ c
  · have h1 : ∀ u, sepPotential Λ (c.cacheQuery t u) = 1 := fun u ↦
      if_pos ((cacheSepFails_cacheQuery_iff Λ c t u hc).mpr (Or.inl hf))
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
    exact le_self_add.trans (add_le_add_left (by simp [sepPotential, hf]) _)
  · have h1 : ∀ u, sepPotential Λ (c.cacheQuery t u) = if ¬ SepAt (Λ t) u then 1 else 0 :=
      fun u ↦ by
        simp only [sepPotential, cacheSepFails_cacheQuery_iff Λ c t u hc, hf, false_or]
    simp only [h1, Finset.sum_boole]
    rw [show sepPotential Λ c = 0 from if_neg hf, zero_add]
    exact card_not_sepAt_div_le (Λ t) (hΛ t) (hL t)

/-- **The out-of-domain answer binds, in the random-oracle model.** For lists `Λ` fixed as a
function of the root (each finite, of at most `L` stacks), a computation of at most `Q` queries to
the out-of-domain oracle, run against the lazy random oracle from the empty cache, ends with some
answered root whose list is not separated at its point with probability at most
`Q · C(L, 2) · n / 2^192`. -/
theorem ood_binding (Λ : Digest → Set (Column n)) (hΛ : ∀ r, (Λ r).Finite) {L : ℕ}
    (hL : ∀ r, (Λ r).ncard ≤ L) {α : Type} (oa : OracleComp (OodSpec n) α) (Q : ℕ)
    (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ (OodSpec n).randomOracle oa).run ∅}[CacheSepFails Λ z.2] ≤
      Q * ((L.choose 2 * n : ℕ) / (2 : ℝ≥0∞) ^ 192) := by
  classical
  have h := prEvent_run_randomOracle_le_of_freshStepBound
    (freshStepBound_sepPotential Λ hΛ hL) oa Q hQ ∅ (fun _ c ↦ CacheSepFails Λ c)
    (fun z _ hz ↦ by simp [sepPotential, hz])
  have h0 : sepPotential Λ ∅ = 0 := by
    refine if_neg ?_
    rintro ⟨r, z, h, -⟩
    simp at h
  rwa [h0, zero_add] at h

/-- **For the deployed code's lists**: the lists are the root words' Johnson lists at level 0
(`rootList`, for any fixed Keccak-256 answers `Hc`), at most `listMax` stacks each
(`candidates_count`). -/
theorem ood_binding_candidates (hw : Whir.Admissible n logInvRate) (Hc : Bytes → Option Digest)
    {α : Type} (oa : OracleComp (OodSpec n) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ (OodSpec n).randomOracle oa).run ∅}[
        CacheSepFails (rootList Hc) z.2] ≤
      Q * (((code₀ n logInvRate).listMax.choose 2 * n : ℕ) / (2 : ℝ≥0∞) ^ 192) :=
  ood_binding (rootList Hc) (fun _ ↦ (candidates_count hw _).1) (fun _ ↦ (candidates_count hw _).2)
    oa Q hQ

/-- **The numbers**: with mumbai's global list bound `L ≤ 2^18` and `n ≤ 32`, the binding's error
per query is at most `2^-152`. -/
theorem binding_bound_le {L m : ℕ} (hL : L ≤ 2 ^ 18) (hm : m ≤ 32) :
    ((L.choose 2 * m : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 152 := by
  have hch : L.choose 2 ≤ 2 ^ 35 := by
    rw [Nat.choose_two_right]
    have h2 : L * (L - 1) ≤ 2 ^ 18 * 2 ^ 18 := Nat.mul_le_mul hL (le_trans (Nat.sub_le _ _) hL)
    calc L * (L - 1) / 2 ≤ 2 ^ 18 * 2 ^ 18 / 2 := Nat.div_le_div_right h2
      _ = 2 ^ 35 := by norm_num
  have hc : L.choose 2 * m ≤ 2 ^ 40 :=
    calc L.choose 2 * m ≤ 2 ^ 35 * 32 := Nat.mul_le_mul hch hm
      _ = 2 ^ 40 := by norm_num
  calc ((L.choose 2 * m : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192
      ≤ ((2 ^ 40 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 152 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show (192 : ℕ) = 40 + 152 from rfl, two_pow_div_two_pow]

/-- At every admissible shape the list is at most mumbai's `2^18` (`listMax_le`). -/
theorem listMax_le_v1 (hw : Whir.Admissible n logInvRate) :
    (code₀ n logInvRate).listMax ≤ 2 ^ 18 :=
  LeanVM.Protocol.EndToEnd.Sound.listMax_le hw

end WhirBridge.Pcs
