/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

The binding of version 1's commitment with the lists read off the random oracle: the adversary has
Keccak-256, Keccak-f[1600] and the out-of-domain oracle, and each root's list is extracted from the
final Keccak-256 answers (leanerVM `mumbai`'s `extract`, https://github.com/Verified-zkEVM/leanerVM,
commit 6175f1a0, MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/Compile/Rom/Extract.lean`), proved with
mumbai's budgeted potential bound (`lean_vm/LeanVM/Protocol/ToVCVio/Rom/Potential.lean`).
-/
import WhirBridge.PcsBinding
import LeanVM.Protocol.Compile.Rom.Encoding

/-!
# Binding with the lists read off the oracle

`ood_binding` fixes the lists before the experiment. Here they are what `pcs_sound`'s event reads:
the Johnson list of the word mumbai's `extract` reads, for the root, off the **final** Keccak-256
answers (`rootList`). The adversary may build Merkle trees after seeing out-of-domain points; what
it cannot do is change the word under a root whose point it has asked for, except by a fresh
Keccak-256 answer that is that root or a digest some answered input (or the new input) holds as a
Merkle child (`extract_stable`): at most `2 k + 2` of the `2^256` answers for a cache of `k`
entries.

* `extract_stable`: recording a fresh Keccak-256 answer `u` at `x` leaves the word extracted for `r`
  unchanged when `u ≠ r`, `u` is no child digest of an answered input, nor of `x`;
* **`ood_binding_rom`**: in the random-oracle model of Keccak-256, Keccak-f[1600] and the
  out-of-domain oracle (`BindSpec`), a computation of at most `Q` queries ends with some root whose
  point it asked for and whose list, extracted from the final answers, is not separated at that
  point, with probability at most `Q · C(L, 2) · n / 2^192 + Q (Q + 1) / 2^256`, `L = listMax`
  (`≤ 2^18`).
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Child digests -/

/-- `d` is one of the two digests the 64-byte input `y` holds (a Merkle node's children). -/
def Emb (y : Bytes) (d : Digest) : Prop :=
  ∃ s, y = digestBytes d ++ digestBytes s ∨ y = digestBytes s ++ digestBytes d

theorem emb_nodeInput (node s : Digest) (q : ℕ) : Emb (nodeInput node s q) node := by
  unfold nodeInput
  split
  · exact ⟨s, Or.inl rfl⟩
  · exact ⟨s, Or.inr rfl⟩

open Classical in
/-- The child digests of an input, as a finite set. -/
noncomputable def embSet (y : Bytes) : Finset Digest := Finset.univ.filter (Emb y)

theorem mem_embSet {y : Bytes} {d : Digest} : d ∈ embSet y ↔ Emb y d := by
  classical
  simp [embSet]

theorem embSet_card (y : Bytes) : (embSet y).card ≤ 2 := by
  classical
  have hsub : embSet y ⊆ Finset.univ.filter (fun d ↦ ∃ s, y = digestBytes d ++ digestBytes s) ∪
      Finset.univ.filter (fun d ↦ ∃ s, y = digestBytes s ++ digestBytes d) := by
    intro d hd
    rw [mem_embSet] at hd
    obtain ⟨s, h | h⟩ := hd
    · exact Finset.mem_union_left _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s, h⟩)
    · exact Finset.mem_union_right _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s, h⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 : (Finset.univ.filter (fun d ↦ ∃ s, y = digestBytes d ++ digestBytes s)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨s', h⟩ := hb
    exact digestBytes_injective (List.append_inj h (by rw [digestBytes_length', digestBytes_length'])).1
  have h2 : (Finset.univ.filter (fun d ↦ ∃ s, y = digestBytes s ++ digestBytes d)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨s', h⟩ := hb
    exact digestBytes_injective (List.append_inj h (by rw [digestBytes_length', digestBytes_length'])).2
  omega

/-! ## Extraction is stable under an unrelated fresh answer -/

section Stable

variable {H H' : Bytes → Option Digest} {x : Bytes} {u r : Digest}

/-- The hypotheses: `H'` is `H` with a fresh answer `u` at `x`, and `u` is neither `r`, nor a
child digest of an input `H` answers, nor of `x`. -/
structure Unrelated (H H' : Bytes → Option Digest) (x : Bytes) (u r : Digest) : Prop where
  fresh : H x = none
  new : H' x = some u
  old : ∀ y, y ≠ x → H' y = H y
  ne_root : u ≠ r
  not_child : ∀ y, H y ≠ none → ¬ Emb y u
  not_child_new : ¬ Emb x u

/-- A climb from the fresh answer to `r` does not exist. -/
theorem climb_from_new (hU : Unrelated H H' x u r) (q : ℕ) (path : List Digest)
    (h : climbWithHash (m := Option) H' u q path = some r) : False := by
  cases path with
  | nil =>
    simp only [climbWithHash, pure, Option.some.injEq] at h
    exact hU.ne_root h
  | cons s ss =>
    rw [climb_cons, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, -⟩ := h
    by_cases hy : nodeInput u s q = x
    · exact hU.not_child_new (hy ▸ emb_nodeInput u s q)
    · rw [hU.old _ hy] at hp
      exact hU.not_child _ (by simp [hp]) (emb_nodeInput u s q)

/-- A climb to `r` under `H'` is one under `H`. -/
theorem climb_of_new (hU : Unrelated H H' x u r) :
    ∀ (path : List Digest) (node : Digest) (q : ℕ),
      climbWithHash (m := Option) H' node q path = some r →
        climbWithHash (m := Option) H node q path = some r
  | [], node, q, h => h
  | s :: ss, node, q, h => by
    rw [climb_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨p, hp, hc⟩ := h
    by_cases hy : nodeInput node s q = x
    · rw [hy, hU.new, Option.some.injEq] at hp
      subst hp
      exact (climb_from_new hU _ _ hc).elim
    · rw [hU.old _ hy] at hp
      exact ⟨p, hp, climb_of_new hU ss p (q / 2) hc⟩

/-- A climb under `H` is one under `H'`. -/
theorem climb_to_new (hU : Unrelated H H' x u r) :
    ∀ (path : List Digest) (node : Digest) (q : ℕ) (r' : Digest),
      climbWithHash (m := Option) H node q path = some r' →
        climbWithHash (m := Option) H' node q path = some r'
  | [], node, q, r', h => h
  | s :: ss, node, q, r', h => by
    rw [climb_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨p, hp, hc⟩ := h
    have hy : nodeInput node s q ≠ x := fun hy ↦ by rw [hy, hU.fresh] at hp; cases hp
    rw [hU.old _ hy]
    exact ⟨p, hp, climb_to_new hU ss p (q / 2) r' hc⟩

/-- **The accepted openings to `r` are the same.** -/
theorem openOne_iff_of_unrelated (hU : Unrelated H H' x u r) (ht w q : ℕ) (o : Opening) :
    openOneWithHash (m := Option) H' r ht w q o = some true ↔
      openOneWithHash (m := Option) H r ht w q o = some true := by
  rw [openOne_eq_some_true_iff, openOne_eq_some_true_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨ld, hld, hc⟩
    by_cases hy : o.leaf.flatMap kBytes = x
    · rw [hy, hU.new, Option.some.injEq] at hld
      subst hld
      exact (climb_from_new hU _ _ hc).elim
    · rw [hU.old _ hy] at hld
      exact ⟨ld, hld, climb_of_new hU _ _ _ hc⟩
  · rintro ⟨ld, hld, hc⟩
    have hy : o.leaf.flatMap kBytes ≠ x := fun hy ↦ by rw [hy, hU.fresh] at hld; cases hld
    exact ⟨ld, by rw [hU.old _ hy]; exact hld, climb_to_new hU _ _ _ _ hc⟩

/-- **Extraction is stable**: the word extracted for `r` does not change. -/
theorem extract_stable (hU : Unrelated H H' x u r) (ht w : ℕ) :
    extract H' r ht w = extract H r ht w := by
  funext q
  unfold extract
  have : (fun o ↦ openOneWithHash (m := Option) H' r ht w q o = some true) =
      fun o ↦ openOneWithHash (m := Option) H r ht w q o = some true :=
    funext fun o ↦ propext (openOne_iff_of_unrelated hU ht w q o)
  rw [this]

end Stable

/-! ## The experiment -/

/-- **The oracles**: Keccak-256 and Keccak-f[1600] (`KeccakCalls`), and the out-of-domain oracle. -/
abbrev BindSpec (n : ℕ) : OracleSpec ((Bytes ⊕ KeccakState) ⊕ Digest) := KeccakCalls + OodSpec n

variable {n : ℕ}

/-- The Keccak-256 answers of a cache. -/
def hOf (c : (BindSpec n).QueryCache) : Bytes → Option Digest := fun y ↦ c (.inl (.inl y))

/-- **The event**: some root's point was asked for, and the root's list, extracted from the cache's
Keccak-256 answers, is not separated at it. -/
def BindBad (c : (BindSpec n).QueryCache) : Prop :=
  ∃ r z, c (.inr r) = some z ∧ ¬ SepAt (rootList (n := n) (hOf c) r) z

/-- The per-query error of the out-of-domain point: `C(L, 2) · n / 2^192`, `L = listMax`. -/
noncomputable def δood (n : ℕ) : ℝ≥0∞ :=
  (((code₀ n logInvRate).listMax.choose 2 * n : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192

/-- The budget's terms: `δ + (2 (k + j) + 2) / 2^256` for a cache of `k` entries. -/
noncomputable def bindSum (n : ℕ) (k : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range m, (δood n + (2 * (k + j) + 2) / (2 : ℝ≥0∞) ^ 256)

open Classical in
/-- **The potential** with `m` queries left: one on a bad cache, otherwise the budget, capped at
one. -/
noncomputable def bindPot (n : ℕ) (m : ℕ) (c : (BindSpec n).QueryCache) : ℝ≥0∞ :=
  if BindBad c then 1 else min 1 (bindSum n c.enncard m)

theorem bindPot_le_one (m : ℕ) (c : (BindSpec n).QueryCache) : bindPot n m c ≤ 1 := by
  unfold bindPot
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem bindSum_succ (k : ℝ≥0∞) (m : ℕ) :
    bindSum n k (m + 1) = (δood n + (2 * k + 2) / (2 : ℝ≥0∞) ^ 256) +
      bindSum n (k + 1) m := by
  unfold bindSum
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem bindSum_mono {k k' : ℝ≥0∞} (h : k ≤ k') (m : ℕ) : bindSum n k m ≤ bindSum n k' m := by
  unfold bindSum
  gcongr

/-- **The step, given the answers that make the cache bad**: from a good cache, if every answer
outside `B` leaves it good and `B` has probability at most `δ + (2k + 2)/2^256`, the potential is a
supermartingale step. -/
theorem bindPot_fresh_of (c : (BindSpec n).QueryCache) (hnb : ¬ BindBad c) (m : ℕ)
    (t : (BindSpec n).Domain) (B : Finset ((BindSpec n).Range t))
    (hB : ∀ u, u ∉ B → ¬ BindBad (c.cacheQuery t u))
    (hβ : (B.card : ℝ≥0∞) / Fintype.card ((BindSpec n).Range t) ≤
      δood n + (2 * c.enncard + 2) / (2 : ℝ≥0∞) ^ 256) :
    (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t) ≤
      bindPot n (m + 1) c := by
  classical
  have hcard : (Fintype.card ((BindSpec n).Range t) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hle1 : (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t) ≤ 1 := by
    calc (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t)
        ≤ (∑ _u : (BindSpec n).Range t, (1 : ℝ≥0∞)) / Fintype.card ((BindSpec n).Range t) :=
          ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ bindPot_le_one m _) _
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          exact ENNReal.div_self hcard (ENNReal.natCast_ne_top _)
  have hpt : ∀ u, bindPot n m (c.cacheQuery t u) ≤
      (if u ∈ B then 1 else 0) + bindSum n (c.enncard + 1) m := by
    intro u
    by_cases hu : u ∈ B
    · simp only [hu, ↓reduceIte]
      exact (bindPot_le_one m _).trans le_self_add
    · simp only [hu, ↓reduceIte, zero_add, bindPot, hB u hu]
      exact (min_le_right _ _).trans (bindSum_mono (QueryCache.enncard_cacheQuery_le c t u) m)
  have havg : (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t) ≤
      bindSum n c.enncard (m + 1) := by
    calc (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t)
        ≤ (∑ u, ((if u ∈ B then 1 else 0) + bindSum n (c.enncard + 1) m)) /
            Fintype.card ((BindSpec n).Range t) :=
          ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
      _ = (B.card : ℝ≥0∞) / Fintype.card ((BindSpec n).Range t) +
            bindSum n (c.enncard + 1) m := by
          rw [sum_add_const_div_card (spec := BindSpec n) t, Finset.sum_boole]
          simp
      _ ≤ (δood n + (2 * c.enncard + 2) / (2 : ℝ≥0∞) ^ 256) + bindSum n (c.enncard + 1) m := by
          gcongr
      _ = bindSum n c.enncard (m + 1) := (bindSum_succ _ m).symm
  simp only [bindPot, hnb, ↓reduceIte]
  exact le_min hle1 havg

/-! ## The three kinds of fresh query -/

/-- The digests a key of a cache holds: an input's child digests, or a root. -/
noncomputable def keyDigests : (BindSpec n).Domain → Finset Digest
  | .inl (.inl y) => embSet y
  | .inl (.inr _) => ∅
  | .inr r => {r}

theorem keyDigests_card (t : (BindSpec n).Domain) : (keyDigests t).card ≤ 2 := by
  rcases t with (y | s) | r
  · exact embSet_card y
  · simp [keyDigests]
  · simp [keyDigests]

/-- A fresh Keccak-f[1600] answer changes neither the Keccak-256 answers nor the points. -/
theorem bindBad_cacheQuery_perm (c : (BindSpec n).QueryCache) (s : KeccakState) (u : KeccakState)
    (h : BindBad (c.cacheQuery (.inl (.inr s)) u)) : BindBad c := by
  obtain ⟨r, z, hz, hsep⟩ := h
  rw [QueryCache.cacheQuery_of_ne _ _ (by simp)] at hz
  have hH : hOf (c.cacheQuery (.inl (.inr s)) u) = hOf c := funext fun y ↦ by
    simp only [hOf]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  rw [hH] at hsep
  exact ⟨r, z, hz, hsep⟩

/-- A fresh point: bad only if the root's list (unchanged) is not separated at the answer. -/
theorem bindBad_cacheQuery_ood (c : (BindSpec n).QueryCache) (r₀ : Digest) (u : Vector E n)
    (h : BindBad (c.cacheQuery (.inr r₀) u)) :
    BindBad c ∨ ¬ SepAt (rootList (n := n) (hOf c) r₀) u := by
  obtain ⟨r, z, hz, hsep⟩ := h
  have hH : hOf (c.cacheQuery (.inr r₀) u) = hOf c := funext fun y ↦ by
    simp only [hOf]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  rw [hH] at hsep
  by_cases hr : r = r₀
  · subst hr
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at hz
    subst hz
    exact Or.inr hsep
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hr)] at hz
    exact Or.inl ⟨r, z, hz, hsep⟩

/-- A fresh Keccak-256 answer `u` at `x`: bad only if `u` is a child digest of an answered input or
of `x`, or a root whose point was asked for (`extract_stable`). -/
theorem bindBad_cacheQuery_hash (c : (BindSpec n).QueryCache) (x : Bytes)
    (hc : c (.inl (.inl x)) = none) (u : Digest) (S : Finset (BindSpec n).Domain)
    (hS : ∀ t, c t ≠ none → t ∈ S) (hu : u ∉ S.biUnion keyDigests ∪ embSet x)
    (h : BindBad (c.cacheQuery (.inl (.inl x)) u)) : BindBad c := by
  obtain ⟨r, z, hz, hsep⟩ := h
  rw [QueryCache.cacheQuery_of_ne _ _ (by simp)] at hz
  have hrS : Sum.inr r ∈ S := hS _ (by simp [hz])
  have hU : Unrelated (hOf c) (hOf (c.cacheQuery (.inl (.inl x)) u)) x u r := by
    refine ⟨hc, ?_, fun y hy ↦ ?_, fun hur ↦ ?_, fun y hy hemb ↦ ?_, fun hemb ↦ ?_⟩
    · simp [hOf]
    · simp only [hOf]
      rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hy)]
    · subst hur
      exact hu (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨_, hrS, by simp [keyDigests]⟩))
    · exact hu (Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨_, hS (.inl (.inl y)) hy, by simpa [keyDigests] using mem_embSet.2 hemb⟩))
    · exact hu (Finset.mem_union_right _ (mem_embSet.2 hemb))
  have hl : rootList (n := n) (hOf (c.cacheQuery (.inl (.inl x)) u)) r =
      rootList (n := n) (hOf c) r := by
    unfold rootList
    rw [extract_stable hU]
  rw [hl] at hsep
  exact ⟨r, z, hz, hsep⟩

theorem card_E_ennreal' : (Fintype.card E : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 192 := card_E_ennreal

/-- **The potential is budgeted.** -/
theorem isBudgetedPotential_bindPot (hw : Whir.Admissible n logInvRate) :
    IsBudgetedPotential (bindPot n) where
  mono m c := by
    unfold bindPot
    split_ifs
    · exact le_rfl
    · refine min_le_min le_rfl ?_
      unfold bindSum
      rw [Finset.sum_range_succ]
      exact le_self_add
  fresh m c t hc := by
    classical
    have hcard : (Fintype.card ((BindSpec n).Range t) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    by_cases hbad : BindBad c
    · -- the potential is one, and never more
      calc (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t)
          ≤ (∑ _u : (BindSpec n).Range t, (1 : ℝ≥0∞)) / Fintype.card ((BindSpec n).Range t) :=
            ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ bindPot_le_one m _) _
        _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            exact ENNReal.div_self hcard (ENNReal.natCast_ne_top _)
        _ = bindPot n (m + 1) c := by simp [bindPot, hbad]
    by_cases htop : c.enncard = ⊤
    · -- an infinite cache: the budget is infinite, the cap is one
      have h1 : bindPot n (m + 1) c = 1 := by
        simp only [bindPot, hbad, ↓reduceIte]
        refine min_eq_left ?_
        rw [bindSum_succ, htop]
        simp [ENNReal.top_div_of_ne_top]
      rw [h1]
      calc (∑ u, bindPot n m (c.cacheQuery t u)) / Fintype.card ((BindSpec n).Range t)
          ≤ (∑ _u : (BindSpec n).Range t, (1 : ℝ≥0∞)) / Fintype.card ((BindSpec n).Range t) :=
            ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ bindPot_le_one m _) _
        _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            exact ENNReal.div_self hcard (ENNReal.natCast_ne_top _)
    -- a finite cache: its keys
    have hfin : c.toSet.Finite := Set.encard_ne_top_iff.mp fun h ↦ htop (by
      simp [QueryCache.enncard, h])
    set S := hfin.toFinset.image Sigma.fst with hSdef
    have hS : ∀ t', c t' ≠ none → t' ∈ S := by
      intro t' ht'
      obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp ht'
      exact Finset.mem_image.mpr ⟨⟨t', u'⟩, hfin.mem_toFinset.mpr hu', rfl⟩
    have hSk : (S.card : ℝ≥0∞) ≤ c.enncard := by
      rw [QueryCache.enncard, hfin.encard_eq_coe_toFinset_card]
      exact_mod_cast Finset.card_image_le
    rcases t with (x | s) | r₀
    · -- Keccak-256
      refine bindPot_fresh_of c hbad m _ (S.biUnion keyDigests ∪ embSet x)
        (fun u hu hb ↦ hbad (bindBad_cacheQuery_hash c x hc u S hS hu hb)) ?_
      have hBc : ((S.biUnion keyDigests ∪ embSet x).card : ℝ≥0∞) ≤ 2 * c.enncard + 2 := by
        have h1 : (S.biUnion keyDigests ∪ embSet x).card ≤ 2 * S.card + 2 := by
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ (embSet_card x))
          refine Finset.card_biUnion_le.trans ?_
          calc ∑ t ∈ S, (keyDigests t).card ≤ ∑ _t ∈ S, 2 :=
                Finset.sum_le_sum fun t _ ↦ keyDigests_card t
            _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        calc ((S.biUnion keyDigests ∪ embSet x).card : ℝ≥0∞) ≤ ((2 * S.card + 2 : ℕ) : ℝ≥0∞) :=
              by exact_mod_cast h1
          _ = 2 * (S.card : ℝ≥0∞) + 2 := by push_cast; ring
          _ ≤ 2 * c.enncard + 2 := by gcongr
      have hrange : Fintype.card ((BindSpec n).Range (.inl (.inl x))) = 2 ^ 256 := card_digest
      rw [hrange, Nat.cast_pow, Nat.cast_ofNat]
      exact (ENNReal.div_le_div_right hBc _).trans le_add_self
    · -- Keccak-f[1600]
      refine bindPot_fresh_of c hbad m _ ∅ (fun u _ hb ↦ hbad (bindBad_cacheQuery_perm c s u hb)) ?_
      simp
    · -- the out-of-domain oracle
      refine bindPot_fresh_of c hbad m _
        (Finset.univ.filter fun u : Vector E n ↦ ¬ SepAt (rootList (n := n) (hOf c) r₀) u)
        (fun u hu hb ↦ ?_) ?_
      · rcases bindBad_cacheQuery_ood c r₀ u hb with hb' | hb'
        · exact hbad hb'
        · exact hu (by simpa using hb')
      · refine le_trans ?_ le_self_add
        exact card_not_sepAt_div_le _ (candidates_count hw _).1 (candidates_count hw _).2

theorem sum_budget : ∀ Q : ℕ,
    ∑ j ∈ Finset.range Q, (2 * ((0 : ℝ≥0∞) + (j : ℝ≥0∞)) + 2) = ((Q * (Q + 1) : ℕ) : ℝ≥0∞)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_budget m]
    push_cast
    ring

/-- **The out-of-domain answer binds, with the lists read off the oracle.** In the random-oracle
model of Keccak-256, Keccak-f[1600] and the out-of-domain oracle, a computation of at most `Q`
queries, from the empty cache, ends with some root whose point it asked for and whose list,
extracted from the final Keccak-256 answers, is not separated at that point with probability at
most `Q · C(L, 2) · n / 2^192 + Q (Q + 1) / 2^256`, `L = listMax`. -/
theorem ood_binding_rom (hw : Whir.Admissible n logInvRate) {α : Type}
    (oa : OracleComp (BindSpec n) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ (BindSpec n).randomOracle oa).run ∅}[BindBad z.2] ≤
      Q * δood n + ((Q * (Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  classical
  have h := prEvent_run_randomOracle_le_of_budgeted (isBudgetedPotential_bindPot hw) oa Q hQ ∅
    (fun _ c ↦ BindBad c) (fun z _ hz ↦ by simp [bindPot, hz])
  refine h.trans ?_
  have hempty : ¬ BindBad (∅ : (BindSpec n).QueryCache) := by
    rintro ⟨r, z, h, -⟩
    simp at h
  simp only [bindPot, hempty, ↓reduceIte, QueryCache.enncard_empty]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  rw [bindSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.sum_div, sum_budget]

/-! ## The numbers at version 1's shapes -/

/-- Level 0's certified list at version 1's shapes (`certOf`, evaluated): `87315` at `n = 15` down
to `3564` at `n = 28`; `C(L, 2) · n ≤ 2^36` at each. -/
theorem listHi_v1 : ∀ n, minVars ≤ n → n ≤ maxVars →
    (LeanVM.Protocol.Whir.Params.certOf n logInvRate 0).listHi *
        ((LeanVM.Protocol.Whir.Params.certOf n logInvRate 0).listHi - 1) / 2 * n ≤ 2 ^ 36 := by
  decide +kernel

/-- **The binding's error per query at version 1's shapes**: `C(L, 2) · n / 2^192 ≤ 2^-156` for
every `15 ≤ n ≤ 28`, `L` the certified list (`listMax ≤ listHi`). -/
theorem δood_le (h1 : minVars ≤ n) (h2 : n ≤ maxVars) : δood n ≤ (2 : ℝ≥0∞)⁻¹ ^ 156 := by
  have hw := admissible_v1 n h1 h2
  have hc : (code₀ n logInvRate).listMax.choose 2 * n ≤ 2 ^ 36 := by
    refine le_trans (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (listMax_le_listHi hw))) ?_
    rw [Nat.choose_two_right]
    exact listHi_v1 n h1 h2
  unfold δood
  calc (((code₀ n logInvRate).listMax.choose 2 * n : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192
      ≤ ((2 ^ 36 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 156 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show (192 : ℕ) = 36 + 156 from rfl, two_pow_div_two_pow]

end WhirBridge.Pcs
