-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsBadQ

/-!
# The cost of an out-of-domain point

A uniform root, then the `n` coordinates' tracked queries: each input is injective in the root (`oodInput_inj`)
and the inputs differ (their coordinates do), so the `n` queries cost at most `n · δq L` (`badB_oodBlock`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α : Type}

/-- A uniform root, as `ProbComp` runs the model's coins. -/
noncomputable def rootDist : ProbComp Digest := simulateQ coinsOf sampleDigest

theorem indep_sampleDigest : StateIndep (simulateQ (edgeOracle (A := A)) sampleDigest) rootDist := by
  simp only [rootDist, sampleDigest, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  exact (StateIndep.mapM' _ _ (fun _ ↦ indep_coinWord _ edge_coin) _).bind' fun _ ↦ StateIndep.pure' _

theorem rootDist_eq : rootDist = (fun t : UInt64 × UInt64 × UInt64 × UInt64 ↦ (#v[t.1, t.2.1, t.2.2.1, t.2.2.2] : Digest))
    <$> (cwDist >>= fun a ↦ (cwDist >>= fun b ↦ (cwDist >>= fun c ↦ cwDist >>= fun d ↦ pure (c, d)) >>=
      fun t ↦ pure (b, t)) >>= fun t ↦ pure (a, t)) := by
  simp only [rootDist, sampleDigest, simulateQ_bind, simulateQ_pure, map_bind,
    pure_bind, map_pure, show List.range 4 = [0, 1, 2, 3] from rfl, List.mapM_cons, List.mapM_nil]
  rfl

theorem prEvent_rootDist (r : Digest) : Pr{let x ← rootDist}[x = r] ≤ pmax := by
  have hinj : Function.Injective fun t : UInt64 × UInt64 × UInt64 × UInt64 ↦ (#v[t.1, t.2.1, t.2.2.1, t.2.2.2] : Digest) :=
    fun a b h ↦ by
      have h0 := congrArg (fun v : Digest ↦ v[0]) h
      have h1 := congrArg (fun v : Digest ↦ v[1]) h
      have h2 := congrArg (fun v : Digest ↦ v[2]) h
      have h3 := congrArg (fun v : Digest ↦ v[3]) h
      simp at h0 h1 h2 h3
      exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  have hr : r = (fun t : UInt64 × UInt64 × UInt64 × UInt64 ↦ (#v[t.1, t.2.1, t.2.2.1, t.2.2.2] : Digest))
      (r[0], r[1], r[2], r[3]) := by
    apply Vector.ext; intro i hi; interval_cases i <;> rfl
  rw [rootDist_eq, hr, prEvent_map_injective _ hinj, prEvent_pair, prEvent_pair, prEvent_pair, prEvent_cwDist,
    prEvent_cwDist, prEvent_cwDist, prEvent_cwDist, pmax]
  calc c64 * (c64 * (c64 * c64)) ≤ c64 * (c64 * (c64 * 1)) := by gcongr; exact c64_le_one
    _ = c64 * (c64 * c64) := by rw [mul_one]

/-- The input of out-of-domain coordinate `j` of a root. -/
def oodX (n : ℕ) (r : Digest) (j : ℕ) : KeccakState := blockIn zeroSt (padBlock (oodInput n r j))

theorem oodX_inj_root (n j : ℕ) : Function.Injective fun r ↦ oodX n r j := fun r r' h ↦
  (oodInput_inj (blockIn_pad_inj (by rw [oodInput_len, oodInput_len]) (by rw [oodInput_len]; omega) h)).1

theorem oodX_inj_coord {n : ℕ} {r : Digest} {i j : ℕ} (hi : i < 256) (hj : j < 256) (h : oodX n r i = oodX n r j) :
    i = j := by
  have := (oodInput_inj (blockIn_pad_inj (by rw [oodInput_len, oodInput_len]) (by rw [oodInput_len]; omega) h)).2
  have := congrArg UInt8.toNat this
  simp only [Nat.toUInt8] at this
  rwa [UInt8.toNat_ofNat_of_lt' (by simpa using hi), UInt8.toNat_ofNat_of_lt' (by simpa using hj)] at this

theorem prEvent_oodX (n j : ℕ) (z : KeccakState) : Pr{let r ← rootDist}[oodX n r j = z] ≤ pmax :=
  prEvent_inj_le _ _ (oodX_inj_root n j) _ prEvent_rootDist z

/-- The coordinates' program, its first queries written out. -/
theorem listF_ood_cons (n : ℕ) (r : Digest) (j : ℕ) (l : List ℕ) (K : List E → FProg A α) :
    (listF (j :: l) fun j ↦ (keccakF (oodInput n r j)).bind fun d ↦ .ret (elementOf ((digestBytes d).drop 8))).bind K =
      .q (oodX n r j) fun y ↦ (listF l fun j ↦ (keccakF (oodInput n r j)).bind fun d ↦
        .ret (elementOf ((digestBytes d).drop 8))).bind fun cs ↦ K (elementOf ((digestBytes (digestOf y)).drop 8) :: cs) := by
  simp only [listF, FProg.bind_assoc]
  rw [keccakF_bind_one _ (by rw [oodInput_len]; rfl)]
  simp only [FProg.bind]
  rfl

theorem badB_listF_ood (L n : ℕ) (hn : n ≤ 256) (r : Digest) (s₀ : Edges × A) (B : ℝ≥0∞) :
    ∀ (l : List ℕ) (s : Edges × A) (K : List E → FProg A α), (∀ j ∈ l, j < n) → l.Nodup →
      (∀ z, inDom s z → inDom s₀ z ∨ ∃ j, j < n ∧ j ∉ l ∧ z = oodX n r j) → s.1.length + l.length ≤ L →
      (∀ cs (s' : Edges × A), s'.1.length = s.1.length + l.length → badB (K cs) s' ≤ B) →
      badB ((listF l fun j ↦ (keccakF (oodInput n r j)).bind fun d ↦
        .ret (elementOf ((digestBytes d).drop 8))).bind K) s ≤
        (l.map fun j ↦ open Classical in if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0).sum +
          l.length * (L * nInv) + B
  | [], s, K, _, _, _, _, hK => by
    simp only [listF, FProg.bind, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_mul, zero_add]
    exact hK [] s (by simp)
  | j :: l, s, K, hl, hnd, hdom, hsz, hK => by
    classical
    rw [listF_ood_cons, badB_q]
    have hj : j < n := hl j (List.mem_cons_self ..)
    have hjl : j ∉ l := (List.nodup_cons.1 hnd).1
    have hind : (if inDom s (oodX n r j) then (1 : ℝ≥0∞) else 0) ≤ if inDom s₀ (oodX n r j) then 1 else 0 := by
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        rcases hdom _ h1 with h | ⟨i, hi, hil, hz⟩
        · exact h2 h
        · have := oodX_inj_coord (by omega) (by omega) hz
          subst this
          exact hil (List.mem_cons_self ..)
      · exact zero_le
      · exact le_rfl
    have hrest : ∀ y, badB ((listF l fun j ↦ (keccakF (oodInput n r j)).bind fun d ↦
        .ret (elementOf ((digestBytes d).drop 8))).bind fun cs ↦
          K (elementOf ((digestBytes (digestOf y)).drop 8) :: cs)) ((oodX n r j, y) :: s.1, s.2) ≤
        (l.map fun j ↦ if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0).sum + l.length * (L * nInv) + B := by
      intro y
      refine badB_listF_ood L n hn r s₀ B l _ _ (fun i hi ↦ hl i (List.mem_cons_of_mem _ hi))
        (List.nodup_cons.1 hnd).2 (fun z hz ↦ ?_) (by simp at hsz ⊢; omega) fun cs s' hs' ↦ hK _ s' (by simp at hs' ⊢; omega)
      rcases (inDom_cons _ _ _ _ _).1 hz with h | h
      · exact Or.inr ⟨j, hj, hjl, h.symm⟩
      · rcases hdom z h with h' | ⟨i, hi, hil, hz'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨i, hi, fun h ↦ hil (List.mem_cons_of_mem _ h), hz'⟩
    calc εq s (oodX n r j) + ∑' y, Pr{let z ← uState}[z = y] * badB _ ((oodX n r j, y) :: s.1, s.2)
        ≤ ((if inDom s (oodX n r j) then 1 else 0) + s.1.length * nInv) +
            ((l.map fun j ↦ if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0).sum + l.length * (L * nInv) + B) :=
          add_le_add (εq_le _ _) (badB_last _ _ _ _ hrest)
      _ ≤ _ := by
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
          have hL : (s.1.length : ℝ≥0∞) * nInv ≤ L * nInv := by
            gcongr; simp at hsz; exact_mod_cast (by omega : s.1.length ≤ L)
          calc (if inDom s (oodX n r j) then (1 : ℝ≥0∞) else 0) + s.1.length * nInv +
                ((l.map fun j ↦ if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0).sum + l.length * (L * nInv) + B)
              ≤ (if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0) + L * nInv +
                ((l.map fun j ↦ if inDom s₀ (oodX n r j) then (1 : ℝ≥0∞) else 0).sum + l.length * (L * nInv) + B) := by
                gcongr
            _ = _ := by ring

theorem tsum_list_sum {γ : Type} (D : ProbComp γ) (l : List ℕ) (g : ℕ → γ → ℝ≥0∞) :
    ∑' u, Pr{let y ← D}[y = u] * (l.map fun j ↦ g j u).sum = (l.map fun j ↦ ∑' u, Pr{let y ← D}[y = u] * g j u).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons, List.sum_cons]; rw [tsum_add_le, ih]

/-- **An out-of-domain point costs at most `n · δq L`.** -/
theorem badB_oodBlock (L n : ℕ) (hn : n ≤ 256) (f : Digest → List E → FProg A α) (s : Edges × A)
    (hs : s.1.length + n ≤ L) (B : ℝ≥0∞) (hk : ∀ r zs (s' : Edges × A), s'.1.length = s.1.length + n → badB (f r zs) s' ≤ B) :
    badB (.step (simulateQ edgeOracle sampleDigest) fun r ↦ (oodF n r).bind (f r)) s ≤ n * δq L + B := by
  classical
  rw [badB_step_indep _ rootDist indep_sampleDigest]
  calc ∑' r, Pr{let y ← rootDist}[y = r] * badB ((oodF n r).bind (f r)) s
      ≤ ∑' r, Pr{let y ← rootDist}[y = r] *
          (((List.range n).map fun j ↦ if inDom s (oodX n r j) then (1 : ℝ≥0∞) else 0).sum + (n * (L * nInv) + B)) := by
        refine ENNReal.tsum_le_tsum fun r ↦ ?_
        gcongr
        have := badB_listF_ood L n hn r s B (List.range n) s (f r) (fun j hj ↦ List.mem_range.1 hj)
          List.nodup_range (fun z hz ↦ Or.inl hz) (by simpa using hs) fun cs s' hs' ↦ hk r cs s' (by simpa using hs')
        simp only [List.length_range] at this
        rw [← add_assoc]
        exact this
    _ = ((List.range n).map fun j ↦ Pr{let r ← rootDist}[inDom s (oodX n r j)]).sum + (n * (L * nInv) + B) := by
        rw [tsum_add_const, tsum_list_sum]
        congr 1
        exact congrArg List.sum (List.map_congr_left fun j _ ↦ tsum_ind _ _)
    _ ≤ ((List.range n).map fun _ ↦ (s.1.length : ℝ≥0∞) * pmax).sum + (n * (L * nInv) + B) := by
        gcongr
        exact List.sum_le_sum fun j _ ↦ prEvent_inDom_le _ _ (prEvent_oodX n j) s
    _ ≤ n * δq L + B := by
        rw [List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul, ← add_assoc]
        have hL : (s.1.length : ℝ≥0∞) ≤ L := by exact_mod_cast (by omega : s.1.length ≤ L)
        calc (n : ℝ≥0∞) * (s.1.length * pmax) + n * (L * nInv) + B ≤ n * (L * pmax) + n * (L * nInv) + B := by
              gcongr
          _ = n * δq L + B := by rw [δq]; ring

end PcsQuotient.EndToEnd
