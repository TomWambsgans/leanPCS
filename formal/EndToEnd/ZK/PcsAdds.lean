-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. Merkle trees over a permutation are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Prover/Run.lean`).
import ZK.PcsBad

/-!
# How many edges a computation adds

`AddsS m a`: every run of `m` adds at most `a` edges. A forward call adds one, Keccak-256 one a block, the
circuit's commitment (`commitmentWith` at `μ = 24`: `2^19` leaves of four blocks, `2^19 − 1` nodes, `24`
out-of-domain coordinates) at most `5 · 2^19 + 24` (`addsS_setup`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Prover
open scoped ENNReal

namespace PcsQuotient.EndToEnd

variable {A γ δ : Type}

/-- **Every run of `m` adds at most `a` edges.** -/
def AddsS (m : StateT (Edges × A) ProbComp γ) (a : ℕ) : Prop :=
  ∀ s, ∀ p ∈ support (m.run s), p.2.1.length ≤ s.1.length + a

theorem addsS_pure (b : γ) : AddsS (A := A) (pure b) 0 := fun s p hp ↦ by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp; simp

theorem AddsS.mono {m : StateT (Edges × A) ProbComp γ} {a b : ℕ} (h : AddsS m a) (hab : a ≤ b) : AddsS m b :=
  fun s p hp ↦ (h s p hp).trans (by omega)

theorem AddsS.bind {m : StateT (Edges × A) ProbComp γ} {k : γ → StateT (Edges × A) ProbComp δ} {a c : ℕ}
    (hm : AddsS m a) (hk : ∀ b, AddsS (k b) c) : AddsS (m >>= k) (a + c) := fun s p hp ↦ by
  simp only [StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  have := hm s q hq
  have := hk q.1 q.2 p hp
  omega

theorem AddsS.map {m : StateT (Edges × A) ProbComp γ} {a : ℕ} (hm : AddsS m a) (f : γ → δ) :
    AddsS (f <$> m) a := by
  rw [map_eq_bind_pure_comp]
  exact (hm.bind fun _ ↦ addsS_pure _).mono (by omega)

theorem addsS_indep {m : StateT (Edges × A) ProbComp γ} {D : ProbComp γ} (h : StateIndep m D) : AddsS m 0 :=
  fun s p hp ↦ by
    rw [h s, support_map] at hp
    obtain ⟨u, -, rfl⟩ := hp
    simp

theorem addsS_edgePerm (x : KeccakState) : AddsS (A := A) (edgePerm x) 1 := fun s p hp ↦ by
  rw [edgePerm_run] at hp
  cases h : forwardLookup s.1 x with
  | some y =>
    simp only [lazy_run_some h, map_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; simp
  | none =>
    simp only [lazy_run_none h, Functor.map_map, support_map, Set.mem_image] at hp
    obtain ⟨y, -, rfl⟩ := hp
    simp

theorem AddsS.mapM {ε : Type} (f : ε → StateT (Edges × A) ProbComp γ) (a : ℕ) (hf : ∀ b, AddsS (f b) a) :
    ∀ l : List ε, AddsS (l.mapM f) (l.length * a)
  | [] => by simpa using addsS_pure []
  | b :: l => by
    rw [List.mapM_cons]
    exact ((hf b).bind fun _ ↦ (AddsS.mapM f a hf l).bind fun _ ↦ addsS_pure _).mono (by simp; ring_nf; omega)

theorem AddsS.arrayMapM {ε : Type} (f : ε → StateT (Edges × A) ProbComp γ) (a : ℕ) (hf : ∀ b, AddsS (f b) a)
    (l : Array ε) : AddsS (l.mapM f) (l.size * a) := by
  rw [Array.mapM_eq_mapM_toList]
  exact ((AddsS.mapM f a hf l.toList).map _).mono (by simp)

theorem addsS_absorbWith : ∀ (b : ℕ) (st : KeccakState) (d : List UInt8),
    AddsS (A := A) (absorbWith edgePerm b st d) (b + 1)
  | 0, _, _ => addsS_edgePerm _
  | b + 1, _, _ => ((addsS_edgePerm _).bind fun _ ↦ addsS_absorbWith b _ _).mono (by omega)

theorem addsS_keccak (data : List UInt8) :
    AddsS (A := A) (keccak256With edgePerm data) (data.length / rate + 1) :=
  ((addsS_absorbWith _ _ _).bind fun _ ↦ addsS_pure _).mono (by omega)

theorem addsS_keccak_le (data : List UInt8) (n : ℕ) (h : data.length / rate + 1 ≤ n) :
    AddsS (A := A) (keccak256With edgePerm data) n := (addsS_keccak data).mono h

theorem addsS_oodPointWith (n : ℕ) (r : Digest) : AddsS (A := A) (oodPointWith edgePerm n r) n := by
  refine (AddsS.mapM _ 1 (fun j ↦ ((addsS_keccak_le _ 1 ?_).bind fun _ ↦ addsS_pure _)) _).mono (by simp)
  rw [oodInput_len]; rfl

theorem stackWord_length (μ R : ℕ) (table : Array K) (p : ℕ) : (stackWordFast μ R table p).length = 64 := by
  simp only [stackWordFast, stackWordFast.stackWordOf]
  split_ifs <;> simp

theorem addsS_levelsM : ∀ (k : ℕ) (level : Array Digest), AddsS (A := A) (levelsM edgePerm k level) (2 ^ k)
  | 0, _ => (addsS_pure _).mono (by omega)
  | k + 1, level => by
    refine (((AddsS.arrayMapM _ 1 (fun j ↦ addsS_keccak_le _ 1 ?_) _).bind fun up ↦
      (addsS_levelsM k up).bind fun _ ↦ addsS_pure _)).mono ?_
    · simp [digestBytes_len, rate]
    · simp [pow_succ]; omega

/-- **The circuit's commitment adds at most `5 · 2^19 + 24` edges.** -/
theorem addsS_setup (table : Array K) : AddsS (A := A) (commitmentWith edgePerm 24 table) (5 * 2 ^ 19 + 24) := by
  unfold commitmentWith commitWith buildTreeM leafDigestsM
  refine ((((AddsS.arrayMapM _ 4 (fun i ↦ addsS_keccak_le _ 4 ?_) _).bind fun leaves ↦
    (addsS_levelsM 19 leaves).bind fun _ ↦ addsS_pure _).bind fun tree ↦
    (addsS_oodPointWith 24 _).bind fun _ ↦ addsS_pure _)).mono ?_
  · have hk : ∀ a : K, (kBytes a).length = 8 := fun _ ↦ rfl
    rw [List.length_flatMap]
    simp only [hk, List.map_const', List.sum_replicate, stackWord_length, smul_eq_mul, rate]
    norm_num
  · simp [laneFold, logInvRate]

end PcsQuotient.EndToEnd
