-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The lazily sampled permutation is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/RandomPermutation.lean`), Keccak-256 over a permutation its `Statement/Keccak.lean`.
import ZK.PcsProc

/-!
# A recorded computation replays

The lazily sampled permutation answers a recorded input from its record. So a computation of the permutation's
forward calls, once run, runs again from any state that extends the state it left as `pure` of the same value
(`Replay`), provided the steps in between only add edges (`Mono`).

* `Ext s s'`: every edge of `s` is an edge of `s'`; `Mono m`: `m` only adds edges; `Replay m`: `m` replays.
* `edgePerm` (a forward call of `π`) is both; so are their binds (`Mono.bind`, `Replay.bind`), Keccak-256
  (`keccak256With`), the chain's seed and challenges, the out-of-domain points; the model's coins leave the
  state unchanged (`mono_sampleDigest`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

variable {A β γ : Type}

/-- **The edges of `s'` extend those of `s`.** -/
def Ext (s s' : Edges × A) : Prop :=
  ∀ x y, forwardLookup s.1 x = some y → forwardLookup s'.1 x = some y

theorem Ext.refl (s : Edges × A) : Ext s s := fun _ _ h ↦ h

theorem Ext.trans {s s' s'' : Edges × A} (h : Ext s s') (h' : Ext s' s'') : Ext s s'' :=
  fun x y hx ↦ h' x y (h x y hx)

/-- **`m` only adds edges.** -/
def Mono (m : StateT (Edges × A) ProbComp β) : Prop := ∀ s, ∀ p ∈ support (m.run s), Ext s p.2

/-- **`m` replays**: from any state extending one it left, it is `pure` of the value it gave. -/
def Replay (m : StateT (Edges × A) ProbComp β) : Prop :=
  ∀ s p, p ∈ support (m.run s) → ∀ s', Ext p.2 s' → m.run s' = pure (p.1, s')

theorem mono_pure (b : β) : Mono (pure b : StateT (Edges × A) ProbComp β) := by
  intro s p hp
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact Ext.refl s

theorem Mono.bind {m : StateT (Edges × A) ProbComp β} {k : β → StateT (Edges × A) ProbComp γ} (hm : Mono m)
    (hk : ∀ b, Mono (k b)) : Mono (m >>= k) := by
  intro s p hp
  simp only [StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  exact (hm s q hq).trans (hk q.1 q.2 p hp)

theorem Mono.map {m : StateT (Edges × A) ProbComp β} (hm : Mono m) (f : β → γ) : Mono (f <$> m) := by
  rw [map_eq_bind_pure_comp]
  exact hm.bind fun b ↦ mono_pure _

theorem replay_pure (b : β) : Replay (pure b : StateT (Edges × A) ProbComp β) := by
  intro s p hp s' _
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rfl

theorem Replay.bind {m : StateT (Edges × A) ProbComp β} {k : β → StateT (Edges × A) ProbComp γ}
    (hm : Replay m) (hk : ∀ b, Replay (k b)) (hk' : ∀ b, Mono (k b)) : Replay (m >>= k) := by
  intro s p hp s' hs'
  simp only [StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  have h1 : m.run s' = pure (q.1, s') := hm s q hq s' ((hk' q.1 q.2 p hp).trans hs')
  rw [StateT.run_bind, h1, pure_bind]
  exact hk q.1 q.2 p hp s' hs'

theorem Replay.map {m : StateT (Edges × A) ProbComp β} (hm : Replay m) (f : β → γ) : Replay (f <$> m) := by
  rw [map_eq_bind_pure_comp]
  exact hm.bind (fun b ↦ replay_pure _) fun b ↦ mono_pure _

theorem Mono.mapM {δ : Type} (f : δ → StateT (Edges × A) ProbComp β) (hf : ∀ a, Mono (f a)) :
    ∀ l : List δ, Mono (l.mapM f)
  | [] => by simpa using mono_pure []
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b ↦ (Mono.mapM f hf l).bind fun _ ↦ mono_pure _

/-! ### A forward call of the permutation -/

theorem edgePerm_run (x : KeccakState) (s : Edges × A) :
    (edgePerm x : StateT (Edges × A) ProbComp KeccakState).run s =
      (fun p ↦ (p.1, (p.2, s.2))) <$> (lazyRandomPermutation (.forward x)).run s.1 := by
  simp only [edgePerm, queryPermutation, simulateQ_spec_query]
  rfl

theorem lazy_run_some {E : Edges} {x y : KeccakState} (h : forwardLookup E x = some y) :
    (lazyRandomPermutation (.forward x)).run E = pure (y, E) := by
  simp only [lazyRandomPermutation, StateT.run, StateT.mk, h]

theorem lazy_run_none {E : Edges} {x : KeccakState} (h : forwardLookup E x = none) :
    (lazyRandomPermutation (.forward x)).run E =
      (fun y ↦ (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd) := by
  simp only [lazyRandomPermutation, StateT.run, StateT.mk, h]

theorem forwardLookup_of_mem_edgePerm {x : KeccakState} {s : Edges × A} {p : KeccakState × (Edges × A)}
    (hp : p ∈ support ((edgePerm x : StateT (Edges × A) ProbComp KeccakState).run s)) :
    forwardLookup p.2.1 x = some p.1 ∧ Ext s p.2 := by
  rw [edgePerm_run] at hp
  cases h : forwardLookup s.1 x with
  | some y =>
    simp only [lazy_run_some h, map_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨h, Ext.refl s⟩
  | none =>
    simp only [lazy_run_none h, Functor.map_map, support_map, Set.mem_image] at hp
    obtain ⟨y, -, rfl⟩ := hp
    refine ⟨by simp [forwardLookup], fun x' y' h' ↦ ?_⟩
    simp only [forwardLookup]
    split_ifs with hx
    · subst hx
      rw [h] at h'
      exact absurd h' (by simp)
    · exact h'

theorem mono_edgePerm (x : KeccakState) : Mono (edgePerm (A := A) x) :=
  fun _ _ hp ↦ (forwardLookup_of_mem_edgePerm hp).2

theorem replay_edgePerm (x : KeccakState) : Replay (edgePerm (A := A) x) := by
  intro s p hp s' hs'
  have h := hs' x p.1 (forwardLookup_of_mem_edgePerm hp).1
  rw [edgePerm_run, lazy_run_some h]
  rfl

/-! ### Keccak-256, the chain, the out-of-domain points -/

theorem absorbBlockWith_mono (state : KeccakState) (block : List UInt8) :
    Mono (absorbBlockWith (edgePerm (A := A)) state block) := mono_edgePerm _

theorem absorbBlockWith_replay (state : KeccakState) (block : List UInt8) :
    Replay (absorbBlockWith (edgePerm (A := A)) state block) := replay_edgePerm _

theorem absorbWith_mono : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    Mono (absorbWith (edgePerm (A := A)) blocks state data)
  | 0, _, _ => absorbBlockWith_mono _ _
  | b + 1, _, _ => (absorbBlockWith_mono _ _).bind fun st ↦ absorbWith_mono b st _

theorem absorbWith_replay : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    Replay (absorbWith (edgePerm (A := A)) blocks state data)
  | 0, _, _ => absorbBlockWith_replay _ _
  | b + 1, _, _ => (absorbBlockWith_replay _ _).bind (fun st ↦ absorbWith_replay b st _)
      fun st ↦ absorbWith_mono b st _

theorem keccak_mono (data : List UInt8) : Mono (keccak256With (edgePerm (A := A)) data) :=
  (absorbWith_mono _ _ _).bind fun _ ↦ mono_pure _

theorem keccak_replay (data : List UInt8) : Replay (keccak256With (edgePerm (A := A)) data) :=
  (absorbWith_replay _ _ _).bind (fun _ ↦ replay_pure _) fun _ ↦ mono_pure _

theorem startWith_mono (label : List UInt8) : Mono (Chain.startWith (edgePerm (A := A)) label) :=
  (keccak_mono _).bind fun _ ↦ mono_pure _

theorem startWith_replay (label : List UInt8) : Replay (Chain.startWith (edgePerm (A := A)) label) :=
  (keccak_replay _).bind (fun _ ↦ replay_pure _) fun _ ↦ mono_pure _

theorem squeezeWith_mono (c : Chain) : Mono (c.squeezeWith (edgePerm (A := A))) :=
  (keccak_mono _).bind fun _ ↦ mono_pure _

theorem squeezeWith_replay (c : Chain) : Replay (c.squeezeWith (edgePerm (A := A))) :=
  (keccak_replay _).bind (fun _ ↦ replay_pure _) fun _ ↦ mono_pure _

theorem oodPointWith_mono (n : ℕ) (root : Digest) : Mono (oodPointWith (edgePerm (A := A)) n root) :=
  Mono.mapM _ (fun _ ↦ (keccak_mono _).bind fun _ ↦ mono_pure _) _

theorem onEdges_run {α : Type} (x : StateT Edges ProbComp α) (s : Edges × A) :
    (onEdges x).run s = (fun p ↦ (p.1, (p.2, s.2))) <$> x.run s.1 := rfl

/-- **The model's coins leave the state unchanged.** -/
theorem coinQuery_run (n : ℕ) (s : Edges × A) :
    (edgeOracle (A := A) (.inl n)).run s = (fun u ↦ (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  rw [show edgeOracle (A := A) (.inl n) = onEdges (lazyRandomPermutationOracles (.inl n)) from rfl,
    onEdges_run]
  simp [lazyRandomPermutationOracles, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift]

theorem mono_coinQuery (n : ℕ) : Mono (edgeOracle (A := A) (.inl n)) := by
  intro s p hp
  rw [coinQuery_run] at hp
  simp only [support_map, Set.mem_image] at hp
  obtain ⟨u, -, rfl⟩ := hp
  exact Ext.refl s

theorem mono_coinWord : Mono (simulateQ (edgeOracle (A := A)) coinWord) := by
  simp only [coinWord, simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
  exact (mono_coinQuery _).bind fun _ ↦ mono_pure _

theorem mono_sampleDigest : Mono (simulateQ (edgeOracle (A := A)) sampleDigest) := by
  simp only [sampleDigest, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  exact (Mono.mapM _ (fun _ ↦ mono_coinWord) _).bind fun _ ↦ mono_pure _

end PcsQuotient.EndToEnd
