-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the opening (`cost_openingWithH`, `vOpen`)
-- and of a commitment (`qc_commitWithH`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/VerifierHCost.lean` and `Rec3VerifierHCost.lean`.
import UniKeccakComplete.K.VerifierHDuplex
import E2ECompleteness.Cost

/-!
# The block count of the Keccak verifier

**`cost_verifierWithH`**: the deployed Keccak verifier over the two calls, of either variant (`keccakMain`,
`keccakRec3`: one function, `KDeployment.verifierWithH … v`), on any proof whose stream has at most `S` bytes, makes at
most `verifierCost D v S` block calls (`hashBlocks`: a Keccak-256 of `n` bytes costs `⌊n / 136⌋ + 1`, a Keccak-f[1600]
one), whatever its opening proofs; **`cost_setupTreeKWithH`** bounds the setup (one tree).

`verifierCost D v S = ivCost D + 1 + walkCost D.shape v + 3 S + 3 openCost`:

* **The walk** (`cc_reduceWithKH`): every challenge hashes the state and the bytes read since the last one. The count
  is amortized by a potential on the channel (`pot`: three per unread byte, one per byte read but not yet hashed): a
  read of `n` bytes releases `2 n`; a challenge costs at most `2` plus the bytes it hashes (`cc_sampleH`,
  `cc_sampleNarrowH`). Every sumcheck round reads its message before its challenge, so the rounds are paid by their
  reads (`cc_sumcheckH`, `cc_sumcheckDrawnH`, the paired batch's `cc_sumcheckPairsDrawnH`): the bound does not depend
  on the stacks' layouts. The other challenges cost `2` each (`walkCost`): the two runs (`α ∈ E^4` and Flock's
  zerocheck coordinates after its seven fixed ones, `drawCost`: one by one on the main line, one challenge and its
  squares at π1-rec3), then `β`, `γ`, Flock's `z`, its `α`, the ring map's six, `t`, `ρ`, `λ`. From the start, the
  potential is `3 S`.
* **The seed** (`80` bytes, one block), **the IV** (`ivCost`: `163` bytes and the program's IV; the Keccak layout
  words and the variant's `11` bytes).
* **The openings**: at most three point claims (the walk's result has at most three openings, the commitments'),
  each `openCost = 46 + vOpen` blocks (E2ECompleteness's `cost_openingWithH`: a claim of at most `255` coordinates, a
  layout word's byte, whatever the opening proof).

The calculus (`CostP`): a computation over the two calls with at most `n` block calls on every path, each outcome
satisfying a postcondition with the blocks left (as mumbai's `DuplexP` carries the answers); `CC x k g P` for the
channel: from any state with `absorbed ≤ cursor ≤ size` (`Inv`), at most `k` blocks beyond the potential, releasing
`g` more, each successful result satisfying `P`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniKeccakComplete.Cost

/-! ## Costs with a postcondition -/

/-- **At most `n` block calls on every path**, each outcome satisfying `Q` with the blocks left. -/
def CostP {α : Type} : OracleComp KeccakCalls α → ℕ → (α → ℕ → Prop) → Prop
  | .pure a, n, Q => Q a n
  | .liftBind t k, n, Q => hashBlocks t ≤ n ∧ ∀ u, CostP (k u) (n - hashBlocks t) Q

theorem costP_query_bind {α : Type} (t : List UInt8 ⊕ KeccakState)
    (k : KeccakCalls.Range t → OracleComp KeccakCalls α) (n : ℕ) (Q : α → ℕ → Prop) :
    CostP (liftM (KeccakCalls.query t) >>= k) n Q ↔ hashBlocks t ≤ n ∧ ∀ u, CostP (k u) (n - hashBlocks t) Q :=
  Iff.rfl

theorem CostP.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {n : ℕ}
    {Q : α → ℕ → Prop} {R : β → ℕ → Prop} (hX : CostP X n Q) (hf : ∀ a r, Q a r → CostP (f a) r R) :
    CostP (X >>= f) n R := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => simpa using hf a n hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [costP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem CostP.mono {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {Q R : α → ℕ → Prop}
    (hX : CostP X n Q) (h : ∀ a r, Q a r → R a r) : CostP X n R := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact h a n hX
  | query_bind t k ih =>
    rw [costP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

/-- A cost with a postcondition is a cost. -/
theorem CostP.toQC {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {Q : α → ℕ → Prop}
    (hX : CostP X n Q) : Common.QueryCostAtMost X hashBlocks n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [costP_query_bind] at hX
    exact (Common.isWeightBound_query_bind_iff hashBlocks t k n).mpr ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

/-- A cost, with `m` more blocks, leaves at least `m`. -/
theorem costP_of_qc {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (hX : Common.QueryCostAtMost X hashBlocks n) (m : ℕ) : CostP X (n + m) fun _ r ↦ m ≤ r := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact Nat.le_add_left m n
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at hX
    rw [costP_query_bind]
    refine ⟨by omega, fun u ↦ ?_⟩
    rw [show n + m - hashBlocks t = (n - hashBlocks t) + m by omega]
    exact ih u (hX.2 u)

/-! ## The channel -/

/-- The channel's monad over the two calls. -/
abbrev CM := ChanM (OracleComp KeccakCalls)

/-- **The potential**: three per unread byte, one per byte read and not yet hashed. -/
def pot (c : Chan) : ℕ := 3 * (c.data.size - c.cursor) + (c.cursor - c.absorbed)

/-- The channel's invariant. -/
def Inv (c : Chan) : Prop := c.absorbed ≤ c.cursor ∧ c.cursor ≤ c.data.size

/-- **`x` from `c`**: at most `k` blocks beyond the potential (and any extra `e`), releasing `g`; each successful
result satisfies `P`, from a state satisfying the invariant. -/
def CCAt {α : Type} (c : Chan) (x : CM α) (k g : ℕ) (P : α → Prop) : Prop :=
  ∀ e, CostP (x.run.run c) (k + pot c + e) fun z rem ↦
    ∀ a, z.1 = .ok a → P a ∧ Inv z.2 ∧ pot z.2 + g + e ≤ rem

/-- **`x` costs at most `k` blocks beyond the potential and releases `g`**, from any state satisfying the
invariant, each successful result satisfying `P`. -/
def CC {α : Type} (x : CM α) (k g : ℕ) (P : α → Prop) : Prop := ∀ c, Inv c → CCAt c x k g P

section Calculus

variable {α β : Type}

theorem cc_bind {x : CM α} {f : α → CM β} {k₁ g₁ k₂ g₂ : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x k₁ g₁ P) (hf : ∀ a, P a → CC (f a) k₂ g₂ Q) :
    CC (x >>= f) (k₁ + (k₂ - g₁)) (g₂ + (g₁ - k₂)) Q := by
  intro c hc e
  rw [show k₁ + (k₂ - g₁) + pot c + e = k₁ + pot c + ((k₂ - g₁) + e) by omega]
  simp only [ExceptT.run_bind, StateT.run_bind]
  refine CostP.bind (hx c hc _) fun z rem hz ↦ ?_
  obtain ⟨r, s⟩ := z
  cases r with
  | error err => exact fun a h ↦ by cases h
  | ok a =>
    obtain ⟨hP, hI, hrem⟩ := hz a rfl
    dsimp only at hI hrem
    have h2 := hf a hP s hI (rem - k₂ - pot s)
    rw [show k₂ + pot s + (rem - k₂ - pot s) = rem by omega] at h2
    exact h2.mono fun z' rem' h a' ha' ↦
      let ⟨h1, h2, h3⟩ := h a' ha'
      ⟨h1, h2, by omega⟩

theorem cc_mono {x : CM α} {k g k' g' : ℕ} {P P' : α → Prop} (h : CC x k g P) (hk : k ≤ k') (hg : g' ≤ g)
    (hP : ∀ a, P a → P' a) : CC x k' g' P' := by
  intro c hc e
  have h1 := h c hc (e + (k' - k))
  rw [show k + pot c + (e + (k' - k)) = k' + pot c + e by omega] at h1
  exact h1.mono fun z rem hz a ha ↦
    let ⟨h1, h2, h3⟩ := hz a ha
    ⟨hP a h1, h2, by omega⟩

/-- A paid step, then the rest from what is left. -/
theorem cc_seq {x : CM α} {f : α → CM β} {k₁ k g : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x k₁ 0 P) (hf : ∀ a, P a → CC (f a) (k - k₁) g Q) (hk : k₁ ≤ k) : CC (x >>= f) k g Q :=
  cc_mono (cc_bind hx hf) (by omega) (by omega) fun _ h ↦ h

/-- A free step. -/
theorem cc_free {x : CM α} {f : α → CM β} {k g : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x 0 0 P) (hf : ∀ a, P a → CC (f a) k g Q) : CC (x >>= f) k g Q :=
  cc_seq hx (fun a h ↦ by simpa using hf a h) (Nat.zero_le _)

theorem cc_pure {a : α} {P : α → Prop} (h : P a) (k : ℕ) : CC (pure a : CM α) k 0 P := by
  intro c hc e a' ha'
  cases ha'
  exact ⟨h, hc, by dsimp only; omega⟩

theorem cc_throw (err : UniError) (k g : ℕ) (P : α → Prop) : CC (throw err : CM α) k g P := by
  intro c hc e a ha
  cases ha

theorem cc_throw_bind (err : UniError) (f : α → CM β) (k g : ℕ) (P : β → Prop) :
    CC (throw err >>= f) k g P := by
  intro c hc e a ha
  cases ha

theorem cc_ite {x y : CM α} {k g : ℕ} {P : α → Prop} (cnd : Prop) [Decidable cnd] (hx : CC x k g P)
    (hy : CC y k g P) : CC (if cnd then x else y) k g P := by
  split
  · exact hx
  · exact hy

theorem cc_map {x : CM α} {k g : ℕ} {P : α → Prop} (f : α → β) (hx : CC x k g P) :
    CC (f <$> x) k g fun _ ↦ True := by
  rw [map_eq_bind_pure_comp]
  exact cc_mono (cc_bind hx fun a _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega)
    fun _ _ ↦ trivial

/-- **A loop** of steps of cost `k`. -/
theorem cc_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → CM (ForInStep β)) {k : ℕ}
    (hf : ∀ a s, CC (f a s) k 0 fun _ ↦ True) : CC (forIn l b f) (l.length * k) 0 fun _ ↦ True := by
  induction l generalizing b with
  | nil => exact cc_pure trivial _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine cc_seq (hf a b) (fun s _ ↦ ?_) (by simp [Nat.succ_mul])
    cases s with
    | done b => exact cc_pure trivial _
    | yield b => exact cc_mono (ih b) (by simp [Nat.succ_mul]) le_rfl fun _ h ↦ h

/-- A loop over `[0:n]`. -/
theorem cc_forIn_range (n : ℕ) (b : β) (f : ℕ → β → CM (ForInStep β)) {k : ℕ}
    (hf : ∀ a s, CC (f a s) k 0 fun _ ↦ True) : CC (forIn [0:n] b f) (n * k) 0 fun _ ↦ True := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact cc_mono (cc_forIn_list _ b f hf) (by simp [Std.Legacy.Range.size]) le_rfl fun _ h ↦ h

/-- A loop releases at least its first step's gain. -/
theorem cc_forIn_list_first {γ : Type} (l : List γ) (hl : l ≠ []) (b : β) (f : γ → β → CM (ForInStep β))
    {g : ℕ} (hf : ∀ a s, CC (f a s) 0 g fun _ ↦ True) : CC (forIn l b f) 0 g fun _ ↦ True := by
  obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := by
    cases l with
    | nil => exact absurd rfl hl
    | cons a l' => exact ⟨a, l', rfl⟩
  rw [List.forIn_cons]
  refine cc_mono (cc_bind (k₂ := 0) (g₂ := 0) (hf a b) fun s _ ↦ ?_) (by omega) (by omega) fun _ h ↦ h
  cases s with
  | done b => exact cc_pure trivial 0
  | yield b =>
    exact cc_mono (cc_forIn_list (k := 0) l b f fun _ _ ↦ cc_mono (hf _ _) le_rfl (Nat.zero_le _) fun _ h ↦ h)
      (by simp) le_rfl fun _ h ↦ h

theorem cc_forIn_range_first (n : ℕ) (hn : 1 ≤ n) (b : β) (f : ℕ → β → CM (ForInStep β)) {g : ℕ}
    (hf : ∀ a s, CC (f a s) 0 g fun _ ↦ True) : CC (forIn [0:n] b f) 0 g fun _ ↦ True := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine cc_forIn_list_first _ ?_ b f hf
  simp [Std.Legacy.Range.size]
  omega

end Calculus

/-! ## The channel's steps -/

section Steps

theorem run_get (c : Chan) : (ExceptT.run (get : CM Chan)).run c = pure (.ok c, c) := by
  show (Except.ok <$> (get : StateT Chan (OracleComp KeccakCalls) Chan)).run c = _
  simp [StateT.run_map, StateT.run_get]

theorem run_set (c c' : Chan) : (ExceptT.run (set c' : CM PUnit)).run c = pure (.ok PUnit.unit, c') := by
  show (Except.ok <$> (set c' : StateT Chan (OracleComp KeccakCalls) PUnit)).run c = _
  simp [StateT.run_map, StateT.run_set]

theorem run_modify (f : Chan → Chan) (c : Chan) :
    (ExceptT.run (modify f : CM PUnit)).run c = pure (.ok PUnit.unit, f c) := by
  show (Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan (OracleComp KeccakCalls) PUnit)).run c = _
  simp [StateT.run_map, StateT.run_modifyGet]

theorem len_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

/-- **A challenge** costs at most `2` blocks beyond the bytes it hashes, which the potential holds. -/
theorem cc_sampleH : CC (sampleH callKeccak256) 2 0 fun _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u a _ ↦ ⟨trivial, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1 ≤ 2 + pot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · exact ⟨le_rfl, hc.2⟩
  · show 3 * (c.data.size - c.cursor) + (c.cursor - c.cursor) + 0 + e ≤
      2 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega

/-- **A read of `n` bytes** releases `2 n`. -/
theorem cc_takeBytes (n : ℕ) : CC (takeBytes (m := OracleComp KeccakCalls) n) 0 (2 * n) fun _ ↦ True := by
  intro c hc e
  unfold takeBytes
  simp only [ExceptT.run_bind, StateT.run_bind, run_get, pure_bind]
  split
  · rename_i h
    simp only [ExceptT.run_bind, StateT.run_bind, run_set, pure_bind]
    refine fun a _ ↦ ⟨trivial, ⟨hc.1.trans (Nat.le_add_right _ _), h⟩, ?_⟩
    simp only [pot]
    have := hc.1
    omega
  · exact fun a ha ↦ by cases ha

theorem cc_nextScalar : CC (nextScalar (m := OracleComp KeccakCalls)) 0 48 fun _ ↦ True := by
  unfold nextScalar
  exact cc_mono (cc_bind (cc_takeBytes 24) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (by omega) fun _ _ ↦ trivial

theorem cc_nextInteger (bytes : ℕ) : CC (nextInteger (m := OracleComp KeccakCalls) bytes) 0 0 fun _ ↦ True := by
  unfold nextInteger
  exact cc_mono (cc_bind (cc_takeBytes bytes) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (Nat.zero_le _) fun _ _ ↦ trivial

theorem cc_nextScalars (count : ℕ) : CC (nextScalars (m := OracleComp KeccakCalls) count) 0 0 fun _ ↦ True := by
  unfold nextScalars
  refine cc_free (cc_mono (cc_forIn_range (k := 0) count _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ cc_pure trivial 0
  exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (Nat.zero_le _) fun _ _ ↦ trivial

/-- At least one scalar read releases `2`. -/
theorem cc_nextScalars_pos (count : ℕ) (h : 1 ≤ count) :
    CC (nextScalars (m := OracleComp KeccakCalls) count) 0 2 fun _ ↦ True := by
  unfold nextScalars
  refine cc_mono (cc_bind (cc_forIn_range_first (g := 48) count h _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (by omega) fun _ _ ↦ trivial

theorem cc_nextRoot : CC (nextRoot (m := OracleComp KeccakCalls)) 0 0 fun _ ↦ True := by
  unfold nextRoot
  exact cc_free (cc_mono (cc_takeBytes 16) le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦
    cc_free (cc_mono (cc_takeBytes 16) le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ cc_pure trivial 0

theorem cc_requireZero (value : E) : CC (requireZero (m := OracleComp KeccakCalls) value) 0 0 fun _ ↦ True := by
  intro c hc e
  unfold requireZero
  rw [run_modify]
  exact fun a _ ↦ ⟨trivial, hc, by simp [pot]⟩

theorem cc_finish : CC (finish (m := OracleComp KeccakCalls)) 0 0 fun _ ↦ True := by
  intro c hc e
  unfold finish
  simp only [ExceptT.run_bind, StateT.run_bind, run_get, pure_bind]
  split
  · exact fun a _ ↦ ⟨trivial, hc, by dsimp only; omega⟩
  · exact fun a ha ↦ by cases ha

/-- **A sumcheck round's message** (of at least two coefficients) releases `2`: it reads two scalars. -/
theorem cc_roundPoly (count : ℕ) (h : 2 ≤ count) (claim : E) (eqFactor : Option E) :
    CC (roundPoly (m := OracleComp KeccakCalls) count claim eqFactor) 0 2 fun _ ↦ True := by
  unfold roundPoly
  cases eqFactor with
  | none =>
    exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_bind (cc_nextScalars _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial
  | some r =>
    exact cc_mono (cc_bind (cc_nextScalars_pos (count - 1) (by omega)) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial

end Steps
/-! ## The verifier's parts -/

section Parts

theorem cc_samplesH (count : ℕ) : CC (samplesH callKeccak256 count) (2 * count) 0 fun _ ↦ True := by
  unfold samplesH
  refine cc_mono (cc_bind (cc_forIn_range (k := 2) count _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  exact cc_mono (cc_bind cc_sampleH fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega) le_rfl
    fun _ h ↦ h

/-- **A sumcheck is paid by its reads**: each round reads its message before its challenge. -/
theorem cc_sumcheckH (claim : E) (count : ℕ) (h : 2 ≤ count) (equalities : List (Option E)) :
    CC (sumcheckH callKeccak256 claim count equalities) 0 0 fun _ ↦ True := by
  unfold sumcheckH
  refine cc_mono (cc_bind (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h
  exact cc_mono (cc_bind (cc_roundPoly count h _ _) fun _ _ ↦ cc_bind cc_sampleH fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h

/-- **A narrow challenge** costs at most `2` blocks beyond the bytes it hashes, as a challenge. -/
theorem cc_sampleNarrowH : CC (sampleNarrowH callKeccak256) 2 0 fun _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u a _ ↦ ⟨trivial, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1 ≤ 2 + pot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · exact ⟨le_rfl, hc.2⟩
  · show 3 * (c.data.size - c.cursor) + (c.cursor - c.cursor) + 0 + e ≤
      2 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega

theorem cc_sampleDrawnH (narrow : Bool) : CC (sampleDrawnH callKeccak256 narrow) 2 0 fun _ ↦ True := by
  cases narrow
  · exact cc_sampleH
  · exact cc_sampleNarrowH

/-- The blocks of a run of `count` challenges beyond the potential: two each drawn one by one (`main`), two for the
first and its squares (the others). -/
def drawCost : FsShape → ℕ → ℕ
  | .main, count => 2 * count
  | .rec1, _ | .rec2, _ | .rec3, _ => 2

theorem cc_drawRunH (fs : FsShape) (count : ℕ) :
    CC (drawRunH callKeccak256 fs count) (drawCost fs count) 0 fun _ ↦ True := by
  cases fs
  · exact cc_samplesH count
  all_goals
    dsimp only [drawRunH, drawCost]
    exact cc_ite _ (cc_pure trivial _) (cc_seq cc_sampleH (fun _ _ ↦ cc_pure trivial _) le_rfl)

/-- **A sumcheck, narrow or not, is paid by its reads.** -/
theorem cc_sumcheckDrawnH (claim : E) (count : ℕ) (h : 2 ≤ count) (equalities : List (Option E)) (narrow : Bool) :
    CC (sumcheckDrawnH callKeccak256 claim count equalities narrow) 0 0 fun _ ↦ True := by
  unfold sumcheckDrawnH
  refine cc_mono (cc_bind (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h
  exact cc_mono (cc_bind (cc_roundPoly count h _ _) fun _ _ ↦ cc_bind (cc_sampleDrawnH narrow) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h

/-- **A pair's round polynomial** releases `2`: it reads at least three scalars. -/
theorem cc_pairRoundPoly (degree : ℕ) (claim : E) :
    CC (pairRoundPoly (m := OracleComp KeccakCalls) degree claim) 0 2 fun _ ↦ True := by
  unfold pairRoundPoly
  exact cc_mono (cc_bind (cc_nextScalars_pos 3 (by norm_num)) fun _ _ ↦ cc_bind (cc_nextScalars _) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial

/-- **The paired sumcheck is paid by its reads**: each pair reads its polynomial before its challenge, and the last
plain round (`degree + 1 ≥ 2` coefficients) too. -/
theorem cc_sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (h : 1 ≤ degree) (narrow : Bool) :
    CC (sumcheckPairsDrawnH callKeccak256 claim degree vars narrow) 0 0 fun _ ↦ True := by
  unfold sumcheckPairsDrawnH
  refine cc_free (cc_mono (cc_forIn_range (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
  · exact cc_mono (cc_bind (cc_pairRoundPoly _ _) fun _ _ ↦ cc_bind (cc_sampleDrawnH narrow) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  · repeat (first
      | exact cc_pure (P := fun _ ↦ True) trivial _
      | refine cc_free (cc_sumcheckDrawnH _ _ (by omega) _ _) fun _ _ ↦ ?_
      | refine cc_ite _ ?_ ?_
      | dsimp only
      | split)

theorem cc_countBits (heights : List ℕ) : CC (countBits (m := OracleComp KeccakCalls) heights) 0 0 fun _ ↦ True := by
  unfold countBits
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ cc_pure trivial 0
  exact cc_free (cc_nextInteger _) fun _ _ ↦ cc_free (cc_requireZero _) fun _ _ ↦
    cc_free (cc_requireZero _) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0

theorem cc_tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    CC (tablePart (m := OracleComp KeccakCalls) t logHeight weights beta w) 0 0 fun _ ↦ True := by
  unfold tablePart
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ ?_
  · exact cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun x _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦
    cc_pure trivial 0
  obtain ⟨pulled, pushed⟩ := x
  repeat (first
    | exact cc_pure (P := fun _ ↦ True) trivial _
    | refine cc_ite _ ?_ ?_
    | refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_)

theorem cc_ringEndH (variant : Flock.Variant) (s : List E) :
    CC (Flock.ringEndH callKeccak256 variant s) 12 0 fun _ ↦ True :=
  cc_seq (cc_samplesH _) (fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial _) (by simp [Flock.ringMapShifts])

/-- One step of the walk: a read, a challenge, a part, or a branch (the do-notation's `if` and `match` carry
the rest of the block in each branch). -/
macro "cc_step" : tactic => `(tactic| first
  | with_reducible_and_instances exact cc_pure (P := fun _ ↦ True) trivial _
  | with_reducible_and_instances exact cc_throw_bind _ _ _ _ _
  | with_reducible_and_instances refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free cc_nextRoot fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_countBits _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_sumcheckPairsDrawnH _ _ _ (by norm_num) _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_sumcheckDrawnH _ 3 (by norm_num) _ _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_map _ (cc_nextScalars _)) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
  | with_reducible_and_instances refine cc_seq (cc_samplesH _) (fun _ _ ↦ ?_) (by omega)
  | with_reducible_and_instances refine cc_seq (cc_ringEndH _ _) (fun _ _ ↦ ?_) (by omega)
  | dsimp only
  | split)

/-- **Flock's zerocheck** (`zerocheckFsH`): the run of its sampled coordinates, the skip's `z`; its rounds paid by
their reads. -/
theorem cc_zerocheckFsH (logN k : ℕ) (fs : FsShape) :
    CC (Flock.zerocheckFsH callKeccak256 logN k fs) (drawCost fs (logN - k - Flock.nFixed) + 2) 0
      fun _ ↦ True := by
  unfold Flock.zerocheckFsH
  refine cc_seq (cc_drawRunH _ _) (fun _ _ ↦ ?_) (by omega)
  split
  · refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _
  · dsimp only
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _

/-- **Flock's front** (`frontKH`): the zerocheck, its `α`; the lincheck's rounds and the slices paid by their reads. -/
theorem cc_frontKH (logN : ℕ) (v : UniKeccak.KeccakVariant) :
    CC (frontKH callKeccak256 logN v) (drawCost v.fs (logN - v.skip - Flock.nFixed) + 4) 0 fun _ ↦ True := by
  unfold frontKH
  refine cc_seq (cc_zerocheckFsH _ _ _) (fun _ _ ↦ ?_) (by omega)
  repeat cc_step

/-- **Flock walked** (`verifyWalkedKH`): the front, the structured terminal (a zero collected), the ring switch's
map. -/
theorem cc_verifyWalkedKH (logN : ℕ) (v : UniKeccak.KeccakVariant) :
    CC (verifyWalkedKH callKeccak256 logN v) (drawCost v.fs (logN - v.skip - Flock.nFixed) + 16) 0
      fun _ ↦ True := by
  unfold verifyWalkedKH
  refine cc_seq (cc_frontKH _ _) (fun _ _ ↦ ?_) (by omega)
  dsimp only
  refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  refine cc_seq (cc_ringEndH _ _) (fun _ _ ↦ ?_) (by omega)
  exact cc_pure trivial _

theorem foldl_push_size3 {X Y : Type} (l : List X) (F : E × E × Array Y → X → E × E × Array Y)
    (hF : ∀ acc x, (F acc x).2.2.size = acc.2.2.size + 1) :
    ∀ init, (l.foldl F init).2.2.size = init.2.2.size + l.length := by
  induction l with
  | nil => intro init; rfl
  | cons x l ih =>
    intro init
    rw [List.foldl_cons, ih, hF, List.length_cons]
    omega

theorem fold_openings_size3 {Y : Type} (combined : List (Commitment × Combined)) (values : List E)
    (F : E × E × Array Y → (Commitment × Combined) × E → E × E × Array Y)
    (hF : ∀ acc x, (F acc x).2.2.size = acc.2.2.size + 1) :
    ((combined.zip values).foldl F (0, 1, #[])).2.2.size ≤ combined.length := by
  rw [foldl_push_size3 _ F hF, List.length_zip]
  simp

/-- The batching sumcheck's tactic: its steps, then the openings' count. -/
macro "cc_batchK" : tactic => `(tactic| (
  unfold batchKH
  repeat cc_step
  all_goals
    refine cc_pure ?_ _
    simp only [Array.length_toList]
    refine fold_openings_size3 _ _ _ fun acc x ↦ ?_
    obtain ⟨s1, s2, os⟩ := acc
    obtain ⟨⟨c, claim⟩, v⟩ := x
    simp))

/-- The batch, plain rounds (the main line). -/
theorem cc_batchKH_main (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) :
    CC (batchKH callKeccak256 .main combined layouts ringMap) 2 0 fun z ↦ z.length ≤ combined.length := by
  cc_batchK

/-- The batch, plain rounds (π1-rec). -/
theorem cc_batchKH_rec1 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) :
    CC (batchKH callKeccak256 .rec1 combined layouts ringMap) 2 0 fun z ↦ z.length ≤ combined.length := by
  cc_batchK

/-- The batch, plain narrow rounds (π1-rec2), step by step (the tactic's search exceeds the heartbeat budget). -/
theorem cc_batchKH_rec2 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) :
    CC (batchKH callKeccak256 .rec2 combined layouts ringMap) 2 0 fun z ↦ z.length ≤ combined.length := by
  unfold batchKH
  dsimp only [FsShape.narrow]
  refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
  try dsimp only
  refine cc_free (cc_sumcheckDrawnH _ 3 (by norm_num) _ _) fun x _ ↦ ?_
  obtain ⟨r, last⟩ := x
  try dsimp only
  refine cc_free (cc_nextScalars _) fun values _ ↦ ?_
  try dsimp only
  refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  refine cc_pure ?_ _
  simp only [Array.length_toList]
  refine fold_openings_size3 _ _ _ fun acc x ↦ ?_
  obtain ⟨s1, s2, os⟩ := acc
  obtain ⟨⟨c, claim⟩, v⟩ := x
  simp

/-- The batch, paired rounds (π1-rec3). -/
theorem cc_batchKH_rec3 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) :
    CC (batchKH callKeccak256 .rec3 combined layouts ringMap) 2 0 fun z ↦ z.length ≤ combined.length := by
  cc_batchK

/-- **The batching sumcheck at any Fiat–Shamir shape**: `λ`, then rounds (paired or not) paid by their reads; at most
one opening per combined claim. -/
theorem cc_batchKH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    CC (batchKH callKeccak256 fs combined layouts ringMap) 2 0 fun z ↦ z.length ≤ combined.length := by
  cases fs
  · exact cc_batchKH_main combined layouts ringMap
  · exact cc_batchKH_rec1 combined layouts ringMap
  · exact cc_batchKH_rec2 combined layouts ringMap
  · exact cc_batchKH_rec3 combined layouts ringMap

/-- The walk's challenges, but the sumchecks' rounds: the two runs (`α ∈ E^4`, Flock's sampled coordinates), then
`β`, `γ`, Flock's `z`, its `α`, the ring map's six, `t`, `ρ`, `λ`, two blocks each. -/
def walkCost (shape : Shape) (v : UniKeccak.KeccakVariant) : ℕ :=
  drawCost v.fs 4 + drawCost v.fs (keccakR1csLogSize + shape.heights.getD opSha3 0 - v.skip - Flock.nFixed) + 26

/-- **The walk, point claims** (either variant): at most `walkCost` blocks beyond the potential, and at most three
openings. -/
theorem cc_reduceWithKH (shape : Shape) (publicWords : List E) (v : UniKeccak.KeccakVariant) :
    CC (reduceWithKH callKeccak256 shape publicWords v .point) (walkCost shape v) 0
      fun r ↦ r.openings.length ≤ 3 := by
  unfold reduceWithKH walkCost
  dsimp only
  split
  · exact cc_throw_bind _ _ _ _ _
  · refine cc_free (cc_countBits _) fun _ _ ↦ ?_
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq (cc_drawRunH _ _) (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq (cc_verifyWalkedKH _ _) (fun x _ ↦ ?_) (by omega)
    obtain ⟨point, end_⟩ := x
    dsimp only
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
    iterate 7 refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    rcases end_ with ⟨map, target⟩ | ⟨ws, value⟩ <;> dsimp only
    all_goals try split
    all_goals
      try dsimp only
      refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
      refine cc_seq (cc_batchKH _ _ _ _) (fun z hz ↦ ?_) (by omega)
      exact cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) (hz.trans (List.length_filterMap_le _ _)) _

end Parts

/-! ## The run, the openings, the deployed verifier -/

section Top

open E2ECompleteness.Cost (QC qc_pure)

theorem name_length : name.length = 16 := by decide +kernel

theorem ivTag_length : ivTag.length = 16 := by decide +kernel

theorem shapeBytes_length (s : Shape) : (shapeBytes s).length = 8 := by simp [shapeBytes]

theorem layoutWord_length (s : Shape) (code vars placed : ℕ) : (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, shapeBytes_length]

theorem layoutWordsK_length (s : Shape) : (UniKeccak.layoutWordsK s).flatten.length = 96 := by
  simp [UniKeccak.layoutWordsK, layoutWord_length]

theorem keccakTag_length : "keccak-vm".toUTF8.toList.length = 9 := by decide +kernel

theorem variantBytesK_length (v : UniKeccak.KeccakVariant) : (UniKeccak.variantBytesK v).length = 11 := by
  simp only [UniKeccak.variantBytesK, List.length_append, keccakTag_length, List.length_cons, List.length_nil]

theorem layoutWordVars_le (w : List UInt8) : layoutWordVars w ≤ 255 := by
  unfold layoutWordVars
  have := UInt8.toNat_lt (w.getD 24 0)
  omega

/-- Budget can only help a cost without postcondition. -/
theorem CostP.weaken {α : Type} {X : OracleComp KeccakCalls α} {n n' : ℕ} (hX : CostP X n fun _ _ ↦ True)
    (h : n ≤ n') : CostP X n' fun _ _ ↦ True := by
  have h' := costP_of_qc hX.toQC (n' - n)
  rw [show n + (n' - n) = n' by omega] at h'
  exact h'.mono fun _ _ _ ↦ trivial

/-- **The walk** from the start of a stream: the potential is three per byte. -/
theorem costP_walk (shape : Shape) (publicWords : List E) (v : UniKeccak.KeccakVariant) (seed : Digest)
    (stream : Array UInt8) (m : ℕ) :
    CostP ((do
        let r ← reduceWithKH callKeccak256 shape publicWords v .point
        finish (m := OracleComp KeccakCalls)
        return r : CM Reduced).run.run (Chan.start seed stream))
      (walkCost shape v + 3 * stream.size + m) fun z rem ↦
        ∀ a, z.1 = .ok a → a.openings.length ≤ 3 ∧ m ≤ rem := by
  have h := cc_mono (k' := walkCost shape v) (g' := 0)
    (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithKH shape publicWords v) fun r hr ↦
      cc_free cc_finish fun _ _ ↦ cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) hr 0) (by omega) le_rfl
    fun _ h ↦ h
  have h2 := h (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m
  rw [show walkCost shape v + pot (Chan.start seed stream) + m = walkCost shape v + 3 * stream.size + m
    by simp [pot, Chan.start]] at h2
  exact h2.mono fun z rem hz a ha ↦ ⟨(hz a ha).1, by have := (hz a ha).2.2; omega⟩

/-- **The run on calldata**: the seed, then the walk; at most three openings, `m` blocks left. -/
theorem costP_runWithKH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : UniKeccak.KeccakVariant) (m : ℕ) :
    CostP (runWithKH callKeccak256 shape iv publicInput stream v .point)
      ((16 + iv.length + publicInput.length) / 136 + 1 + (walkCost shape v + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → r.openings.length ≤ 3 ∧ m ≤ rem := by
  unfold runWithKH seedWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (name ++ iv ++ publicInput).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length]
    omega
  · rw [show (16 + iv.length + publicInput.length) / 136 + 1 + (walkCost shape v + 3 * stream.size + m) -
        hashBlocks (Sum.inl (name ++ iv ++ publicInput)) = walkCost shape v + 3 * stream.size + m by
      show _ - ((name ++ iv ++ publicInput).length / 136 + 1) = _
      simp only [List.length_append, name_length]
      omega]
    exact (costP_walk shape _ v seed stream m).bind fun z rem hz r hr ↦ hz r hr

/-- `PCS_OPEN`'s cost: a claim of at most `255` coordinates (`46` blocks of IV), then the opening's run. -/
def openCost : ℕ := 46 + E2ECompleteness.Cost.vOpen

theorem qc_pcsOpenWithH (vars : ℕ) (hv : vars ≤ 255) (root : Digest) (pt : List E) (value : E)
    (p : LeanVM.Protocol.Compile.Proof) :
    QC (pcsOpenWithH callKeccak256 callKeccakF1600 vars root [⟨pt, value⟩] p) openCost :=
  E2ECompleteness.Cost.cost_openingWithH (plainLayout vars) root _ p
    (by
      show vars - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * LeanVM.Protocol.Verifier.costHeight
      simp only [PcsQuotient.laneFold, PcsQuotient.logInvRate, LeanVM.Protocol.Verifier.costHeight]
      omega) 46
    (by
      show 76 + 24 * (1 * (vars + 1)) < 136 * 46
      omega)

theorem qc_forIn_list {γ β : Type} (l : List γ) (b : β) (f : γ → β → OracleComp KeccakCalls (ForInStep β))
    {c : ℕ} (hf : ∀ a s, QC (f a s) c) : QC (forIn l b f) (l.length * c) := by
  induction l generalizing b with
  | nil => exact qc_pure _ _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind_le (b := l.length * c) (fun s ↦ ?_) (by simp [Nat.succ_mul]; omega)
    cases s with
    | done b => exact qc_pure _ _
    | yield b => exact ih b

/-- **The verifier**: the run, then at most three openings. -/
theorem costP_verifyWithKH (shape : Shape) (v : UniKeccak.KeccakVariant) (iv : List UInt8) (roots : SetupRoots)
    (publicInput : Vector UInt8 32) (proof : UniKeccak.KeccakProof) :
    CostP (verifyWithKH callKeccak256 callKeccakF1600 shape v iv roots publicInput proof)
      ((16 + iv.length + 32) / 136 + 1 + (walkCost shape v + 3 * proof.stream.size + 3 * openCost))
      fun _ _ ↦ True := by
  unfold verifyWithKH
  rw [show 16 + iv.length + 32 = 16 + iv.length + publicInput.toList.length by simp]
  refine CostP.bind (costP_runWithKH shape iv publicInput.toList proof.stream v (3 * openCost))
    fun o rem ho ↦ ?_
  split
  · trivial
  · split
    · trivial
    · rename_i r hr
      obtain ⟨hl, hrem⟩ := ho r hr
      refine CostP.weaken (n := 3 * openCost + 0) ((costP_of_qc ?_ 0).mono fun _ _ _ ↦ trivial) (by omega)
      refine (qc_forIn_list (c := openCost) _ _ _ fun x s ↦ ?_).bind_le (b := 0) (fun s ↦ ?_) ?_
      · split
        split
        · exact (qc_pcsOpenWithH _ (layoutWordVars_le _) _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
        · exact qc_pure _ _
      · split <;> exact qc_pure _ _
      · have : r.openings.length * openCost ≤ 3 * openCost := Nat.mul_le_mul_right _ hl
        omega

/-- The Keccak contract's IV: the tag, the program's IV, the setup's root, the shape, the three Keccak layout words
and the variant's eleven bytes. -/
def ivCost (D : UniKeccak.KDeployment) : ℕ := (163 + D.programIv.length) / 136 + 1

/-- **The deployed Keccak verifier's block count** on a proof of a stream of at most `S` bytes: the IV, the seed (one
block), the walk, three per stream byte, the three openings. -/
def verifierCost (D : UniKeccak.KDeployment) (v : UniKeccak.KeccakVariant) (S : ℕ) : ℕ :=
  ivCost D + 1 + walkCost D.shape v + 3 * S + 3 * openCost

theorem ivInput_length (s : Shape) (v : UniKeccak.KeccakVariant) (programIv : List UInt8) (roots : SetupRoots) :
    (ivTag ++ programIv ++ digestBytes roots.bytecode ++
      shapeBytes s ++ (UniKeccak.layoutWordsK s).flatten ++ UniKeccak.variantBytesK v).length =
      163 + programIv.length := by
  simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWordsK_length,
    variantBytesK_length]
  omega

/-- **The deployed Keccak verifier over the two calls makes at most `verifierCost D v S` block calls** on any proof
whose stream has at most `S` bytes, whatever its opening proofs, for either variant (`keccakMain`, `keccakRec3`; any
variant). -/
theorem cost_verifierWithH (D : UniKeccak.KDeployment) (v : UniKeccak.KeccakVariant) (roots : SetupRoots)
    (input : Vector UInt8 32) (proof : UniKeccak.KeccakProof) (S : ℕ) (hS : proof.stream.size ≤ S) :
    Common.QueryCostAtMost (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D v roots input proof)
      hashBlocks (verifierCost D v S) := by
  refine CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold KDeployment.verifierWithH KDeployment.ivWithH contractIvKWithH callKeccak256
  rw [bind_assoc, costP_query_bind]
  refine ⟨?_, fun d ↦ ?_⟩
  · show (ivTag ++ D.programIv ++ digestBytes roots.bytecode ++
      shapeBytes D.shape ++ (UniKeccak.layoutWordsK D.shape).flatten ++
      UniKeccak.variantBytesK v).length / 136 + 1 ≤ _
    rw [ivInput_length]
    unfold verifierCost ivCost
    omega
  · rw [pure_bind]
    refine (costP_verifyWithKH D.shape v (digestBytes d) roots input proof).weaken ?_
    show _ ≤ verifierCost D v S - ((ivTag ++ D.programIv ++ digestBytes roots.bytecode ++
      shapeBytes D.shape ++ (UniKeccak.layoutWordsK D.shape).flatten ++
      UniKeccak.variantBytesK v).length / 136 + 1)
    rw [ivInput_length, len_digestBytes]
    unfold verifierCost ivCost
    omega

/-- The setup's block count: the setup stack's tree (`5 · 2^(μ − 5)` blocks). -/
def setupCost (D : UniKeccak.KDeployment) : ℕ := 5 * 2 ^ ((setupLayout D.shape).vars - 6 + 1)

/-- **The setup over the two calls makes at most `setupCost D` block calls.** -/
theorem cost_setupTreeKWithH (D : UniKeccak.KDeployment) :
    Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks (setupCost D) :=
  E2ECompleteness.Cost.qc_commitWithH _ _

theorem openCost_le : openCost ≤ 121492 := by
  unfold openCost E2ECompleteness.Cost.vOpen LeanVM.Protocol.Verifier.whirBound
  norm_num

/-- **The main line's verifier** (`cost_verifierWithH` at `keccakMain`). -/
theorem cost_verifierWithH_main (D : UniKeccak.KDeployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) (S : ℕ) (hS : proof.stream.size ≤ S) :
    Common.QueryCostAtMost
      (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D UniKeccak.keccakMain roots input proof)
      hashBlocks (verifierCost D UniKeccak.keccakMain S) :=
  cost_verifierWithH D _ roots input proof S hS

/-- **π1-rec3's verifier** (`cost_verifierWithH` at `keccakRec3`). -/
theorem cost_verifierWithH_rec3 (D : UniKeccak.KDeployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) (S : ℕ) (hS : proof.stream.size ≤ S) :
    Common.QueryCostAtMost
      (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D UniKeccak.keccakRec3 roots input proof)
      hashBlocks (verifierCost D UniKeccak.keccakRec3 S) :=
  cost_verifierWithH D _ roots input proof S hS

/-- `walkCost` at the main line: two per sampled coordinate. -/
theorem walkCost_main (shape : Shape) :
    walkCost shape UniKeccak.keccakMain = 8 + 2 * (17 + shape.heights.getD opSha3 0 - 3 - 7) + 26 := rfl

/-- `walkCost` at π1-rec3: `30`, whatever the shape. -/
theorem walkCost_rec3 (shape : Shape) : walkCost shape UniKeccak.keccakRec3 = 30 := rfl

end Top

end UniKeccakComplete.Cost

/-- info: 'UniKeccakComplete.Cost.cost_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Cost.cost_verifierWithH

/-- info: 'UniKeccakComplete.Cost.cost_setupTreeKWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Cost.cost_setupTreeKWithH
