-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the prover's opening
-- (`cost_proveOpeningWithH`, `blockFactor`) and of a commitment (`qc_commitWithH`, `treeCost`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/ProverCost.lean`.
import UniKeccakComplete.K.ProverDuplex
import UniKeccakComplete.K.ProverBounds
import UniKeccakComplete.K.VerifierHCost
import UniKeccakComplete.K.Reference

/-!
# The block count of the Keccak VM's honest prover (main line), and the size of its stream

**`cost_uniProverWith`**: the deployed honest prover over the two calls makes at most `proverBlocks D rows k w`
block calls (`hashBlocks`: a Keccak-256 of `n` bytes `⌊n / 136⌋ + 1`, a Keccak-f[1600] one), and
**`costP_uniProverWith`**: every proof it returns has a stream of at most `proverStream D rows w` bytes, the bound
`cost_verifierWithH` takes. Both explicit from the shape; Flock's prover is a parameter and the facts used of it are
named, **`FlockCost flock k w`** (at `log_n` and a Keccak variant: at most `k` blocks beyond one per byte it writes,
at most `w` bytes).

* **The writer's calculus** (`WC x k w P`): from any writer's state, at most `k` blocks beyond one per byte written
  and the potential (`wpot`: the bytes written, not yet hashed), at most `w` bytes written, each outcome satisfying
  `P` with its final state. A challenge costs one block beyond the bytes it hashes (`wc_sampleW`: `⌊(32 + n)/136⌋ + 1
  ≤ 1 + n`), a write of `n` bytes is paid by its `n` (`wc_sendBytes`), a commitment is its tree (`wc_lift`).
* **The stream** (`wc_proveStreamWith`): `streamBlocks` (`C1`'s and `C2`'s trees, the challenges `α ∈ E^4`, `β`, `γ`,
  `t`, `ρ`, `λ`, one per batching round, at most `batchVarsBound` of them, Flock's) beyond `streamBytes` bytes (the
  row counts, the roots, Flock's, at most `valuesBound` values at `t`, two scalars per round, the claims' three
  values; no matrices); its point claims have at most `batchVarsBound` coordinates (`StreamOK`). The sizes are
  `ProverBounds`'.
* **The prover** (`costP_proveWith`, `uniProverCost`): the setup's one tree, the Keccak contract's IV (`163` bytes and
  the program IV), the seed (`80` bytes, one block), the stream, three openings (`openP`, E2ECompleteness's
  `cost_proveOpeningWithH`: WHIR's prover at `nonceFuel = 2^25` nonces a proof of work, at its fixed height, whatever
  the stack's size).
* **At the reference shape** (`UniKeccakSound.keccakRefShape`: memory `2^20`, bytecode `2^18`, heights 15 16 15 16
  14 15; `log_n = 32` for Flock): the stacks have `27`, `26`, `23` variables (`Reference.lean`'s `reference_vars`),
  the batch `27` rounds (`reference_batchVars`); the prover makes at most `2^47` block calls
  (`proverBlocks_reference`; nearly all the three WHIR provers', `3 · 40481 · (14 · 2^26 + 2) ≈ 2^46.7`), for
  Flock's prover within `2^32` blocks and `2^32` bytes, a program IV of `2^16` bytes; the stream has at most
  `proverStream_reference` bytes beyond Flock's.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement

namespace UniKeccakComplete.Cost

open UniComplete

open E2ECompleteness.Cost (QC qc_pure qc_H_le qc_commitWithH treeCost)
open Bounds (batchVarsBound valuesBound)

/-! ## Wire lengths -/

theorem length_be64 (w : UInt64) : (be64 w).length = 8 := by simp [be64]

theorem length_scalarWire (x : E) : (scalarWire x).length = 24 := by simp [scalarWire, length_be64]

theorem length_flatMap_scalarWire : ∀ xs : List E, (xs.flatMap scalarWire).length = 24 * xs.length
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, length_scalarWire, length_flatMap_scalarWire xs, List.length_cons]
    ring

theorem length_integerWire (n bytes : ℕ) : (integerWire n bytes).length = bytes := by simp [integerWire]

theorem length_rootWord (h : E × E) : (rootWord h).length = 32 := by simp [rootWord, length_be64]

/-! ## Costs with a postcondition, on the result alone -/

section CostP

variable {α β : Type}

theorem CostP.mono_budget {X : OracleComp KeccakCalls α} {n n' : ℕ} {P : α → Prop}
    (h : CostP X n fun a _ ↦ P a) (hn : n ≤ n') : CostP X n' fun a _ ↦ P a := by
  induction X using OracleComp.inductionOn generalizing n n' with
  | pure a => exact h
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun u ↦ ih u (h.2 u) (by omega)⟩

theorem costP_bind_qc {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {a b : ℕ}
    {P : β → Prop} (hX : QC X a) (hf : ∀ x, CostP (f x) b fun y _ ↦ P y) :
    CostP (X >>= f) (a + b) fun y _ ↦ P y :=
  CostP.bind (costP_of_qc hX b) fun x _ hr ↦ (hf x).mono_budget hr

end CostP

/-! ## The writer's calculus -/

/-- **The potential**: the bytes written and not yet hashed. -/
def wpot (c : Wr) : ℕ := c.stream.size - c.absorbed

/-- The writer's invariant. -/
def WInv (c : Wr) : Prop := c.absorbed ≤ c.stream.size

/-- **`x` makes at most `k` block calls beyond one per byte it writes, writing at most `w` bytes**: from any state
satisfying the invariant, with any extra budget `e`, at most `k + w` blocks beyond the potential; each outcome
satisfies `P` with its final state, which has grown by at most `w` bytes, its potential and `e` left. -/
def WC {α : Type} (x : PM α) (k w : ℕ) (P : α → Wr → Prop) : Prop :=
  ∀ c, WInv c → ∀ e, CostP (x.run c) (k + w + wpot c + e) fun z rem ↦
    P z.1 z.2 ∧ WInv z.2 ∧ c.stream.size ≤ z.2.stream.size ∧ z.2.stream.size ≤ c.stream.size + w ∧
      wpot z.2 + e ≤ rem

section Calculus

variable {α β : Type}

theorem wc_bind {x : PM α} {f : α → PM β} {k₁ w₁ k₂ w₂ : ℕ} {P : α → Wr → Prop} {Q : β → Wr → Prop}
    (hx : WC x k₁ w₁ P) (hf : ∀ a s, P a s → WC (f a) k₂ w₂ Q) : WC (x >>= f) (k₁ + k₂) (w₁ + w₂) Q := by
  intro c hc e
  rw [StateT.run_bind]
  have h1 := hx c hc (k₂ + w₂ + e)
  rw [show k₁ + w₁ + wpot c + (k₂ + w₂ + e) = k₁ + k₂ + (w₁ + w₂) + wpot c + e by omega] at h1
  refine CostP.bind h1 fun z rem hz ↦ ?_
  obtain ⟨hP, hI, hs1, hs2, hrem⟩ := hz
  have h2 := hf z.1 z.2 hP z.2 hI (rem - k₂ - w₂ - wpot z.2)
  rw [show k₂ + w₂ + wpot z.2 + (rem - k₂ - w₂ - wpot z.2) = rem by omega] at h2
  exact h2.mono fun z' rem' h ↦ ⟨h.1, h.2.1, by omega, by omega, by omega⟩

theorem wc_mono {x : PM α} {k w k' w' : ℕ} {P P' : α → Wr → Prop} (h : WC x k w P) (hk : k ≤ k') (hw : w ≤ w')
    (hP : ∀ a s, P a s → P' a s) : WC x k' w' P' := by
  intro c hc e
  have h1 := h c hc (e + (k' - k) + (w' - w))
  rw [show k + w + wpot c + (e + (k' - k) + (w' - w)) = k' + w' + wpot c + e by omega] at h1
  exact h1.mono fun z rem h ↦ ⟨hP _ _ h.1, h.2.1, h.2.2.1, by omega, by omega⟩

/-- A step paid from the budget, then the rest from what is left. -/
theorem wc_seq {x : PM α} {f : α → PM β} {k₁ w₁ k w : ℕ} {P : α → Wr → Prop} {Q : β → Wr → Prop}
    (hx : WC x k₁ w₁ P) (hf : ∀ a s, P a s → WC (f a) (k - k₁) (w - w₁) Q) (hk : k₁ ≤ k) (hw : w₁ ≤ w) :
    WC (x >>= f) k w Q :=
  wc_mono (wc_bind hx hf) (by omega) (by omega) fun _ _ h ↦ h

theorem wc_pure (a : α) : WC (pure a : PM α) 0 0 fun b _ ↦ b = a :=
  fun c hc e ↦ ⟨rfl, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

/-- A result read off the state. -/
theorem wc_get_pure (F : Wr → α) (P : α → Wr → Prop) (h : ∀ s, P (F s) s) :
    WC ((get : PM Wr) >>= fun s ↦ pure (F s)) 0 0 P :=
  fun c hc e ↦ ⟨h c, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

theorem wc_map {x : PM α} {k w : ℕ} {P : α → Wr → Prop} (f : α → β) (hx : WC x k w P) :
    WC (f <$> x) k w fun b s ↦ ∃ a, b = f a ∧ P a s := by
  intro c hc e
  rw [StateT.run_map, map_eq_bind_pure_comp]
  exact CostP.bind (hx c hc e) fun z rem h ↦ ⟨⟨z.1, rfl, h.1⟩, h.2⟩

theorem wc_sendBytes (b : List UInt8) :
    WC (sendBytes (m := OracleComp KeccakCalls) b) 0 b.length fun _ _ ↦ True := by
  intro c hc e
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;>
    simp only [WInv, wpot, Array.size_append, List.size_toArray] at hc ⊢ <;> omega

theorem wc_sendScalar (x : E) : WC (sendScalar (m := OracleComp KeccakCalls) x) 0 24 fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_scalarWire]) fun _ _ h ↦ h

theorem wc_sendScalars (xs : List E) :
    WC (sendScalars (m := OracleComp KeccakCalls) xs) 0 (24 * xs.length) fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_flatMap_scalarWire]) fun _ _ h ↦ h

theorem wc_sendInteger (n bytes : ℕ) :
    WC (sendInteger (m := OracleComp KeccakCalls) n bytes) 0 bytes fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_integerWire]) fun _ _ h ↦ h

theorem wc_sendRoot (halves : E × E) : WC (sendRoot (m := OracleComp KeccakCalls) halves) 0 32 fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_rootWord]) fun _ _ h ↦ h

/-- **A challenge** costs at most one block beyond the bytes it hashes, which the potential holds. -/
theorem wc_sampleW : WC (sampleW callKeccak256) 1 0 fun _ _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨trivial, ?_, ?_, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1 ≤
      1 + 0 + wpot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show c.stream.size ≤ c.stream.size
    exact le_rfl
  · exact le_rfl
  · show c.stream.size ≤ c.stream.size + 0
    omega
  · show c.stream.size - c.stream.size + e ≤ 1 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega

/-- A lifted computation of the two calls: its blocks, no write. -/
theorem wc_lift {X : OracleComp KeccakCalls α} {n : ℕ} (hX : QC X n) :
    WC (StateT.lift X : PM α) n 0 fun _ _ ↦ True := by
  intro c hc e
  rw [StateT.run_lift]
  have h := costP_of_qc hX (wpot c + e)
  rw [show n + (wpot c + e) = n + 0 + wpot c + e by omega] at h
  exact CostP.bind h fun a rem hr ↦ ⟨trivial, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

/-- **A loop** of steps of cost `(k, w)`. -/
theorem wc_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → PM (ForInStep β)) {k w : ℕ}
    (hf : ∀ a s, WC (f a s) k w fun _ _ ↦ True) :
    WC (forIn l b f) (l.length * k) (l.length * w) fun _ _ ↦ True := by
  induction l generalizing b with
  | nil => exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  | cons a l ih =>
    rw [List.forIn_cons]
    refine wc_mono (wc_bind (k₂ := l.length * k) (w₂ := l.length * w) (Q := fun _ _ ↦ True) (hf a b)
      fun s _ _ ↦ ?_) (by rw [List.length_cons, Nat.succ_mul]; omega)
      (by rw [List.length_cons, Nat.succ_mul]; omega) fun _ _ h ↦ h
    cases s with
    | done b => exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
    | yield b => exact ih b

/-- **A loop whose steps yield**, with an invariant counting them. -/
theorem wc_forIn_yield {γ : Type} (l : List γ) (g : γ → β → PM β) {k w : ℕ} (I : ℕ → β → Prop)
    (hg : ∀ i a s, I i s → WC (g a s) k w fun s' _ ↦ I (i + 1) s') :
    ∀ (b : β) (i : ℕ), I i b →
      WC (forIn l b fun a s ↦ g a s >>= fun s' ↦ pure (ForInStep.yield s')) (l.length * k) (l.length * w)
        fun r _ ↦ I (i + l.length) r := by
  induction l with
  | nil => intro b i h; exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ hb ↦ by rw [hb]; exact h
  | cons a l ih =>
    intro b i h
    rw [List.forIn_cons, bind_assoc]
    simp only [pure_bind]
    refine wc_mono (wc_bind (hg i a b h) fun s' _ hs' ↦ ih s' (i + 1) hs')
      (by rw [List.length_cons, Nat.succ_mul]; omega) (by rw [List.length_cons, Nat.succ_mul]; omega)
      fun r _ hr ↦ ?_
    rw [List.length_cons, show i + (l.length + 1) = i + 1 + l.length by omega]
    exact hr

theorem wc_samplesW : ∀ count : ℕ, WC (samplesW callKeccak256 count) count 0 fun _ _ ↦ True
  | 0 => wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial
  | count + 1 => by
    unfold samplesW
    exact wc_seq wc_sampleW (fun _ _ _ ↦ wc_seq (wc_samplesW count) (fun _ _ _ ↦
      wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial) (by omega) le_rfl)
      (by omega) (Nat.zero_le _)

/-- **A round of the batching sumcheck**: two scalars, a challenge; the point grows by one. -/
theorem wc_batchRound (lambda : E) (j : ℕ) (st : BatchState) :
    WC (batchRound callKeccak256 lambda j st) 1 48 fun st' _ ↦ st'.point.length = st.point.length + 1 := by
  unfold batchRound
  exact wc_seq (wc_sendScalar _) (fun _ _ _ ↦ wc_seq (wc_sendScalar _) (fun _ _ _ ↦ wc_seq wc_sampleW
    (fun r _ _ ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by rw [hb]; simp)
    (by omega) (Nat.zero_le _)) (Nat.zero_le _) (by omega)) (Nat.zero_le _) (by omega)

/-- **The batching sumcheck's rounds**: `vars` rounds; the point grows by `vars`. -/
theorem wc_batchRounds (lambda : E) (vars : ℕ) (st : BatchState) :
    WC (batchRounds callKeccak256 lambda vars st) vars (48 * vars) fun r _ ↦ r.length = st.point.length + vars := by
  unfold batchRounds
  have h := wc_forIn_yield (List.range vars) (fun j s ↦ batchRound callKeccak256 lambda j s)
    (fun i s ↦ s.point.length = st.point.length + i)
    (fun i a s hs ↦ wc_mono (wc_batchRound lambda a s) le_rfl le_rfl fun s' _ h ↦ by rw [h, hs]; omega) st 0
    (by simp)
  rw [List.length_range] at h
  exact wc_seq h (fun r _ hr ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by
    rw [hb, hr]; omega) (by omega) (by omega)

end Calculus

/-! ## The stream -/

theorem qc_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    QC (commitReal callKeccak256 c vars stack) (treeCost vars) :=
  (qc_commitWithH vars stack).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

/-- **What the openings and the verifier need of the stream**: its bytes are the writer's; its point claims have
at most `V` coordinates. -/
def StreamOK (V : ℕ) (out : CoreOut) (s : Wr) : Prop :=
  out.stream = s.stream ∧ ∀ x ∈ out.claims, x.2.1.length ≤ V

/-- **The stream's blocks beyond its bytes**: `C1`'s and `C2`'s trees, the challenges (`α ∈ E^4`, `β`, `γ`, `t`,
`ρ`, `λ`, one per batching round), Flock's. -/
def streamBlocks (shape : Shape) (kF : ℕ) : ℕ :=
  treeCost (UniKeccak.c1LayoutK shape).vars + 6 + kF +
    treeCost (((UniKeccak.layoutsOfK shape).lookup .c2).getD default).vars + 3 + batchVarsBound shape

/-- **The stream's bytes**: the row counts, the two roots, Flock's, the values at `t`, the batching rounds' two
scalars each, the three claims' values. -/
def streamBytes (shape : Shape) (rows wF : ℕ) : ℕ :=
  4 * rows + 64 + wF + 24 * valuesBound + 48 * batchVarsBound shape + 72

theorem length_combined (f : Commitment → Option (Commitment × Combined)) :
    (commitments.filterMap f).length ≤ 3 :=
  (List.length_filterMap_le _ _).trans (by decide)

theorem length_claims {α : Type} (f : Commitment → Option (Commitment × Combined)) (g : Commitment × Combined → α)
    (h : α → E) : 24 * (((commitments.filterMap f).map g).map h).length ≤ 72 := by
  simp only [List.length_map]
  have := length_combined f
  omega

/-- **The stream's cost** (the main line), given Flock's prover's at its `log_n`. -/
theorem wc_proveStreamWith (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (tr : Trace)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakMain tr.qflock) kF wF
      fun _ _ ↦ True) :
    WC (proveStreamWith callKeccak256 (commitReal callKeccak256) flock tr)
      (streamBlocks tr.shape kF) (streamBytes tr.shape tr.rows.length wF) (StreamOK (batchVarsBound tr.shape)) := by
  unfold proveStreamWith streamBlocks streamBytes
  refine wc_seq (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_samplesW 4) (fun alphas _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun beta _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun gamma _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_map some hF) (fun flockOut _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun t _ _ ↦ ?_) (by omega) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun rho _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun lambda _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_batchRounds _ _ _) hvars (Nat.mul_le_mul_left 48 hvars) fun r _ h ↦ h)
    (fun r _ hr ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

/-! ## The prover -/

section Prover

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)

/-- **The prover's opening's blocks**, a claim of at most `v` coordinates: its IV, its seed's permutation, the
root's two absorptions, WHIR's prover at its fixed height (E2ECompleteness's `cost_proveOpeningWithH`). -/
def openP (fuel v : ℕ) : ℕ := (76 + 24 * (v + 1)) / 136 + 1 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel

theorem qc_proveOpening1 (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
    (pt : List E) (value : E) {v : ℕ} (hv : pt.length ≤ v) :
    QC (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack [⟨pt, value⟩])
      (openP fuel v) :=
  E2ECompleteness.Cost.cost_proveOpeningWithH fuel L tree stack _ v _
    (fun c hc ↦ by
      simp only [List.mem_singleton] at hc
      subst hc
      exact hv)
    (by simp only [List.length_singleton, Nat.one_mul]; omega)

/-- A step of cost `a`, then the rest from what is left. -/
theorem costP_seq_qc {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {a n : ℕ}
    {P : β → Prop} (hX : QC X a) (hf : ∀ x, CostP (f x) (n - a) fun y _ ↦ P y) (h : a ≤ n) :
    CostP (X >>= f) n fun y _ ↦ P y := by
  have := costP_bind_qc hX hf
  rw [show a + (n - a) = n by omega] at this
  exact this

theorem qc_setupTreeOf (tr : Trace) : QC (setupTreeOf callKeccak256 tr) (treeCost (setupLayout tr.shape).vars) :=
  qc_commitWithH _ _

/-- The proof's stream, if a proof is returned. -/
theorem stream_of_some {s : Array UInt8} {p1 p2 p3 : Option LeanVM.Protocol.Compile.Proof}
    {p : UniKeccak.KeccakProof}
    (h : (do
      let c1 ← p1
      let c2 ← p2
      let c3 ← p3
      pure ⟨s, c1, c2, c3⟩ : Option UniKeccak.KeccakProof) = some p) : p.stream = s := by
  revert h
  cases p1 <;> cases p2 <;> cases p3 <;> simp
  rintro rfl
  rfl

/-- **The honest prover's blocks**: the setup's tree, the IV, the seed, the stream (its blocks and its bytes),
three openings of claims of at most `batchVarsBound` coordinates. -/
def uniProverCost (shape : Shape) (programIvLen rows kF wF : ℕ) : ℕ :=
  treeCost (setupLayout shape).vars + ((163 + programIvLen) / 136 + 1) + 1 +
    (streamBlocks shape kF + streamBytes shape rows wF) + 3 * openP PcsQuotient.nonceFuel (batchVarsBound shape)

set_option hygiene false in
/-- One step of the three openings' walk (`hc`, `h1` … `h3` the local facts on the claims, `hS` on the stream). -/
macro "open_step" : tactic => `(tactic| first
  | exact fun p hp ↦ by rw [stream_of_some hp]; exact hS
  | refine costP_seq_qc (qc_proveOpening1 _ _ _ _ _ _ (v := batchVarsBound tr.shape) (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3))) (fun _ ↦ ?_) (by omega))

/-- **The honest prover's block count** (the main line), given Flock's prover's at its `log_n`: and every proof it
returns has a stream of at most `streamBytes` bytes. -/
theorem costP_proveWith (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ)
    (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakMain tr.qflock) kF wF
      fun _ _ ↦ True) :
    CostP (proveWith callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock programIv tr)
      (uniProverCost tr.shape programIv.length tr.rows.length kF wF)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes tr.shape tr.rows.length wF := by
  unfold proveWith contractIvOf seedOf
  simp only [bind_assoc, pure_bind]
  refine costP_seq_qc (qc_setupTreeOf tr) (fun tree ↦ ?_) (by unfold uniProverCost; omega)
  refine costP_seq_qc (qc_H_le (k := (163 + programIv.length) / 136 + 1) (by
    simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWordsK_length,
      variantBytesK_length]
    omega))
    (fun d ↦ ?_) (by unfold uniProverCost; omega)
  refine costP_seq_qc (qc_H_le (k := 1) (by
    simp only [List.length_append, name_length, len_digestBytes, hpub]; omega)) (fun seed ↦ ?_)
    (by unfold uniProverCost; omega)
  have hW := wc_proveStreamWith flock kF wF tr hF (Wr.start seed) (by simp [WInv, Wr.start])
    (uniProverCost tr.shape programIv.length tr.rows.length kF wF -
      treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
      (streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF))
  rw [show streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF + wpot (Wr.start seed) +
      (uniProverCost tr.shape programIv.length tr.rows.length kF wF -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
        (streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF)) =
      uniProverCost tr.shape programIv.length tr.rows.length kF wF -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1
      by simp only [wpot, Wr.start, Array.size_empty]; unfold uniProverCost; omega] at hW
  refine CostP.bind hW fun z rem hz ↦ ?_
  obtain ⟨⟨hstream, hc0⟩, -, -, hsize, hrem⟩ := hz
  have hS : z.1.stream.size ≤ streamBytes tr.shape tr.rows.length wF := by
    rw [hstream]
    simpa [Wr.start] using hsize
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  refine CostP.mono_budget (n := 3 * openP PcsQuotient.nonceFuel (batchVarsBound tr.shape)) ?_
    (by unfold uniProverCost at hrem; omega)
  obtain ⟨out, _⟩ := z
  dsimp only at hS hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat open_step

end Prover

/-! ## The deployed honest prover -/

section Deployed

/-- **Flock's prover's cost** (`FlockCost flock k w`): over the two calls, at `log_n` and a Keccak variant, from any
writer's state, it makes at most `k logN v` block calls beyond one per byte it writes (each challenge one, the bytes
it hashes paid by the writes, `wc_sampleW`) and writes at most `w logN v` bytes. A prover built from `sampleW`,
`sendBytes` and pure code proves it with this file's calculus (`wc_seq`, `wc_sampleW`, `wc_sendScalar`, …). -/
def FlockCost (flock : FlockProverH) (k w : ℕ → UniKeccak.KeccakVariant → ℕ) : Prop :=
  ∀ logN v words, WC (flock callKeccak256 logN v words) (k logN v) (w logN v) fun _ _ ↦ True

/-- Flock's `log_n` at a shape: the Keccak-f block's `17` and `SHA3`'s height. -/
abbrev flockLogN (shape : Shape) : ℕ := keccakR1csLogSize + shape.heights.getD opSha3 0

/-- **The deployed honest prover's block count**, at `rows` row counts, Flock's prover's costs `k`, `w`. -/
def proverBlocks (D : UniKeccak.KDeployment) (rows : ℕ) (k w : ℕ → UniKeccak.KeccakVariant → ℕ) : ℕ :=
  uniProverCost D.shape D.programIv.length rows (k (flockLogN D.shape) UniKeccak.keccakMain)
    (w (flockLogN D.shape) UniKeccak.keccakMain)

/-- **The honest stream's bytes**, at most. -/
def proverStream (D : UniKeccak.KDeployment) (rows : ℕ) (w : ℕ → UniKeccak.KeccakVariant → ℕ) : ℕ :=
  streamBytes D.shape rows (w (flockLogN D.shape) UniKeccak.keccakMain)

/-- **The deployed honest prover over the two calls makes at most `proverBlocks` block calls, and every proof it
returns has a stream of at most `proverStream` bytes**, given Flock's prover's cost. -/
theorem costP_uniProverWith (flock : FlockProverH) (k w : ℕ → UniKeccak.KeccakVariant → ℕ) (hF : FlockCost flock k w)
    (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    CostP (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      (proverBlocks D rows.length k w)
      fun o _ ↦ ∀ proof, o = some proof → proof.stream.size ≤ proverStream D rows.length w :=
  costP_proveWith (flock callKeccak256) _ _ D.programIv (honestTrace D input rows q)
    (by simp [honestTrace]) (hF _ _ _)

/-- **The deployed honest prover over the two calls makes at most `proverBlocks` block calls.** -/
theorem cost_uniProverWith (flock : FlockProverH) (k w : ℕ → UniKeccak.KeccakVariant → ℕ) (hF : FlockCost flock k w)
    (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Common.QueryCostAtMost (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (proverBlocks D rows.length k w) :=
  (costP_uniProverWith flock k w hF D input rows q).toQC

/-- **A cost with a postcondition on the result holds on the support.** -/
theorem CostP.mem_support {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {P : α → Prop}
    (h : CostP X n fun a _ ↦ P a) : ∀ a ∈ support X, P a := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a =>
    intro b hb
    rw [support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact h
  | query_bind t k ih =>
    intro b hb
    rw [costP_query_bind] at h
    rw [mem_support_bind_iff] at hb
    obtain ⟨u, -, hu⟩ := hb
    exact ih u (h.2 u) b hu

end Deployed

/-! ## At the reference shape -/

section Reference

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)
open UniKeccakSound (keccakRefShape)

theorem treeCost_mono {a b : ℕ} (h : a ≤ b) : treeCost a ≤ treeCost b := by
  unfold treeCost
  exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem openP_mono (fuel : ℕ) {a b : ℕ} (h : a ≤ b) : openP fuel a ≤ openP fuel b := by
  unfold openP
  have : (76 + 24 * (a + 1)) / 136 ≤ (76 + 24 * (b + 1)) / 136 := Nat.div_le_div_right (by omega)
  omega

theorem valuesBound_eq : valuesBound = 173 := by decide +kernel

theorem reference_flockLogN : flockLogN keccakRefShape = 32 := by decide +kernel

theorem reference_sha3Height : keccakRefShape.heights.getD opSha3 0 = 15 := by decide +kernel

theorem c1LayoutK_eq (s : Shape) : UniKeccak.c1LayoutK s = StackLayout.new (c1Columns s) := rfl

theorem c2LayoutK_eq (s : Shape) :
    ((UniKeccak.layoutsOfK s).lookup .c2).getD default = StackLayout.new (UniKeccak.Shape.c2ColumnsK s) := rfl

theorem setupLayout_eq (s : Shape) : setupLayout s = StackLayout.new (setupColumns s) := rfl

/-- **At the reference shape, the stacks have `27`, `26`, `23` variables and the batching sumcheck `27` rounds**
(`Reference.lean`'s `reference_vars`). -/
theorem reference_stackVars : (UniKeccak.c1LayoutK keccakRefShape).vars = 27 ∧
    (((UniKeccak.layoutsOfK keccakRefShape).lookup .c2).getD default).vars = 26 ∧
    (setupLayout keccakRefShape).vars = 23 ∧ batchVarsBound keccakRefShape = 27 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c1LayoutK_eq]
    exact reference_c1Vars
  · rw [c2LayoutK_eq]
    exact reference_c2Vars
  · rw [setupLayout_eq]
    exact reference_setupVars
  · unfold batchVarsBound
    rw [reference_vars]
    rfl

/-- **The honest prover's blocks at the reference shape: at most `2^47`**, for six row counts, a program IV of at
most `2^16` bytes, Flock's prover at `log_n = 32` of at most `2^32` blocks beyond its bytes and `2^32` bytes. (Nearly
all of it the three WHIR provers': `3 · 40481 · (14 · 2^26 + 2) ≈ 2^46.7`.) -/
theorem proverBlocks_reference (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) (k w : ℕ → UniKeccak.KeccakVariant → ℕ)
    (hk : k 32 UniKeccak.keccakMain ≤ 2 ^ 32) (hw : w 32 UniKeccak.keccakMain ≤ 2 ^ 32) :
    proverBlocks D 6 k w ≤ 2 ^ 47 := by
  obtain ⟨h1, h2, h3, h4⟩ := reference_stackVars
  unfold proverBlocks uniProverCost streamBlocks streamBytes
  rw [hD, reference_flockLogN, h1, h2, h3, h4]
  rw [valuesBound_eq]
  unfold openP
  norm_num [treeCost, blockFactor, whirBound, costHeight, PcsQuotient.nonceFuel]
  omega

/-- **The honest stream at the reference shape**: the six row counts (`24`), the two roots (`64`), the values at `t`,
`27` batching rounds (`48` bytes each), the claims' three values: `5608` bytes, and Flock's. -/
theorem proverStream_reference (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (w : ℕ → UniKeccak.KeccakVariant → ℕ) :
    proverStream D 6 w = 5608 + w 32 UniKeccak.keccakMain := by
  obtain ⟨-, -, -, h4⟩ := reference_stackVars
  unfold proverStream streamBytes
  rw [hD, reference_flockLogN, h4, valuesBound_eq]
  omega

end Reference

end UniKeccakComplete.Cost

/-- info: 'UniKeccakComplete.Cost.cost_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Cost.cost_uniProverWith

/-- info: 'UniKeccakComplete.Cost.costP_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Cost.costP_uniProverWith

/-- info: 'UniKeccakComplete.Cost.proverBlocks_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Cost.proverBlocks_reference
