-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak π1-rec3's run is `formal/UniKeccak`'s
-- (`UniKeccak/Verifier.lean`: `reduceWithK`, `runWithK`, `runK`).
import RecCompose.Pi2Run
import RecCompose.CompleteCouplings

/-!
# The Keccak π1-rec3's run leaves no matrices' claim and reads its roots as two limbs: `Pi1RunShape`

**`pi1RunShape`**: a run of the Keccak π1-rec3's verifier (`UniKeccak.runK keccak128 … keccakRec3 .point`) that returns
a result has no matrices' claim and roots whose four halves have zero top limbs. Through `reduceWithK` (`HoldsE`,
postconditions on a channel computation's results): its result is built with no matrices' claim (the Keccak-f block's
Flock leaves none: `reduceWithK` returns `none` there), and its roots are the two `nextRoot`s, each half `eNew _ _ 0`
(`holdsE_nextRoot`). Unlike the BLAKE2s VM's `reduceWithFs`, nothing of the batch is needed.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Every result of a channel computation satisfies `P`**, from any channel. -/
def HoldsE {α : Type} (X : ChanM m α) (P : α → Prop) : Prop :=
  ∀ c : Chan, Holds ((X.run).run c) fun p ↦ ∀ a, p.1 = .ok a → P a

theorem holdsE_true {α : Type} (X : ChanM m α) : HoldsE X fun _ ↦ True :=
  fun _ ↦ holds_mono (holds_true _) fun _ _ _ _ ↦ trivial

theorem holdsE_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : HoldsE (pure a : ChanM m α) P := by
  intro c
  have e : ((pure a : ChanM m α).run).run c = pure (.ok a, c) := by simp
  rw [e]
  refine holds_pure fun b hb ↦ ?_
  simp only [Except.ok.injEq] at hb
  exact hb ▸ h

theorem holdsE_pure_eq {α : Type} (a : α) : HoldsE (pure a : ChanM m α) fun b ↦ b = a := holdsE_pure rfl

theorem holdsE_bind {α β : Type} {X : ChanM m α} {k : α → ChanM m β} {Q : α → Prop} {P : β → Prop}
    (hX : HoldsE X Q) (hk : ∀ a, Q a → HoldsE (k a) P) : HoldsE (X >>= k) P := by
  intro c
  rw [ExceptT.run_bind, StateT.run_bind]
  refine holds_bind (hX c) ?_
  rintro ⟨e, c'⟩ hq
  cases e with
  | error err =>
    simp only [StateT.run_pure]
    exact holds_pure fun b hb ↦ absurd hb (by simp)
  | ok a =>
    simp only
    exact hk a (hq a rfl) c'

theorem holdsE_throw {α : Type} (e : UniError) {P : α → Prop} : HoldsE (throw e : ChanM m α) P := by
  intro c
  have h : ((throw e : ChanM m α).run).run c = pure (.error e, c) := by simp
  rw [h]
  exact holds_pure fun b hb ↦ absurd hb (by simp)

theorem holdsE_nextRoot : HoldsE (nextRoot (m := m)) fun x ↦ x.1.limb 2 = 0 ∧ x.2.limb 2 = 0 := by
  intro c
  refine holds_mono (reads_nextRoot c) ?_
  rintro p ⟨-, hok, -⟩ a ha
  obtain ⟨-, rfl⟩ := hok a ha
  exact ⟨rfl, rfl⟩

/-- The result of the Keccak π1-rec3's reduction: no matrices' claim, the roots' halves with zero top limbs. -/
def ShapeOK (r : Reduced) : Prop :=
  r.matrices = none ∧ (r.roots.1.1.limb 2 = 0 ∧ r.roots.1.2.limb 2 = 0) ∧
    (r.roots.2.1.limb 2 = 0 ∧ r.roots.2.2.limb 2 = 0)

/-- **The Keccak verifier's reduction** (any shape, variant and claims' mode) returns no matrices' claim and roots
read as two limbs. -/
theorem holdsE_reduceWithK (F : KeccakState → m KeccakState) (shape : UniStatement.Shape) (stmt : List E)
    (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    HoldsE (UniKeccak.reduceWithK F shape stmt v mode) ShapeOK := by
  unfold UniKeccak.reduceWithK
  dsimp only
  repeat (first
    | exact holdsE_pure ⟨rfl, ‹_›, ‹_›⟩
    | exact holdsE_bind (holdsE_throw (m := m) _) fun _ h ↦ False.elim h
    | refine holdsE_bind holdsE_nextRoot fun _ _ ↦ ?_
    | (refine holdsE_bind (holdsE_pure_eq (m := m) _) fun _ h ↦ ?_; subst h; try dsimp only)
    | refine holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ ?_
    | split)

/-- **The Keccak verifier's run, over any permutation**: a result has no matrices' claim and roots read as two
limbs. -/
theorem runWithK_shape (F : KeccakState → m KeccakState) (shape : UniStatement.Shape) (iv publicInput : List UInt8)
    (stream : Array UInt8) (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    Holds (UniKeccak.runWithK F shape iv publicInput stream v mode) fun o ↦ ∀ r, o.result = .ok r → ShapeOK r := by
  unfold UniKeccak.runWithK
  refine holds_bind (holds_true _) fun seed _ ↦ holds_bind (Q := fun p ↦ ∀ a, p.1 = .ok a → ShapeOK a) ?_
    fun p hp ↦ ?_
  · exact holdsE_bind (holdsE_reduceWithK F shape _ v mode) (fun a ha ↦ holdsE_bind (holdsE_true (m := m) _)
      fun _ _ ↦ holdsE_pure ha) _
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

end Generic

/-- **`Pi1RunShape`**: a run of the Keccak π1-rec3's verifier that returns a result has no matrices' claim and roots
whose halves have zero top limbs. -/
theorem pi1RunShape : Pi1RunShape := by
  intro iv publicInput stream r hr
  have h := holds_id (runWithK_shape (m := Id) (fun s ↦ pure (keccakF1600 s)) RecGraphKeccak.Pi1.keccak128 iv
    publicInput stream UniKeccak.keccakRec3 .point) r hr
  exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2.1, h.2.2.2⟩

end RecCompose

/-- info: 'RecCompose.pi1RunShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1RunShape
