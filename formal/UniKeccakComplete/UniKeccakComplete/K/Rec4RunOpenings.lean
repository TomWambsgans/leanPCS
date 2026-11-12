-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's run is `formal/UniKeccak`'s
-- (`UniKeccak/Verifier4.lean`: `reduceWithK4`, `batchK4`, `runWithK4`, `runK4`; `UniKeccak/Pcs.lean`:
-- `verifyWithK4`, `pcsOpenK`); `combine` and `heapRelations` are `formal/UniStatement`'s. The postcondition calculus
-- (`Holds`, `HoldsE`) and the argument follow `formal/RecCompose/RecCompose/Holds.lean`, `RunShape.lean` and
-- `RunOpenings.lean` (π1-rec3's `pi1RunOpenings`), restated here for π1-rec4 (this library cannot import RecCompose).
import UniKeccakComplete.K.Rec4End

/-!
# π1-rec4's run leaves three point openings

* **`runK4_openings`**: a run of π1-rec4's verifier (`UniKeccak.runK4 shape … keccakRec4 .point`, any shape) that
  returns a result has three point openings, `C1`'s, `C2`'s and the setup's, in `commitments` order, with no bit slice
  (`reduceWithK4`: each commitment has a relation, so `combine` claims on each; `batchK4` makes one point claim per
  given claim, its values as many as the claims).
* **`pcsOpenK_length`**: a PCS claim's opening accepts only at a point of `n` coordinates, so in an accepting
  `verifyWithK4` the three points have `stackVarsK shape c` coordinates (at the reference shape `27`, `26`, `23`).
* For the honest prover's proofs, `Rec4.honest_openings4` (`Rec4Core.lean`) gives the openings with their lengths at
  every challenge (no bad event excluded).
-/

set_option linter.unusedSectionVars false

namespace UniKeccakComplete.Rec4.RO

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-! ## Postconditions -/

/-- **Every output of `X` satisfies `P`.** -/
def Holds {α : Type} (X : m α) (P : α → Prop) : Prop :=
  (fun x ↦ (x, P x)) <$> X = (fun x ↦ (x, True)) <$> X

theorem holds_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : Holds (pure a : m α) P := by
  unfold Holds
  simp only [map_pure, eq_true h]

theorem bind_congr_of_holds {α β : Type} {X : m α} {Q : α → Prop} (hX : Holds X Q) {h h' : α → m β}
    (hh : ∀ a, Q a → h a = h' a) : X >>= h = X >>= h' := by
  classical
  calc X >>= h = ((fun a ↦ (a, True)) <$> X) >>= fun p ↦ (if p.2 then h p.1 else h' p.1) := by
        rw [bind_map_left]; simp
    _ = ((fun a ↦ (a, Q a)) <$> X) >>= fun p ↦ (if p.2 then h p.1 else h' p.1) := by
        unfold Holds at hX; rw [hX]
    _ = X >>= fun a ↦ if Q a then h a else h' a := by rw [bind_map_left]
    _ = X >>= h' := by
        congr 1
        funext a
        split_ifs with hq
        · exact hh a hq
        · rfl

theorem holds_bind {α β : Type} {X : m α} {k : α → m β} {Q : α → Prop} {P : β → Prop} (hX : Holds X Q)
    (hk : ∀ a, Q a → Holds (k a) P) : Holds (X >>= k) P := by
  unfold Holds
  rw [map_bind, map_bind]
  exact bind_congr_of_holds hX fun a ha ↦ hk a ha

theorem holds_true {α : Type} (X : m α) : Holds X fun _ ↦ True := rfl

theorem holds_mono {α : Type} {X : m α} {P P' : α → Prop} (hX : Holds X P) (h : ∀ a, P a → P' a) :
    Holds X P' := by
  have e : X = X >>= pure := (bind_pure X).symm
  rw [e]
  exact holds_bind hX fun a ha ↦ holds_pure (h a ha)

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

theorem holdsE_mono {α : Type} {X : ChanM m α} {P P' : α → Prop} (hX : HoldsE X P) (h : ∀ a, P a → P' a) :
    HoldsE X P' := fun c ↦ holds_mono (hX c) fun _ hp a ha ↦ h a (hp a ha)

/-- A loop pushing one element a step adds one element a step. -/
theorem holdsE_forIn_push {γ : Type} (f : γ → Array E → ChanM m (ForInStep (Array E)))
    (hf : ∀ x b, HoldsE (f x b) fun st ↦ ∃ y, st = .yield (b.push y)) :
    ∀ (l : List γ) (b : Array E), HoldsE (forIn l b f) fun r ↦ r.size = b.size + l.length
  | [], b => by
    simp only [List.forIn_nil, List.length_nil, Nat.add_zero]
    exact holdsE_pure rfl
  | x :: l, b => by
    rw [List.forIn_cons]
    refine holdsE_bind (hf x b) fun st ⟨y, hst⟩ ↦ ?_
    subst hst
    simp only
    refine holdsE_mono (holdsE_forIn_push f hf l (b.push y)) fun r hr ↦ ?_
    simp only [Array.size_push, List.length_cons] at hr ⊢
    omega

theorem holdsE_nextScalars_length (count : ℕ) :
    HoldsE (nextScalars (m := m) count) fun l ↦ l.length = count := by
  unfold nextScalars
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine holdsE_bind (holdsE_forIn_push _ (fun x b ↦ ?_) _ _) fun out h ↦ holdsE_pure ?_
  · exact holdsE_bind (holdsE_true (m := m) _) fun y _ ↦ holdsE_pure ⟨y, rfl⟩
  · simp only [List.size_toArray, List.length_range', Std.Legacy.Range.size] at h ⊢
    simp [h]

end Generic

theorem holds_id {α : Type} {X : Id α} {P : α → Prop} (h : Holds X P) : P X.run := by
  have h2 : ((X.run, P X.run) : α × Prop) = (X.run, True) := h
  exact of_eq_true (congrArg Prod.snd h2)

/-! ## The combined claims -/

/-- Three point openings, `C1`'s, `C2`'s and the setup's, no bit slice. -/
def OpeningsShape (l : List (Commitment × Opening)) : Prop :=
  ∃ pt1 v1 pt2 v2 pt3 v3, l = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none), (.setup, .point pt3 v3 none)]

theorem combine_isSome (rels : List Relation) (c : Commitment) (rho : E)
    (h : ∃ rel ∈ rels, rel.commitment = c) : (combine rels c rho).isSome := by
  obtain ⟨rel, hrel, hc⟩ := h
  unfold combine
  have hne : (rels.filter (·.commitment == c)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨rel, List.mem_filter.mpr ⟨hrel, by simp [hc]⟩⟩
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem filterMap_combine_fst (rels : List Relation) (rho : E)
    (h : ∀ c ∈ commitments, ∃ rel ∈ rels, rel.commitment = c) :
    ((commitments.filterMap fun c ↦ (combine rels c rho).map fun x ↦ (c, x)).map (·.1)) =
      [.c1, .c2, .setup] := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c1 rho (h .c1 (by simp [commitments])))
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c2 rho (h .c2 (by simp [commitments])))
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .setup rho (h .setup (by simp [commitments])))
  simp [commitments, List.filterMap, ha, hb, hd]

/-- **`heapRelations` makes a relation on `C2`**: its first, the heap's value. -/
theorem heapRelations_c2 (shape : UniStatement.Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) :
    ∃ rel ∈ (heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush
      bytecodePull bytecodePush w constraintChunks).1, rel.commitment = .c2 := by
  refine ⟨Relation.equal .heap (w.take shape.heap.h) heapValue, ?_, rfl⟩
  have inv : ∀ (l : List (Block × ℕ)) (f : Block × ℕ → Array Relation × Array (Column × ℕ × Bool) →
      Id (ForInStep (Array Relation × Array (Column × ℕ × Bool)))),
      (∀ x b, ∃ r' c', f x b = .yield (r', c') ∧ ∀ y ∈ b.1, y ∈ r') →
      ∀ b : Array Relation × Array (Column × ℕ × Bool), ∀ y ∈ b.1, y ∈ (Id.run (forIn l b f)).1 := by
    intro l f hf
    induction l with
    | nil => intro b y hy; simpa using hy
    | cons x l ih =>
      intro b y hy
      obtain ⟨r', c', hfx, hsub⟩ := hf x b
      simp only [List.forIn_cons, Id.run, hfx]
      exact ih (r', c') y (hsub y hy)
  unfold heapRelations
  dsimp only
  rw [Id.run_bind]
  simp only [Id.run_pure, Array.toList_push, List.mem_append]
  left
  rw [Array.mem_toList_iff]
  refine inv _ _ ?_ _ _ ?_
  · intro x b
    split <;> exact ⟨_, _, rfl, fun y hy ↦ Array.mem_push_of_mem _ hy⟩
  · simp

theorem exists_push_of {P : Relation → Prop} {X : Array Relation} (q : Relation) (h : ∃ rel ∈ X.toList, P rel) :
    ∃ rel ∈ (X.push q).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

theorem exists_push_self {P : Relation → Prop} (X : Array Relation) {q : Relation} (h : P q) :
    ∃ rel ∈ (X.push q).toList, P rel := ⟨q, by simp, h⟩

theorem exists_append_left {P : Relation → Prop} {X : Array Relation} (Y : Array Relation)
    (h : ∃ rel ∈ X.toList, P rel) : ∃ rel ∈ (X ++ Y).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

theorem exists_append_list {P : Relation → Prop} (X : Array Relation) {L : List Relation}
    (h : ∃ rel ∈ L, P rel) : ∃ rel ∈ (X ++ L.toArray).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

theorem list_three {α : Type} {l : List α} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  match l, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-! ## The batch and the reduction -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **π1-rec4's batch makes one point claim per given claim, in order.** -/
theorem holdsE_batchK4_openings (F : KeccakState → m KeccakState) (lambda : E)
    (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (hc : combined.map (·.1) = [.c1, .c2, .setup]) :
    HoldsE (UniKeccak.batchK4 F lambda combined layouts ringMap) OpeningsShape := by
  obtain ⟨x1, x2, x3, rfl⟩ := list_three (by simpa using congrArg List.length hc)
  obtain ⟨k1, a⟩ := x1
  obtain ⟨k2, b⟩ := x2
  obtain ⟨k3, d⟩ := x3
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hc
  obtain ⟨rfl, rfl, rfl, -⟩ := hc
  unfold UniKeccak.batchK4
  dsimp only
  repeat (first
    | (refine holdsE_bind (holdsE_nextScalars_length (m := m) _) fun vals hv ↦ ?_
       obtain ⟨v1, v2, v3, rfl⟩ := list_three (l := vals) (by simpa using hv)
       simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
       exact holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ holdsE_pure ⟨_, _, _, _, _, _, rfl⟩)
    | refine holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ ?_
    | split)

set_option maxHeartbeats 1600000 in
/-- **π1-rec4's reduction** (point claims) makes three point openings, `C1`'s, `C2`'s and the setup's. -/
theorem holdsE_reduceWithK4_openings (F : KeccakState → m KeccakState) (shape : UniStatement.Shape)
    (stmt : List E) :
    HoldsE (UniKeccak.reduceWithK4 F shape stmt UniKeccak.keccakRec4 .point) fun r ↦ OpeningsShape r.openings := by
  unfold UniKeccak.reduceWithK4
  dsimp only
  split
  · exact holdsE_bind (holdsE_throw (m := m) _) fun _ h ↦ False.elim h
  repeat (first
    | exact holdsE_pure (‹_ ∧ OpeningsShape _›).2
    | exact holdsE_pure ‹OpeningsShape _›
    | refine holdsE_bind (holdsE_batchK4_openings F _ _ _ _ ?_) fun y hy ↦ ?_
    | refine holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ ?_
    | split)
  all_goals try exact holdsE_pure ‹OpeningsShape _›
  all_goals
    refine filterMap_combine_fst _ _ fun c hc ↦ ?_
    simp only [commitments, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact exists_push_of _ (exists_append_left _ (exists_push_of _ (exists_push_of _ (exists_push_of _
        (exists_push_of _ (exists_push_of _ (exists_push_self _ rfl)))))))
    · exact exists_push_of _ (exists_append_list _ (heapRelations_c2 _ _ _ _ _ _ _ _ _ _ _ _ _))
    · exact exists_push_of _ (exists_append_left _ (exists_push_of _ (exists_push_of _ (exists_push_of _
        (exists_push_of _ (exists_push_self _ rfl))))))

/-- **π1-rec4's run, over any permutation**: a result has three point openings. -/
theorem runWithK4_openings (F : KeccakState → m KeccakState) (shape : UniStatement.Shape)
    (iv publicInput : List UInt8) (stream : Array UInt8) :
    Holds (UniKeccak.runWithK4 F shape iv publicInput stream UniKeccak.keccakRec4 .point) fun o ↦
      ∀ r, o.result = .ok r → OpeningsShape r.openings := by
  unfold UniKeccak.runWithK4
  refine holds_bind (holds_true _) fun seed _ ↦
    holds_bind (Q := fun p ↦ ∀ a, p.1 = .ok a → OpeningsShape a.openings) ?_ fun p hp ↦ ?_
  · refine holdsE_bind (Q := fun r : Reduced ↦ OpeningsShape r.openings)
      (P := fun r : Reduced ↦ OpeningsShape r.openings) (holdsE_reduceWithK4_openings F shape _) (fun a ha ↦ ?_) _
    exact holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ holdsE_pure ha
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

end Generic

end UniKeccakComplete.Rec4.RO

namespace UniKeccakComplete.Rec4

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **π1-rec4's run on Keccak-f[1600] leaves three point openings**: a run (`runK4`, any shape) that returns a result
has `C1`'s, `C2`'s and the setup's point openings, in this order, no bit slice. -/
theorem runK4_openings (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (r : Reduced) (hr : (runK4 shape iv publicInput stream keccakRec4 .point).result = .ok r) :
    ∃ pt1 v1 pt2 v2 pt3 v3, r.openings =
      [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none), (.setup, .point pt3 v3 none)] :=
  RO.holds_id (RO.runWithK4_openings (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream) r hr

/-- A PCS claim's opening accepts only at a point of its commitment's variables. -/
theorem pcsOpenK_length {F : KeccakState → KeccakState} {n : ℕ} {root : Digest} {ood : E} {pt : List E} {v : E}
    {p : LeanVM.Protocol.Compile.Proof} (h : pcsOpenK (m := Id) (fun s ↦ pure (F s)) n root ood pt v p = true) :
    pt.length = n := by
  unfold pcsOpenK at h
  split at h
  · assumption
  · exact absurd h (by simp)

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.runK4_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.runK4_openings
