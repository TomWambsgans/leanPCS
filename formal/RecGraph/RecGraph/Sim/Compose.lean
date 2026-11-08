-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Sim.ComposeSpec

/-!
# The composition's small pieces

The lemmas of `reduce`'s composition that the Keccak VM's (`RecGraphKeccak.Sim.Compose`, `reduce_simQK`) uses:
`Relations::equal` (`equalS_psim`), pushing relations (`RpRels.push`, `RpRels.append`), the memory's and the ring
term's relations (`memRel_rp`, `ringRel_rp`), and the challenge nodes along a growth (`chIds_getD_grow`,
`couple_getD`).
-/

-- The judgments are `RecGraph.Sim.Sim`, `RecGraph.Sim.SimE`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The shape's facts -/

theorem eqKernel_sizeC (xs : List E) : (UniStatement.eqKernel xs).size = 2 ^ xs.length := by
  unfold UniStatement.eqKernel
  suffices h : ∀ (a : Array E) (k : Nat), a.size = 2 ^ k →
      (xs.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) a).size = 2 ^ (k + xs.length) by
    simpa using h #[1] 0 rfl
  induction xs with
  | nil => intro a k h; simpa using h
  | cons x xs ih =>
    intro a k h
    rw [List.foldl_cons, ih _ (k + 1) (by simp [h, Nat.pow_succ]; ring)]
    simp only [List.length_cons]
    ring_nf

theorem digits_length (t : E) (n : Nat) : (UniStatement.digits t n).length = n := by
  rw [digits_eq]; simp

/-! ## Small pieces -/

section Pieces

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- **`Relations::equal(column, point, value)`**. -/
theorem equalS_psim (st : RecState) (hg : Good st) (col : Column) {pt : List Nat} {ptE : List E} {v : Nat} {vE : E}
    (hpt : RpL π iv publicInput stream st pt ptE) (hv : Rp π iv publicInput stream st v vE) :
    PSim st (equalS col pt v) (Relation.equal col ptE vE) (RpRel π iv publicInput stream) := by
  unfold equalS Relation.equal
  refine PSim.bind (oneP π iv publicInput stream hg) fun st' o hst ho ↦ PSim.pure hst.good ?_
  exact ⟨List.Forall₂.cons ⟨rfl, rfl, hpt.pgrow hg hst, ho⟩ List.Forall₂.nil, hv.pgrow hg hst⟩

theorem RpRels.push {st : RecState} {a : Array RelationS} {b : Array Relation} {r : RelationS} {u : Relation}
    (h : RpRels π iv publicInput stream st a.toList b.toList) (hr : RpRel π iv publicInput stream st r u) :
    RpRels π iv publicInput stream st (a.push r).toList (b.push u).toList := by
  rw [Array.toList_push, Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons hr List.Forall₂.nil)

theorem RpRels.append {st : RecState} {a : Array RelationS} {b : Array Relation} {rs : List RelationS}
    {us : List Relation} (h : RpRels π iv publicInput stream st a.toList b.toList)
    (hr : RpRels π iv publicInput stream st rs us) :
    RpRels π iv publicInput stream st (a ++ rs.toArray).toList (b ++ us.toArray).toList := by
  rw [Array.toList_append, Array.toList_append, List.toList_toArray, List.toList_toArray]
  exact List.rel_append h hr

/-- An entry of an array of nodes, represented. -/
theorem RpL.arr {st : RecState} {a : Array Nat} {b : Array E} (h : RpL π iv publicInput stream st a.toList b.toList)
    {k : Nat} (hk : k < b.size) : Rp π iv publicInput stream st (a.getD k 0) (b.getD k 0) :=
  RpL.arrGetDC π iv publicInput stream h (by have := h.length; simp at this; omega)

/-- The memory's pull relation. -/
theorem memRel_rp {st : RecState} {w : List Nat} {wE : List E} {weights : Array Nat} {weightsE : Array E}
    {mp4 : Nat} {V : E} (hw : RpL π iv publicInput stream st w wE)
    (hwt : RpL π iv publicInput stream st weights.toList weightsE.toList) (hws : weightsE.size = 16)
    (hv : Rp π iv publicInput stream st mp4 V) (lm : Nat) :
    RpRel π iv publicInput stream st
      { terms := (List.range 3).map fun k ↦ termS (.memory k) (w.take lm) (weights.getD (3 + k) 0), value := mp4 }
      { terms := (List.range 3).map fun k ↦ term (.memory k) (wE.take lm) (weightsE.getD (3 + k) 0), value := V } := by
  refine ⟨?_, hv⟩
  show List.Forall₂ _ _ _
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun k hk ↦ ⟨rfl, rfl, RpL.takeC π iv publicInput stream hw lm, ?_⟩
  exact hwt.arr (by rw [hws]; simp at hk; omega)

/-- The ring term's relation. -/
theorem ringRel_rp {st : RecState} {fp : List Nat} {fpE : List E} {o tgt : Nat} {tgtE : E}
    (hfp : RpL π iv publicInput stream st fp fpE) (ho : Rp π iv publicInput stream st o 1)
    (ht : Rp π iv publicInput stream st tgt tgtE) :
    RpRel π iv publicInput stream st
      { terms := [{ column := .qflock, point := fp, twist := ringTwist, coefficient := o }], value := tgt }
      { terms := [{ column := .qflock, point := fpE, twist := ringTwist, coefficient := 1 }], value := tgtE } :=
  ⟨List.Forall₂.cons ⟨rfl, rfl, hfp, ho⟩ List.Forall₂.nil, ht⟩

end Pieces

/-! ## The tail, in the form `reduce` has it -/

section Tail

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

end Tail

/-- `regrow hg hgr`: transport the representations along `hgr : Grows st st'` (`hg : Good st`). -/
macro "regrow " hg:ident hgr:ident : tactic =>
  `(tactic| (have hk' := ($hg).inv.kinv; sgrow hk' $hgr; clear hk' $hgr))

/-! ## `reduce` against `reduceWithFs` -/

section Reduce

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

theorem getD_toList_map {st : RecState} {l : List Nat} (k : Nat) (hk : k < l.length) :
    (l.map (val π iv publicInput stream st)).getD k 0 = val π iv publicInput stream st (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem chIds_getD_grow {st st' : RecState} (hgr : Grows st st') {k : Nat} (hk : k < (chIds st).length) :
    (chIds st').getD k 0 = (chIds st).getD k 0 := by
  obtain ⟨l, hl⟩ := chIds_grows hgr
  rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk,
    List.getElem_append_left hk]

theorem getD_of_prefix {a b : Array E} {l : List E} (h : a.toList = b.toList ++ l) {k : Nat} (hk : k < b.size) :
    a.getD k 0 = b.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← Array.getElem?_toList, h,
    List.getElem?_append_left (by simpa using hk)]

/-- The challenges' values a coupled channel holds. -/
theorem couple_getD {st : RecState} {c : Chan} (hc : Couple π iv publicInput stream st c) {k : Nat}
    (hk : k < (chIds st).length) :
    c.challenges.getD k 0 = val π iv publicInput stream st ((chIds st).getD k 0) := by
  have e := hc.chal
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e, ← List.getD_eq_getElem?_getD]
  exact getD_toList_map k hk

end Reduce

end RecGraph.Sim
