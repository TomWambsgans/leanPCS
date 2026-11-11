-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The specification follows `UniSound/FsChain.lean`'s
-- (`uniSpec`, `uView`) for Compose's wide chain (`Compose/WideChain.lean`'s `ChainSpecW`).
import Compose.WideRate
import UniSound.FsChain
import UniKeccakSound.Rec4.Prog4

/-!
# π1-rec4's transcript as a wide chain

The univariate transcript (`UniSound/FsChain.lean`) for π1-rec4's verifier: one Keccak-256 call a round, its digest
and its tail (the rate past the digest) the round's challenges (`Compose.chalsW`), a round's message absorbed with
`pv j` scalars before its root (`C2`'s `64` slices: `pv4`).

* **`uniEncW p`**: a message's bytes, its first `p` scalars, its root, the rest;
* **`UniRf4`**: an input refers to a digest by `Refers`, or as the root at byte `32` (after a state), `56` (after a
  state and the row counts: `C1`'s) or `1568` (after a state and `64` scalars: `C2`'s); at most six digests;
* **`uSpec4 κ nV np`**: the chain on `rec4Rounds κ nV np` (`ChainSpecW`);
* **`msgsAtW`**, **`uView4`**, **`uDone4`**, **`uTail4`**: the proof's stream read with the scalars before the roots.
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM.Parameters UniStatement UniSound
open scoped ENNReal

/-! ## A message's bytes -/

/-- **A message's bytes, `p` scalars before the root**: the first `p` scalars, the root (if any), the rest. -/
def uniEncW (p : ℕ) (m : RMsg E) : List UInt8 :=
  scalars24 (m.2.take p) ++ (match m.1 with
    | some r => revRoot r
    | none => []) ++ scalars24 (m.2.drop p)

theorem uniEncW_inj (p : ℕ) {sp : RoundSpec} {m m' : RMsg E} (h : m.Fits sp) (h' : m'.Fits sp)
    (he : uniEncW p m = uniEncW p m') : m = m' := by
  obtain ⟨r, l⟩ := m
  obtain ⟨r', l'⟩ := m'
  obtain ⟨hr, hl⟩ := h
  obtain ⟨hr', hl'⟩ := h'
  simp only at hr hl hr' hl'
  have hll : l.length = l'.length := hl.trans hl'.symm
  have ht : (l.take p).length = (l'.take p).length := by simp [hll]
  have hd : (l.drop p).length = (l'.drop p).length := by simp [hll]
  unfold uniEncW at he
  simp only at he
  rw [List.append_assoc, List.append_assoc] at he
  obtain ⟨h1, h2⟩ := List.append_inj he (by simp [ht])
  have e1 := scalars24_inj ht h1
  have hrr : r.isSome = r'.isSome := hr.trans hr'.symm
  cases r with
  | none =>
    cases r' with
    | none =>
      simp only [List.nil_append] at h2
      have e2 := scalars24_inj hd h2
      rw [← List.take_append_drop p l, ← List.take_append_drop p l', e1, e2]
    | some _ => exact absurd hrr (by simp)
  | some a =>
    cases r' with
    | none => exact absurd hrr (by simp)
    | some a' =>
      obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp)
      have e2 := scalars24_inj hd h4
      rw [revRoot_injective h3, ← List.take_append_drop p l, ← List.take_append_drop p l', e1, e2]

/-! ## What an input refers to -/

/-- **An input refers to a digest** (π1-rec4): `Refers`, or the digest is the root the input absorbs after a state
(bytes `32 … 64`), after a state and the row counts (bytes `56 … 88`, `C1`'s), or after a state and `64` scalars
(bytes `1568 … 1600`, `C2`'s). -/
def UniRf4 (y : List UInt8) (d : Bytes32) : Prop :=
  Refers y d ∨ revRoot d = (y.drop 32).take 32 ∨ revRoot d = (y.drop 56).take 32 ∨
    revRoot d = (y.drop 1568).take 32

open Classical in
/-- The digests an input refers to. -/
noncomputable def uniRefs4 (y : List UInt8) : List Bytes32 :=
  (Finset.univ.filter fun d : Bytes32 => UniRf4 y d).toList

set_option maxRecDepth 100000 in
theorem uniRf4_refs (y : List UInt8) (d : Bytes32) (h : UniRf4 y d) : d ∈ uniRefs4 y := by
  classical
  unfold uniRefs4
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

open Classical in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most six digests. -/
theorem length_uniRefs4 (y : List UInt8) : (uniRefs4 y).length ≤ 6 := by
  unfold uniRefs4
  rw [Finset.length_toList]
  have h1 : ∀ z : List UInt8,
      (Finset.univ.filter fun u : Bytes32 => revRoot u = z).card ≤ 1 :=
    fun z => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact revRoot_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => UniRf4 y u) ⊆
      (((Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
        (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 32).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 56).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 1568).take 32) := by
    intro u hu'
    simp only [Finset.mem_filter] at hu'
    obtain ⟨-, h⟩ := hu'
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨Finset.mem_univ _, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩))
    · exact Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h2 := Finset.card_union_le ((Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
    (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 32).take 32))
    (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 56).take 32)
  have h2' := Finset.card_union_le (Finset.univ.filter fun u : Bytes32 => Refers y u)
    (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 32).take 32)
  have h3 := card_refers_le y
  have h4 := h1 ((y.drop 32).take 32)
  have h5 := h1 ((y.drop 56).take 32)
  have h6 := h1 ((y.drop 1568).take 32)
  omega

/-! ## The chain's specification -/

section Spec

variable (κ nV np : ℕ)

theorem rec4Rounds_ns_le : ∀ sp ∈ rec4Rounds κ nV np, sp.ns ≤ 4 := by
  intro sp hsp
  simp only [rec4Rounds, kRoundsMid, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
    or_false] at hsp
  aesop

theorem rec4Rounds_spec_c2 : (uniK (rec4Rounds κ nV np)).spec (28 + κ) = ⟨true, 65, 4⟩ := by
  show (rec4Rounds κ nV np).getD (28 + κ) ⟨false, 0, 0⟩ = _
  have e : rec4Rounds κ nV np = (⟨true, 1, 3⟩ :: kRoundsMid κ) ++ (⟨true, 65, 4⟩ :: ⟨false, nV, 3⟩ ::
      (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) := by
    simp [rec4Rounds]
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [length_kRoundsMid])]
  simp only [List.length_cons, length_kRoundsMid, show 28 + κ - (27 + κ + 1) = 0 by omega]
  rfl

/-- **π1-rec4's transcript as a wide chain**: the rounds `rec4Rounds κ nV np`, the seed's input and the row counts'
bytes as π1-rec3's, a round's message with `pv4 κ j` scalars before its root. -/
noncomputable def uSpec4 : ChainSpecW E FSt where
  K := uniK (rec4Rounds κ nV np)
  ns_le := rec4Rounds_ns_le κ nV np
  label := uniLabel
  pre s := s.2.2.toList
  pre_len s s' := by simp
  stmt_inj := uniStmt_inj
  enc j := uniEncW (pv4 κ j)
  enc_inj j _ _ _ h h' he := uniEncW_inj (pv4 κ j) h h' he
  Rf := UniRf4
  nRf := 6
  refs := uniRefs4
  rf_refs := uniRf4_refs
  length_refs := length_uniRefs4
  refers_rf y d h := Or.inl h
  rf_enc j st r l h := by
    by_cases hj : j = 28 + κ
    · subst hj
      rw [rec4Rounds_spec_c2] at h
      have hl : l.length = 65 := h.2
      refine Or.inr (Or.inr (Or.inr ?_))
      simp only [stepIn, uniEncW, pv4, ite_true]
      have h64 : (scalars24 (l.take 64)).length = 1536 := by simp [hl]
      rw [show (st.toList ++ (scalars24 (l.take 64) ++ revRoot r ++ scalars24 (l.drop 64))) =
          (st.toList ++ scalars24 (l.take 64)) ++ (revRoot r ++ scalars24 (l.drop 64)) by simp,
        List.drop_left' (by simp [h64]), List.take_left' (by simp)]
    · refine Or.inr (Or.inl ?_)
      simp only [stepIn, uniEncW, pv4, ite_eq_right hj, List.take_zero, List.drop_zero]
      rw [show scalars24 [] = [] from rfl, List.nil_append, List.drop_left' (by simp),
        List.take_left' (by simp)]
  rf_pre s st r l _ := by
    refine Or.inr (Or.inr (Or.inl ?_))
    have h0 : pv4 κ 0 = 0 := by unfold pv4; rw [ite_eq_right (by omega)]
    simp only [stepIn, uniEncW, h0, List.take_zero, List.drop_zero]
    rw [show scalars24 [] = [] from rfl, List.nil_append,
      show (st.toList ++ (s.2.2.toList ++ (revRoot r ++ scalars24 l))).drop 56 = revRoot r ++ scalars24 l by
        rw [show (56 : ℕ) = 32 + 24 from rfl, ← List.drop_drop, List.drop_left' (by simp),
          List.drop_left' (by simp)],
      List.take_left' (by simp)]

@[simp] theorem uSpec4_rounds : (uSpec4 κ nV np).K.rounds = rec4Rounds κ nV np := rfl

theorem uSpec4_nQ : (uSpec4 κ nV np).nQ = 32 + κ + np := by
  show (rec4Rounds κ nV np).length + 1 = _
  rw [length_rec4Rounds]
  omega

end Spec

/-! ## The proof the chain reads -/

/-- **A round's message from byte `o`**, `p` scalars before its root: the root (if any) after them. -/
def msgOfW (b : Array UInt8) (p o : ℕ) (r : RoundSpec) : UMsg :=
  ((if r.root then some (halvesAt b (o + 24 * p)) else none),
    (List.range r.nv).map fun k => scalarAt b (o + (if r.root && decide (p ≤ k) then 32 else 0) + 24 * k))

/-- **The rounds' messages the stream carries**, from round `j` and byte `o` on, `pv j` scalars before round `j`'s
root. -/
def msgsAtW (b : Array UInt8) (pv : ℕ → ℕ) : ℕ → ℕ → List RoundSpec → List UMsg
  | _, _, [] => []
  | j, o, r :: rs => msgOfW b (pv j) o r :: msgsAtW b pv (j + 1) (o + roundBytes r) rs

theorem length_msgsAtW (b : Array UInt8) (pv : ℕ → ℕ) : ∀ (j o : ℕ) (rs : List RoundSpec),
    (msgsAtW b pv j o rs).length = rs.length
  | _, _, [] => rfl
  | j, o, r :: rs => by simp [msgsAtW, length_msgsAtW b pv _ _ rs]

/-- The stream's messages fit the rounds. -/
theorem fitsAll_msgsAtW (b : Array UInt8) (pv : ℕ → ℕ) : ∀ (j o : ℕ) (rs : List RoundSpec),
    FitsAll rs ((msgsAtW b pv j o rs).map toRMsg)
  | _, _, [] => trivial
  | j, o, r :: rs => by
    simp only [msgsAtW, List.map_cons]
    refine ⟨⟨?_, by simp [toRMsg, msgOfW]⟩, fitsAll_msgsAtW b pv _ _ rs⟩
    rcases r with ⟨_ | _, nv, ns⟩ <;> simp [toRMsg, msgOfW]

/-- **What the chain reads of a proof** (π1-rec4): the statement, and the rounds' messages from byte `24`, `pv j`
scalars before round `j`'s root. -/
def uViewW (rounds : List RoundSpec) (pv : ℕ → ℕ) (π : UPf) : FSt × List (RMsg E) :=
  ((π.iv, π.input, rowBytes π.proof.stream), (msgsAtW π.proof.stream pv 0 24 rounds).map toRMsg)

/-- **The transcript the chain program reads**: the messages and the challenges. -/
def uDoneW (rounds : List RoundSpec) (pv : ℕ → ℕ) (π : UPf) (ch : List (List E)) : Done :=
  (msgsAtW π.proof.stream pv 0 24 rounds).zip ch

/-- **The tail**: the three scalars after the rounds. -/
def uTailW (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 3).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTailW (rounds : List RoundSpec) (π : UPf) : (uTailW rounds π).length = 3 := by
  simp [uTailW]

theorem fitsAll_uViewW (rounds : List RoundSpec) (pv : ℕ → ℕ) (π : UPf) :
    FitsAll rounds (uViewW rounds pv π).2 :=
  fitsAll_msgsAtW _ _ _ _ _

/-- π1-rec4's view. -/
abbrev uView4 (κ nV np : ℕ) : UPf → FSt × List (RMsg E) := uViewW (rec4Rounds κ nV np) (pv4 κ)

end UniKeccakSound.Rec4
