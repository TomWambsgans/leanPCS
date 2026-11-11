-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/ListChain.lean` of this repository (the chain, the parse, the
-- bad events, the union bound and the trace, whose structure follows `formal/QuotientRpm/ChainRom.lean`)
-- to the chain of the EIP's PCS claims (`crates/membership/quotient/src/{protocol,transcript}.rs`,
-- `formal/Statement/PcsQuotient/Reduction.lean`'s `reduceWith`); the generic lemmas of `Compose` and
-- `QuotientRpm` (list commitments, transcripts, logging, the fresh-query engine, F1's rounds) are
-- reused as they are.
import Compose.ListChain

/-!
# The reduction with four real roots: the list union, query by query

The membership proof of the EIP's PCS claims carries **four commitments**, each a Merkle root and its
out-of-domain answer: the witness table `W`, then the quotient table's three parts `H`, `Q`, `G`; then
the five values (and the parts' two values, never hashed). The chain (`chainWith4`,
`Reduction.lean`'s `reduceWith`) hashes

* the label (`labelOf4`, 136 bytes): the tag, the circuit's commitment (its root, then its
  out-of-domain answer as 24 bytes, `elementBytes`), the statement's 64 bytes; `st₀`;
* `st₀ ‖ commitment W` (128 bytes): `st₁`, giving `α`; `st₂ = H(st₁)`, `β`; `st₃ = H(st₂)`, `γ`;
* `st₃ ‖ commitment H ‖ commitment Q ‖ commitment G` (320 bytes): `st₄`, giving `t`;
* `st₄ ‖ a₀ ‖ a₁ ‖ a₂ ‖ a₃ ‖ next` (192 bytes): `st₅`, giving `ρ`.

A commitment is its root's two **big-endian halves** (`halfWords`: sixteen zero bytes, then sixteen
bytes of the root, twice; `rootHalves`) and its out-of-domain answer's word (`commitWords`, 96 bytes).

What a root commits to is read off the hash's answers by a list commitment (`Compose.ListCommit`,
reused unchanged: the Merkle extraction `TableCode.commit` is one), `L_W` candidates for `W`'s root
(witness messages, `B.Msg₁`) and `L_H`, `L_Q`, `L_G` for the parts', which an assembly map `asm`
turns into F1's second message (`Commits4`). So `(α, β, γ)` are union-bounded over `L_W`
candidates and `t`, `ρ` over `L_W L_H L_Q L_G` quadruples (`listFactor4`).

An input **refers** to a digest (`Refers4`) as `Compose.Refers` has it (its first two 32-byte
chunks: a Merkle node's children, a chain state), or when the digest's half-words are bytes `32`,
`128` or `224` onwards of it (the roots the chain absorbs after a state): at most six digests an
input (`card_refers4_le`). A fresh query is bad (`listBad4`) when its answer collides (`Coll4`,
`7 |H| + 6` values), or when it is the chain's input after `W`'s commitment, the three parts', or the
values (the chain before it asked, without collision) and its answer turns the reduction's state
from lost to won for some candidate (tuple) of the roots before it. **`prob_listBad4`**: at most
`(7 |H| + 6) / 2^256 + listFactor4 · roundError`; **`trace_listBad4`**: a winning run asks one;
**`knowledgeSoundness_list4`**: `(Q + 6 + QV) (listFactor4 · roundError + 7 (Q + 6 + QV) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params

/-! ## The bytes -/

/-- **A root as the chain hashes it** (`root_halves`, `transcript.rs`; `Reduction.lean`'s
`rootHalves`): its two 128-bit halves, each a big-endian scalar (limb `1` the first eight bytes, limb
`0` the next eight, limb `2` zero), as their two words: sixteen zero bytes, then the half. -/
def halfWords (r : Bytes32) : List UInt8 :=
  List.replicate 16 0 ++ r.toList.take 16 ++ List.replicate 16 0 ++ r.toList.drop 16

@[simp] theorem length_halfWords (r : Bytes32) : (halfWords r).length = 64 := by
  simp [halfWords]

theorem halfWords_injective : Function.Injective halfWords := fun a b h => by
  have ha : a.toList.length = 32 := a.length_toList
  have hb : b.toList.length = 32 := b.length_toList
  simp only [halfWords, List.append_assoc] at h
  obtain ⟨-, h⟩ := List.append_inj h rfl
  obtain ⟨h1, h⟩ := List.append_inj h (by simp [ha, hb])
  obtain ⟨-, h2⟩ := List.append_inj h rfl
  apply Vector.toList_inj.mp
  rw [← List.take_append_drop 16 a.toList, ← List.take_append_drop 16 b.toList, h1, h2]

/-- The limbs of a root's two halves (`halves`, `statement.rs`): half `h`'s limb `1` the big-endian
word of bytes `16 h … 16 h + 7`, its limb `0` that of the next eight. -/
def halfLimbs (r : Bytes32) : Limbs × Limbs :=
  ((ofBe64 (r.toList.drop 8), ofBe64 r.toList, 0), (ofBe64 (r.toList.drop 24), ofBe64 (r.toList.drop 16), 0))

/-- **The half-words are the halves' scalar words**: what `Chain::sample` hashes for the two scalars
`rootHalves` sends. -/
theorem halfWords_eq (r : Bytes32) :
    halfWords r = scalarWord (halfLimbs r).1 ++ scalarWord (halfLimbs r).2 := by
  have hl : r.toList.length = 32 := r.length_toList
  have e0 : be64 (ofBe64 r.toList) = r.toList.take 8 := be64_ofBe64 _ (by omega)
  have e1 : be64 (ofBe64 (r.toList.drop 8)) = (r.toList.drop 8).take 8 := be64_ofBe64 _ (by simp [hl])
  have e2 : be64 (ofBe64 (r.toList.drop 16)) = (r.toList.drop 16).take 8 :=
    be64_ofBe64 _ (by simp [hl])
  have e3 : be64 (ofBe64 (r.toList.drop 24)) = (r.toList.drop 24).take 8 :=
    be64_ofBe64 _ (by simp [hl])
  have t16 : r.toList.take 16 = r.toList.take 8 ++ (r.toList.drop 8).take 8 := by
    rw [show 16 = 8 + 8 from rfl, List.take_add]
  have d16 : r.toList.drop 16 = (r.toList.drop 16).take 8 ++ (r.toList.drop 24).take 8 := by
    have h24 : (r.toList.drop 24).take 8 = r.toList.drop 24 := List.take_of_length_le (by simp [hl])
    rw [h24, show r.toList.drop 24 = (r.toList.drop 16).drop 8 by simp, List.take_append_drop]
  rw [halfWords, t16, d16]
  simp only [scalarWord, halfLimbs, be64_zero, e0, e1, e2, e3, List.append_assoc,
    List.replicate_append_replicate, Nat.reduceAdd]

/-! ## Inputs that refer to a digest -/

/-- An input **refers** to a digest when `Compose.Refers` says so (its first or second 32-byte
chunk: a Merkle node's children, a chain state), or when the digest's half-words are its bytes
`32`, `128` or `224` onwards (a root the chain absorbs after a state: `W`'s, or `H`'s, `Q`'s,
`G`'s). -/
def Refers4 (y : List UInt8) (d : Bytes32) : Prop :=
  Refers y d ∨ halfWords d = (y.drop 32).take 64 ∨ halfWords d = (y.drop 128).take 64 ∨
    halfWords d = (y.drop 224).take 64

open Classical in
-- The linter runs out of recursion depth on this proof.
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most six digests. -/
theorem card_refers4_le (y : List UInt8) :
    (Finset.univ.filter fun u : Bytes32 => Refers4 y u).card ≤ 6 := by
  have hh : ∀ k, (Finset.univ.filter fun u : Bytes32 => halfWords u = (y.drop k).take 64).card ≤ 1 :=
    fun k => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact halfWords_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => Refers4 y u) ⊆
      (Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
        ((Finset.univ.filter fun u : Bytes32 => halfWords u = (y.drop 32).take 64) ∪
          ((Finset.univ.filter fun u : Bytes32 => halfWords u = (y.drop 128).take 64) ∪
            (Finset.univ.filter fun u : Bytes32 => halfWords u = (y.drop 224).take 64))) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hu ⊢
    exact hu
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h0 := card_refers_le y
  have h1 := (Finset.card_union_le _ _).trans (Nat.add_le_add (hh 32)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (hh 128) (hh 224))))
  omega

/-! ## The proof, the chain -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-- **A proof of the reduction with four real commitments**: the statement's 64 bytes, the four
commitments (each a root and its out-of-domain answer: the witness table's, the quotient parts'
`H`, `Q`, `G`), and the five values (`ReductionProof` without the parts' two values, which no
challenge follows, and the openings). The circuit's commitment (`ir`, `io`) is the setup's, not the
prover's (the experiments that compute it set it). -/
structure RootProof4 (F : Type) where
  stmt : Vector UInt8 64
  rW : Bytes32
  oW : F
  rH : Bytes32
  oH : F
  rQ : Bytes32
  oQ : F
  rG : Bytes32
  oG : F
  v : (Fin 4 → F) × F
  ir : Bytes32
  io : F

/-- What the label holds: the circuit's root, its out-of-domain answer, the statement. -/
abbrev Pre (F : Type) := Bytes32 × F × Vector UInt8 64

/-- A commitment: a root and its out-of-domain answer. -/
abbrev Com (F : Type) := Bytes32 × F

/-- The three parts' commitments. -/
abbrev Com3 (F : Type) := Com F × Com F × Com F

/-- The label's data. -/
def RootProof4.pre (π : RootProof4 F) : Pre F := (π.ir, π.io, π.stmt)

/-- The witness table's commitment. -/
def RootProof4.comW (π : RootProof4 F) : Com F := (π.rW, π.oW)

/-- The quotient parts' commitments. -/
def RootProof4.comHQG (π : RootProof4 F) : Com3 F := ((π.rH, π.oH), (π.rQ, π.oQ), (π.rG, π.oG))

variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- **The label** (`label`, `Reduction.lean`): the tag, the circuit's root, its out-of-domain answer
as 24 bytes (`elementBytes`: limbs `c2`, `c1`, `c0`, big-endian, its word without the eight zero
bytes), the statement's 64 bytes. -/
def labelOf4 (pre : Pre F) : List UInt8 :=
  tag ++ pre.1.toList ++ (W.word pre.2.1).drop 8 ++ pre.2.2.toList

/-- A commitment as the chain hashes it: the root's half-words, then the out-of-domain answer's
word. -/
def commitWords (c : Com F) : List UInt8 := halfWords c.1 ++ W.word c.2

/-- The chain's input after the witness table's commitment. -/
def afterW (st : Bytes32) (c : Com F) : List UInt8 := st.toList ++ commitWords W c

/-- The chain's input after the quotient parts' three commitments. -/
def afterHQG (st : Bytes32) (c : Com3 F) : List UInt8 :=
  st.toList ++ (commitWords W c.1 ++ commitWords W c.2.1 ++ commitWords W c.2.2)

/-- **The chain** of `reduceWith` over a hash `H` in any monad: the label; `W`'s commitment after
the seed; two more states; `H`'s, `Q`'s and `G`'s commitments; the values. -/
def chainWith4 {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) (π : RootProof4 F) :
    m (Chals F) := do
  let st₀ ← H (labelOf4 W π.pre)
  let st₁ ← H (afterW W st₀ π.comW)
  let st₂ ← H st₁.toList
  let st₃ ← H st₂.toList
  let st₄ ← H (afterHQG W st₃ π.comHQG)
  let st₅ ← H (W.afterValues st₄ π.v)
  pure ⟨W.chal st₁, W.chal st₂, W.chal st₃, W.chal st₄, W.chal st₅⟩

/-! ## The inputs determine what they absorb -/

section Bytes

theorem word_eq_drop (x : F) : W.word x = List.replicate 8 0 ++ (W.word x).drop 8 := by
  simp [Wire.word, scalarWord]

theorem length_tag4 : tag.length = 16 := rfl

@[simp] theorem length_labelOf4 (pre : Pre F) : (labelOf4 W pre).length = 136 := by
  simp [labelOf4, length_tag4]

@[simp] theorem length_commitWords (c : Com F) : (commitWords W c).length = 96 := by
  simp [commitWords]

@[simp] theorem length_afterW (st : Bytes32) (c : Com F) : (afterW W st c).length = 128 := by
  simp [afterW]

@[simp] theorem length_afterHQG (st : Bytes32) (c : Com3 F) : (afterHQG W st c).length = 320 := by
  simp [afterHQG]

theorem labelOf4_injective {pre pre' : Pre F} (h : labelOf4 W pre = labelOf4 W pre') :
    pre = pre' := by
  obtain ⟨ir, io, sb⟩ := pre
  obtain ⟨ir', io', sb'⟩ := pre'
  simp only [labelOf4, List.append_assoc, List.append_cancel_left_eq] at h
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  have e : W.word io = W.word io' := by rw [word_eq_drop W io, word_eq_drop W io', h2]
  rw [Vector.toList_inj.mp h1, W.word_injective e, Vector.toList_inj.mp h3]

theorem commitWords_injective {c c' : Com F} (h : commitWords W c = commitWords W c') : c = c' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact Prod.ext (halfWords_injective h1) (W.word_injective h2)

theorem afterW_injective {st st' : Bytes32} {c c' : Com F} (h : afterW W st c = afterW W st' c') :
    st = st' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, commitWords_injective W h2⟩

theorem afterHQG_injective {st st' : Bytes32} {c c' : Com3 F}
    (h : afterHQG W st c = afterHQG W st' c') : st = st' ∧ c = c' := by
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h, h4⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, Prod.ext (commitWords_injective W h2)
    (Prod.ext (commitWords_injective W h3) (commitWords_injective W h4))⟩

theorem take_afterW (st : Bytes32) (c : Com F) : (afterW W st c).take 32 = st.toList := by
  simp [afterW]

theorem take_afterHQG (st : Bytes32) (c : Com3 F) : (afterHQG W st c).take 32 = st.toList := by
  simp [afterHQG]

theorem rootPart_afterW (st : Bytes32) (c : Com F) :
    ((afterW W st c).drop 32).take 64 = halfWords c.1 := by
  simp [afterW, commitWords]

theorem rootPart_afterHQG₁ (st : Bytes32) (c : Com3 F) :
    ((afterHQG W st c).drop 32).take 64 = halfWords c.1.1 := by
  simp [afterHQG, commitWords]

theorem rootPart_afterHQG₂ (st : Bytes32) (c : Com3 F) :
    ((afterHQG W st c).drop 128).take 64 = halfWords c.2.1.1 := by
  have e : (afterHQG W st c).drop 128 = commitWords W c.2.1 ++ commitWords W c.2.2 := by
    rw [afterHQG, show 128 = 32 + 96 from rfl, ← List.drop_drop,
      List.drop_left' (by simp), List.append_assoc, List.drop_left' (by simp)]
  rw [e]
  simp [commitWords]

theorem rootPart_afterHQG₃ (st : Bytes32) (c : Com3 F) :
    ((afterHQG W st c).drop 224).take 64 = halfWords c.2.2.1 := by
  have e : (afterHQG W st c).drop 224 = commitWords W c.2.2 := by
    rw [afterHQG, show 224 = 32 + 192 from rfl, ← List.drop_drop,
      List.drop_left' (by simp)]
    exact List.drop_left' (by simp)
  rw [e]
  simp [commitWords]

end Bytes

/-! ## List commitments for the four roots -/

/-- **The four list commitments**: the witness table's root gives F1's first message; the
quotient parts' roots give candidates that `asm` assembles into F1's second message. -/
structure Commits4 (B : P.Bounds) (MH MQ MG : Type) where
  CW : ListCommit B.Msg₁
  CH : ListCommit MH
  CQ : ListCommit MQ
  CG : ListCommit MG
  /-- F1's second message from the three parts. -/
  asm : MH → MQ → MG → B.Msg₂

variable {MH MQ MG : Type} (K : Commits4 B MH MQ MG)

/-- The second messages the parts' three roots stand for: every assembled triple of candidates. -/
def Commits4.quot (H : Hist) (T : Table) (rH rQ rG : Bytes32) : List B.Msg₂ :=
  (K.CH.cands H T rH).flatMap fun h => (K.CQ.cands H T rQ).flatMap fun q =>
    (K.CG.cands H T rG).map fun g => K.asm h q g

theorem Commits4.mem_quot {H : Hist} {T : Table} {rH rQ rG : Bytes32} {R : B.Msg₂} :
    R ∈ K.quot H T rH rQ rG ↔ ∃ h ∈ K.CH.cands H T rH, ∃ q ∈ K.CQ.cands H T rQ,
      ∃ g ∈ K.CG.cands H T rG, K.asm h q g = R := by
  simp [Commits4.quot, List.mem_flatMap, List.mem_map]

theorem length_flatMap_le {α γ : Type} (f : α → List γ) (n : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length ≤ n) → (l.flatMap f).length ≤ l.length * n
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := length_flatMap_le f n l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    omega

theorem Commits4.length_quot_le (H : Hist) (T : Table) (rH rQ rG : Bytes32) :
    (K.quot H T rH rQ rG).length ≤ K.CH.bound * K.CQ.bound * K.CG.bound := by
  unfold Commits4.quot
  refine (length_flatMap_le _ (K.CQ.bound * K.CG.bound) _ fun h _ => ?_).trans ?_
  · refine (length_flatMap_le _ K.CG.bound _ fun q _ => ?_).trans ?_
    · simpa using K.CG.length_le H T rG
    · exact Nat.mul_le_mul_right _ (K.CQ.length_le H T rQ)
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (K.CH.length_le H T rH)

theorem Commits4.quot_congr (H : Hist) (T T' : Table) (rH rQ rG : Bytes32)
    (h : ∀ d ∈ H, T d = T' d) : K.quot H T rH rQ rG = K.quot H T' rH rQ rG := by
  simp only [Commits4.quot, K.CH.congr H T T' rH h, K.CQ.congr H T T' rQ h, K.CG.congr H T T' rG h]

/-- **The union bound's factor**: `L_W` candidates for `(α, β, γ)`, `L_W L_H L_Q L_G` tuples for
`t` and `ρ`. -/
def listFactor4 (LW LH LQ LG : ℕ) : ℕ := max LW (LW * (LH * LQ * LG))

/-- With non-empty part lists, the factor is the product of the four bounds. -/
theorem listFactor4_eq {LW LH LQ LG : ℕ} (h : 1 ≤ LH * LQ * LG) :
    listFactor4 LW LH LQ LG = LW * LH * LQ * LG := by
  unfold listFactor4
  rw [max_eq_right (Nat.le_mul_of_pos_right _ h)]
  ring

theorem le_listFactor4_left (LW LH LQ LG : ℕ) : LW ≤ listFactor4 LW LH LQ LG := le_max_left _ _

theorem le_listFactor4_right (LW LH LQ LG : ℕ) : LW * (LH * LQ * LG) ≤ listFactor4 LW LH LQ LG :=
  le_max_right _ _

/-! ## The bad events -/

/-- **A collision**: the fresh answer at `x` repeats an earlier answer, or an input asked before,
or `x`, refers to it. -/
def Coll4 (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  (∃ y ∈ H, T y = T x) ∨ ∃ y ∈ insert x H, Refers4 y (T x)

/-- `x` is the input after the witness table's commitment `cW`, for the label's data `pre`. -/
def ParseFirst4 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) : Prop :=
  ∃ st₀, Has H T (labelOf4 W pre) st₀ ∧ x = afterW W st₀ cW ∧ Set.InjOn T ↑H

open Classical in
/-- The triple the input after `W`'s commitment leads to, its states not asked before, makes the
first round's state go from lost to won for some candidate of `W`'s root. -/
def FreshFirst4 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) : Prop :=
  (T x).toList ∉ H ∧ (T (T x).toList).toList ∉ H ∧ (T (T x).toList).toList ≠ (T x).toList ∧
    ∃ g ∈ K.CW.cands H T cW.1, ¬ State₁ (W.decode pre.2.2) g ∧
      State₂ (W.decode pre.2.2) g (W.chal (T x), W.chal (T (T x).toList),
        W.chal (T (T (T x).toList).toList))

/-- `x` is the input after the parts' commitments: the chain before it was asked, without
collision, and gave the first challenges `c`. -/
def ParseSecond4 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) (c3 : Com3 F)
    (c : F × F × F) : Prop :=
  ∃ st₀ st₁ st₂ st₃, Has H T (labelOf4 W pre) st₀ ∧ Has H T (afterW W st₀ cW) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ x = afterHQG W st₃ c3 ∧
    c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ Set.InjOn T ↑H

/-- `x` is the input after the five values: the chain before it was asked, without collision,
and gave the challenges `c` and `t`. -/
def ParseThird4 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) (c3 : Com3 F)
    (c : F × F × F) (t : F) (v : (Fin 4 → F) × F) : Prop :=
  ∃ st₀ st₁ st₂ st₃ st₄, Has H T (labelOf4 W pre) st₀ ∧ Has H T (afterW W st₀ cW) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ Has H T (afterHQG W st₃ c3) st₄ ∧
    x = W.afterValues st₄ v ∧ c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ t = W.chal st₄ ∧
    Set.InjOn T ↑H

/-- The first round, for some candidate. -/
def FirstBad4 (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW, ParseFirst4 W H x T pre cW ∧ FreshFirst4 W K H x T pre cW

open Classical in
/-- The second round, for some candidate of `W`'s root and some assembled triple of the parts'. -/
def SecondBad4 (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW c3 c, ParseSecond4 W H x T pre cW c3 c ∧
    ∃ g ∈ K.CW.cands H T cW.1, ∃ R ∈ K.quot H T c3.1.1 c3.2.1.1 c3.2.2.1,
      ¬ State₃ (W.decode pre.2.2) g c R ∧ State₄ (W.decode pre.2.2) g c R (W.chal (T x))

open Classical in
/-- The third round, for some candidate of `W`'s root and some assembled triple of the parts'. -/
def ThirdBad4 (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW c3 c t v, ParseThird4 W H x T pre cW c3 c t v ∧
    ∃ g ∈ K.CW.cands H T cW.1, ∃ R ∈ K.quot H T c3.1.1 c3.2.1.1 c3.2.2.1,
      ¬ State₄ (W.decode pre.2.2) g c R t ∧ State₆ (W.decode pre.2.2) g c R t v (W.chal (T x))

/-- **A bad fresh query.** -/
def listBad4 (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll4 H x T ∨ FirstBad4 W K H x T ∨ SecondBad4 W K H x T ∨ ThirdBad4 W K H x T

/-! ## The parse is unique, and reads only the history -/

section Parse

variable {W}

theorem parseFirst4_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x pre cW) :
    ParseFirst4 W H x T pre cW ↔ ParseFirst4 W H x T' pre cW := by
  simp only [ParseFirst4, has_congr h, injOn_congr h]

theorem parseSecond4_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x pre cW c3 c) :
    ParseSecond4 W H x T pre cW c3 c ↔ ParseSecond4 W H x T' pre cW c3 c := by
  simp only [ParseSecond4, has_congr h, injOn_congr h]

theorem parseThird4_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d)
    (x pre cW c3 c t v) :
    ParseThird4 W H x T pre cW c3 c t v ↔ ParseThird4 W H x T' pre cW c3 c t v := by
  simp only [ParseThird4, has_congr h, injOn_congr h]

theorem parseFirst4_unique {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW'}
    (h : ParseFirst4 W H x T pre cW) (h' : ParseFirst4 W H x T pre' cW') :
    pre = pre' ∧ cW = cW' := by
  obtain ⟨st₀, h0, hx, hi⟩ := h
  obtain ⟨st₀', h0', hx', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := afterW_injective W (hx.symm.trans hx')
  exact ⟨labelOf4_injective W (has_inj hi h0 h0'), rfl⟩

theorem parseSecond4_unique {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW' c3 c3' c c'}
    (h : ParseSecond4 W H x T pre cW c3 c) (h' : ParseSecond4 W H x T pre' cW' c3' c') :
    pre = pre' ∧ cW = cW' ∧ c3 = c3' ∧ c = c' := by
  obtain ⟨st₀, st₁, st₂, st₃, h0, h1, h2, h3, hx, hc, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', h0', h1', h2', h3', hx', hc', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := afterHQG_injective W (hx.symm.trans hx')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := afterW_injective W (has_inj hi h1 h1')
  exact ⟨labelOf4_injective W (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm⟩

theorem parseThird4_unique {H : Hist} {x : List UInt8} {T : Table}
    {pre pre' cW cW' c3 c3' c c' t t' v v'}
    (h : ParseThird4 W H x T pre cW c3 c t v) (h' : ParseThird4 W H x T pre' cW' c3' c' t' v') :
    pre = pre' ∧ cW = cW' ∧ c3 = c3' ∧ c = c' ∧ t = t' ∧ v = v' := by
  obtain ⟨st₀, st₁, st₂, st₃, st₄, h0, h1, h2, h3, h4, hx, hc, ht, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', st₄', h0', h1', h2', h3', h4', hx', hc', ht', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := W.afterValues_injective (hx.symm.trans hx')
  obtain ⟨rfl, rfl⟩ := afterHQG_injective W (has_inj hi h4 h4')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := afterW_injective W (has_inj hi h1 h1')
  exact ⟨labelOf4_injective W (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm, ht.trans ht'.symm,
    rfl⟩

/-- The three inputs have three lengths (`128`, `320`, `192`). -/
theorem parseFirst4_parseSecond4 {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW' c3 c}
    (h : ParseFirst4 W H x T pre cW) (h' : ParseSecond4 W H x T pre' cW' c3 c) : False := by
  obtain ⟨_, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

theorem parseFirst4_parseThird4 {H : Hist} {x : List UInt8} {T : Table}
    {pre pre' cW cW' c3 c t v}
    (h : ParseFirst4 W H x T pre cW) (h' : ParseThird4 W H x T pre' cW' c3 c t v) : False := by
  obtain ⟨_, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

theorem parseSecond4_parseThird4 {H : Hist} {x : List UInt8} {T : Table}
    {pre pre' cW cW' c3 c3' c c' t v}
    (h : ParseSecond4 W H x T pre cW c3 c) (h' : ParseThird4 W H x T pre' cW' c3' c' t v) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

end Parse

/-! ## Each fresh query is bad with small probability -/

section Probability

variable {S : Finset (List UInt8)}

/-- **A collision has probability at most `(7 |H| + 6) / 2^256`.** -/
theorem prob_coll4 (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[Coll4 (histOf c) t.1 (tableOf c g)] ≤
      ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let Bad : Finset Bytes32 := (histOf c).image (tableOf c g₀) ∪ (insert t.1 (histOf c)).biUnion
    fun y => Finset.univ.filter fun u : Bytes32 => Refers4 y u
  refine (prEvent_mono _ _ (fun g => g t ∈ Bad) fun g h => ?_).trans ?_
  · rw [← tableOf_fresh c ht g]
    rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y, hy, by rw [tableOf_eq_of_mem c hy g₀ g, hyx]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, by simpa using h⟩)
  · refine (prEvent_cell t (fun u => u ∈ Bad)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have hc : Bad.card ≤ 7 * (histOf c).card + 6 := by
      refine (Finset.card_union_le _ _).trans ?_
      have h2 := Finset.card_biUnion_le (s := insert t.1 (histOf c)) (t := fun y =>
        Finset.univ.filter fun u : Bytes32 => Refers4 y u)
      have h3 : ∑ y ∈ insert t.1 (histOf c), (Finset.univ.filter fun u : Bytes32 =>
          Refers4 y u).card ≤ (insert t.1 (histOf c)).card * 6 := by
        simpa using Finset.sum_le_card_nsmul _ _ 6 fun y _ => card_refers4_le y
      have h4 := Finset.card_insert_le t.1 (histOf c)
      have h5 := Finset.card_image_le (s := histOf c) (f := tableOf c g₀)
      nlinarith
    have : ((Finset.univ.filter fun u : Bytes32 => u ∈ Bad).card : ℝ≥0∞) ≤
        ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast hc
    rw [Nat.cast_pow, Nat.cast_ofNat]
    gcongr

theorem quot_tableOf (c : SCache S) (g g' : ↥S → Bytes32) (rH rQ rG : Bytes32) :
    K.quot (histOf c) (tableOf c g) rH rQ rG = K.quot (histOf c) (tableOf c g') rH rQ rG :=
  K.quot_congr _ _ _ _ _ _ fun _ hd => tableOf_eq_of_mem c hd g g'

/-- The first round's fresh part, for one candidate, has probability at most the round error. -/
theorem prob_freshFirst4_one (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) (hlen : t.1.length = 128) (sb : Vector UInt8 64) (gm : B.Msg₁) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[(tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode sb) gm ∧
      State₂ (W.decode sb) gm (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList))] ≤
      (roundError P B : ℝ≥0∞) := by
  let f : Bytes32 → ↥S := fun u => ⟨u.toList, hS₀ u⟩
  let Q : Bytes32 → Bytes32 → Bytes32 → Prop := fun a b d =>
    ¬ State₁ (W.decode sb) gm ∧ State₂ (W.decode sb) gm (W.chal a, W.chal b, W.chal d)
  refine (prEvent_mono _ _ (fun g => f (g t) ≠ t ∧ f (g (f (g t))) ≠ t ∧
    f (g (f (g t))) ≠ f (g t) ∧ Q (g t) (g (f (g t))) (g (f (g (f (g t))))))
    fun g h => ?_).trans ?_
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [tableOf_fresh c ht g] at h1 h2 h3 h5
    rw [tableOf_of_not_mem c (hS₀ _) h1 g] at h2 h3 h5
    rw [tableOf_of_not_mem c (hS₀ _) h2 g] at h5
    refine ⟨fun e => ?_, fun e => ?_, fun e => h3 (congrArg Subtype.val e), h4, h5⟩
    · have := congrArg (fun s : ↥S => s.1.length) e
      simp [f, hlen] at this
    · have := congrArg (fun s : ↥S => s.1.length) e
      simp [f, hlen] at this
  · refine (prEvent_three_cells t f Q).trans ?_
    rw [prEvent_three_draws]
    exact prob_first_chain W (W.decode sb) gm

/-- A candidate of `W`'s root and an assembled triple of the parts', union-bounded. -/
theorem prob_pairs4 (c : SCache S) {rW rH rQ rG : Bytes32}
    (E : B.Msg₁ → B.Msg₂ → (↥S → Bytes32) → Prop)
    (hE : ∀ gm R, Pr{let g ← $ᵗ (↥S → Bytes32)}[E gm R g] ≤ (roundError P B : ℝ≥0∞)) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[∃ gm ∈ K.CW.cands (histOf c) (tableOf c g) rW,
      ∃ R ∈ K.quot (histOf c) (tableOf c g) rH rQ rG, E gm R g] ≤
      (listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let l₁ := K.CW.cands (histOf c) (tableOf c g₀) rW
  let l₂ := K.quot (histOf c) (tableOf c g₀) rH rQ rG
  refine (prEvent_mono _ _ (fun g => ∃ gm ∈ l₁, ∃ R ∈ l₂, E gm R g) fun g h => ?_).trans ?_
  · rwa [cands_tableOf K.CW c g g₀, quot_tableOf K c g g₀] at h
  refine (prEvent_exists_mem_le _ (fun gm g => ∃ R ∈ l₂, E gm R g)
    ((l₂.length : ℝ≥0∞) * (roundError P B : ℝ≥0∞)) l₁ fun gm _ =>
      prEvent_exists_mem_le _ (fun R g => E gm R g) _ l₂ fun R _ => hE gm R).trans ?_
  rw [← mul_assoc]
  gcongr
  have h1 := K.CW.length_le (histOf c) (tableOf c g₀) rW
  have h2 := K.length_quot_le (histOf c) (tableOf c g₀) rH rQ rG
  exact_mod_cast (Nat.mul_le_mul h1 h2).trans (le_listFactor4_right _ _ _ _)

/-- **The rounds' bad events have probability at most `listFactor4` times the largest round
error**: the parse is read off the history, so at most one round and one parse are possible,
and the candidates are fixed by the history. -/
theorem prob_round4 (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FirstBad4 W K (histOf c) t.1 (tableOf c g) ∨
      SecondBad4 W K (histOf c) t.1 (tableOf c g) ∨ ThirdBad4 W K (histOf c) t.1 (tableOf c g)] ≤
      (listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases h1 : ∃ pre cW, ParseFirst4 W (histOf c) t.1 (tableOf c g₀) pre cW
  · obtain ⟨pre, cW, hp⟩ := h1
    have hlen : t.1.length = 128 := by
      obtain ⟨st₀, -, hx, -⟩ := hp
      rw [hx]
      simp
    let l₁ := K.CW.cands (histOf c) (tableOf c g₀) cW.1
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ l₁, (tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode pre.2.2) gm ∧
      State₂ (W.decode pre.2.2) gm (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList)))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', hf⟩ | ⟨pre', cW', c3', c', hp', -⟩ |
        ⟨pre', cW', c3', c', tt, v, hp', -⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl⟩ := parseFirst4_unique hp' hp
        obtain ⟨f1, f2, f3, gm, hgm, f4, f5⟩ := hf
        rw [cands_tableOf K.CW c g g₀] at hgm
        exact ⟨gm, hgm, f1, f2, f3, f4, f5⟩
      · rw [parseSecond4_congr (hcg g)] at hp'
        exact (parseFirst4_parseSecond4 hp hp').elim
      · rw [parseThird4_congr (hcg g)] at hp'
        exact (parseFirst4_parseThird4 hp hp').elim
    · refine (prEvent_exists_mem_le _ _ (roundError P B : ℝ≥0∞) l₁ fun gm _ =>
        prob_freshFirst4_one W hS₀ c t ht hlen pre.2.2 gm).trans ?_
      gcongr
      exact_mod_cast (K.CW.length_le _ _ _).trans (le_listFactor4_left _ _ _ _)
  by_cases h2 : ∃ pre cW c3 c', ParseSecond4 W (histOf c) t.1 (tableOf c g₀) pre cW c3 c'
  · obtain ⟨pre, cW, c3, c', hp⟩ := h2
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ K.CW.cands (histOf c) (tableOf c g) cW.1,
      ∃ R ∈ K.quot (histOf c) (tableOf c g) c3.1.1 c3.2.1.1 c3.2.2.1,
        ¬ State₃ (W.decode pre.2.2) gm c' R ∧
        State₄ (W.decode pre.2.2) gm c' R (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', c3', c'', hp', hf⟩ |
        ⟨pre', cW', c3', c'', tt, v, hp', -⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        exact (parseFirst4_parseSecond4 hp' hp).elim
      · rw [parseSecond4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := parseSecond4_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
      · rw [parseThird4_congr (hcg g)] at hp'
        exact (parseSecond4_parseThird4 hp hp').elim
    · exact prob_pairs4 K c _ fun gm R =>
        (prEvent_cell t (fun u => ¬ State₃ (W.decode pre.2.2) gm c' R ∧
          State₄ (W.decode pre.2.2) gm c' R (W.chal u))).trans (prob_second_chain W _ gm c' R)
  by_cases h3 : ∃ pre cW c3 c' tt v,
      ParseThird4 W (histOf c) t.1 (tableOf c g₀) pre cW c3 c' tt v
  · obtain ⟨pre, cW, c3, c', tt, v, hp⟩ := h3
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ K.CW.cands (histOf c) (tableOf c g) cW.1,
      ∃ R ∈ K.quot (histOf c) (tableOf c g) c3.1.1 c3.2.1.1 c3.2.2.1,
        ¬ State₄ (W.decode pre.2.2) gm c' R tt ∧
        State₆ (W.decode pre.2.2) gm c' R tt v (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', c3', c'', hp', -⟩ |
        ⟨pre', cW', c3', c'', tt', v', hp', hf⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        exact (parseFirst4_parseThird4 hp' hp).elim
      · rw [parseSecond4_congr (hcg g)] at hp'
        exact (parseSecond4_parseThird4 hp' hp).elim
      · rw [parseThird4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := parseThird4_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
    · exact prob_pairs4 K c _ fun gm R =>
        (prEvent_cell t (fun u => ¬ State₄ (W.decode pre.2.2) gm c' R tt ∧
          State₆ (W.decode pre.2.2) gm c' R tt v (W.chal u))).trans
          (prob_third_chain W _ gm c' R tt v)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => ?_]
    · simp
    rcases h with ⟨pre, cW, hp, -⟩ | ⟨pre, cW, c3, c', hp, -⟩ | ⟨pre, cW, c3, c', tt, v, hp, -⟩
    · exact h1 ⟨pre, cW, (parseFirst4_congr (hcg g) _ _ _).mp hp⟩
    · exact h2 ⟨pre, cW, c3, c', (parseSecond4_congr (hcg g) _ _ _ _ _).mp hp⟩
    · exact h3 ⟨pre, cW, c3, c', tt, v, (parseThird4_congr (hcg g) _ _ _ _ _ _ _).mp hp⟩

/-- **A fresh query is bad with probability at most
`(7 |H| + 6) / 2^256 + listFactor4 · roundError`.** -/
theorem prob_listBad4 (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBad4 W K (histOf c) t.1 (tableOf c g)] ≤
      ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll4 c t ht) (prob_round4 W K hS₀ c t ht))

end Probability

/-! ## The run, the experiment -/

/-- **A run**: the adversary's reduction proof and the rest of what it outputs (the parts' two
values, the openings), the chain's challenges, and what the verifier computes after the chain. -/
structure Run4 (F O β : Type) where
  proof : RootProof4 F
  rest : O
  chals : Chals F
  out : β

variable {O β : Type}

/-- **The run**: the adversary, the chain on its reduction proof, then `post` (the openings, any
computation of the hash). -/
def rootRun4 (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) :
    OracleComp HashSpec (Run4 F O β) :=
  A >>= fun p => chainWith4 W hashQuery p.1 >>= fun ch => post p ch >>= fun b =>
    pure ⟨p.1, p.2, ch, b⟩

/-- **The experiment**: the run, with the transcript of every query. -/
def rootExperiment4 (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) :
    OracleComp HashSpec (Run4 F O β × Transcript) :=
  logged (rootRun4 W A post)

/-- **What wins**: some candidate of each of the four roots, read off the transcript, satisfy the
claims the verifier checks at the chain's challenges (the parts' assembled), while the witness
candidate's cells fail the relation for the statement. -/
def ListWins4 (z : Run4 F O β × Transcript) : Prop :=
  ∃ g ∈ K.CW.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rW,
    ∃ h ∈ K.CH.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rH,
      ∃ q ∈ K.CQ.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rQ,
        ∃ gg ∈ K.CG.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rG,
          P.Accepts (W.decode z.1.proof.stmt) g.1 (K.asm h q gg).1 z.1.chals.α z.1.chals.β
              z.1.chals.γ z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ ∧
            ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)

/-! ## An accepted run of a false statement makes a fresh query bad -/

section Trace

theorem chain4_queryBound (π : RootProof4 F) : IsTotalQueryBound (chainWith4 W hashQuery π) 6 := by
  simp only [chainWith4, hashQuery]
  repeat' (first | trivial | refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩)

theorem rootRun4_queryBound (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (rootRun4 W A post) (Q + 6 + QV) := by
  have h : ∀ p : RootProof4 F × O, IsTotalQueryBound (chainWith4 W hashQuery p.1 >>= fun ch =>
      post p ch >>= fun b => (pure ⟨p.1, p.2, ch, b⟩ : OracleComp HashSpec (Run4 F O β)))
        (6 + (QV + 0)) :=
    fun p => isTotalQueryBound_bind (chain4_queryBound W p.1) fun ch =>
      isTotalQueryBound_bind (hV p ch) fun b =>
        (trivial : IsTotalQueryBound (pure ⟨p.1, p.2, ch, b⟩ : OracleComp HashSpec (Run4 F O β)) 0)
  have := isTotalQueryBound_bind hQ h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

theorem rootExperiment4_queryBound (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (rootExperiment4 W A post) (Q + 6 + QV) :=
  isTotalQueryBound_logged_run _ _ _ (rootRun4_queryBound W A post Q QV hQ hV)

/-- The run against a table: the adversary's output, the chain's challenges, the verdict after,
and the chain's six inputs between the adversary's queries and the openings'. -/
theorem rootRun4_run (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (T : Table) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := labelOf4 W p.1.pre
    let x₁ := afterW W (T x₀) p.1.comW
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := afterHQG W (T x₃) p.1.comHQG
    let x₅ := W.afterValues (T x₄) p.1.v
    let ch : Chals F := ⟨W.chal (T x₁), W.chal (T x₂), W.chal (T x₃), W.chal (T x₄), W.chal (T x₅)⟩
    (tableQueryLog (rootRun4 W A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ([x₀, x₁, x₂, x₃, x₄, x₅] ++ (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (rootRun4 W A post) =
        ⟨p.1, p.2, ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch)⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅ ch
  constructor
  · simp only [rootRun4, chainWith4, hashQuery, tableQueryLog_bind, tableQueryLog_pure,
      List.map_append, List.append_nil, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl
  · simp only [rootRun4, chainWith4, hashQuery, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- The experiment against a table: the run's result and its transcript. -/
theorem rootExperiment4_run (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (T : Table) :
    tableQueryLog (rootExperiment4 W A post) T = tableQueryLog (rootRun4 W A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (rootExperiment4 W A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (rootRun4 W A post),
          (tableQueryLog (rootRun4 W A post) T).map fun q => (q.1, q.2)) := by
  refine ⟨log_logged_run T _ [], ?_⟩
  have := eval_logged_run T (rootRun4 W A post) []
  rw [List.nil_append] at this
  exact this

/-- No collision makes the order of the queries the order of what they refer to. -/
theorem refers4_before {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBad4 W K) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, Refers4 z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBad4 W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4 W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

/-- **After a root is absorbed, its candidates are the ones the history already fixed**: on a log
without a bad fresh query, if `y` (asked) refers to `r` and comes no later than `z`, the
candidates of `r` read off the whole log are those read off the inputs before `z`. -/
theorem stab4 {L : List (List UInt8)} {T : Table}
    (hord : ∀ y ∈ L, ∀ z ∈ L, Refers4 z (T y) → y ∈ before L z)
    {M : Type} (C : ListCommit M) (r : Bytes32) (y z : List UInt8) (hy : y ∈ L)
    (hry : Refers4 y r) (hyz : y = z ∨ y ∈ before L z) :
    C.cands L.toFinset T r = C.cands (before L z) T r := by
  have hsub : ∀ w, w ∈ before L y → w ∈ before L z := by
    rcases hyz with rfl | h
    · exact fun w hw => hw
    · exact fun w hw => before_subset_of_mem L y z h hw
  refine C.stable (before L z) L.toFinset T r (fun w hw => List.mem_toFinset.mpr
    (mem_of_mem_before L w z hw)) (fun w hw hwr => ?_) (fun y' hy' w hw h => ?_)
  · rw [← hwr] at hry
    exact hsub w (hord w (List.mem_toFinset.mp hw) y hy hry)
  · exact before_subset_of_mem L y' z hy' (hord w (List.mem_toFinset.mp hw) y'
      (mem_of_mem_before L y' z hy') (Or.inl h))

open Classical in
/-- **The trace, on a log**: if the log holds the chain's six inputs, and some candidates of the
four roots, read off the log, satisfy the verifier's claims at the chain's challenges while the
witness candidate's cells fail the relation, then some fresh input of the log is bad. -/
theorem trace_core4 (L : List (List UInt8)) (T : Table) (π : RootProof4 F) (g : B.Msg₁)
    (h : MH) (q : MQ) (gg : MG) :
    let x₀ := labelOf4 W π.pre
    let x₁ := afterW W (T x₀) π.comW
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := afterHQG W (T x₃) π.comHQG
    let x₅ := W.afterValues (T x₄) π.v
    (∀ y ∈ [x₀, x₁, x₂, x₃, x₄, x₅], y ∈ L) → g ∈ K.CW.cands L.toFinset T π.rW →
      h ∈ K.CH.cands L.toFinset T π.rH → q ∈ K.CQ.cands L.toFinset T π.rQ →
      gg ∈ K.CG.cands L.toFinset T π.rG →
      P.Accepts (W.decode π.stmt) g.1 (K.asm h q gg).1 (W.chal (T x₁)) (W.chal (T x₂))
        (W.chal (T x₃)) (W.chal (T x₄)) π.v.1 π.v.2 (W.chal (T x₅)) →
      ¬ P.Sat (W.decode π.stmt) (P.cells g.1) → FreshBad (listBad4 W K) T ∅ L := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ mem hg hh hq hgg hacc hsat
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBad4 W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4 W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
    intro y hy z hz hyz
    by_contra hne
    rcases before_trichotomy L y z hy hz hne with h | h
    · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
    · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))
  have hord := refers4_before W K hnb
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  have m0 := mem x₀ (by simp)
  have m1 := mem x₁ (by simp)
  have m2 := mem x₂ (by simp)
  have m3 := mem x₃ (by simp)
  have m4 := mem x₄ (by simp)
  have m5 := mem x₅ (by simp)
  have take32 : ∀ st : Bytes32, st.toList.take 32 = st.toList := fun st =>
    List.take_of_length_le (by simp)
  -- The chain's inputs come in their order.
  have b01 : x₀ ∈ before L x₁ := hord x₀ m0 x₁ m1 (Or.inl (Or.inl (take_afterW W _ _).symm))
  have b12 : x₁ ∈ before L x₂ := hord x₁ m1 x₂ m2 (Or.inl (Or.inl (take32 _).symm))
  have b23 : x₂ ∈ before L x₃ := hord x₂ m2 x₃ m3 (Or.inl (Or.inl (take32 _).symm))
  have b34 : x₃ ∈ before L x₄ := hord x₃ m3 x₄ m4 (Or.inl (Or.inl (take_afterHQG W _ _).symm))
  have b45 : x₄ ∈ before L x₅ := hord x₄ m4 x₅ m5 (Or.inl (Or.inl (W.take_afterValues _ _).symm))
  have s12 := before_subset_of_mem L x₁ x₂ b12
  have s23 := before_subset_of_mem L x₂ x₃ b23
  have s34 := before_subset_of_mem L x₃ x₄ b34
  have s45 := before_subset_of_mem L x₄ x₅ b45
  have c04 : x₀ ∈ before L x₄ := s34 (s23 (s12 b01))
  have c14 : x₁ ∈ before L x₄ := s34 (s23 b12)
  have c24 : x₂ ∈ before L x₄ := s34 b23
  -- The roots the chain absorbs.
  have hrW : Refers4 x₁ π.rW := Or.inr (Or.inl (rootPart_afterW W (T x₀) π.comW).symm)
  have hrH : Refers4 x₄ π.rH := Or.inr (Or.inl (rootPart_afterHQG₁ W (T x₃) π.comHQG).symm)
  have hrQ : Refers4 x₄ π.rQ := Or.inr (Or.inr (Or.inl (rootPart_afterHQG₂ W (T x₃) π.comHQG).symm))
  have hrG : Refers4 x₄ π.rG := Or.inr (Or.inr (Or.inr (rootPart_afterHQG₃ W (T x₃) π.comHQG).symm))
  have g1 : g ∈ K.CW.cands (before L x₁) T π.rW := by
    rwa [stab4 hord K.CW π.rW x₁ x₁ m1 hrW (Or.inl rfl)] at hg
  have g4 : g ∈ K.CW.cands (before L x₄) T π.rW := by
    rwa [stab4 hord K.CW π.rW x₁ x₄ m1 hrW (Or.inr c14)] at hg
  have g5 : g ∈ K.CW.cands (before L x₅) T π.rW := by
    rwa [stab4 hord K.CW π.rW x₁ x₅ m1 hrW (Or.inr (s45 c14))] at hg
  have R4 : K.asm h q gg ∈ K.quot (before L x₄) T π.rH π.rQ π.rG := by
    refine K.mem_quot.mpr ⟨h, ?_, q, ?_, gg, ?_, rfl⟩
    · rwa [stab4 hord K.CH π.rH x₄ x₄ m4 hrH (Or.inl rfl)] at hh
    · rwa [stab4 hord K.CQ π.rQ x₄ x₄ m4 hrQ (Or.inl rfl)] at hq
    · rwa [stab4 hord K.CG π.rG x₄ x₄ m4 hrG (Or.inl rfl)] at hgg
  have R5 : K.asm h q gg ∈ K.quot (before L x₅) T π.rH π.rQ π.rG := by
    refine K.mem_quot.mpr ⟨h, ?_, q, ?_, gg, ?_, rfl⟩
    · rwa [stab4 hord K.CH π.rH x₄ x₅ m4 hrH (Or.inr b45)] at hh
    · rwa [stab4 hord K.CQ π.rQ x₄ x₅ m4 hrQ (Or.inr b45)] at hq
    · rwa [stab4 hord K.CG π.rG x₄ x₅ m4 hrG (Or.inr b45)] at hgg
  -- The round that F1's trace names.
  let π' : Proof P B := ⟨W.decode π.stmt, g, K.asm h q gg, π.v⟩
  let tbl : ∀ k, Answer P B k := fun k => match k with
    | .first .. => (W.chal (T x₁), W.chal (T x₂), W.chal (T x₃))
    | .second .. => W.chal (T x₄)
    | .third .. => W.chal (T x₅)
  rcases bad_of_accepts π' tbl hacc hsat with hb | hb | hb
  · obtain ⟨h1, h2⟩ := hb
    refine nb x₁ m1 (Or.inr (Or.inl ⟨π.pre, π.comW, ⟨T x₀, ⟨b01, rfl⟩, rfl, injB x₁⟩,
      ⟨fun h => not_mem_before_of_mem_before b12 h, fun h => ?_, fun h => ?_, g, g1, h1, h2⟩⟩))
    · exact not_mem_before_of_mem_before (s23 b12) h
    · have e : x₃ = x₂ := h
      rw [e] at b23
      exact not_mem_before_self L x₂ b23
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₄ m4 (Or.inr (Or.inr (Or.inl ⟨π.pre, π.comW, π.comHQG, _, ⟨T x₀, T x₁, T x₂, T x₃,
      ⟨c04, rfl⟩, ⟨c14, rfl⟩, ⟨c24, rfl⟩, ⟨b34, rfl⟩, rfl, rfl, injB x₄⟩, g, g4, _, R4, h1,
      h2⟩)))
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₅ m5 (Or.inr (Or.inr (Or.inr ⟨π.pre, π.comW, π.comHQG, _, _, π.v,
      ⟨T x₀, T x₁, T x₂, T x₃, T x₄, ⟨s45 c04, rfl⟩, ⟨s45 c14, rfl⟩, ⟨s45 c24, rfl⟩,
        ⟨s45 b34, rfl⟩, ⟨b45, rfl⟩, rfl, rfl, rfl, injB x₅⟩, g, g5, _, R5, h1, h2⟩)))

open Classical in
/-- **The trace**: on every table, a winning run asks a bad fresh query. -/
theorem trace_listBad4 (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (T : Table)
    (hwin : ListWins4 W K (evalWithAnswerFn (QueryImpl.ofFn T) (rootExperiment4 W A post))) :
    FreshBad (listBad4 W K) T ∅
      ((tableQueryLog (rootExperiment4 W A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := rootExperiment4_run W A post T
  obtain ⟨hL, heval⟩ := rootRun4_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  set L := (tableQueryLog (rootRun4 W A post) T).map Sigma.fst
  rw [hlogE]
  rw [hevalE, heval] at hwin
  set tr : Transcript := (tableQueryLog (rootRun4 W A post) T).map fun q => (q.1, q.2)
  have htrH : histOfTr tr = L.toFinset := by
    simp only [histOfTr, tr, L, List.map_map]
    rfl
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = T d := by
    intro d hd
    refine tableOfTr_eq T tr (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact tableQueryLog_snd T _ q hq
  obtain ⟨g, hg, h, hh, q, hq, gg, hgg, hacc, hsat⟩ := hwin
  simp only at hg hh hq hgg hacc hsat
  rw [K.CW.congr _ _ _ _ htrT, htrH] at hg
  rw [K.CH.congr _ _ _ _ htrT, htrH] at hh
  rw [K.CQ.congr _ _ _ _ htrT, htrH] at hq
  rw [K.CG.congr _ _ _ _ htrT, htrH] at hgg
  exact trace_core4 W K L T π g h q gg (fun y hy => by
    rw [hL]
    exact List.mem_append_right _ (List.mem_append_left _ hy)) hg hh hq hgg hacc hsat

end Trace

/-! ## Knowledge soundness with four real roots -/

/-- **The reduction's knowledge soundness with four real roots, union-bounded over the lists, in
the random-oracle model.** For every adversary making at most `Q` queries of the random oracle
`H : bytes → 32 bytes` that outputs a statement, four commitments, five values and anything else
(the parts' values, the openings), and every computation `post` after the chain of at most `QV`
queries (the openings' verifier), the probability that some candidates of the four roots (read off
the transcript of every query, by any list commitments) satisfy the verifier's claims at the
chain's challenges while the witness candidate's cells fail the relation is at most
`(Q + 6 + QV) (listFactor4 · roundError + 7 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_list4 (A : OracleComp HashSpec (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment4 W A post)).run' ∅}[ListWins4 W K z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad (rootExperiment4 W A post) (Q + 6 + QV)
    (rootExperiment4_queryBound W A post Q QV hQ hV) (Set.range fun v : Bytes32 => v.toList)
    (Set.finite_range _) (ListWins4 W K) (listBad4 W K) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_listBad4 W K A post T h)
  have hS' : ∀ v : Bytes32, v.toList ∈ S := fun v => hS _ ⟨v, rfl⟩
  refine (prob_listBad4 W K hS' c t ht).trans ?_
  have hcard' : (histOf c).card < Q + 6 + QV := by
    simpa [histOf, Finset.card_map] using hcard
  rw [add_comm]
  gcongr
  have : 7 * (histOf c).card + 6 ≤ 7 * (Q + 6 + QV) := by omega
  calc ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) ≤ ((7 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

end ComposePcs
