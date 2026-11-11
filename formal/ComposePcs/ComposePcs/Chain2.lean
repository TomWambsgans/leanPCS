-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/ComposePcs/ComposePcs/{ListChain4,Pinned4,TwoOracle4,AdversaryLog4}.lean` of this repository
-- (the chain, the parse, the bad events with each root's candidates pinned by its out-of-domain answer, the trace,
-- the two-oracle view, the roots answered after the adversary) and `formal/QuotientRpm/Uniform.lean` (uniform
-- challenges) to the deployed membership protocol (`pcs-quotient-kc3`, `docs/membership/PROTOCOL.md`): two
-- commitments, `W` and `T`, and the reduction of `formal/Kc3`. The generic lemmas of those files (pins,
-- `prEvent_pinned_le`, collisions, `stab4`, the fresh-query engine) are reused as they are.
import ComposePcs.Pinned4
import Kc3.Protocol

/-!
# The two-root chain of the deployed protocol, each root's candidates pinned by its out-of-domain answer

The membership proof carries **two commitments**, each a Merkle root and its out-of-domain answer: the witness
table `W`, then the quotient table `T`; then the four values (`X`, `C`, `V + Y` at `t`, and `next`). The chain
(`chainWith2`, `formal/Statement/PcsQuotient/Reduction.lean`'s `reduceWith`) hashes

* the label (`labelOf2`, 136 bytes): the tag `pcs-quotient-kc3`, the circuit's commitment (its root, then its
  out-of-domain answer as 24 bytes), the statement's 64 bytes; `st₀`;
* `st₀ ‖ commitment W` (128 bytes): `st₁`, giving `α`; `st₂ = H(st₁)`, `β`; `st₃ = H(st₂)`, `μ`;
* `st₃ ‖ commitment T` (128 bytes): `st₄`, giving `t`;
* `st₄ ‖ X ‖ C ‖ (V + Y) ‖ next` (160 bytes): `st₅`, giving `ρ`.

The two commitments' inputs have one length; they are told apart by the chain (an injective history: `st₀` is the
label's answer, `st₃` a 32-byte state's). **The rounds** are `formal/Kc3`'s (`Kc3.Params.State₁ … State₆`); their
counts (`RoundsSound`, `Kc3/Rounds.lean`'s `card_round1_le`, `card_round2_le`, `card_round3_le`) give each fresh
chain query's error `roundError`. **`prob_listBad2P`**: a fresh query is bad with probability at most
`(7 |H| + 6) / 2^256 + roundError`; **`trace_core2P`**: a log holding the chain's inputs with pinned candidates of
the two roots satisfying the verifier's decision while the witness fails the relation has a bad fresh input;
**`prob_advBad2P`**: the same in mumbai's two-oracle model with the roots answered after the adversary
(`2 / 2^256`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm Kc3 Kc3.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-! ## The wire -/

/-- The transcript's tag, the label's first sixteen bytes: `b"pcs-quotient-kc3"` in ASCII
(`quotient::protocol::NAME`). -/
def tag3 : List UInt8 :=
  [0x70, 0x63, 0x73, 0x2d, 0x71, 0x75, 0x6f, 0x74, 0x69, 0x65, 0x6e, 0x74, 0x2d, 0x6b, 0x63, 0x33]

theorem length_tag3 : tag3.length = 16 := rfl

/-- **What the chain reads besides the proof**: how the statement's 64 bytes are read as the eleven pinned values
(`decode`), and how a field element is held as limbs (`limbs`, `F192`'s `(c0, c1, c2)`). -/
structure Wire2 (P : Kc3.Params F) where
  decode : Vector UInt8 64 → Stmt F
  limbs : F ≃ Limbs

variable {P : Kc3.Params F} (W : Wire2 P)

namespace Wire2

/-- A field element as the chain hashes it. -/
def word (x : F) : List UInt8 := scalarWord (W.limbs x)

/-- **A challenge**: the low 192 bits of the new state, as a field element. -/
def chal (st : Bytes32) : F := W.limbs.symm (stateLimbs st)

/-- The four values as the chain hashes them, in the order sent: `X`, `C`, `V + Y`, then `next`. -/
def valueWords (v : (Fin 3 → F) × F) : List UInt8 :=
  W.word (v.1 0) ++ W.word (v.1 1) ++ W.word (v.1 2) ++ W.word v.2

/-- The chain's input after the four values. -/
def afterValues (st : Bytes32) (v : (Fin 3 → F) × F) : List UInt8 := st.toList ++ W.valueWords v

theorem word_injective : Function.Injective W.word := fun _ _ h =>
  W.limbs.injective (scalarWord_injective h)

@[simp] theorem length_word (x : F) : (W.word x).length = 32 := by simp [Wire2.word]

theorem valueWords_injective : Function.Injective W.valueWords := by
  intro a b h
  simp only [Wire2.valueWords] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp)
  have e0 := W.word_injective h0
  have e1 := W.word_injective h1
  have e2 := W.word_injective h2
  have e3 := W.word_injective h3
  refine Prod.ext (funext fun i => ?_) e3
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

@[simp] theorem length_afterValues (st : Bytes32) (v : (Fin 3 → F) × F) :
    (W.afterValues st v).length = 160 := by
  simp [Wire2.afterValues, Wire2.valueWords]

theorem take_afterValues (st : Bytes32) (v : (Fin 3 → F) × F) :
    (W.afterValues st v).take 32 = st.toList := by
  simp [Wire2.afterValues, List.take_append]

theorem afterValues_injective {st st' : Bytes32} {v v' : (Fin 3 → F) × F}
    (h : W.afterValues st v = W.afterValues st' v') : st = st' ∧ v = v' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, W.valueWords_injective h2⟩

/-- The low 192 bits of a state, as limbs, have `256^8` states each. -/
theorem chal_fiber (x : F) :
    (Finset.univ.filter fun st : Bytes32 => W.chal st = x).card =
      (Finset.univ : Finset (Vector UInt8 8)).card := by
  have h : (Finset.univ.filter fun st : Bytes32 => W.chal st = x) =
      Finset.univ.filter fun st : Bytes32 => stateLimbs st = W.limbs x :=
    Finset.filter_congr fun st _ => by simp only [Wire2.chal, Equiv.symm_apply_eq]
  rw [h]
  exact stateLimbs_fiber (W.limbs x)

/-- **The low 192 bits of a uniform state are uniform.** -/
theorem prEvent_chal (p : F → Prop) :
    Pr{let st ← $ᵗ Bytes32}[p (W.chal st)] = Pr{let x ← $ᵗ F}[p x] := by
  classical
  exact prEvent_uniform_balanced W.chal _ W.chal_fiber p

/-- The three challenges of three uniform states are uniform. -/
theorem prEvent_chal₃ (p : F × F × F → Prop) :
    Pr{let s ← $ᵗ (Bytes32 × Bytes32 × Bytes32)}[p (W.chal s.1, W.chal s.2.1, W.chal s.2.2)] =
      Pr{let c ← $ᵗ (F × F × F)}[p c] := by
  classical
  have h2 := card_fiber_prod W.chal W.chal _ _ W.chal_fiber W.chal_fiber
  have h3 := card_fiber_prod W.chal (fun s : Bytes32 × Bytes32 => (W.chal s.1, W.chal s.2)) _ _
    W.chal_fiber h2
  exact prEvent_uniform_balanced (fun s : Bytes32 × Bytes32 × Bytes32 =>
    (W.chal s.1, W.chal s.2.1, W.chal s.2.2)) _ h3 p

end Wire2

/-! ## The proof, the chain -/

/-- **A proof of the reduction with two real commitments**: the statement's 64 bytes, the two commitments (each a
root and its out-of-domain answer: the witness table's, the quotient table's), and the four values (`ReductionProof`
without the openings). The circuit's commitment (`ir`, `io`) is the setup's, not the prover's (the experiments that
compute it set it). -/
structure RootProof2 (F : Type) where
  stmt : Vector UInt8 64
  rW : Bytes32
  oW : F
  rT : Bytes32
  oT : F
  v : (Fin 3 → F) × F
  ir : Bytes32
  io : F

/-- The label's data. -/
def RootProof2.pre (π : RootProof2 F) : Pre F := (π.ir, π.io, π.stmt)

/-- The witness table's commitment. -/
def RootProof2.comW (π : RootProof2 F) : Com F := (π.rW, π.oW)

/-- The quotient table's commitment. -/
def RootProof2.comT (π : RootProof2 F) : Com F := (π.rT, π.oT)

/-- **The label** (`label`, `Reduction.lean`): the tag, the circuit's root, its out-of-domain answer as 24 bytes,
the statement's 64 bytes. -/
def labelOf2 (pre : Pre F) : List UInt8 :=
  tag3 ++ pre.1.toList ++ (W.word pre.2.1).drop 8 ++ pre.2.2.toList

/-- A commitment as the chain hashes it: the root's half-words, then the out-of-domain answer's word. -/
def commitWords2 (c : Com F) : List UInt8 := halfWords c.1 ++ W.word c.2

/-- The chain's input after a commitment: the state, then the commitment's words. -/
def afterC (st : Bytes32) (c : Com F) : List UInt8 := st.toList ++ commitWords2 W c

/-- **The chain** of `reduceWith` over a hash `H` in any monad: the label; `W`'s commitment after the seed; two
more states; `T`'s commitment; the values. -/
def chainWith2 {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) (π : RootProof2 F) :
    m (Chals F) := do
  let st₀ ← H (labelOf2 W π.pre)
  let st₁ ← H (afterC W st₀ π.comW)
  let st₂ ← H st₁.toList
  let st₃ ← H st₂.toList
  let st₄ ← H (afterC W st₃ π.comT)
  let st₅ ← H (W.afterValues st₄ π.v)
  pure ⟨W.chal st₁, W.chal st₂, W.chal st₃, W.chal st₄, W.chal st₅⟩

/-! ## The inputs determine what they absorb -/

section Bytes

theorem word2_eq_drop (x : F) : W.word x = List.replicate 8 0 ++ (W.word x).drop 8 := by
  simp [Wire2.word, scalarWord]

@[simp] theorem length_labelOf2 (pre : Pre F) : (labelOf2 W pre).length = 136 := by
  simp [labelOf2, length_tag3]

@[simp] theorem length_commitWords2 (c : Com F) : (commitWords2 W c).length = 96 := by
  simp [commitWords2]

@[simp] theorem length_afterC (st : Bytes32) (c : Com F) : (afterC W st c).length = 128 := by
  simp [afterC]

theorem labelOf2_injective {pre pre' : Pre F} (h : labelOf2 W pre = labelOf2 W pre') : pre = pre' := by
  obtain ⟨ir, io, sb⟩ := pre
  obtain ⟨ir', io', sb'⟩ := pre'
  simp only [labelOf2, List.append_assoc, List.append_cancel_left_eq] at h
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  have e : W.word io = W.word io' := by rw [word2_eq_drop W io, word2_eq_drop W io', h2]
  rw [Vector.toList_inj.mp h1, W.word_injective e, Vector.toList_inj.mp h3]

theorem commitWords2_injective {c c' : Com F} (h : commitWords2 W c = commitWords2 W c') : c = c' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact Prod.ext (halfWords_injective h1) (W.word_injective h2)

theorem afterC_injective {st st' : Bytes32} {c c' : Com F} (h : afterC W st c = afterC W st' c') :
    st = st' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, commitWords2_injective W h2⟩

theorem take_afterC (st : Bytes32) (c : Com F) : (afterC W st c).take 32 = st.toList := by
  simp [afterC]

theorem rootPart_afterC (st : Bytes32) (c : Com F) :
    ((afterC W st c).drop 32).take 64 = halfWords c.1 := by
  simp [afterC, commitWords2]

end Bytes

/-! ## The bad events -/

/-- `x` is the input after the witness table's commitment `cW`, for the label's data `pre`. -/
def ParseFirst2 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) : Prop :=
  ∃ st₀, Has H T (labelOf2 W pre) st₀ ∧ x = afterC W st₀ cW ∧ Set.InjOn T ↑H

/-- `x` is the input after the quotient table's commitment: the chain before it was asked, without collision, and
gave the first challenges `c`. -/
def ParseSecond2 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW cT : Com F) (c : F × F × F) :
    Prop :=
  ∃ st₀ st₁ st₂ st₃, Has H T (labelOf2 W pre) st₀ ∧ Has H T (afterC W st₀ cW) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ x = afterC W st₃ cT ∧
    c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ Set.InjOn T ↑H

/-- `x` is the input after the four values: the chain before it was asked, without collision, and gave the
challenges `c` and `t`. -/
def ParseThird2 (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW cT : Com F) (c : F × F × F)
    (t : F) (v : (Fin 3 → F) × F) : Prop :=
  ∃ st₀ st₁ st₂ st₃ st₄, Has H T (labelOf2 W pre) st₀ ∧ Has H T (afterC W st₀ cW) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ Has H T (afterC W st₃ cT) st₄ ∧
    x = W.afterValues st₄ v ∧ c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ t = W.chal st₄ ∧
    Set.InjOn T ↑H

/-- **The two roots' pins**: the inputs `zin` they read (never a chain input: no `32`, `128` or `160` bytes),
`W`'s and `T`'s, F1's first message read off `W`'s object, F1's second message off `T`'s. -/
structure Pins2 (P : Kc3.Params F) (NW NT : Type) where
  zin : List UInt8 → Prop
  zin_len : ∀ x, zin x → x.length ≠ 32 ∧ x.length ≠ 128 ∧ x.length ≠ 160
  pW : Pin zin F NW
  pT : Pin zin F NT
  rdW : NW → P.Msg₁
  rdT : NT → P.Msg₂

variable {NW NT : Type} (K : Pins2 P NW NT)

/-- **The pinned pair**: a pinned candidate of each root, each root's only one. -/
def Pins2.Tup (H : Hist) (T : Table) (cW cT : Com F) (u : NW × NT) : Prop :=
  (K.pW.Mem H T cW.1 cW.2 u.1 ∧ K.pW.One H T cW.1 cW.2) ∧
    (K.pT.Mem H T cT.1 cT.2 u.2 ∧ K.pT.One H T cT.1 cT.2)

theorem Pins2.tup_unique {H : Hist} {T : Table} {cW cT : Com F} {u u' : NW × NT}
    (h : K.Tup H T cW cT u) (h' : K.Tup H T cW cT u') : u = u' := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := h
  obtain ⟨⟨a1', -⟩, ⟨b1', -⟩⟩ := h'
  exact Prod.ext (a2 _ _ a1 a1') (b2 _ _ b1 b1')

theorem Pins2.tup_congr {H : Hist} {T T' : Table} {cW cT : Com F} {u : NW × NT}
    (hH : ∀ d ∈ H, T d = T' d) (hz : ∀ x, K.zin x → T x = T' x) :
    K.Tup H T cW cT u ↔ K.Tup H T' cW cT u := by
  unfold Pins2.Tup
  rw [K.pW.mem_congr hH hz, K.pW.one_congr hH hz, K.pT.mem_congr hH hz, K.pT.one_congr hH hz]

/-- The triple the input after `W`'s commitment leads to, its states not asked before, makes the first round's
state go from lost to won for **the** pinned candidate of `W`'s root. -/
def FreshFirst2P (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) : Prop :=
  (T x).toList ∉ H ∧ (T (T x).toList).toList ∉ H ∧ (T (T x).toList).toList ≠ (T x).toList ∧
    ∃ n, (K.pW.Mem H T cW.1 cW.2 n ∧ K.pW.One H T cW.1 cW.2) ∧ ¬ State₁ (W.decode pre.2.2) (K.rdW n) ∧
      State₂ (W.decode pre.2.2) (K.rdW n) (W.chal (T x), W.chal (T (T x).toList),
        W.chal (T (T (T x).toList).toList))

/-- The first round, for the pinned candidate. -/
def FirstBad2P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW, ParseFirst2 W H x T pre cW ∧ FreshFirst2P W K H x T pre cW

/-- The second round, for the pinned pair. -/
def SecondBad2P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW cT c, ParseSecond2 W H x T pre cW cT c ∧ ∃ u, K.Tup H T cW cT u ∧
    ¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c (K.rdT u.2) ∧
      State₄ (W.decode pre.2.2) (K.rdW u.1) c (K.rdT u.2) (W.chal (T x))

/-- The third round, for the pinned pair. -/
def ThirdBad2P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW cT c t v, ParseThird2 W H x T pre cW cT c t v ∧ ∃ u, K.Tup H T cW cT u ∧
    ¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c (K.rdT u.2) t ∧
      State₆ (W.decode pre.2.2) (K.rdW u.1) c (K.rdT u.2) t v (W.chal (T x))

/-- **A bad fresh query**, the candidates pinned: a collision (`Coll4`), or a round turned from lost to won. -/
def listBad2P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll4 H x T ∨ FirstBad2P W K H x T ∨ SecondBad2P W K H x T ∨ ThirdBad2P W K H x T

/-! ## The parse is unique, and reads only the history -/

section Parse

variable {W}

theorem parseFirst2_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x pre cW) :
    ParseFirst2 W H x T pre cW ↔ ParseFirst2 W H x T' pre cW := by
  simp only [ParseFirst2, has_congr h, injOn_congr h]

theorem parseSecond2_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x pre cW cT c) :
    ParseSecond2 W H x T pre cW cT c ↔ ParseSecond2 W H x T' pre cW cT c := by
  simp only [ParseSecond2, has_congr h, injOn_congr h]

theorem parseThird2_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x pre cW cT c t v) :
    ParseThird2 W H x T pre cW cT c t v ↔ ParseThird2 W H x T' pre cW cT c t v := by
  simp only [ParseThird2, has_congr h, injOn_congr h]

theorem parseFirst2_unique {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW'}
    (h : ParseFirst2 W H x T pre cW) (h' : ParseFirst2 W H x T pre' cW') : pre = pre' ∧ cW = cW' := by
  obtain ⟨st₀, h0, hx, hi⟩ := h
  obtain ⟨st₀', h0', hx', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := afterC_injective W (hx.symm.trans hx')
  exact ⟨labelOf2_injective W (has_inj hi h0 h0'), rfl⟩

theorem parseSecond2_unique {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW' cT cT' c c'}
    (h : ParseSecond2 W H x T pre cW cT c) (h' : ParseSecond2 W H x T pre' cW' cT' c') :
    pre = pre' ∧ cW = cW' ∧ cT = cT' ∧ c = c' := by
  obtain ⟨st₀, st₁, st₂, st₃, h0, h1, h2, h3, hx, hc, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', h0', h1', h2', h3', hx', hc', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := afterC_injective W (hx.symm.trans hx')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := afterC_injective W (has_inj hi h1 h1')
  exact ⟨labelOf2_injective W (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm⟩

theorem parseThird2_unique {H : Hist} {x : List UInt8} {T : Table}
    {pre pre' cW cW' cT cT' c c' t t' v v'}
    (h : ParseThird2 W H x T pre cW cT c t v) (h' : ParseThird2 W H x T pre' cW' cT' c' t' v') :
    pre = pre' ∧ cW = cW' ∧ cT = cT' ∧ c = c' ∧ t = t' ∧ v = v' := by
  obtain ⟨st₀, st₁, st₂, st₃, st₄, h0, h1, h2, h3, h4, hx, hc, ht, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', st₄', h0', h1', h2', h3', h4', hx', hc', ht', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := W.afterValues_injective (hx.symm.trans hx')
  obtain ⟨rfl, rfl⟩ := afterC_injective W (has_inj hi h4 h4')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := afterC_injective W (has_inj hi h1 h1')
  exact ⟨labelOf2_injective W (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm, ht.trans ht'.symm, rfl⟩

/-- The first and the second inputs have one length (`128`), but the chain tells them apart: the state before the
first is the label's answer, the state before the second a 32-byte state's, and the history is injective. -/
theorem parseFirst2_parseSecond2 {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW' cT c}
    (h : ParseFirst2 W H x T pre cW) (h' : ParseSecond2 W H x T pre' cW' cT c) : False := by
  obtain ⟨st₀, h0, hx, hi⟩ := h
  obtain ⟨_, _, st₂, st₃, _, _, _, h3, hx', _, _⟩ := h'
  obtain ⟨rfl, -⟩ := afterC_injective W (hx.symm.trans hx')
  have := congrArg List.length (has_inj hi h0 h3)
  simp at this

theorem parseFirst2_parseThird2 {H : Hist} {x : List UInt8} {T : Table} {pre pre' cW cW' cT c t v}
    (h : ParseFirst2 W H x T pre cW) (h' : ParseThird2 W H x T pre' cW' cT c t v) : False := by
  obtain ⟨_, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

theorem parseSecond2_parseThird2 {H : Hist} {x : List UInt8} {T : Table}
    {pre pre' cW cW' cT cT' c c' t v}
    (h : ParseSecond2 W H x T pre cW cT c) (h' : ParseThird2 W H x T pre' cW' cT' c' t v) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

end Parse

/-! ## The rounds' errors -/

attribute [local instance] Classical.propDecidable

/-- **The rounds' counts** (`formal/Kc3`'s `card_round1_le`, `card_round2_le`, `card_round3_le`, stated on the
states): each challenge turns a lost state into a won one for at most `E1 · q²` triples, `E1` values of `t`, `E1`
values of `ρ`. -/
structure RoundsSound (P : Kc3.Params F) : Prop where
  first : ∀ (stmt : Stmt F) (g : P.Msg₁), ¬ State₁ stmt g →
    (Finset.univ.filter fun c : F × F × F => State₂ stmt g c).card ≤ P.E1 * Fintype.card F ^ 2
  second : ∀ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂), ¬ State₃ stmt g c R →
    (Finset.univ.filter fun t : F => State₄ stmt g c R t).card ≤ P.E1 * Fintype.card F ^ 0
  third : ∀ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (t : F) (v : (Fin 3 → F) × F),
    ¬ State₄ stmt g c R t →
      (Finset.univ.filter fun ρ : F => State₆ stmt g c R t v ρ).card ≤ P.E1 * Fintype.card F ^ 0

theorem roundError_eq_coe : P.roundError =
    (((P.E1 : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  have hq : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div hq]
  rfl

variable (hR : RoundsSound P)
include hR

/-- The first round's error, for the three challenges read off three uniform states. -/
theorem prob_first_chain2 (stmt : Stmt F) (g : P.Msg₁) :
    Pr{let s ← $ᵗ (Bytes32 × Bytes32 × Bytes32)}[¬ State₁ stmt g ∧
      State₂ stmt g (W.chal s.1, W.chal s.2.1, W.chal s.2.2)] ≤ P.roundError := by
  rw [W.prEvent_chal₃ (fun c => ¬ State₁ stmt g ∧ State₂ stmt g c), SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card (F × F × F) : ENNReal) = ((Fintype.card F ^ (2 + 1) : ℕ) : ENNReal) := by
    rw [Fintype.card_prod, Fintype.card_prod]; push_cast; ring
  rw [hcard, roundError_eq_coe]
  refine QuotientSecurity.card_div_le Fintype.card_pos ?_
  by_cases hs : State₁ stmt g
  · simp [hs]
  · refine le_trans (Finset.card_le_card fun c hc => ?_) (hR.first stmt g hs)
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.2⟩

/-- The second round's error, for the challenge read off a uniform state. -/
theorem prob_second_chain2 (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) :
    Pr{let s ← $ᵗ Bytes32}[¬ State₃ stmt g c R ∧ State₄ stmt g c R (W.chal s)] ≤ P.roundError := by
  rw [W.prEvent_chal (fun t => ¬ State₃ stmt g c R ∧ State₄ stmt g c R t), SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card F : ENNReal) = ((Fintype.card F ^ (0 + 1) : ℕ) : ENNReal) := by simp
  rw [hcard, roundError_eq_coe]
  refine QuotientSecurity.card_div_le Fintype.card_pos ?_
  by_cases hs : State₃ stmt g c R
  · simp [hs]
  · refine le_trans (Finset.card_le_card fun t ht => ?_) (hR.second stmt g c R hs)
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, ht.2.2⟩

/-- The third round's error, for the challenge read off a uniform state. -/
theorem prob_third_chain2 (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (t : F)
    (v : (Fin 3 → F) × F) :
    Pr{let s ← $ᵗ Bytes32}[¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v (W.chal s)] ≤ P.roundError := by
  rw [W.prEvent_chal (fun ρ => ¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v ρ),
    SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card F : ENNReal) = ((Fintype.card F ^ (0 + 1) : ℕ) : ENNReal) := by simp
  rw [hcard, roundError_eq_coe]
  refine QuotientSecurity.card_div_le Fintype.card_pos ?_
  by_cases hs : State₄ stmt g c R t
  · simp [hs]
  · refine le_trans (Finset.card_le_card fun ρ hρ => ?_) (hR.third stmt g c R t v hs)
    rw [Finset.mem_filter] at hρ ⊢
    exact ⟨Finset.mem_univ _, hρ.2.2⟩

omit hR in
/-- **An accepted transcript of a false statement makes one round bad.** -/
theorem bad_of_accepts2 (stmt : Stmt F) (g : P.Msg₁) (R : P.Msg₂) (c : F × F × F) (t : F)
    (v : (Fin 3 → F) × F) (ρ : F) (hacc : P.Accepts stmt g.1 R.1 c.1 c.2.1 c.2.2 t v.1 v.2 ρ)
    (hsat : ¬ P.Sat stmt (P.cells g.1)) :
    (¬ State₁ stmt g ∧ State₂ stmt g c) ∨ (¬ State₃ stmt g c R ∧ State₄ stmt g c R t) ∨
      (¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v ρ) := by
  by_cases h2 : State₂ stmt g c
  · exact Or.inl ⟨hsat, h2⟩
  · have h3 : ¬ State₃ stmt g c R := by
      rintro (h | h)
      · exact h2 (Or.inl h)
      · exact h2 (Or.inr ⟨_, h⟩)
    by_cases h4 : State₄ stmt g c R t
    · exact Or.inr (Or.inl ⟨h3, h4⟩)
    · exact Or.inr (Or.inr ⟨h4, Or.inr hacc⟩)

/-! ## Each fresh query is bad with probability at most the round error -/

section Probability

variable {S : Finset (List UInt8)}

/-- The first round's fresh part, for one candidate, has probability at most the round error. -/
theorem prob_freshFirst2_one (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) (hlen : t.1.length = 128) (sb : Vector UInt8 64) (gm : P.Msg₁) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[(tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode sb) gm ∧
      State₂ (W.decode sb) gm (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList))] ≤ P.roundError := by
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
    exact prob_first_chain2 W hR (W.decode sb) gm

/-- **The rounds' bad events, the candidates pinned, have probability at most the round error**: the parse is read
off the history; the answers at the out-of-domain inputs fix the pinned candidate (pair), and the answers the round
reads are uniform. -/
theorem prob_round2P (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FirstBad2P W K (histOf c) t.1 (tableOf c g) ∨
      SecondBad2P W K (histOf c) t.1 (tableOf c g) ∨ ThirdBad2P W K (histOf c) t.1 (tableOf c g)] ≤
      P.roundError := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  have hhA : ∀ g g' : ↥S → Bytes32, ∀ d ∈ histOf c, tableOf c g d = tableOf c g' d := fun g g' _ hd =>
    tableOf_eq_of_mem c hd g g'
  have hzA : ∀ g g' : ↥S → Bytes32, (∀ x : ↥S, K.zin x.1 → g x = g' x) →
      ∀ x, K.zin x → tableOf c g x = tableOf c g' x := fun g g' h x hx => tableOf_agree c (Z := K.zin) h hx
  have hnz : ∀ y : List UInt8, (y.length = 32 ∨ y.length = 128 ∨ y.length = 160) → ¬ K.zin y :=
    fun y hy hz => by
      have := K.zin_len y hz
      omega
  have h32 : ∀ v : Bytes32, ¬ K.zin v.toList := fun v => hnz _ (Or.inl (by simp))
  by_cases h1 : ∃ pre cW, ParseFirst2 W (histOf c) t.1 (tableOf c g₀) pre cW
  · obtain ⟨pre, cW, hp⟩ := h1
    have hlen : t.1.length = 128 := by
      obtain ⟨st₀, -, hx, -⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ n, (K.pW.Mem (histOf c) (tableOf c g) cW.1 cW.2 n ∧
      K.pW.One (histOf c) (tableOf c g) cW.1 cW.2) ∧ ((tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode pre.2.2) (K.rdW n) ∧
      State₂ (W.decode pre.2.2) (K.rdW n) (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', hf⟩ | ⟨pre', cW', cT', c', hp', -⟩ |
        ⟨pre', cW', cT', c', tt, v, hp', -⟩
      · rw [parseFirst2_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl⟩ := parseFirst2_unique hp' hp
        obtain ⟨f1, f2, f3, n, hn, f4, f5⟩ := hf
        exact ⟨n, hn, f1, f2, f3, f4, f5⟩
      · rw [parseSecond2_congr (hcg g)] at hp'
        exact (parseFirst2_parseSecond2 hp hp').elim
      · rw [parseThird2_congr (hcg g)] at hp'
        exact (parseFirst2_parseThird2 hp hp').elim
    · refine prEvent_pinned_le K.zin _ _ _ (fun n g g' h hn => ?_) (fun n g g' h hb => ?_)
        (fun n n' g hn hn' => hn.2 n n' hn.1 hn'.1)
        (fun n => prob_freshFirst2_one W hR hS₀ c t ht hlen pre.2.2 (K.rdW n))
      · exact ⟨(K.pW.mem_congr (hhA g g') (hzA g g' h)).mp hn.1,
          (K.pW.one_congr (hhA g g') (hzA g g' h)).mp hn.2⟩
      · have e1 : tableOf c g t.1 = tableOf c g' t.1 :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (hnz _ (Or.inr (Or.inl hlen)))
        have e2 : tableOf c g (tableOf c g' t.1).toList = tableOf c g' (tableOf c g' t.1).toList :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (h32 _)
        have e3 : tableOf c g (tableOf c g' (tableOf c g' t.1).toList).toList =
            tableOf c g' (tableOf c g' (tableOf c g' t.1).toList).toList :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (h32 _)
        obtain ⟨f1, f2, f3, f4, f5⟩ := hb
        rw [e1] at f1 f2 f3 f5
        rw [e2] at f2 f3 f5
        rw [e3] at f5
        exact ⟨f1, f2, f3, f4, f5⟩
  by_cases h2 : ∃ pre cW cT c', ParseSecond2 W (histOf c) t.1 (tableOf c g₀) pre cW cT c'
  · obtain ⟨pre, cW, cT, c', hp⟩ := h2
    have hlen : t.1.length = 128 := by
      obtain ⟨_, _, _, _, _, _, _, _, hx, _⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ u, K.Tup (histOf c) (tableOf c g) cW cT u ∧
      (¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) ∧
        State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) (W.chal (g t))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', cT', c'', hp', u, hu, hf⟩ |
        ⟨pre', cW', cT', c'', tt, v, hp', -⟩
      · rw [parseFirst2_congr (hcg g)] at hp'
        exact (parseFirst2_parseSecond2 hp' hp).elim
      · rw [parseSecond2_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := parseSecond2_unique hp' hp
        rw [tableOf_fresh c ht g] at hf
        exact ⟨u, hu, hf⟩
      · rw [parseThird2_congr (hcg g)] at hp'
        exact (parseSecond2_parseThird2 hp hp').elim
    · refine prEvent_pinned_le K.zin _ _ _
        (fun u g g' h hu => (K.tup_congr (hhA g g') (hzA g g' h)).mp hu)
        (fun u g g' h hb => by rwa [← h t (hnz _ (Or.inr (Or.inl hlen)))])
        (fun u u' g hu hu' => K.tup_unique hu hu')
        (fun u => (prEvent_cell t (fun s => ¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) ∧
          State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) (W.chal s))).trans
          (prob_second_chain2 W hR _ _ c' _))
  by_cases h3 : ∃ pre cW cT c' tt v, ParseThird2 W (histOf c) t.1 (tableOf c g₀) pre cW cT c' tt v
  · obtain ⟨pre, cW, cT, c', tt, v, hp⟩ := h3
    have hlen : t.1.length = 160 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hx, _⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ u, K.Tup (histOf c) (tableOf c g) cW cT u ∧
      (¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) tt ∧
        State₆ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) tt v (W.chal (g t))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', cT', c'', hp', -⟩ |
        ⟨pre', cW', cT', c'', tt', v', hp', u, hu, hf⟩
      · rw [parseFirst2_congr (hcg g)] at hp'
        exact (parseFirst2_parseThird2 hp' hp).elim
      · rw [parseSecond2_congr (hcg g)] at hp'
        exact (parseSecond2_parseThird2 hp' hp).elim
      · rw [parseThird2_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := parseThird2_unique hp' hp
        rw [tableOf_fresh c ht g] at hf
        exact ⟨u, hu, hf⟩
    · refine prEvent_pinned_le K.zin _ _ _
        (fun u g g' h hu => (K.tup_congr (hhA g g') (hzA g g' h)).mp hu)
        (fun u g g' h hb => by rwa [← h t (hnz _ (Or.inr (Or.inr hlen)))])
        (fun u u' g hu hu' => K.tup_unique hu hu')
        (fun u => (prEvent_cell t (fun s => ¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) tt ∧
          State₆ (W.decode pre.2.2) (K.rdW u.1) c' (K.rdT u.2) tt v (W.chal s))).trans
          (prob_third_chain2 W hR _ _ c' _ tt v))
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => ?_]
    · simp
    rcases h with ⟨pre, cW, hp, -⟩ | ⟨pre, cW, cT, c', hp, -⟩ | ⟨pre, cW, cT, c', tt, v, hp, -⟩
    · exact h1 ⟨pre, cW, (parseFirst2_congr (hcg g) _ _ _).mp hp⟩
    · exact h2 ⟨pre, cW, cT, c', (parseSecond2_congr (hcg g) _ _ _ _ _).mp hp⟩
    · exact h3 ⟨pre, cW, cT, c', tt, v, (parseThird2_congr (hcg g) _ _ _ _ _ _ _).mp hp⟩

/-- **A fresh query is bad, the candidates pinned, with probability at most
`(7 |H| + 6) / 2^256 + roundError`.** -/
theorem prob_listBad2P (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBad2P W K (histOf c) t.1 (tableOf c g)] ≤
      ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 + P.roundError :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll4 c t ht) (prob_round2P W K hR hS₀ c t ht))

end Probability

omit hR

/-! ## The trace -/

section Trace

/-- No collision makes the order of the queries the order of what they refer to. -/
theorem refers4_before2P {L : List (List UInt8)} {T : Table} (hnb : ¬ FreshBad (listBad2P W K) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, Refers4 z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBad2P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad2P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBad2P {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBad2P W K) T ∅ L) : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
  have nb : ∀ y ∈ L, ¬ listBad2P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad2P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz hyz
  by_contra hne
  rcases before_trichotomy L y z hy hz hne with h | h
  · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
  · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))

/-- **The trace, the candidates pinned**: if the log holds the chain's six inputs, and pinned candidates of the two
roots, read off the log, each its root's only one, satisfy the verifier's decision at the chain's challenges while
the witness's cells fail the relation, then some fresh input of the log is bad. -/
theorem trace_core2P (L : List (List UInt8)) (T : Table) (π : RootProof2 F) (uW : NW) (uT : NT) :
    let x₀ := labelOf2 W π.pre
    let x₁ := afterC W (T x₀) π.comW
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := afterC W (T x₃) π.comT
    let x₅ := W.afterValues (T x₄) π.v
    (∀ y ∈ [x₀, x₁, x₂, x₃, x₄, x₅], y ∈ L) →
      K.pW.Mem L.toFinset T π.rW π.oW uW → K.pW.One L.toFinset T π.rW π.oW →
      K.pT.Mem L.toFinset T π.rT π.oT uT → K.pT.One L.toFinset T π.rT π.oT →
      P.Accepts (W.decode π.stmt) (K.rdW uW).1 (K.rdT uT).1 (W.chal (T x₁)) (W.chal (T x₂))
        (W.chal (T x₃)) (W.chal (T x₄)) π.v.1 π.v.2 (W.chal (T x₅)) →
      ¬ P.Sat (W.decode π.stmt) (P.cells (K.rdW uW).1) → FreshBad (listBad2P W K) T ∅ L := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ mem hW hW1 hT hT1 hacc hsat
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBad2P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad2P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj := injOn_of_not_freshBad2P W K hnb
  have hord := refers4_before2P W K hnb
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
  have b01 : x₀ ∈ before L x₁ := hord x₀ m0 x₁ m1 (Or.inl (Or.inl (take_afterC W _ _).symm))
  have b12 : x₁ ∈ before L x₂ := hord x₁ m1 x₂ m2 (Or.inl (Or.inl (take32 _).symm))
  have b23 : x₂ ∈ before L x₃ := hord x₂ m2 x₃ m3 (Or.inl (Or.inl (take32 _).symm))
  have b34 : x₃ ∈ before L x₄ := hord x₃ m3 x₄ m4 (Or.inl (Or.inl (take_afterC W _ _).symm))
  have b45 : x₄ ∈ before L x₅ := hord x₄ m4 x₅ m5 (Or.inl (Or.inl (W.take_afterValues _ _).symm))
  have s12 := before_subset_of_mem L x₁ x₂ b12
  have s23 := before_subset_of_mem L x₂ x₃ b23
  have s34 := before_subset_of_mem L x₃ x₄ b34
  have s45 := before_subset_of_mem L x₄ x₅ b45
  have c04 : x₀ ∈ before L x₄ := s34 (s23 (s12 b01))
  have c14 : x₁ ∈ before L x₄ := s34 (s23 b12)
  have c24 : x₂ ∈ before L x₄ := s34 b23
  -- The roots the chain absorbs.
  have hrW : Refers4 x₁ π.rW := Or.inr (Or.inl (rootPart_afterC W (T x₀) π.comW).symm)
  have hrT : Refers4 x₄ π.rT := Or.inr (Or.inl (rootPart_afterC W (T x₃) π.comT).symm)
  have w1 := pin_stab hord K.pW π.rW π.oW uW x₁ x₁ m1 hrW (Or.inl rfl) hW hW1
  have w4 := pin_stab hord K.pW π.rW π.oW uW x₁ x₄ m1 hrW (Or.inr c14) hW hW1
  have w5 := pin_stab hord K.pW π.rW π.oW uW x₁ x₅ m1 hrW (Or.inr (s45 c14)) hW hW1
  have T4 : K.Tup (before L x₄) T π.comW π.comT (uW, uT) :=
    ⟨w4, pin_stab hord K.pT π.rT π.oT uT x₄ x₄ m4 hrT (Or.inl rfl) hT hT1⟩
  have T5 : K.Tup (before L x₅) T π.comW π.comT (uW, uT) :=
    ⟨w5, pin_stab hord K.pT π.rT π.oT uT x₄ x₅ m4 hrT (Or.inr b45) hT hT1⟩
  -- The round the decision makes bad.
  rcases bad_of_accepts2 (W.decode π.stmt) (K.rdW uW) (K.rdT uT)
    (W.chal (T x₁), W.chal (T x₂), W.chal (T x₃)) (W.chal (T x₄)) π.v (W.chal (T x₅)) hacc hsat with
    hb | hb | hb
  · obtain ⟨h1, h2⟩ := hb
    refine nb x₁ m1 (Or.inr (Or.inl ⟨π.pre, π.comW, ⟨T x₀, ⟨b01, rfl⟩, rfl, injB x₁⟩,
      ⟨fun h => not_mem_before_of_mem_before b12 h, fun h => ?_, fun h => ?_, uW, w1, h1, h2⟩⟩))
    · exact not_mem_before_of_mem_before (s23 b12) h
    · have e : x₃ = x₂ := h
      rw [e] at b23
      exact not_mem_before_self L x₂ b23
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₄ m4 (Or.inr (Or.inr (Or.inl ⟨π.pre, π.comW, π.comT, _, ⟨T x₀, T x₁, T x₂, T x₃,
      ⟨c04, rfl⟩, ⟨c14, rfl⟩, ⟨c24, rfl⟩, ⟨b34, rfl⟩, rfl, rfl, injB x₄⟩, (uW, uT), T4, h1, h2⟩)))
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₅ m5 (Or.inr (Or.inr (Or.inr ⟨π.pre, π.comW, π.comT, _, _, π.v,
      ⟨T x₀, T x₁, T x₂, T x₃, T x₄, ⟨s45 c04, rfl⟩, ⟨s45 c14, rfl⟩, ⟨s45 c24, rfl⟩,
        ⟨s45 b34, rfl⟩, ⟨b45, rfl⟩, rfl, rfl, rfl, injB x₅⟩, (uW, uT), T5, h1, h2⟩)))

end Trace

/-! ## In mumbai's two-oracle model -/

open LeanVM LeanVM.Protocol LeanVM.Semantics

/-- **A bad query of both oracles, the candidates pinned**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBad2P (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => listBad2P W K (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad fresh Keccak-256 input of the view is a bad fresh query. -/
theorem freshBad_kc2P (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBad2P W K) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBad2P W K) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kc2P T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kc2P T _ L ?_)
    rwa [viewH_insert_inr]

/-- `listBad2P` reads the table on the inputs asked, at the fresh input, at the 32-byte inputs (the states the
first round's lookahead hashes) and at the pins' inputs. -/
theorem listBad2P_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) (hz : ∀ y, K.zin y → T y = T' y) :
    listBad2P W K H x T ↔ listBad2P W K H x T' := by
  have hcoll : Coll4 H x T ↔ Coll4 H x T' := by
    unfold Coll4
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  have htup : ∀ cW cT u, K.Tup H T cW cT u ↔ K.Tup H T' cW cT u := fun _ _ _ => K.tup_congr hH hz
  have hmW : ∀ r o n, K.pW.Mem H T r o n ↔ K.pW.Mem H T' r o n := fun _ _ _ => K.pW.mem_congr hH hz
  have hoW : ∀ r o, K.pW.One H T r o ↔ K.pW.One H T' r o := fun _ _ => K.pW.one_congr hH hz
  unfold listBad2P FirstBad2P SecondBad2P ThirdBad2P ParseFirst2 FreshFirst2P ParseSecond2 ParseThird2
  simp only [hcoll, hx, hs, htup, hmW, hoW, has_congr hH, injOn_congr hH]

/-- **Each fresh query of both oracles is bad, the candidates pinned, with probability at most
`(7 |H| + 6) / 2^256 + roundError`**, the pins' inputs in the table's uniform part. -/
theorem prob_kcBad2P (hR : RoundsSound P) (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (hSz : ∀ x, K.zin x → (Sum.inl x : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBad2P W K
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 + P.roundError := by
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hx : x ∈ viewH S := mem_viewH.mpr hd
    have hS₁ : ∀ v : Bytes32, v.toList ∈ viewH S := fun v => mem_viewH.mpr (hS₀ v)
    have hc₁ : viewC S c ⟨x, hx⟩ = none := by simp [viewC, ht]
    have hH : histOf (viewC S c) ⊆ viewH S := fun y hy => (mem_histOf.mp hy).1
    have hev : ∀ g, kcBad2P W K ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBad2P W K (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBad2P W K _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBad2P_congr W K (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
        (fun y hy => viewT_extendTable c g (mem_viewH.mpr (hSz y hy)))
    refine (prEvent_mono _ _ (fun g => listBad2P W K (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBad2P W K (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBad2P W K hR hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    gcongr
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    omega

/-! ## The roots answered after the adversary -/

/-- The two roots a proof announces. -/
def RootProof2.roots (π : RootProof2 F) : List Bytes32 := [π.rW, π.rT]

/-- **A fresh Keccak-256 answer after the adversary's last query is one of its two roots.** -/
def rootBad2 {O : Type} (A : OracleComp KeccakCalls (RootProof2 F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => (∀ q ∈ (tableQueryLog A T).map Sigma.fst, q ∈ H) ∧
      viewT T x ∈ (evalWithAnswerFn (QueryImpl.ofFn T) A).1.roots
  | .inr _ => False

theorem prob_rootBad2 {O : Type} (A : OracleComp KeccakCalls (RootProof2 F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[rootBad2 A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤ (2 : ℝ≥0∞) / 2 ^ 256 := by
  classical
  set Hm := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hagree : ∀ g g', ∀ q ∈ Hm, extendTable S (completeTable c g) q =
        extendTable S (completeTable c g') q := by
      intro g g' q hq
      obtain ⟨⟨q', hq'S⟩, hq'c, rfl⟩ := Finset.mem_map.mp hq
      rw [show (Function.Embedding.subtype (· ∈ S)) ⟨q', hq'S⟩ = (⟨q', hq'S⟩ : ↥S).1 from rfl,
        extendTable_subtype, extendTable_subtype]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (mem_cacheDom.mp hq'c)
      simp [completeTable, hv]
    by_cases hex : ∃ g₀, ∀ q ∈ (tableQueryLog A (extendTable S (completeTable c g₀))).map
        Sigma.fst, q ∈ Hm
    · obtain ⟨g₀, hg₀⟩ := hex
      set π₀ := (evalWithAnswerFn (QueryImpl.ofFn (extendTable S (completeTable c g₀))) A).1
      have hx : x ∈ viewH S := mem_viewH.mpr hd
      refine (prEvent_mono _ _ (fun g => ∃ r ∈ π₀.roots, viewG S g ⟨x, hx⟩ = r) ?_).trans ?_
      · intro g hg
        obtain ⟨hq, hroot⟩ := hg
        have hc := run_congr A (extendTable S (completeTable c g₀))
          (extendTable S (completeTable c g)) fun q hq' => hagree g₀ g q (hg₀ q hq')
        have hfresh : viewT (extendTable S (completeTable c g)) x = viewG S g ⟨x, hx⟩ := by
          show toB (extendTable S (completeTable c g) (⟨.inl x, hd⟩ : ↥S).1) = _
          rw [extendTable_subtype]
          simp [completeTable, ht, viewG]
        rw [hfresh, ← hc.1] at hroot
        exact ⟨_, hroot, rfl⟩
      · rw [prEvent_view S (fun h => ∃ r ∈ π₀.roots, h ⟨x, hx⟩ = r)]
        refine (prEvent_exists_mem_le _ (fun r (h : ↥(viewH S) → Bytes32) => h ⟨x, hx⟩ = r)
          ((1 : ℝ≥0∞) / 2 ^ 256) π₀.roots fun r _ =>
            (prEvent_cell (⟨x, hx⟩ : ↥(viewH S)) (fun u : Bytes32 => u = r)).trans
              (prEvent_bytes32_eq_le r)).trans (le_of_eq ?_)
        simp only [RootProof2.roots, List.length_cons, List.length_nil]
        rw [mul_one_div]
        norm_num
    · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
      intro g h
      exact hex ⟨g, h.1⟩

/-- A bad query: `kcBad2P`, or a fresh answer that is an announced root. -/
def advBad2P {O : Type} (A : OracleComp KeccakCalls (RootProof2 F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBad2P W K H d T ∨ rootBad2 A H d T

/-- **Each fresh query is bad, the candidates pinned, with probability at most
`(7 |H| + 8) / 2^256 + roundError`.** -/
theorem prob_advBad2P (hR : RoundsSound P) {O : Type} (A : OracleComp KeccakCalls (RootProof2 F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (hSz : ∀ x, K.zin x → (Sum.inl x : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBad2P W K A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 8 : ℕ) : ℝ≥0∞) / 2 ^ 256 + P.roundError := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBad2P W K hR S hS₀ hSz c t ht)
    (prob_rootBad2 A S c t ht)).trans (le_of_eq ?_))
  rw [add_comm (((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256), add_assoc,
    ENNReal.div_add_div_same, add_comm]
  congr 2
  push_cast
  ring

/-! ## The adversary's extractor, the chain's queries -/

/-- **The extractor**: an explicit, computable function of the adversary's Keccak-256 query log (inputs and answers)
and the proof: the witness table's Merkle tree climbed down from the proof's `W` root through the log's answers, then
decoded. -/
def adversaryExtractor2 (c₁ : TableCode P.Msg₁) (log : Transcript) (π : RootProof2 F) : List P.Msg₁ :=
  c₁.dec (merkleWord (histOfTr log) (tableOfTr log) c₁.height c₁.leafLen π.rW)

theorem chain2_queryBound_kc (π : RootProof2 F) : IsTotalQueryBound (chainWith2 W hash256 π) 6 := by
  simp only [chainWith2, hash256, callKeccak256, bind_assoc, pure_bind]
  repeat' (first | trivial | refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩)

end ComposePcs
