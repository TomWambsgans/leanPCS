-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The calldata's layout is `crates/membership/evm/src/quotient.rs`'s (`calldata`); the roots' bytes use
-- leanerVM's lanes (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0: `wordBytes_leLane`, `leLane_lanesBytes`, `common/Common/Lanes.lean`).
import Implementation.Reduce
import PcsQuotient.Verifier
import Common.Lanes

/-!
# The calldata of a proof, and the leaves the graph reads from it

`calldata` is `quotient.rs`'s (`273` bytes, no selector): the statement's `64` bytes, the two roots' `32` bytes
each (the witness table's, then the quotient table's: the digests their halves name, `rootOfHalves`; a proof whose
roots' halves have a top limb has no calldata, as the Rust's `NotARoot`), the six other scalars of the
reduction's proof, `24` bytes each (`elementBytes`: the two out-of-domain answers, the three values `X`, `C`,
`V + Y`, `next`), and the index of the frame of PCS claims. `deployed` is what the contract
reads: the deployed Keccak-256, and the circuit's commitment in storage (the root's bytes, the
out-of-domain answer's word).

`leafOK_calldata`: on such calldata, the graph's leaves hold the Statement's leaves (`chainVals`: the
statement, the challenges of the reduction's Keccak-256 chain, the proof's values); `reduce_eq`: the
Statement's `reduce` is `claimsAt` at those challenges.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Rpm PcsQuotient
  PcsQuotient.Transcript Program Emitted

local notation "W" => word limbsEquiv
local notation "EL" => elem limbsEquiv

/-! ## Roots -/

theorem lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := rfl

theorem take_drop_append (l : List UInt8) (s n : ℕ) : (l.drop s).take n ++ l.drop (s + n) = l.drop s := by
  rw [← List.drop_drop, List.take_append_drop]

theorem split32 (b : List UInt8) (hb : b.length = 32) :
    (b.drop 0).take 8 ++ (b.drop 8).take 8 ++ (b.drop 16).take 8 ++ (b.drop 24).take 8 = b := by
  rw [List.take_of_length_le (l := b.drop 24) (by simp; omega), List.append_assoc, List.append_assoc,
    take_drop_append b 16 8, take_drop_append b 8 8, take_drop_append b 0 8, List.drop_zero]

theorem digestBytes_lanes (b : List UInt8) (hb : b.length = 32) :
    digestBytes #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3] = b := by
  have hs : ∀ i, i < 4 → wordBytes (leLane b i) = (b.drop (8 * i)).take 8 := fun i hi => by
    rw [wordBytes_leLane, map_getD_slice b _ 8 (by omega)]
  have e : digestBytes #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3] =
      wordBytes (leLane b 0) ++ wordBytes (leLane b 1) ++ wordBytes (leLane b 2) ++
        wordBytes (leLane b 3) := by
    simp [digestBytes]
  rw [e, hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num)]
  exact split32 b hb

theorem take16_4 (A B C D : List UInt8) (hA : A.length = 8) (hB : B.length = 8) :
    (A ++ B ++ C ++ D).take 16 = A ++ B := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc A B]
  exact List.take_left' (by simp [hA, hB])

theorem drop16_4 (A B C D : List UInt8) (hA : A.length = 8) (hB : B.length = 8) :
    (A ++ B ++ C ++ D).drop 16 = C ++ D := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc A B]
  exact List.drop_left' (by simp [hA, hB])

/-- **The root two scalars name** has bytes whose two 16-byte halves are those scalars' numbers. -/
theorem rootOfHalves_bytes {s : E × E} {r : Digest} (h : rootOfHalves s = some r) :
    W s.1 = beNat ((digestBytes r).take 16) ∧ W s.2 = beNat ((digestBytes r).drop 16) := by
  unfold rootOfHalves at h
  split_ifs at h with h0
  obtain ⟨h1, h2⟩ := h0
  cases h
  rw [digestBytes_lanes _ (by simp [length_beBytes8]), take16_4 _ _ _ _ (length_beBytes8 _) (length_beBytes8 _),
    drop16_4 _ _ _ _ (length_beBytes8 _) (length_beBytes8 _)]
  have z1 : (s.1.limb 2).lane.toNat = 0 := by rw [h1]; rfl
  have z2 : (s.2.limb 2).lane.toNat = 0 := by rw [h2]; rfl
  rw [beNat_append, beNat_append, beNat_beBytes8, beNat_beBytes8, beNat_beBytes8,
    beNat_beBytes8, length_beBytes8, length_beBytes8, word_eq, word_eq, z1, z2]
  constructor <;> ring

theorem rootOfHalves_ofLimbs (a b c d : UInt64) :
    rootOfHalves (E.ofLimbs (K.ofLane a) (K.ofLane b) 0, E.ofLimbs (K.ofLane c) (K.ofLane d) 0) =
      some #v[leLane (Transcript.beBytes b ++ Transcript.beBytes a ++ Transcript.beBytes d ++
          Transcript.beBytes c) 0,
        leLane (Transcript.beBytes b ++ Transcript.beBytes a ++ Transcript.beBytes d ++ Transcript.beBytes c) 1,
        leLane (Transcript.beBytes b ++ Transcript.beBytes a ++ Transcript.beBytes d ++ Transcript.beBytes c) 2,
        leLane (Transcript.beBytes b ++ Transcript.beBytes a ++ Transcript.beBytes d ++ Transcript.beBytes c) 3] := by
  unfold rootOfHalves
  rw [if_pos ⟨rfl, rfl⟩]
  rfl

/-- The digest two scalars name, back to the scalars. -/
theorem rootOfHalves_rootHalves (d : Digest) : rootOfHalves (rootHalves d) = some d := by
  have hl := length_digestBytes d
  have hb : (Digest.toBytes d).toList = digestBytes d := rfl
  have hlb : digestBytes d = lanesBytes d.toList := rfl
  generalize digestBytes d = b at hl hb hlb
  have hw : ∀ s, s + 8 ≤ 32 → Transcript.beBytes (beWord b s) = (b.drop s).take 8 := fun s hs => by
    rw [beBytes8_eq, beWord_slice b s (by omega)]
    exact beBytes_eq_of_beNat (by simp; omega) rfl
  have e : rootHalves d = (E.ofLimbs (K.ofLane (beWord b 8)) (K.ofLane (beWord b 0)) 0,
      E.ofLimbs (K.ofLane (beWord b 24)) (K.ofLane (beWord b 16)) 0) := by
    simp [rootHalves, halves, hb]
  rw [e, rootOfHalves_ofLimbs, hw 0 (by norm_num), hw 8 (by norm_num), hw 16 (by norm_num), hw 24 (by norm_num)]
  have hsplit := split32 b hl
  rw [hsplit]
  congr 1
  apply Vector.ext
  intro i hi
  rw [hlb]
  interval_cases i <;> simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] <;> rw [leLane_lanesBytes _ _ (by simp)] <;> simp

/-! ## The calldata -/

/-- The reduction's proof's scalars that are not roots' halves, in the order of the calldata: the two
out-of-domain answers, the three values, `next`. -/
def scalarsOf (p : ReductionProof) : List E :=
  [p.witness.ood, p.table.ood] ++ p.values.toList ++ [p.next]

/-- **`quotient.rs`'s `calldata`**: the statement, the two roots' bytes, the other scalars, the frame's index (no
selector); `none` for a proof whose roots' halves have a top limb. -/
def calldata (stmt : Statement) (p : ReductionProof) (frame : UInt8) : Option (List UInt8) := do
  let rw ← rootOfHalves p.witness.root
  let rt ← rootOfHalves p.table.root
  pure ((stmt.y.toList ++ stmt.root.toList) ++
    ([rw, rt].flatMap digestBytes ++ ((scalarsOf p).flatMap elementBytes ++ [frame])))

/-- Keccak-256 as the EVM's `KECCAK256` returns it. -/
def keccakBytes (l : List UInt8) : Vector UInt8 32 := Digest.toBytes (keccak256 l)

/-- **What the deployed contract reads** on calldata `cd`: the deployed Keccak-256, the circuit's
commitment `index` in storage (slot 0 the root's bytes, slot 1 the out-of-domain answer's word). -/
def deployed (index : Commitment) (cd : List UInt8) : Env :=
  ⟨keccakBytes, digestBytes index.root, W index.ood, cd⟩

/-! ## The chain -/

/-- A transcript step: the Keccak-256 of the state's bytes and of the scalars' words. -/
def stOf (prev : Digest) (xs : List E) : Digest := keccak256 (digestBytes prev ++ xs.flatMap scalarBytes)

/-- The chain's states. -/
def states (index : Commitment) (stmt : Statement) (p : ReductionProof) : List Digest :=
  let s0 := keccak256 (label index stmt)
  let s1 := stOf s0 [p.witness.root.1, p.witness.root.2, p.witness.ood]
  let s2 := stOf s1 []
  let s3 := stOf s2 []
  let s4 := stOf s3 [p.table.root.1, p.table.root.2, p.table.ood]
  let s5 := stOf s4 (p.values.toList ++ [p.next])
  [s0, s1, s2, s3, s4, s5]

/-- **The Statement's leaves** for a proof: the statement, the challenges of its chain, its values. -/
def chainVals (index : Commitment) (stmt : Statement) (p : ReductionProof) : Formula.Vals :=
  let s := states index stmt p
  ⟨stmt, challengeOf (s.getD 1 default), challengeOf (s.getD 2 default), challengeOf (s.getD 3 default),
    challengeOf (s.getD 4 default), challengeOf (s.getD 5 default), p.values, p.next⟩

theorem foldl_absorb (c : Chain) (l : List E) :
    (l.foldl Chain.absorb c) = ⟨c.state, c.pending ++ l⟩ := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp [Chain.absorb]

/-- **The Statement's reduction** on a proof whose roots name digests: the commitments, and `claimsAt`
at the chain's challenges. -/
theorem reduce_eq (index : Commitment) (stmt : Statement) (p : ReductionProof) {rw rt : Digest}
    (hw : rootOfHalves p.witness.root = some rw) (ht : rootOfHalves p.table.root = some rt) :
    reduce 22 index stmt p =
      (claimsAt 22 stmt (chainVals index stmt p).α (chainVals index stmt p).β (chainVals index stmt p).μ
        (chainVals index stmt p).t (chainVals index stmt p).ρ p.values p.next).map
        fun claims ↦ ⟨⟨⟨rw, p.witness.ood⟩, ⟨rt, p.table.ood⟩⟩, claims⟩ := by
  have hs : Supported 22 := by decide
  simp only [reduce, reduceWith, readCommitment, Chain.startWith, Chain.squeezeWith, Chain.absorb,
    hw, ht, Option.map_some, if_neg (not_not.mpr hs), foldl_absorb]
  rfl

/-! ## Reading the calldata -/

theorem flatMap_chunk {α : Type} (f : α → List UInt8) (k : ℕ) (hf : ∀ a, (f a).length = k) :
    ∀ (L : List α) (i : ℕ) (hi : i < L.length) (rest : List UInt8),
      ((L.flatMap f ++ rest).drop (k * i)).take k = f L[i]
  | [], _, hi, _ => absurd hi (by simp)
  | a :: L, 0, _, rest => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero, List.append_assoc]
    exact List.take_left' (hf a)
  | a :: L, i + 1, hi, rest => by
    have ih := flatMap_chunk f k hf L i (by simpa using hi) rest
    rw [List.flatMap_cons, List.append_assoc, show k * (i + 1) = (f a).length + k * i by rw [hf]; ring,
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left,
      List.getElem_cons_succ]
    exact ih

theorem calldata_some {stmt : Statement} {p : ReductionProof} {frame : UInt8} {cd : List UInt8}
    (h : calldata stmt p frame = some cd) : ∃ rw rt,
      rootOfHalves p.witness.root = some rw ∧ rootOfHalves p.table.root = some rt ∧
      cd = (stmt.y.toList ++ stmt.root.toList) ++
        ([rw, rt].flatMap digestBytes ++ ((scalarsOf p).flatMap elementBytes ++ [frame])) := by
  unfold calldata at h
  rcases hw : rootOfHalves p.witness.root with _ | rw <;> rw [hw] at h
  · cases h
  rcases ht : rootOfHalves p.table.root with _ | rt <;> rw [ht] at h
  · cases h
  exact ⟨rw, rt, rfl, rfl, (Option.some.inj h).symm⟩

end Implementation
