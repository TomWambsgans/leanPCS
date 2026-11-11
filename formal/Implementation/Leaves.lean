-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Calldata

/-!
# The leaves on calldata

On the calldata of a statement and a proof (`calldata`), with the deployed Keccak-256 and the circuit's
commitment in storage (`deployed`), the graph's leaves are the Statement's (`leafOK_calldata`, against
`chainVals`): the statement's halves, the roots' halves, the out-of-domain answers and the other scalars,
the transcript's states (`values_seed`, the hashes) and challenges (the `low` nodes), byte for byte.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient PcsQuotient.Transcript
  Program Emitted

local notation "W" => word limbsEquiv
local notation "EL" => elem limbsEquiv

/-! ## Words of calldata -/

theorem cdWord_slice (cd : List UInt8) (o : Nat) (h : o + 32 ≤ cd.length) :
    cdWord cd o = beNat ((cd.drop o).take 32) := by
  rw [cdWord, map_getD_slice cd o 32 h]

theorem cdWord_shr (cd : List UInt8) (o : Nat) (h : o + 24 ≤ cd.length) :
    cdWord cd o >>> 64 = beNat ((cd.drop o).take 24) := by
  rw [cdWord, show 32 = 24 + 8 from rfl, List.range_add, List.map_append, beNat_append,
    map_getD_slice cd o 24 h, Nat.shiftRight_eq_div_pow]
  have hl := beNat_lt (((List.range 8).map (24 + ·)).map fun k => cd.getD (o + k) 0)
  simp only [List.length_map, List.length_range] at hl
  rw [show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
  simp only [List.length_map, List.length_range]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hl, zero_add]

theorem drop_append_add {A rest : List UInt8} {k : ℕ} (hA : A.length = k) (n : ℕ) :
    (A ++ rest).drop (k + n) = rest.drop n := by
  subst hA
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem beNat_top (b : List UInt8) (hb : b.length = 32) : beNat b >>> 128 = beNat (b.take 16) := by
  rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 128 = 256 ^ (b.length - 16) by rw [hb]; norm_num,
    beNat_take_div _ _ (by omega)]

theorem beNat_bot (b : List UInt8) (hb : b.length = 32) : beNat b % 2 ^ 128 = beNat (b.drop 16) := by
  rw [beNat_split _ 16 (by omega), hb]
  have := beNat_lt (b.drop 16)
  rw [List.length_drop, hb] at this
  norm_num at this ⊢
  omega

/-- A hash node over a digest's state and scalars' words is the next state. -/
theorem values_hash_st {e : Env} (hH : e.H = keccakBytes) {k st : ℕ} {xs : List ℕ}
    (hk : nodes[k]? = some (.hash st xs)) {d : Digest} (hst : (values e).getD st 0 = beNat (digestBytes d))
    {ys : List E} (hxs : xs.map (fun x => (values e).getD x 0) = ys.map (word limbsEquiv)) :
    (values e).getD k 0 = beNat (digestBytes (stOf d ys)) := by
  rw [values_hash e hk, hst, beBytes32_digest, hH]
  have hf : xs.flatMap (fun x => beBytes 32 ((values e).getD x 0)) = ys.flatMap scalarBytes := by
    calc xs.flatMap (fun x => beBytes 32 ((values e).getD x 0))
        = (xs.map (fun x => (values e).getD x 0)).flatMap (beBytes 32) := by simp [List.flatMap_map]
      _ = (ys.map (word limbsEquiv)).flatMap (beBytes 32) := by rw [hxs]
      _ = ys.flatMap scalarBytes := by simp [List.flatMap_map, ← scalarBytes_eq]
  rw [hf]
  rfl

/-- A `low` node of a state is its challenge. -/
theorem values_low_st {e : Env} {k a : ℕ} (hk : nodes[k]? = some (.low a)) {d : Digest}
    (ha : (values e).getD a 0 = beNat (digestBytes d)) :
    (values e).getD k 0 = word limbsEquiv (challengeOf d) := by
  rw [values_low e hk, ha, word_challengeOf]

/-! ## The nodes the leaves are -/

theorem node_facts :
    nodes[0]? = some .seed ∧ nodes[2]? = some (.statement 0) ∧ nodes[3]? = some (.statement 1) ∧
    nodes[4]? = some (.statement 2) ∧ nodes[5]? = some (.statement 3) ∧
    nodes[6]? = some (.root 0) ∧ nodes[7]? = some (.root 1) ∧ nodes[8]? = some (.input 0) ∧
    nodes[9]? = some (.hash 0 [6, 7, 8]) ∧ nodes[10]? = some (.low 9) ∧
    nodes[11]? = some (.hash 9 []) ∧ nodes[12]? = some (.low 11) ∧
    nodes[13]? = some (.hash 11 []) ∧ nodes[14]? = some (.low 13) ∧
    nodes[15]? = some (.root 2) ∧ nodes[16]? = some (.root 3) ∧ nodes[17]? = some (.input 1) ∧
    nodes[18]? = some (.root 4) ∧ nodes[19]? = some (.root 5) ∧ nodes[20]? = some (.input 2) ∧
    nodes[21]? = some (.root 6) ∧ nodes[22]? = some (.root 7) ∧ nodes[23]? = some (.input 3) ∧
    nodes[24]? = some (.hash 13 [15, 16, 17, 18, 19, 20, 21, 22, 23]) ∧ nodes[25]? = some (.low 24) ∧
    nodes[26]? = some (.input 4) ∧ nodes[27]? = some (.input 5) ∧ nodes[28]? = some (.input 6) ∧
    nodes[29]? = some (.input 7) ∧ nodes[30]? = some (.input 8) ∧
    nodes[31]? = some (.hash 24 [26, 27, 28, 29, 30]) ∧ nodes[32]? = some (.low 31) ∧
    nodes[651]? = some (.input 9) ∧ nodes[652]? = some (.input 10) := by
  decide +kernel

/-! ## On calldata -/

/-- The calldata of a statement, a proof with these roots, and a frame's index (`calldata_some`). -/
def cdOf (stmt : Statement) (p : ReductionProof) (frame : UInt8) (rw rh rq rg : Digest) : List UInt8 :=
  (bytesOf selector ++ stmt.y.toList ++ stmt.root.toList) ++
    ([rw, rh, rq, rg].flatMap digestBytes ++ ((scalarsOf p).flatMap elementBytes ++ [frame]))

section Calldata

variable (index : Commitment) (stmt : Statement) (p : ReductionProof) (frame : UInt8) (cd : List UInt8)
  (rw rh rq rg : Digest)

local notation "CD" => cdOf stmt p frame rw rh rq rg

local notation "E0" => deployed index CD

theorem length_selector : (bytesOf selector).length = 4 := rfl

theorem length_head : (bytesOf selector ++ stmt.y.toList ++ stmt.root.toList).length = 68 := by
  simp [length_selector]

theorem length_roots : ([rw, rh, rq, rg].flatMap digestBytes).length = 128 := by
  simp [length_digestBytes]

theorem length_scalars : ((scalarsOf p).flatMap elementBytes).length = 264 := by
  simp [scalarsOf, length_elementBytes]

theorem length_CD : (CD).length = 461 := by
  simp [cdOf, length_selector, length_digestBytes, scalarsOf, length_elementBytes]

theorem wellFormed_CD : WellFormed CD := by
  refine ⟨by rw [length_CD]; rfl, ?_⟩
  rw [cdOf, List.append_assoc, List.append_assoc]
  exact List.take_left' length_selector

theorem stmt_slice : ((CD).drop 4).take 64 = stmt.y.toList ++ stmt.root.toList := by
  rw [cdOf]
  simp only [List.append_assoc]
  rw [List.drop_left' length_selector, ← List.append_assoc]
  exact List.take_left' (by simp)

theorem y_slice : ((CD).drop 4).take 32 = stmt.y.toList := by
  have := congrArg (List.take 32) (stmt_slice stmt p frame rw rh rq rg)
  rw [List.take_take, List.take_left' (by simp)] at this
  simpa using this

theorem root_slice : ((CD).drop 36).take 32 = stmt.root.toList := by
  have := congrArg (List.drop 32) (stmt_slice stmt p frame rw rh rq rg)
  rw [List.drop_take, List.drop_drop, List.drop_left' (by simp)] at this
  simpa using this

theorem roots_slice (j : ℕ) (hj : j < 4) :
    ((CD).drop (68 + 32 * j)).take 32 = digestBytes ([rw, rh, rq, rg][j]'(by simpa using hj)) := by
  rw [cdOf, drop_append_add (length_head stmt) (32 * j)]
  exact flatMap_chunk digestBytes 32 length_digestBytes _ j (by simpa using hj) _

theorem scalars_slice (i : ℕ) (hi : i < 11) :
    ((CD).drop (196 + 24 * i)).take 24 = elementBytes ((scalarsOf p)[i]'(by simp [scalarsOf]; omega)) := by
  rw [cdOf, show 196 + 24 * i = 68 + (128 + 24 * i) by ring, drop_append_add (length_head stmt),
    drop_append_add (length_roots rw rh rq rg)]
  exact flatMap_chunk elementBytes 24 length_elementBytes _ i (by simp [scalarsOf]; omega) _

/-! ### Values of the leaves -/

local notation "VS" => values E0

theorem vals_seed : (VS).getD 0 0 = beNat (digestBytes (keccak256 (label index stmt))) := by
  rw [values_seed E0 node_facts.1]
  have hn : bytesOf name = "pcs-quotient-kc1".toUTF8.toList := by decide +kernel
  have ho : (beBytes 32 (W index.ood)).drop 8 = elementBytes index.ood := by
    rw [← scalarBytes_eq]
    simp [scalarBytes, elementBytes]
  show beNat (digestBytes (keccak256 (bytesOf name ++ digestBytes index.root ++
    (beBytes 32 (W index.ood)).drop 8 ++ ((CD).drop 4).take 64))) = _
  rw [stmt_slice, hn, ho]
  simp only [label, List.append_assoc]

theorem vals_stmt :
    (VS).getD 2 0 = W (halves stmt.y).1 ∧ (VS).getD 3 0 = W (halves stmt.y).2 ∧
    (VS).getD 4 0 = W (halves stmt.root).1 ∧ (VS).getD 5 0 = W (halves stmt.root).2 := by
  have hl := length_CD stmt p frame rw rh rq rg
  have hy : cdWord CD 4 = beNat stmt.y.toList := by
    rw [cdWord_slice _ _ (by omega), y_slice]
  have hr : cdWord CD 36 = beNat stmt.root.toList := by
    rw [cdWord_slice _ _ (by omega), root_slice]
  have top : ∀ b : Bytes32, beNat b.toList >>> 128 = beNat (b.toList.take 16) := fun b => by
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 128 = 256 ^ (b.toList.length - 16) by simp,
      beNat_take_div _ _ (by simp)]
  have bot : ∀ b : Bytes32, beNat b.toList % 2 ^ 128 = beNat (b.toList.drop 16) := fun b => by
    have hb : b.toList.length = 32 := by simp
    rw [beNat_split _ 16 (by omega), hb]
    have := beNat_lt (b.toList.drop 16)
    rw [List.length_drop, hb] at this
    norm_num at this ⊢
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [values_statement E0 node_facts.2.1, word_halves_fst]
    show half (cdWord CD 4) 0 = _
    rw [hy, half, if_pos rfl, top]
  · rw [values_statement E0 node_facts.2.2.1, word_halves_snd]
    show half (cdWord CD 4) 1 = _
    rw [hy, half, if_neg (by decide), bot]
  · rw [values_statement E0 node_facts.2.2.2.1, word_halves_fst]
    show half (cdWord CD 36) 2 = _
    rw [hr, half, if_pos rfl, top]
  · rw [values_statement E0 node_facts.2.2.2.2.1, word_halves_snd]
    show half (cdWord CD 36) 3 = _
    rw [hr, half, if_neg (by decide), bot]

theorem vals_input (i : ℕ) (hi : i < 11) (n : ℕ) (hn : nodes[n]? = some (.input i)) :
    (VS).getD n 0 = W ((scalarsOf p)[i]'(by simp [scalarsOf]; omega)) := by
  have hl := length_CD stmt p frame rw rh rq rg
  rw [values_input E0 hn]
  show cdWord (CD) (4 + 192 + 24 * i) >>> 64 = _
  rw [cdWord_shr _ _ (by omega), show 4 + 192 + 24 * i = 196 + 24 * i by ring,
    scalars_slice stmt p frame rw rh rq rg i hi,
    beNat_elementBytes]

theorem vals_root (j : ℕ) (hj : j < 4) (n : ℕ) (hn : nodes[n]? = some (.root (2 * j))) (n' : ℕ)
    (hn' : nodes[n']? = some (.root (2 * j + 1))) :
    (VS).getD n 0 = beNat ((digestBytes ([rw, rh, rq, rg][j]'(by simpa using hj))).take 16) ∧
      (VS).getD n' 0 = beNat ((digestBytes ([rw, rh, rq, rg][j]'(by simpa using hj))).drop 16) := by
  have hl := length_CD stmt p frame rw rh rq rg
  have hw : cdWord (CD) (4 + 64 + 32 * j) = beNat (digestBytes ([rw, rh, rq, rg][j]'(by simpa using hj))) := by
    rw [cdWord_slice _ _ (by omega), show 4 + 64 + 32 * j = 68 + 32 * j by ring,
      roots_slice stmt p frame rw rh rq rg j hj]
  constructor
  · rw [values_root E0 hn]
    show half (cdWord (CD) (4 + 64 + 32 * (2 * j / 2))) (2 * j) = _
    rw [show 2 * j / 2 = j by omega, hw, half, if_pos (by omega), beNat_top _ (length_digestBytes _)]
  · rw [values_root E0 hn']
    show half (cdWord (CD) (4 + 64 + 32 * ((2 * j + 1) / 2))) (2 * j + 1) = _
    rw [show (2 * j + 1) / 2 = j by omega, hw, half, if_neg (by omega), beNat_bot _ (length_digestBytes _)]

variable {p rw rh rq rg} in
/-- **The leaves' values on calldata**, as the Statement's elements: the roots' halves, the other
scalars, the states and the challenges. -/
theorem vals_leaves (hw : rootOfHalves p.witness.root = some rw) (hh : rootOfHalves p.h.root = some rh)
    (hq : rootOfHalves p.q.root = some rq) (hg : rootOfHalves p.g.root = some rg) :
    let s := states index stmt p
    (VS).getD 6 0 = W p.witness.root.1 ∧ (VS).getD 7 0 = W p.witness.root.2 ∧
    (VS).getD 8 0 = W p.witness.ood ∧
    (VS).getD 15 0 = W p.h.root.1 ∧ (VS).getD 16 0 = W p.h.root.2 ∧ (VS).getD 17 0 = W p.h.ood ∧
    (VS).getD 18 0 = W p.q.root.1 ∧ (VS).getD 19 0 = W p.q.root.2 ∧ (VS).getD 20 0 = W p.q.ood ∧
    (VS).getD 21 0 = W p.g.root.1 ∧ (VS).getD 22 0 = W p.g.root.2 ∧ (VS).getD 23 0 = W p.g.ood ∧
    (VS).getD 26 0 = W p.values[0] ∧ (VS).getD 27 0 = W p.values[1] ∧
    (VS).getD 28 0 = W p.values[2] ∧ (VS).getD 29 0 = W p.values[3] ∧
    (VS).getD 30 0 = W p.next ∧ (VS).getD 651 0 = W p.qValue ∧ (VS).getD 652 0 = W p.gValue ∧
    (VS).getD 10 0 = W (challengeOf (s.getD 1 default)) ∧ (VS).getD 12 0 = W (challengeOf (s.getD 2 default)) ∧
    (VS).getD 14 0 = W (challengeOf (s.getD 3 default)) ∧ (VS).getD 25 0 = W (challengeOf (s.getD 4 default)) ∧
    (VS).getD 32 0 = W (challengeOf (s.getD 5 default)) := by
  intro s
  obtain ⟨n0, -, -, -, -, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22,
    n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n651, n652⟩ := node_facts
  have r0 := vals_root index stmt p frame rw rh rq rg 0 (by norm_num) 6 n6 7 n7
  have r1 := vals_root index stmt p frame rw rh rq rg 1 (by norm_num) 15 n15 16 n16
  have r2 := vals_root index stmt p frame rw rh rq rg 2 (by norm_num) 18 n18 19 n19
  have r3 := vals_root index stmt p frame rw rh rq rg 3 (by norm_num) 21 n21 22 n22
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1 r2 r3
  have b0 := rootOfHalves_bytes hw
  have b1 := rootOfHalves_bytes hh
  have b2 := rootOfHalves_bytes hq
  have b3 := rootOfHalves_bytes hg
  have i0 := vals_input index stmt p frame rw rh rq rg 0 (by norm_num) 8 n8
  have i1 := vals_input index stmt p frame rw rh rq rg 1 (by norm_num) 17 n17
  have i2 := vals_input index stmt p frame rw rh rq rg 2 (by norm_num) 20 n20
  have i3 := vals_input index stmt p frame rw rh rq rg 3 (by norm_num) 23 n23
  have i4 := vals_input index stmt p frame rw rh rq rg 4 (by norm_num) 26 n26
  have i5 := vals_input index stmt p frame rw rh rq rg 5 (by norm_num) 27 n27
  have i6 := vals_input index stmt p frame rw rh rq rg 6 (by norm_num) 28 n28
  have i7 := vals_input index stmt p frame rw rh rq rg 7 (by norm_num) 29 n29
  have i8 := vals_input index stmt p frame rw rh rq rg 8 (by norm_num) 30 n30
  have i9 := vals_input index stmt p frame rw rh rq rg 9 (by norm_num) 651 n651
  have i10 := vals_input index stmt p frame rw rh rq rg 10 (by norm_num) 652 n652
  have hv : p.values.toList = [p.values[0], p.values[1], p.values[2], p.values[3]] := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [Vector.length_toList] at h1
    interval_cases k <;> simp
  simp only [scalarsOf, hv, List.cons_append, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ,
    List.getElem_append_left, List.getElem_append_right, Vector.getElem_toList] at i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  have hH : (E0).H = keccakBytes := rfl
  have v0 := vals_seed index stmt p frame rw rh rq rg
  have v9 := values_hash_st hH n9 v0 (ys := [p.witness.root.1, p.witness.root.2, p.witness.ood])
    (by simp only [List.map_cons, List.map_nil, r0.1, r0.2, i0, b0.1, b0.2])
  have v11 := values_hash_st hH n11 v9 (ys := []) rfl
  have v13 := values_hash_st hH n13 v11 (ys := []) rfl
  have v24 := values_hash_st hH n24 v13 (ys := [p.h.root.1, p.h.root.2, p.h.ood, p.q.root.1, p.q.root.2,
    p.q.ood, p.g.root.1, p.g.root.2, p.g.ood])
    (by simp only [List.map_cons, List.map_nil, r1.1, r1.2, i1, b1.1, b1.2, r2.1, r2.2, i2, b2.1, b2.2,
      r3.1, r3.2, i3, b3.1, b3.2])
  have v31 := values_hash_st hH n31 v24 (ys := p.values.toList ++ [p.next])
    (by
      rw [hv]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, i4, i5, i6, i7, i8])
  refine ⟨r0.1.trans b0.1.symm, r0.2.trans b0.2.symm, i0, r1.1.trans b1.1.symm, r1.2.trans b1.2.symm, i1,
    r2.1.trans b2.1.symm, r2.2.trans b2.2.symm, i2, r3.1.trans b3.1.symm, r3.2.trans b3.2.symm, i3,
    i4, i5, i6, i7, i8, i9, i10, values_low_st n10 v9, values_low_st n12 v11, values_low_st n14 v13,
    values_low_st n25 v24, values_low_st n32 v31⟩

end Calldata

end Implementation
