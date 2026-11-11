-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Calldata

/-!
# The leaves on calldata

On the calldata of a statement and a proof (`calldata`), with the deployed Keccak-256 and the circuit's
commitment in storage (`deployed`), the graph's leaves are the Statement's (`leafOK_calldata`, against
`chainVals`): the statement's eight words, the roots' halves, the out-of-domain answers and the other scalars,
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
    nodes[0]? = some .seed ∧
    nodes[10]? = some (.root 0) ∧ nodes[11]? = some (.root 1) ∧ nodes[12]? = some (.input 0) ∧
    nodes[13]? = some (.hash 0 [10, 11, 12]) ∧ nodes[14]? = some (.low 13) ∧
    nodes[15]? = some (.hash 13 []) ∧ nodes[16]? = some (.low 15) ∧
    nodes[17]? = some (.hash 15 []) ∧ nodes[18]? = some (.low 17) ∧
    nodes[19]? = some (.root 2) ∧ nodes[20]? = some (.root 3) ∧ nodes[21]? = some (.input 1) ∧
    nodes[22]? = some (.hash 17 [19, 20, 21]) ∧ nodes[23]? = some (.low 22) ∧
    nodes[24]? = some (.input 2) ∧ nodes[25]? = some (.input 3) ∧ nodes[26]? = some (.input 4) ∧
    nodes[27]? = some (.input 5) ∧
    nodes[28]? = some (.hash 22 [24, 25, 26, 27]) ∧ nodes[29]? = some (.low 28) := by
  decide +kernel

theorem node_statement : ∀ k < 8, nodes[k + 2]? = some (.statement k) := by decide +kernel

/-! ## On calldata -/

/-- The calldata of a statement, a proof with these roots, and a frame's index (`calldata_some`). -/
def cdOf (stmt : Statement) (p : ReductionProof) (frame : UInt8) (rw rt : Digest) : List UInt8 :=
  (stmt.y.toList ++ stmt.root.toList) ++
    ([rw, rt].flatMap digestBytes ++ ((scalarsOf p).flatMap elementBytes ++ [frame]))

section Calldata

variable (index : Commitment) (stmt : Statement) (p : ReductionProof) (frame : UInt8) (cd : List UInt8)
  (rw rt : Digest)

local notation "CD" => cdOf stmt p frame rw rt

local notation "E0" => deployed index CD

theorem length_head : (stmt.y.toList ++ stmt.root.toList).length = 64 := by simp

theorem length_roots : ([rw, rt].flatMap digestBytes).length = 64 := by
  simp [length_digestBytes]

theorem length_scalars : ((scalarsOf p).flatMap elementBytes).length = 144 := by
  simp [scalarsOf, length_elementBytes]

theorem length_CD : (CD).length = 273 := by
  simp [cdOf, length_digestBytes, scalarsOf, length_elementBytes]

theorem wellFormed_CD : WellFormed CD := by
  rw [WellFormed, length_CD]
  rfl

theorem stmt_slice : (CD).take 64 = stmt.y.toList ++ stmt.root.toList := by
  rw [cdOf]
  exact List.take_left' (length_head stmt)

theorem word_slice (k : ℕ) (hk : k < 8) : ((CD).drop (8 * k)).take 8 =
    ((stmt.y.toList ++ stmt.root.toList).drop (8 * k)).take 8 := by
  rw [← stmt_slice stmt p frame rw rt, List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem roots_slice (j : ℕ) (hj : j < 2) :
    ((CD).drop (64 + 32 * j)).take 32 = digestBytes ([rw, rt][j]'(by simpa using hj)) := by
  rw [cdOf, drop_append_add (length_head stmt) (32 * j)]
  exact flatMap_chunk digestBytes 32 length_digestBytes _ j (by simpa using hj) _

theorem scalars_slice (i : ℕ) (hi : i < 6) :
    ((CD).drop (128 + 24 * i)).take 24 = elementBytes ((scalarsOf p)[i]'(by simp [scalarsOf]; omega)) := by
  rw [cdOf, show 128 + 24 * i = 64 + (64 + 24 * i) by ring, drop_append_add (length_head stmt),
    drop_append_add (length_roots rw rt)]
  exact flatMap_chunk elementBytes 24 length_elementBytes _ i (by simp [scalarsOf]; omega) _

/-! ### Values of the leaves -/

local notation "VS" => values E0

theorem vals_seed : (VS).getD 0 0 = beNat (digestBytes (keccak256 (label index stmt))) := by
  rw [values_seed E0 node_facts.1]
  have hn : bytesOf name = protocolName := by decide +kernel
  have ho : (beBytes 32 (W index.ood)).drop 8 = elementBytes index.ood := by
    rw [← scalarBytes_eq]
    simp [scalarBytes, elementBytes]
  show beNat (digestBytes (keccak256 (bytesOf name ++ digestBytes index.root ++
    (beBytes 32 (W index.ood)).drop 8 ++ (CD).take 64))) = _
  rw [stmt_slice, hn, ho]
  simp only [label, List.append_assoc]

/-- A statement word is the big-endian number of its eight bytes of the statement. -/
theorem word_words (k : ℕ) (hk : k < 8) :
    W (ofK (stmt.words.getD k 0)) = beNat (((stmt.y.toList ++ stmt.root.toList).drop (8 * k)).take 8) := by
  have hy : stmt.y.toList.length = 32 := by simp
  rw [word_ofK]
  by_cases h4 : k < 4
  · have e : stmt.words.getD k 0 = K.ofLane (beWord stmt.y.toList (8 * k)) := by
      rw [Statement.words, List.getD_append _ _ _ _ (by simp [bytesWords]; omega)]
      simp [bytesWords, List.getD_eq_getElem?_getD, h4]
    rw [e, lane_ofLane, beWord_slice _ _ (by omega), List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega)]
  · have e : stmt.words.getD k 0 = K.ofLane (beWord stmt.root.toList (8 * (k - 4))) := by
      rw [Statement.words, List.getD_append_right _ _ _ _ (by simp [bytesWords]; omega)]
      simp [bytesWords, List.getD_eq_getElem?_getD, show k - 4 < 4 by omega]
    rw [e, lane_ofLane, beWord_slice _ _ (by simp; omega), List.drop_append, hy,
      List.drop_eq_nil_of_le (as := stmt.y.toList) (by rw [hy]; omega), List.nil_append,
      show 8 * k - 32 = 8 * (k - 4) by omega]

theorem vals_stmt (k : ℕ) (hk : k < 8) : (VS).getD (k + 2) 0 = W (ofK (stmt.words.getD k 0)) := by
  have hl := length_CD stmt p frame rw rt
  rw [values_statement E0 (node_statement k hk), word_words stmt k hk, ← word_slice stmt p frame rw rt k hk]
  show cdWord (CD) (8 * k) >>> 192 = _
  rw [cdWord_slice _ _ (by omega), Nat.shiftRight_eq_div_pow]
  have h32 : (((CD).drop (8 * k)).take 32).length = 32 := by simp; omega
  rw [show (2 : ℕ) ^ 192 = 256 ^ ((((CD).drop (8 * k)).take 32).length - 8) by rw [h32]; norm_num,
    beNat_take_div _ _ (by omega), List.take_take, Nat.min_eq_left (by omega)]

theorem vals_input (i : ℕ) (hi : i < 6) (n : ℕ) (hn : nodes[n]? = some (.input i)) :
    (VS).getD n 0 = W ((scalarsOf p)[i]'(by simp [scalarsOf]; omega)) := by
  have hl := length_CD stmt p frame rw rt
  rw [values_input E0 hn]
  show cdWord (CD) (128 + 24 * i) >>> 64 = _
  rw [cdWord_shr _ _ (by omega), scalars_slice stmt p frame rw rt i hi, beNat_elementBytes]

theorem vals_root (j : ℕ) (hj : j < 2) (n : ℕ) (hn : nodes[n]? = some (.root (2 * j))) (n' : ℕ)
    (hn' : nodes[n']? = some (.root (2 * j + 1))) :
    (VS).getD n 0 = beNat ((digestBytes ([rw, rt][j]'(by simpa using hj))).take 16) ∧
      (VS).getD n' 0 = beNat ((digestBytes ([rw, rt][j]'(by simpa using hj))).drop 16) := by
  have hl := length_CD stmt p frame rw rt
  have hw : cdWord (CD) (64 + 32 * j) = beNat (digestBytes ([rw, rt][j]'(by simpa using hj))) := by
    rw [cdWord_slice _ _ (by omega), roots_slice stmt p frame rw rt j hj]
  constructor
  · rw [values_root E0 hn]
    show half (cdWord (CD) (64 + 32 * (2 * j / 2))) (2 * j) = _
    rw [show 2 * j / 2 = j by omega, hw, half, if_pos (by omega), beNat_top _ (length_digestBytes _)]
  · rw [values_root E0 hn']
    show half (cdWord (CD) (64 + 32 * ((2 * j + 1) / 2))) (2 * j + 1) = _
    rw [show (2 * j + 1) / 2 = j by omega, hw, half, if_neg (by omega), beNat_bot _ (length_digestBytes _)]

variable {p rw rt} in
/-- **The leaves' values on calldata**, as the Statement's elements: the roots' halves, the other
scalars, the states and the challenges. -/
theorem vals_leaves (hw : rootOfHalves p.witness.root = some rw) (ht : rootOfHalves p.table.root = some rt) :
    let s := states index stmt p
    (VS).getD 10 0 = W p.witness.root.1 ∧ (VS).getD 11 0 = W p.witness.root.2 ∧
    (VS).getD 12 0 = W p.witness.ood ∧
    (VS).getD 19 0 = W p.table.root.1 ∧ (VS).getD 20 0 = W p.table.root.2 ∧ (VS).getD 21 0 = W p.table.ood ∧
    (VS).getD 24 0 = W p.values[0] ∧ (VS).getD 25 0 = W p.values[1] ∧
    (VS).getD 26 0 = W p.values[2] ∧ (VS).getD 27 0 = W p.next ∧
    (VS).getD 14 0 = W (challengeOf (s.getD 1 default)) ∧ (VS).getD 16 0 = W (challengeOf (s.getD 2 default)) ∧
    (VS).getD 18 0 = W (challengeOf (s.getD 3 default)) ∧ (VS).getD 23 0 = W (challengeOf (s.getD 4 default)) ∧
    (VS).getD 29 0 = W (challengeOf (s.getD 5 default)) := by
  intro s
  obtain ⟨n0, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28,
    n29⟩ := node_facts
  have r0 := vals_root index stmt p frame rw rt 0 (by norm_num) 10 n10 11 n11
  have r1 := vals_root index stmt p frame rw rt 1 (by norm_num) 19 n19 20 n20
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1
  have b0 := rootOfHalves_bytes hw
  have b1 := rootOfHalves_bytes ht
  have i0 := vals_input index stmt p frame rw rt 0 (by norm_num) 12 n12
  have i1 := vals_input index stmt p frame rw rt 1 (by norm_num) 21 n21
  have i2 := vals_input index stmt p frame rw rt 2 (by norm_num) 24 n24
  have i3 := vals_input index stmt p frame rw rt 3 (by norm_num) 25 n25
  have i4 := vals_input index stmt p frame rw rt 4 (by norm_num) 26 n26
  have i5 := vals_input index stmt p frame rw rt 5 (by norm_num) 27 n27
  have hv : p.values.toList = [p.values[0], p.values[1], p.values[2]] := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [Vector.length_toList] at h1
    interval_cases k <;> simp
  simp only [scalarsOf, hv, List.cons_append, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ,
    List.getElem_append_left, List.getElem_append_right, Vector.getElem_toList] at i0 i1 i2 i3 i4 i5
  have hH : (E0).H = keccakBytes := rfl
  have v0 := vals_seed index stmt p frame rw rt
  have v13 := values_hash_st hH n13 v0 (ys := [p.witness.root.1, p.witness.root.2, p.witness.ood])
    (by simp only [List.map_cons, List.map_nil, r0.1, r0.2, i0, b0.1, b0.2])
  have v15 := values_hash_st hH n15 v13 (ys := []) rfl
  have v17 := values_hash_st hH n17 v15 (ys := []) rfl
  have v22 := values_hash_st hH n22 v17 (ys := [p.table.root.1, p.table.root.2, p.table.ood])
    (by simp only [List.map_cons, List.map_nil, r1.1, r1.2, i1, b1.1, b1.2])
  have v28 := values_hash_st hH n28 v22 (ys := p.values.toList ++ [p.next])
    (by
      rw [hv]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, i2, i3, i4, i5])
  refine ⟨r0.1.trans b0.1.symm, r0.2.trans b0.2.symm, i0, r1.1.trans b1.1.symm, r1.2.trans b1.2.symm, i1,
    i2, i3, i4, i5, values_low_st n14 v13, values_low_st n16 v15, values_low_st n18 v17,
    values_low_st n23 v22, values_low_st n29 v28⟩

end Calldata

end Implementation
