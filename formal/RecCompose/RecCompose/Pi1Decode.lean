-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The byte round trips go through `UInt64.toNat`, as
-- `formal/UniComplete/UniComplete/AlgCRun.lean`'s `run_fold_be64` (reused) and `SyncBasic.lean`'s do.
import RecCompose.Basic
import UniKeccakComplete.K.AlgCRun
import UniKeccakComplete.K.SyncBasic
import UniSound.FsWalkProof

/-!
# π1's own claims, decoded

`decodePi1Call` (`RecStatement.Security`) reads the Keccak π1's contract's claim words (`UniKeccak.pcsClaimWordsK`: the
root's 32 bytes, the out-of-domain answer's word, the point's coordinates' words, the value's word) back into the
claim's root (`digestOfBytes32` of the bytes), answer, point and value (`decodePi1Call_claim`); `C1`'s and `C2`'s roots
are the stream's bytes `rootWord h`, which read back to `rootOf h` (`digestOfBytes32_rootWord`), the setup's
`digestBytes F`, which reads back to `F` (`digestOfBytes32_digestBytes`). A decoded claim's point has the word count
less three coordinates (`claimOfWords_length`).
-/

namespace RecCompose.Pi1Decode

open RecStatement UniStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Words -/

theorem length_be64 (u : UInt64) : (be64 u).length = 8 := by simp [be64]

@[simp] theorem length_elementWord (x : E) : (elementWord x).length = 32 := by
  simp [elementWord]

@[simp] theorem length_numberWord (n : ℕ) : (numberWord n).length = 32 := by
  simp [numberWord]

/-- The big-endian fold of `be64 u` placed at `at'` is `u`. -/
theorem fold_be64_at (pre post : List UInt8) (u : UInt64) (at' : ℕ) (h : pre.length = at') :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((pre ++ be64 u ++ post).getD (at' + k) 0).toUInt64)
      (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [UniKeccakComplete.AlgC.run_fold_be64 u (fun k ↦ (pre ++ be64 u ++ post).getD (at' + k) 0) (fun k hk ↦ by
    rw [← h, List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [length_be64]; omega)]) 8 le_rfl]
  simp

/-- **An element word reads back its element.** -/
theorem elementOfWord_elementWord (x : E) : elementOfWord (elementWord x) = some x := by
  unfold elementOfWord
  have hz : ((elementWord x).take 8).all (· = 0) = true := by
    simp [elementWord]
  rw [ite_eq_left ⟨length_elementWord x, by simpa using hz⟩]
  have e : elementWord x = (List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane) ++
      be64 (x.limb 0).lane ++ [] := by simp [elementWord, List.append_assoc]
  have h24 := fold_be64_at (List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane) [] (x.limb 0).lane 24
    (by simp)
  have h16 := fold_be64_at (List.replicate 8 0 ++ be64 (x.limb 2).lane) (be64 (x.limb 0).lane) (x.limb 1).lane 16
    (by simp)
  have h8 := fold_be64_at (List.replicate 8 0) (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) (x.limb 2).lane 8
    (by simp)
  have e16 : elementWord x = List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++
      be64 (x.limb 0).lane := by simp [elementWord]
  have e8 : elementWord x = List.replicate 8 0 ++ be64 (x.limb 2).lane ++
      (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) := by simp [elementWord, List.append_assoc]
  rw [← e] at h24
  rw [show List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++ be64 (x.limb 0).lane =
    elementWord x from e16.symm] at h16
  rw [show List.replicate 8 0 ++ be64 (x.limb 2).lane ++ (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) =
    elementWord x from e8.symm] at h8
  simp only [h24, h16, h8]
  exact congrArg some (UniKeccakComplete.eNew_limbs x)

/-! ## A root word read back -/

/-- Byte `k` of a word, little-endian, as a number. -/
theorem byte_toNat (u : UInt64) {k : ℕ} (hk : k < 8) :
    ((u >>> (8 * k).toUInt64).toUInt8).toNat = u.toNat / 2 ^ (8 * k) % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (8 * k).toUInt64.toNat % 64 = 8 * k := by interval_cases k <;> rfl
  rw [this]

/-- The little-endian fold of a word's first `j` bytes is the word modulo `2^(8 j)`. -/
theorem le_fold_toNat (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (u >>> (8 * k).toUInt64).toUInt8) :
    ∀ j ≤ 8, ((List.range j).foldl (fun (acc : UInt64) k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64))
      (0 : UInt64)).toNat = u.toNat % 2 ^ (8 * j)
  | 0, _ => by simp [Nat.mod_one]
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.toNat_or,
      le_fold_toNat u f hf j (by omega), UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hf j (by omega),
      byte_toNat u (by omega)]
    have h64 : (8 * j).toUInt64.toNat % 64 = 8 * j := by
      have : j < 8 := by omega
      interval_cases j <;> rfl
    rw [h64]
    have hlt : (u.toNat / 2 ^ (8 * j) % 256) <<< (8 * j) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      calc u.toNat / 2 ^ (8 * j) % 256 * 2 ^ (8 * j) < 256 * 2 ^ (8 * j) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by norm_num)) (by positivity)
        _ = 2 ^ (8 * j + 8) := by rw [pow_add]; ring
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt hlt, Nat.lor_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)), Nat.shiftLeft_eq,
      show 8 * (j + 1) = 8 * j + 8 by ring, pow_add, Nat.mod_mul]
    ring_nf

/-- **The little-endian fold of a word's bytes is the word.** -/
theorem le_fold (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (u >>> (8 * k).toUInt64).toUInt8) :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64)) (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [le_fold_toNat u f hf 8 le_rfl, Nat.mod_eq_of_lt (by simpa using u.toNat_lt)]

/-- Byte `k` of `be64 u` reversed is the word's byte `k`, little-endian. -/
theorem be64_reverse_getD (u : UInt64) {k : ℕ} (hk : k < 8) :
    (be64 u).reverse.getD k 0 = (u >>> (8 * k).toUInt64).toUInt8 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [length_be64]; exact hk), length_be64,
    ← List.getD_eq_getElem?_getD, UniKeccakComplete.be64_getD u (by omega)]
  congr 3
  omega

theorem getD_append_left {l r : List UInt8} {k : ℕ} (h : k < l.length) : (l ++ r).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (l r : List UInt8) (k : ℕ) : (l ++ r).getD (l.length + k) 0 = r.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

/-! ## A call's words -/

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

/-- **Words of 32 bytes, concatenated, are cut back into them.** -/
theorem chunks_flatten : ∀ (W : List (List UInt8)), (∀ w ∈ W, w.length = 32) →
    (List.range (W.flatten.length / 32)).map (fun j ↦ (W.flatten.drop (32 * j)).take 32) = W
  | [], _ => by simp
  | a :: W, h => by
    have ha : a.length = 32 := h a (List.mem_cons_self ..)
    have hW : ∀ w ∈ W, w.length = 32 := fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    have hl : (a :: W).flatten.length / 32 = W.flatten.length / 32 + 1 := by
      rw [List.flatten_cons, List.length_append, ha]
      omega
    rw [hl, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons]
    congr 1
    · simp [List.take_left' ha]
    · conv_rhs => rw [← chunks_flatten W hW]
      refine List.map_congr_left fun j _ ↦ ?_
      simp only [Function.comp_apply]
      rw [show 32 * (j + 1) = a.length + 32 * j by rw [ha]; ring, ← List.drop_drop, List.drop_left]

theorem mapM_map_succ {β : Type} (gf : ℕ → Option β) : ∀ (l : List ℕ),
    (l.map Nat.succ).mapM gf = l.mapM fun j ↦ gf (j + 1)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, mapM_map_succ gf l, Nat.succ_eq_add_one]

/-- `n` reads that each give the list's entry give the list. -/
theorem mapM_range_eq_some {β : Type} (d : β) : ∀ (l : List β) (gf : ℕ → Option β),
    (∀ j < l.length, gf j = some (l.getD j d)) → (List.range l.length).mapM gf = some l
  | [], _, _ => rfl
  | a :: l, gf, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.mapM_cons, mapM_map_succ,
      mapM_range_eq_some d l (fun j ↦ gf (j + 1)) fun j hj ↦ by
        rw [h (j + 1) (by simp; omega)]; rfl, h 0 (by simp)]
    rfl

theorem length_flatten_32 : ∀ (W : List (List UInt8)), (∀ w ∈ W, w.length = 32) → W.flatten.length = 32 * W.length
  | [], _ => rfl
  | a :: W, h => by
    rw [List.flatten_cons, List.length_append, h a (List.mem_cons_self ..),
      length_flatten_32 W fun w hw ↦ h w (List.mem_cons_of_mem _ hw), List.length_cons]
    ring

theorem getD_append_left' {α : Type} {l r : List α} {k : ℕ} (d : α) (h : k < l.length) :
    (l ++ r).getD k d = l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} (l r : List α) (k : ℕ) (d : α) : (l ++ r).getD (l.length + k) d = r.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

/-- Element words read back. -/
theorem mapM_elementOfWord : ∀ l : List E, (l.map elementWord).mapM elementOfWord = some l
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.mapM_cons, elementOfWord_elementWord, mapM_elementOfWord l]
    rfl

/-- `mapM` in `Option` keeps the length. -/
theorem length_of_mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys.length = l.length
  | [], ys, h => by simp only [List.mapM_nil] at h; cases h; rfl
  | x :: l, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys', hys', rfl⟩ := h
    simp [length_of_mapM_some f l ys' hys']

/-- **A decoded claim's point has its words' count less three coordinates.** -/
theorem claimOfWords_length (w : List (List UInt8)) (x : Pi1Opening) (h : claimOfWords w = some x) :
    x.2.2.1.length = w.length - 3 := by
  unfold claimOfWords at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨root, -, oodW, -, valueW, -, h⟩ := h

  split at h
  · exact absurd h (by simp)
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ood, -, pt, hpt, value, -, rfl⟩ := h
    rw [length_of_mapM_some _ _ _ hpt]
    simp
    omega

/-- **π1's claim words, decoded** (`decodePi1Call` of `pcsClaimWordsK`' words of a point claim): the root's bytes read
back (`digestOfBytes32`), the out-of-domain answer, the point, the value. -/
theorem decodePi1Call_claim (rootB : List UInt8) (ood : E) (pt : List E) (v : E) (hr : rootB.length = 32) :
    decodePi1Call (rootB ++ elementWord ood ++ pt.flatMap elementWord ++ elementWord v) =
      some (digestOfBytes32 rootB, ood, pt, v) := by
  set W : List (List UInt8) := [rootB, elementWord ood] ++ (pt.map elementWord ++ [elementWord v]) with hW
  have hcall : rootB ++ elementWord ood ++ pt.flatMap elementWord ++ elementWord v = W.flatten := by
    simp [hW, List.flatten_append, List.flatMap, List.append_assoc]
  have hlen : ∀ w ∈ W, w.length = 32 := by
    intro w hw'
    simp only [hW, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hw'
    rcases hw' with (rfl | rfl) | ⟨x, -, rfl⟩ | rfl <;> simp [hr]
  have hflen : W.flatten.length = 32 * W.length := length_flatten_32 W hlen
  unfold decodePi1Call words32
  rw [hcall, ite_eq_right (by rw [hflen]; omega), chunks_flatten W hlen]
  unfold claimOfWords
  have h0 : W.head? = some rootB := rfl
  have h1 : W[1]? = some (elementWord ood) := rfl
  have hl : W.getLast? = some (elementWord v) := by
    rw [hW, List.getLast?_append, List.getLast?_append]
    simp
  have hd : (W.drop 2).dropLast = pt.map elementWord := by simp [hW]
  have hc : (3 ≤ W.length ∧ rootB.length = 32) := ⟨by simp [hW], hr⟩
  have hm : pt.mapM (elementOfWord ∘ elementWord) = some pt := by
    rw [← mapM_elementOfWord pt, List.mapM_map]
  simp [h0, h1, hl, hd, hc, elementOfWord_elementWord, hm, rootOfWord]


end RecCompose.Pi1Decode

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A digest's bytes read back. -/
theorem digestOfBytes32_digestBytes (d : Digest) : UniStatement.digestOfBytes32 (digestBytes d) = d := by
  have l8 : ∀ u : UInt64, (wordBytes u).length = 8 := fun u ↦ by simp [wordBytes]
  have hw : ∀ (u : UInt64) {k : ℕ}, k < 8 → (wordBytes u).getD k 0 = (u >>> (8 * k).toUInt64).toUInt8 := by
    intro u k hk
    simp [wordBytes, List.getD_eq_getElem?_getD, hk]
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [a, b, c, e], _ =>
    have hb : digestBytes ⟨⟨[a, b, c, e]⟩, rfl⟩ = wordBytes a ++ (wordBytes b ++ (wordBytes c ++ wordBytes e)) := by
      simp [digestBytes]
    unfold UniStatement.digestOfBytes32
    rw [hb]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    interval_cases j
    · refine Pi1Decode.le_fold a _ fun k hk ↦ ?_
      rw [show 8 * 0 + k = k by ring, Pi1Decode.getD_append_left (by rw [l8]; exact hk), hw a hk]
    · refine Pi1Decode.le_fold b _ fun k hk ↦ ?_
      rw [show 8 * 1 + k = (wordBytes a).length + k by rw [l8], Pi1Decode.getD_append_right,
        Pi1Decode.getD_append_left (by rw [l8]; exact hk), hw b hk]
    · refine Pi1Decode.le_fold c _ fun k hk ↦ ?_
      rw [show 8 * 2 + k = (wordBytes a).length + ((wordBytes b).length + k) by rw [l8, l8]; ring,
        Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, Pi1Decode.getD_append_left (by rw [l8]; exact hk),
        hw c hk]
    · refine Pi1Decode.le_fold e _ fun k hk ↦ ?_
      rw [show 8 * 3 + k = (wordBytes a).length + ((wordBytes b).length + ((wordBytes c).length + k)) by
          rw [l8, l8, l8]; ring,
        Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, hw e hk]

/-- **A stream root's bytes read back** to the root π1's verifier names (`rootOf`). -/
theorem digestOfBytes32_rootWord (h : E × E) : UniStatement.digestOfBytes32 (UniStatement.rootWord h) =
    UniStatement.rootOf h := by
  rw [← UniSound.digestBytes_rootOf, digestOfBytes32_digestBytes]

end RecCompose

/-- info: 'RecCompose.Pi1Decode.elementOfWord_elementWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Decode.elementOfWord_elementWord

/-- info: 'RecCompose.Pi1Decode.decodePi1Call_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Decode.decodePi1Call_claim
