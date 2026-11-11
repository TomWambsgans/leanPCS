-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The byte lemmas of
-- `RecCompose/Pi1Decode.lean` and `RecCompose/OpeningsAgree.lean` (`le_fold`, `digestOfBytes32_digestBytes`), for the
-- Fiat–Shamir layer's files, which import neither.
import RecStatement
import UniKeccakComplete.K.AlgCRun
import UniKeccakComplete.K.SyncBasic

/-!
# A digest's bytes read back

`RecStatement.rootOfWord` (`UniStatement.digestOfBytes32`: four little-endian words) of a digest's bytes is the digest
(`rootOfWord_digestBytes`); an element's word read back is the element (`elementOfWord_elementWord`).
-/

namespace RecCompose.FsBytes

open RecStatement UniStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

theorem byte_toNat (u : UInt64) {k : ℕ} (hk : k < 8) :
    ((u >>> (8 * k).toUInt64).toUInt8).toNat = u.toNat / 2 ^ (8 * k) % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (8 * k).toUInt64.toNat % 64 = 8 * k := by interval_cases k <;> rfl
  rw [this]

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

theorem le_fold (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (u >>> (8 * k).toUInt64).toUInt8) :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64)) (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [le_fold_toNat u f hf 8 le_rfl, Nat.mod_eq_of_lt (by simpa using u.toNat_lt)]

theorem getD_append_left {l r : List UInt8} {k : ℕ} (h : k < l.length) : (l ++ r).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (l r : List UInt8) (k : ℕ) : (l ++ r).getD (l.length + k) 0 = r.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

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
    · refine le_fold a _ fun k hk ↦ ?_
      rw [show 8 * 0 + k = k by ring, getD_append_left (by rw [l8]; exact hk), hw a hk]
    · refine le_fold b _ fun k hk ↦ ?_
      rw [show 8 * 1 + k = (wordBytes a).length + k by rw [l8], getD_append_right,
        getD_append_left (by rw [l8]; exact hk), hw b hk]
    · refine le_fold c _ fun k hk ↦ ?_
      rw [show 8 * 2 + k = (wordBytes a).length + ((wordBytes b).length + k) by rw [l8, l8]; ring,
        getD_append_right, getD_append_right, getD_append_left (by rw [l8]; exact hk), hw c hk]
    · refine le_fold e _ fun k hk ↦ ?_
      rw [show 8 * 3 + k = (wordBytes a).length + ((wordBytes b).length + ((wordBytes c).length + k)) by
          rw [l8, l8, l8]; ring,
        getD_append_right, getD_append_right, getD_append_right, hw e hk]

/-- **A root word of a digest's bytes names the digest.** -/
theorem rootOfWord_digestBytes (d : Digest) : rootOfWord (digestBytes d) = d :=
  digestOfBytes32_digestBytes d

@[simp] theorem length_elementWord (x : E) : (elementWord x).length = 32 := by
  simp [elementWord]

theorem fold_be64_at (pre post : List UInt8) (u : UInt64) (at' : ℕ) (h : pre.length = at') :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((pre ++ be64 u ++ post).getD (at' + k) 0).toUInt64)
      (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [UniKeccakComplete.AlgC.run_fold_be64 u (fun k ↦ (pre ++ be64 u ++ post).getD (at' + k) 0) (fun k hk ↦ by
    rw [← h, List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simp [be64]; omega)]) 8 le_rfl]
  simp

/-- **An element's word read back** (`elementOfWord`) is the element. -/
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

/-- Elements' words read back. -/
theorem mapM_elementOfWord (l : List E) : (l.map elementWord).mapM elementOfWord = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, elementOfWord_elementWord, ih]

/-- Elements' words read back, as `mapM` of the composite. -/
theorem mapM_comp_elementOfWord : ∀ l : List E, List.mapM (elementOfWord ∘ elementWord) l = some l
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, mapM_comp_elementOfWord l]
    simp [elementOfWord_elementWord]

/-- A list read by `mapM` keeps its length. -/
theorem length_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β), l.mapM f = some l' →
    l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        simp [length_of_mapM f l bs hl]

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

end RecCompose.FsBytes
