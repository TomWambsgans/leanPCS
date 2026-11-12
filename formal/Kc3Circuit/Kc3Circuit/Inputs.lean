-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Circuit/Outputs.lean` and `Build.lean` (`u8_bit`)
-- (commit `f96a7938`): a secret's input bits, and `secretOfInputs` inverting them.
import Kc3Circuit.Secret
import Circuit.Defs

/-!
# A secret's input bits

* `membershipInputs_eq`: the Statement's `membershipInputs` is `formal/Circuit`'s `Secret.inputs` of the same
  secret (`secretTr`); `membershipInputs_length`: `8480` bits;
* `secretOfInputs_membershipInputs`: `secretOfInputs` inverts `membershipInputs`.
-/

namespace Kc3Bridge

theorem u8_bit (b : UInt8) (k : ℕ) (hk : k < 8) :
    (b >>> k.toUInt8 &&& 1 = 1) ↔ b.toNat.testBit k = true := by
  rw [← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight]
  have hk' : k.toUInt8.toNat % 8 = k := by
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega
  rw [hk', UInt8.toNat_one, Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (b.toNat >>> k) with h | h <;> simp [h]

/-- A statement secret as `formal/Circuit`'s. -/
def secretTr (w : PcsQuotient.Secret) : PcsCircuit.Secret where
  x := w.x.toList
  siblings := w.siblings.toList.map Vector.toList
  directions := PcsCircuit.bitsToNat w.directions.toList

theorem bits_eq (b : PcsQuotient.Bytes32) :
    ((List.range 256).map fun i => decide ((b.toList.getD (i / 8) 0 >>> (i % 8).toUInt8) &&& 1 = 1)) =
      PcsCircuit.bytesBits b.toList := by
  unfold PcsCircuit.bytesBits
  refine List.map_congr_left fun i _ => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact u8_bit _ _ (Nat.mod_lt _ (by norm_num))

theorem secretTr_siblings (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) :
    (secretTr w).siblings.getD i [] = w.siblings[i].toList := by
  simp [secretTr, List.getD_eq_getElem?_getD]

theorem secretTr_directions (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) :
    (secretTr w).directions.testBit i = w.directions[i] := by
  simp [secretTr, PcsCircuit.bitsToNat_testBit, List.getD_eq_getElem?_getD]

/-- **The input bits of a secret**: the Statement's `membershipInputs` is `formal/Circuit`'s `Secret.inputs`. -/
theorem membershipInputs_eq (w : PcsQuotient.Secret) :
    PcsQuotient.membershipInputs w = (secretTr w).inputs.toList := by
  unfold PcsQuotient.membershipInputs PcsCircuit.Secret.inputs
  simp only [List.toList_toArray]
  rw [bits_eq]
  congr 1
  have hr : List.range PcsCircuit.depth = (List.finRange PcsQuotient.depth).map Fin.val :=
    (finRange_map_val 32).symm
  rw [hr]
  simp only [List.flatMap, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  rw [bits_eq, secretTr_siblings, secretTr_directions]

theorem membershipInputs_length (w : PcsQuotient.Secret) :
    (PcsQuotient.membershipInputs w).length = 8480 := by
  simp [PcsQuotient.membershipInputs, PcsQuotient.depth]

theorem byteOfBits_testBit_self (b : UInt8) : PcsCircuit.byteOfBits (fun t => b.toNat.testBit t) = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · rw [PcsCircuit.byteOfBits_testBit _ _ ht]
  · have h1 : (PcsCircuit.byteOfBits fun t => b.toNat.testBit t).toNat < 2 ^ 8 := UInt8.toNat_lt _
    have h2 : b.toNat < 2 ^ 8 := UInt8.toNat_lt _
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem bytesOfBits_bits (b : PcsQuotient.Bytes32) (f : ℕ → Bool)
    (hf : ∀ t < 256, f t = (b.toList.getD (t / 8) 0).toNat.testBit (t % 8)) :
    PcsCircuit.bytesOfBits f = b.toList := by
  unfold PcsCircuit.bytesOfBits
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [byteOfBits_congr (g := fun t => (b.toList.getD p 0).toNat.testBit t) fun t ht => by
    rw [hf _ (by omega)]
    congr 3 <;> omega]
  rw [byteOfBits_testBit_self, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]
  rfl

theorem length_flatMap_range (g : ℕ → List Bool) (m : ℕ) (hg : ∀ j, (g j).length = m) :
    ∀ n, ((List.range n).flatMap g).length = m * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range g m hg n]
    simp [hg]
    ring

theorem getD_flatMap_range (g : ℕ → List Bool) (m : ℕ) (hg : ∀ j, (g j).length = m) :
    ∀ n i t, i < n → t < m → ((List.range n).flatMap g).getD (m * i + t) false = (g i).getD t false
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, t, hi, ht => by
    rw [List.range_succ, List.flatMap_append]
    have hl := length_flatMap_range g m hg n
    rcases Nat.lt_or_ge i n with hin | hin
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      exact getD_flatMap_range g m hg n i t hin ht
    · have hi' : i = n := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      omega

theorem membershipInputs_level (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) (t : ℕ)
    (ht : t < 257) :
    (PcsQuotient.membershipInputs w).getD (256 + 257 * i.val + t) false =
      (PcsCircuit.bytesBits w.siblings[i].toList ++ [w.directions[i]]).getD t false := by
  rw [membershipInputs_eq]
  simp only [PcsCircuit.Secret.inputs, List.toList_toArray]
  rw [List.getD_append_right _ _ _ _ (by simp [PcsCircuit.bytesBits]; omega)]
  have hlen : (PcsCircuit.bytesBits (secretTr w).x).length = 256 := by simp [PcsCircuit.bytesBits]
  rw [hlen, show 256 + 257 * i.val + t - 256 = 257 * i.val + t by omega]
  rw [getD_flatMap_range _ 257 (fun j => by simp [PcsCircuit.bytesBits]) PcsCircuit.depth i t i.isLt ht]
  rw [secretTr_siblings, secretTr_directions]

theorem membershipInputs_x (w : PcsQuotient.Secret) (t : ℕ) (ht : t < 256) :
    (PcsQuotient.membershipInputs w).getD t false =
      (w.x.toList.getD (t / 8) 0).toNat.testBit (t % 8) := by
  rw [membershipInputs_eq]
  simp only [PcsCircuit.Secret.inputs, List.toList_toArray]
  rw [List.getD_append _ _ _ _ (by simp [PcsCircuit.bytesBits]; omega)]
  simp [PcsCircuit.bytesBits, List.getD_eq_getElem?_getD, ht, secretTr]

/-- **`secretOfInputs` inverts `membershipInputs`**. -/
theorem secretOfInputs_membershipInputs (w : PcsQuotient.Secret) :
    PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs w) = w := by
  obtain ⟨x, sib, dir⟩ := w
  have hx : (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).x = x := by
    apply Vector.toList_inj.mp
    rw [secretOfInputs_x]
    exact bytesOfBits_bits x _ fun t ht => membershipInputs_x _ t ht
  have hs : ∀ i : Fin PcsQuotient.depth,
      (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).siblings[i] = sib[i] := by
    intro i
    apply Vector.toList_inj.mp
    rw [secretOfInputs_siblings]
    refine bytesOfBits_bits sib[i] _ fun t ht => ?_
    rw [membershipInputs_level _ i t (by omega), List.getD_append _ _ _ _ (by
      simp [PcsCircuit.bytesBits]; omega)]
    simp [PcsCircuit.bytesBits, List.getD_eq_getElem?_getD, ht]
  have hd : ∀ i : Fin PcsQuotient.depth,
      (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).directions[i] = dir[i] := by
    intro i
    rw [secretOfInputs_directions, membershipInputs_level _ i 256 (by omega),
      List.getD_append_right _ _ _ _ (by simp [PcsCircuit.bytesBits])]
    simp [PcsCircuit.bytesBits]
  cases h : PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩) with
  | mk x' sib' dir' =>
    rw [h] at hx hs hd
    simp only at hx hs hd
    subst hx
    congr 1
    · exact Vector.ext fun i hi => hs ⟨i, hi⟩
    · exact Vector.ext fun i hi => hd ⟨i, hi⟩

end Kc3Bridge
