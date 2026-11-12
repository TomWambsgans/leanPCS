-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The encoding is `crates/pcs_claim`'s (`PcsClaim::encode`,
-- `RecStatement.pcsClaimBytes`).
import RecStatement.Security

/-!
# A PCS claim's encoding determines the claim

`pcsClaimBytes` writes a claim's words as the EIP draft's encoding: `[1, n]`, the root's 32 bytes, then each element
word's low 24 bytes. On words that decode (`claimOfWords`: a 32-byte root, every element word 32 bytes with its top 8
bytes zero) it loses nothing: **`words_eq_of_pcsClaimBytes`**, two decodable claims of one encoding are the same words,
so **`claimOfWords_eq_of_pcsClaimBytes`**, the same claim. (π2's circuit binds π1's claims by their encodings'
Keccak-256s; where the encodings agree, the claims do.)
-/

namespace RecCompose

open RecStatement LeanVM.Parameters

/-- The list's 24-byte chunks (its last one shorter). -/
def chunks24 (l : List UInt8) : List (List UInt8) :=
  if l = [] then [] else l.take 24 :: chunks24 (l.drop 24)
termination_by l.length
decreasing_by
  rename_i h
  have : 0 < l.length := List.length_pos_iff.mpr h
  simp only [List.length_drop]
  omega

theorem chunks24_nil : chunks24 [] = [] := by
  rw [chunks24]; simp

theorem chunks24_append (a r : List UInt8) (ha : a.length = 24) : chunks24 (a ++ r) = a :: chunks24 r := by
  have hne : a ++ r ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [ha] at this
  have h1 : (a ++ r).take 24 = a := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have h2 : (a ++ r).drop 24 = r := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  rw [chunks24]
  simp only [hne, ↓reduceIte]
  rw [h1, h2]

/-- An element word: 32 bytes, its top 8 zero. -/
def ElemWord (w : List UInt8) : Prop := w.length = 32 ∧ w.take 8 = List.replicate 8 0

theorem elemWord_of_elementOfWord {w : List UInt8} {x : E} (h : elementOfWord w = some x) : ElemWord w := by
  unfold elementOfWord at h
  split at h
  · rename_i hw
    refine ⟨hw.1, ?_⟩
    have h8 : (w.take 8).length = 8 := by rw [List.length_take]; omega
    exact List.eq_replicate_iff.mpr ⟨h8, fun b hb ↦ by simpa using List.all_eq_true.mp hw.2 b hb⟩
  · exact absurd h (by simp)

theorem elemWord_restore {w : List UInt8} (h : ElemWord w) : List.replicate 8 0 ++ w.drop 8 = w := by
  rw [← h.2, List.take_append_drop]

theorem chunks24_flatMap : ∀ ws : List (List UInt8), (∀ w ∈ ws, ElemWord w) →
    chunks24 (ws.flatMap (·.drop 8)) = ws.map (·.drop 8)
  | [], _ => by simp [chunks24_nil]
  | w :: ws, h => by
    rw [List.flatMap_cons, chunks24_append _ _ (by rw [List.length_drop, (h w (by simp)).1]),
      chunks24_flatMap ws fun v hv ↦ h v (by simp [hv]), List.map_cons]

/-- **The words back from an encoding**: the root (bytes `2 … 34`), then each 24-byte chunk with its 8 zero bytes. -/
def restoreWords (bytes : List UInt8) : List (List UInt8) :=
  (bytes.drop 2).take 32 :: (chunks24 ((bytes.drop 2).drop 32)).map (List.replicate 8 0 ++ ·)

theorem mapM_some_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (ys : List β), l.mapM f = some ys →
    ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => absurd hx (by simp)
  | a :: l, ys, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, ys', hys', -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact mapM_some_mem f l ys' hys' x hx

/-- **What a decoded claim's words are**: a 32-byte root, then element words. -/
theorem claimOfWords_words {ws : List (List UInt8)} {x : Pi1Opening} (h : claimOfWords ws = some x) :
    ∃ r rest, ws = r :: rest ∧ r.length = 32 ∧ ∀ w ∈ rest, ElemWord w := by
  unfold claimOfWords at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨root, hr, oodW, ho, valueW, hv, h⟩ := h
  split at h
  · exact absurd h (by simp)
  rename_i hlen
  have hl : 3 ≤ ws.length ∧ root.length = 32 := by
    by_contra hc
    exact hlen (by simp [hc])
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨ood, hood, pt, hpt, value, hval, -⟩ := h
  obtain ⟨r, o, mid, rfl⟩ : ∃ r o mid, ws = r :: o :: mid := by
    match ws, hl.1 with
    | r :: o :: mid, _ => exact ⟨r, o, mid, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hr
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ho
  subst hr ho
  refine ⟨_, _, rfl, hl.2, fun w hw ↦ ?_⟩
  rcases List.mem_cons.mp hw with rfl | hw
  · exact elemWord_of_elementOfWord hood
  · have hmid : mid ≠ [] := by
      intro h0; subst h0; simp at hl
    have hsplit := List.dropLast_append_getLast hmid
    rw [← hsplit] at hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy⟩ := mapM_some_mem _ _ _ hpt w (by simpa using hw)
      exact elemWord_of_elementOfWord hy
    · rw [List.mem_singleton] at hw
      subst hw
      have hl2 : (r :: o :: mid).getLast? = some (mid.getLast hmid) := by
        rw [List.getLast?_eq_some_getLast (by simp), List.getLast_cons (by simp), List.getLast_cons hmid]
      rw [hl2, Option.some.injEq] at hv
      rw [hv]
      exact elemWord_of_elementOfWord hval

/-- **A decodable claim's words are restored from its encoding.** -/
theorem restoreWords_pcsClaimBytes {ws : List (List UInt8)} {x : Pi1Opening} (h : claimOfWords ws = some x) :
    restoreWords (pcsClaimBytes ws) = ws := by
  obtain ⟨r, rest, rfl, hr, hrest⟩ := claimOfWords_words h
  have e : (pcsClaimBytes (r :: rest)).drop 2 = r ++ rest.flatMap (·.drop 8) := by
    simp [pcsClaimBytes]
  unfold restoreWords
  rw [e, List.take_left' hr, List.drop_left' hr, chunks24_flatMap rest hrest, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id rest]
  exact List.map_congr_left fun w hw ↦ elemWord_restore (hrest w hw)

/-- **Two decodable claims of one encoding are the same words.** -/
theorem words_eq_of_pcsClaimBytes {a b : List (List UInt8)} {x y : Pi1Opening} (ha : claimOfWords a = some x)
    (hb : claimOfWords b = some y) (h : pcsClaimBytes a = pcsClaimBytes b) : a = b := by
  rw [← restoreWords_pcsClaimBytes ha, ← restoreWords_pcsClaimBytes hb, h]

/-- **Two decodable claims of one encoding are the same claim.** -/
theorem claimOfWords_eq_of_pcsClaimBytes {a b : List (List UInt8)} {x y : Pi1Opening}
    (ha : claimOfWords a = some x) (hb : claimOfWords b = some y) (h : pcsClaimBytes a = pcsClaimBytes b) : x = y := by
  rw [words_eq_of_pcsClaimBytes ha hb h, hb] at ha
  exact (Option.some.inj ha).symm

end RecCompose
