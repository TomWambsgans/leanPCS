-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.BridgeKeccak

/-!
# The membership rows: the two builders make the same rows

`sim_membershipBuilder`: from every builder, the statement's `membershipBuilder` and F0b's
`membershipBuild` make the same rows and inputs and return the same wires of `y` and of the root
(read by `srcTr`). `finish_rows`: the closed circuits' rows are the same, for every builder and
wires of `y` and root.
-/

namespace Kc3Bridge

/-! ## The statement's builder, its loops named -/

namespace Q

open PcsQuotient PcsQuotient.Build

/-- One bit of a level's swap. -/
def swapStep (node sibling : List Src) (keep : Src) (i : ℕ) (lr : Array Src × Array Src) :
    BuildM (ForInStep (Array Src × Array Src)) := do
  let differ ← xor (node.getD i .zero) (sibling.getD i .zero)
  let l ← chi (node.getD i .zero) keep differ
  let r ← xor l differ
  pure (ForInStep.yield (lr.1.push l, lr.2.push r))

/-- One level of the path. -/
def levelStep (node : List Src) : BuildM (ForInStep (List Src)) := do
  let sibling ← (List.range 256).mapM fun _ => input
  let direction ← input
  let keep ← not direction
  let lr ← forIn [:256] ((#[] : Array Src), (#[] : Array Src)) fun i lr => swapStep node sibling keep i lr
  let node ← keccak256Block (lr.1.toList ++ lr.2.toList)
  pure (ForInStep.yield node)

/-- The membership rows. -/
def membershipBuilder : BuildM (List Src × List Src) := do
  let x ← (List.range 256).mapM fun _ => input
  let y ← keccak256Block (x ++ constantBlock yPad)
  let node ← keccak256Block (x ++ constantBlock leafPad)
  let root ← forIn [:depth] node fun _ node => levelStep node
  pure (y, root)

end Q

theorem membershipBuilder_eq : PcsQuotient.membershipBuilder = Q.membershipBuilder := by
  simp only [PcsQuotient.membershipBuilder, Q.membershipBuilder, Q.levelStep, Q.swapStep]

/-! ## Wires -/

theorem getD_toArray_map (l : List PcsQuotient.Src) (k : ℕ) :
    (l.map srcTr).toArray.getD k .zero = srcTr (l.getD k .zero) := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[k]? <;> rfl

theorem u8_bit (b : UInt8) (k : ℕ) (hk : k < 8) :
    (b >>> k.toUInt8 &&& 1 = 1) ↔ b.toNat.testBit k = true := by
  rw [← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight]
  have hk' : k.toUInt8.toNat % 8 = k := by
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega
  rw [hk', UInt8.toNat_one, Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (b.toNat >>> k) with h | h <;> simp [h]

theorem constantBlock_map (byte : UInt8) :
    ((PcsQuotient.constantBlock byte).map srcTr).toArray = Kc3Circuit.constantBlock byte := by
  unfold PcsQuotient.constantBlock Kc3Circuit.constantBlock
  congr 1
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  by_cases h : byte.toNat.testBit (i % 8) = true
  · rw [if_pos ((u8_bit byte (i % 8) (Nat.mod_lt _ (by norm_num))).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((u8_bit byte (i % 8) (Nat.mod_lt _ (by norm_num))).mp h')), if_neg h]; rfl

theorem yPad_eq : PcsQuotient.yPad = PcsCircuit.yPad := rfl
theorem leafPad_eq : PcsQuotient.leafPad = PcsCircuit.leafPad := rfl
theorem depth_eq : PcsQuotient.depth = PcsCircuit.depth := rfl

/-! ## A level, the membership rows -/

theorem sim_levelStep (node : List PcsQuotient.Src) :
    SimR (Q.levelStep node) (Kc3Circuit.level (node.map srcTr).toArray)
      (fun st t => ∃ s', st = .yield s' ∧ t = (s'.map srcTr).toArray) := by
  unfold Q.levelStep Kc3Circuit.level
  simp only [Kc3Circuit.Builder.freeBits, bind_assoc, pure_bind]
  refine (simS_mapM (List.range 256) _ _ fun _ _ => sim_input).bind fun sib sib' hsib => ?_
  subst hsib
  refine sim_input.bind fun d d' hd => ?_
  subst hd
  refine (sim_not d).bind fun keep keep' hk => ?_
  subst hk
  rw [forIn_range]
  refine (simR_forIn (List.range 256) _ _
    (fun lrs (lr : Array PcsQuotient.Src × Array PcsQuotient.Src) =>
      lr.1.toList.map srcTr = lrs.map Prod.fst ∧ lr.2.toList.map srcTr = lrs.map Prod.snd)
    [] (#[], #[]) ⟨rfl, rfl⟩ fun i hi acc lr _ hlr => ?_).bind fun lr lrs h => ?_
  · simp only [List.getElem_range]
    unfold Q.swapStep
    rw [getD_toArray_map, getD_toArray_map]
    refine (sim_xor _ _).bind fun df df' hdf => ?_
    subst hdf
    refine (sim_chi _ _ _).bind fun l l' hl => ?_
    subst hl
    refine (sim_xor _ _).bind fun r r' hr => ?_
    subst hr
    exact SimR.pure ⟨_, rfl, by simp [hlr.1], by simp [hlr.2]⟩
  · simp only [List.nil_append] at h
    have hm : ((lr.1.toList ++ lr.2.toList).map srcTr).toArray =
        (lrs.map Prod.fst).toArray ++ (lrs.map Prod.snd).toArray := by
      rw [List.map_append, h.1.1, h.1.2, ← List.append_toArray]
    rw [← hm]
    exact (sim_keccak256Block _).bind_left fun o o' ho => SimR.pure ⟨o, rfl, ho⟩

/-- **The membership rows**: the same rows and inputs, the same wires of `y` and of the root. -/
theorem sim_membershipBuilder :
    SimR PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild
      (fun r r' => r'.1 = (r.1.map srcTr).toArray ∧ r'.2 = (r.2.map srcTr).toArray) := by
  rw [membershipBuilder_eq]
  unfold Q.membershipBuilder Kc3Circuit.membershipBuild
  simp only [Kc3Circuit.Builder.freeBits, bind_assoc, pure_bind]
  refine (simS_mapM (List.range 256) _ _ fun _ _ => sim_input).bind fun x x' hx => ?_
  subst hx
  have hy : ((x ++ PcsQuotient.constantBlock PcsQuotient.yPad).map srcTr).toArray =
      (x.map srcTr).toArray ++ Kc3Circuit.constantBlock PcsCircuit.yPad := by
    rw [List.map_append, ← constantBlock_map, yPad_eq, ← List.append_toArray]
  have hl : ((x ++ PcsQuotient.constantBlock PcsQuotient.leafPad).map srcTr).toArray =
      (x.map srcTr).toArray ++ Kc3Circuit.constantBlock PcsCircuit.leafPad := by
    rw [List.map_append, ← constantBlock_map, leafPad_eq, ← List.append_toArray]
  rw [← hy, ← hl]
  refine (sim_keccak256Block _).bind fun y y' hy' => ?_
  subst hy'
  refine (sim_keccak256Block _).bind fun leaf leaf' hl' => ?_
  subst hl'
  rw [forIn_range, ← depth_eq]
  exact (simR_forIn_foldlM (List.range PcsQuotient.depth) _ _
    (fun s t => t = (s.map srcTr).toArray) leaf _ rfl fun _ _ s t hst => by
      subst hst
      exact sim_levelStep s).bind fun root root' hr => SimR.pure ⟨rfl, hr⟩

end Kc3Bridge
