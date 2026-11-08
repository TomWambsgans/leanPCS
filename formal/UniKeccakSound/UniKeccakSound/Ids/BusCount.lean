-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof is `UniSound/Ids/LvLink.lean`'s
-- (`busBound`, `lvBusCount`) for `formal/KeccakVm`'s instance.
import UniKeccakSound.Ids.Build

/-!
# The Keccak VM's bus counts (`KvBusCountK`)

**`kvBusCount`**: at counts in range, each side of the Keccak VM's bus has at most `busBoundK D.shape` tuples:
every table's flushes (`tablesKeccak`'s push tuples, as many as the instance's on either side, `pushes_eqK`,
`pulls_eqK`) times its height, the memory's and the bytecode's blocks, the state boundary.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak

/-- **The bus bound** at a shape on the Keccak VM. -/
def busBoundK (S : Shape) : ℕ :=
  ∑ j ∈ Finset.range 6, (tablesKeccak.getD j default).flushes.push.length * 2 ^ S.heights.getD j 0 +
    2 ^ S.logMemory + 2 ^ S.logBytecode + 1

/-- **The instance's push flushes are the verifier's**, table by table. -/
theorem pushes_eqK : ∀ j : Fin 6,
    ((KeccakVm.KeccakIsa.flushes ⟨j.val + 3, by omega⟩).filter fun f ↦
      decide (f.1 = Lv42.Protocol.Side.push)).length = (tablesKeccak.getD j.val default).flushes.push.length := by
  decide +kernel

/-- **The instance's pull flushes are as many**, table by table. -/
theorem pulls_eqK : ∀ j : Fin 6,
    ((KeccakVm.KeccakIsa.flushes ⟨j.val + 3, by omega⟩).filter fun f ↦
      decide (f.1 = Lv42.Protocol.Side.pull)).length = (tablesKeccak.getD j.val default).flushes.push.length := by
  decide +kernel

/-- A side of the bus has at most `busBoundK` tuples at counts in range. -/
theorem busCountK_le (D : KDeployment) (rows : List ℕ) (hfit : CountsFit D.shape rows)
    (side : Lv42.Protocol.Side)
    (hside : ∀ j : Fin 6, ((KeccakVm.KeccakIsa.flushes ⟨j.val + 3, by omega⟩).filter fun f ↦
      decide (f.1 = side)).length = (tablesKeccak.getD j.val default).flushes.push.length) :
    Heap.busCount (D.inst rows) side ≤ busBoundK D.shape := by
  have hb : (((D.inst rows).boundary.filter fun b ↦ decide (b.side = side)).map fun b ↦ 2 ^ b.κ).sum =
      2 ^ 0 + (2 ^ D.shape.logMemory + (2 ^ D.shape.logBytecode + 0)) := by
    rw [D.logBytecode_eq]
    cases side <;> rfl
  let g : ℕ → ℕ := fun j ↦ if 3 ≤ j then
    (tablesKeccak.getD (j - 3) default).flushes.push.length * 2 ^ D.shape.heights.getD (j - 3) 0 else 0
  have hle : ∀ j : Fin (D.inst rows).ntab,
      (((D.inst rows).flushes j).filter fun f ↦ decide (f.1 = side)).length * (D.inst rows).rows j ≤
        g j.val := by
    intro j
    rcases j with ⟨_ | _ | _ | j, hj⟩
    · have h0 : (D.inst rows).flushes ⟨0, hj⟩ = [] := rfl
      rw [h0]
      simp
    · have h0 : (D.inst rows).flushes ⟨1, hj⟩ = [] := rfl
      rw [h0]
      simp
    · have h0 : (D.inst rows).flushes ⟨2, hj⟩ = [] := rfl
      rw [h0]
      simp
    · have hj6 : j < 6 := by
        have h9 : (D.inst rows).ntab = 9 := rfl
        omega
      have hlen : (((D.inst rows).flushes ⟨j + 1 + 1 + 1, hj⟩).filter fun f ↦
          decide (f.1 = side)).length = (tablesKeccak.getD j default).flushes.push.length := hside ⟨j, hj6⟩
      have hrows : (D.inst rows).rows ⟨j + 1 + 1 + 1, hj⟩ = rows.getD j 0 := rfl
      have hg : g (j + 1 + 1 + 1) =
          (tablesKeccak.getD j default).flushes.push.length * 2 ^ D.shape.heights.getD j 0 := by
        simp only [g, show 3 ≤ j + 1 + 1 + 1 by omega, show j + 1 + 1 + 1 - 3 = j by omega, ↓reduceIte]
      rw [hlen, hrows]
      show _ ≤ g (j + 1 + 1 + 1)
      rw [hg]
      exact Nat.mul_le_mul_left _ (hfit.2 j hj6)
  have hA : ((List.finRange (D.inst rows).ntab).map fun j ↦
      (((D.inst rows).flushes j).filter fun f ↦ decide (f.1 = side)).length * (D.inst rows).rows j).sum ≤
        ∑ j ∈ Finset.range 6, (tablesKeccak.getD j default).flushes.push.length *
          2 ^ D.shape.heights.getD j 0 := by
    rw [← Fin.sum_univ_def]
    calc _ ≤ ∑ j : Fin 9, g j.val := Finset.sum_le_sum fun j _ ↦ hle j
      _ = ∑ j ∈ Finset.range 9, g j := Fin.sum_univ_eq_sum_range g 9
      _ = ∑ j ∈ Finset.range 3, g j + ∑ x ∈ Finset.range 6, g (3 + x) := Finset.sum_range_add g 3 6
      _ = _ := by
        rw [Finset.sum_eq_zero (fun x hx ↦ by
          have : x < 3 := Finset.mem_range.mp hx
          simp only [g, show ¬ 3 ≤ x by omega, ↓reduceIte]), zero_add]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [g, show 3 ≤ 3 + x by omega, show 3 + x - 3 = x by omega, ↓reduceIte]
  unfold Heap.busCount busBoundK
  rw [hb]
  omega

/-- **The bus counts** (`KvBusCountK`): at counts in range, at most `busBoundK` tuples a side. -/
theorem kvBusCount (D : KDeployment) : KvBusCountK D (busBoundK D.shape) := fun rows hfit ↦
  ⟨busCountK_le D rows hfit _ pushes_eqK, busCountK_le D rows hfit _ pulls_eqK⟩

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.kvBusCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.kvBusCount
