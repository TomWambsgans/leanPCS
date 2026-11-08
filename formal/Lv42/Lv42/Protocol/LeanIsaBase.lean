/-
  Lv42.Protocol.LeanIsaBase

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Protocol/LeanIsa.lean. MIT OR Apache-2.0; see AGENTS.md.
  `LeanVM` renamed `Lv42`.

  The instruction-set-independent part of `Lv42.Protocol.LeanIsa` (shared by the Keccak VM's
  instance): the counted channels, the bus sides, the announced sizes, the stacked size's bounds,
  the rate check, and the five opcode tables both instruction sets have (`baseComponent`) with
  their degree bounds. `Lv42.Protocol.LeanIsa` imports this module; every declaration keeps its
  name.
-/

module

public import LeanVM.Protocol.ToClean.ComponentPolynomial
public import Lv42.Arithmetization.Tables.Xor
public import Lv42.Arithmetization.Tables.MulNative
public import Lv42.Arithmetization.Tables.SetConstant
public import Lv42.Arithmetization.Tables.Deref
public import Lv42.Arithmetization.Tables.Jump
public import Lv42.Protocol.Spine.Instance

namespace Lv42.Protocol
open LeanVM.Protocol

open Lv42.Parameters Lv42.Semantics Lv42.Arithmetization CompPoly CPoly LeanVM.Parameters
open Air.Flat (Component)

@[expose] public section

namespace LeanIsa

/-- The channels whose coordinate `1` is a read count: the memory and bytecode pulls (§6.2). -/
def counted (c : RawChannel K) : Bool := c.name = MemPull.name || c.name = BytecodePull.name

/-- The side of the bus a direction flushes on. -/
def sideOf : Arithmetization.Direction → Side
  | .push => .push
  | .pull => .pull

/-! ## Sizes -/

/-- The announced sizes: the memory log-size, positive, and the six opcode tables'
log-heights. -/
structure Sizes where
  /-- The memory log-size `log_mem`. -/
  logMem : ℕ
  /-- The memory has at least two cells. -/
  logMem_pos : 0 < logMem
  /-- The opcode tables' row counts, in the ensemble's order. -/
  rows : Fin 6 → ℕ

/-- An opcode table's log-height: the least `τ` with `rows ≤ 2^τ` (`log2_ceil`,
`python-verifier/verifier.py:886`), `0` for no row. -/
def Sizes.τ (s : Sizes) (j : Fin 6) : ℕ := Nat.clog 2 (s.rows j)

/-- An opcode table's rows fit in its height. -/
theorem Sizes.rows_le (s : Sizes) (j : Fin 6) : s.rows j ≤ 2 ^ s.τ j :=
  Nat.le_pow_clog (by norm_num) _

/-- The minimum stacked size, `MIN_MU` (`pcs.rs:49`). -/
def minMu : ℕ := 15

/-- The maximum stacked size, `MAX_MU` (`pcs.rs:51`). -/
def maxMu : ℕ := 28

/-- The WHIR rate check (`pcs/src/whir_config.rs:43-55`): the inverse rate's logarithm is in
`[1, 4]`. A parameter of the commitment, read off the same announcement. -/
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4

instance (ρ : ℕ) : Decidable (validRate ρ) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## The five shared opcode tables -/

/-- The five opcode tables both instruction sets have, in the ensemble's order: `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP` (`opcodeComponent`'s first five). -/
def baseComponent : Fin 5 → Component K
  | 0 => ⟨xorTable⟩
  | 1 => ⟨mulTable⟩
  | 2 => ⟨setTable⟩
  | 3 => ⟨derefTable⟩
  | 4 => ⟨jumpTable⟩

/-- Shared opcode table `j` as an M3 table. -/
def baseTable (j : Fin 5) : M3Table K Arithmetization.Direction :=
  (baseComponent j).toM3 channelSep channelDir counted

/-- Every assert expression of a shared opcode table has syntactic degree at most two. -/
theorem base_constraints_degreeBound :
    ∀ j : Fin 5, ∀ e ∈ (baseComponent j).rowOperations.constraints, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every message coordinate of a shared opcode table has syntactic degree at most two. -/
theorem base_flushes_degreeBound :
    ∀ j : Fin 5, ∀ i ∈ (baseComponent j).rowOperations.interactions,
      ∀ e ∈ i.msg.toList, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every constraint of a shared opcode table has total degree at most two. -/
theorem baseTable_constraints_degree (j : Fin 5) :
    ∀ C ∈ (baseTable j).constraints, C.totalDegree ≤ 2 :=
  toM3_constraints_degree _ _ _ _ (base_constraints_degreeBound j)

/-- Every flush coordinate of a shared opcode table has total degree at most two. -/
theorem baseTable_flushes_degree (j : Fin 5) :
    ∀ f ∈ (baseTable j).flushes, ∀ k, (f.2.get k).totalDegree ≤ 2 :=
  fun f hf k ↦ toM3_flushes_degree _ _ _ _ (base_flushes_degreeBound j) f hf k

end LeanIsa

end

end Lv42.Protocol
