-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls and their random-permutation model, `rpmError`, the duplex
-- discipline `DuplexVm` and the block cost `hashBlocks`.
import E2ECompleteness.Chain
import E2ECompleteness.Transfer
import E2ECompleteness.Regular
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.WithHash
import PcsQuotient.Security

/-!
# Two numeric lemmas

`two_pow_mul_inv_pow` and `inv_pow_le_inv_pow`, in `ℝ≥0∞`.

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-! ## The numbers -/

/-- `2^k · 2^-(n + k) = 2^-n`. -/
theorem two_pow_mul_inv_pow (k n : ℕ) : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ (n + k) =
    (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [pow_add, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ n), ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

theorem inv_pow_le_inv_pow {m n : ℕ} (h : m ≤ n) : (2 : ℝ≥0∞)⁻¹ ^ n ≤ (2 : ℝ≥0∞)⁻¹ ^ m :=
  pow_le_pow_of_le_one (by simp) (by simp) h

end E2ECompleteness
