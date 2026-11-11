-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniComplete.DomainBasis
import QuotientSecurity.Cantor

/-!
# π2's points and the subfield `K`

The points `ω_i` (`pi2Omega`: `Heap.omega` of the Cantor basis, the verifier's `pointE`) and the subfield `K` of `E`
(`subK`), shared by the tables' layer (`Layers`, `Tables`) and the honest prover's algebra (`Pi2Honest*`).
-/

namespace RecCompose

open LeanVM.Parameters

/-- The subfield `K` of `E`. -/
abbrev subK : Subfield E := (algebraMap K E).fieldRange

/-- The points `ω_i` (`Heap.omega` of the Cantor basis, `pointE`). -/
noncomputable abbrev pi2Omega : ℕ → E := Heap.omega UniComplete.Domain.basisE

/-- π2's points are the verifier's: `ω_i = pointE i`. -/
theorem pi2Omega_eq (i : ℕ) : pi2Omega i = UniStatement.pointE i := UniComplete.Domain.omega_basisE i

/-- `s^l(ω_x) = ω_{x >> l}` (`x < 2^32`). -/
theorem sq_iterate_pi2Omega (l : ℕ) {x : ℕ} (hx : x < 2 ^ 32) :
    QuotientSecurity.sq^[l] (pi2Omega x) = pi2Omega (x >>> l) := by
  rw [pi2Omega_eq, pi2Omega_eq]
  exact UniComplete.Domain.sq_iterate_pointE l hx

/-- `ω_0 = 0`. -/
theorem pi2Omega_zero : pi2Omega 0 = 0 := by rw [pi2Omega_eq]; exact UniComplete.Domain.pointE_zero

end RecCompose
