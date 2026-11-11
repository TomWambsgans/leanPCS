-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverDefs.lean` (the previous prover's computations, named) to the
-- PCS claims' prover (`formal/Statement/PcsQuotient/Prover.lean`: `quotientTables`, with the blinding of
-- `h`). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import PcsQuotient.Prover

/-!
# The Statement's computed constants

`Constants` states the Statement's computed constants' defining properties (`PcsConstants.lean` proves it).
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-- **The Statement's computed constants have their defining properties** (`Domain.lean`):
`beta()` is a Cantor basis, `coordinates(11)` reads the region's coordinates and `row_vanishing(24)`
vanishes exactly on the `X` cells. -/
structure Constants : Prop where
  cantor : IsCantorBasis
  coords : CoordinatesRead 11
  rows : RowVanishingProperty 24

end E2ECompleteness.Pcs
