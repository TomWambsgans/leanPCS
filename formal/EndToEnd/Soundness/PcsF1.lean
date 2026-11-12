-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Soundness.PcsVerifier

/-!
# What a satisfying first message must spell

The extractor (`PcsQuotient.secretOfStack`) reads a candidate stack as the witness table: its `2^24` entries are the
cells' polynomial in the novel basis, `Domain.values` takes them to the cells' values, and the input rows' `V` cells
are the secret's bits. **`StackRel P readW`** is what the composition needs of the circuit and of that reading: a
stack whose read first message (`readW`, the witness table's column read as F1's row polynomials) satisfies F1's
relation for the statement's pinned values spells a secret of the statement. At the deployed instance it is the
circuit layer's (`formal/Kc3Circuit`: a satisfying assignment of the membership circuit proves membership) composed
with the additive transform (`Bridge.Ntt`: `Domain.values` is the table's polynomial on the cells).
-/

namespace PcsKS

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs PcsQuotient SoundPcs

/-- **A satisfying first message spells a secret**: for every statement and stack, if the first message `readW`
reads off the stack satisfies F1's relation for the statement's pinned values, the extractor's secret of the stack
satisfies the relation. -/
def StackRel (P : Kc3.Params E) (readW : Column 24 → P.Msg₁) : Prop :=
  ∀ (stmt : PcsQuotient.Statement) (st : Vector K (2 ^ 24)),
    P.Sat (stmtVals (stmt.y ++ stmt.root)) (P.cells (readW ⟨st⟩).1) →
      PcsQuotient.Relation stmt (secretOfStack (membership PcsQuotient.logRows) st)

end PcsKS
