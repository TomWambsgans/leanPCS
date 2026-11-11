-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Node
import Implementation.Graph
import Implementation.Arith
import Implementation.Interp
import Implementation.Program
import Implementation.Field
import Implementation.Semantics
import Implementation.Blocks
import Implementation.Frobenius
import Implementation.Field192
import Implementation.Formula
import Implementation.Bytes
import Implementation.Tau
import Implementation.Constants
import Implementation.Reduce
import Implementation.Calldata
import Implementation.Leaves
import Implementation.Verifier

/-!
# The implementation is the Statement's reduction (layer F5)

The EVM contract is compiled from an operation graph recorded from the Rust verifier
(`crates/membership/evm/src/record.rs`). `Implementation/Graph.lean` is that graph, written by the Rust
(`crates/membership/evm/src/lean.rs`, whose test fails when the file is stale): its nodes, the node it
requires nonzero, the words it writes, and the six PCS claims it checks declared (each the output words of
its root, its out-of-domain answer, its point and its value). `Interp.lean` interprets it on calldata as
the bytecode generator compiles each node (EVM words, `XOR`, `FIELD_MUL`, `KECCAK256` of `MSTORE`d words,
`CALLDATALOAD`, shifts and masks, the circuit's commitment from storage), for any hash `H`, and packs the
claims as `evm_link`'s `Item::DeclaredClaim` does (`calls`: `1 ‖ n ‖ root ‖ ood ‖ point ‖ value`).

Proved here:

* `Program.reduceIds_eq`, `Program.checkId_eq` (kernel evaluation): the Lean transcription of
  `quotient::protocol::reduce` over node indices finds every node it asks for in the graph, gives exactly
  the words of the six claims the contract checks, and the node it requires nonzero;
* `reduceIds_spec`, `checkId_spec` (`Reduce.lean`): on `Primitives.F192` (mumbai's `E`) with its Rust limbs
  (`isF192_primitives`, `Field192.lean`; the Frobenius node is `x^(2^64)`, `frobOK`), those nodes hold the
  Statement's formulas (`Formula.claims`, which is `PcsQuotient.claimsAt`, `Formula.claimsAt_eq`) at the
  leaves' values, and the nonzero node the product of the Statement's denominators; the graph's constants
  are the Statement's (`Constants.lean`: the Cantor basis, `coordinates 11`, `rowVanishing 24` through
  `Tau.lean`'s elimination, `extension`, the slopes);
* `leafOK_calldata`, `vals_leaves` (`Leaves.lean`): on the calldata of a statement and a proof
  (`calldata`, `quotient.rs`'s), with the deployed Keccak-256 and the circuit's commitment in storage
  (`deployed`), the leaves are the Statement's: the statement's and roots' halves, the scalars, the
  transcript's states and challenges (`chainVals`; `reduce_eq`: `PcsQuotient.reduce` is `claimsAt` at them);
* **`run_calldata`**, `accepts_calldata` (`Verifier.lean`): on such calldata the contract reaches its checks
  exactly when `PcsQuotient.reduce` accepts, and the six claims it checks declared are then, byte for byte,
  the EIP encodings `PcsQuotient.pcsClaimBytes` of the reduction's six claims on their commitments
  (`checkPairs`, the order of `Claims::all`).

Tested, not proved: the bytecode computes the graph (`crates/membership/evm`'s parity tests against the
Rust verifier and `Implementation/Diff.lean` against this interpreter), and that the Rust's `F192`
arithmetic is `mulE` (`mulE` transcribes its software `clmul` and `reduce`; F0c's kernel-checked
vectors, `Field/Test.lean`).
-/

/-- info: 'Implementation.Program.reduceIds_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Implementation.Program.reduceIds_eq

/-- info: 'Implementation.Program.checkId_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Implementation.Program.checkId_eq

/-- info: 'Implementation.reduceIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.reduceIds_spec

/-- info: 'Implementation.checkId_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.checkId_spec

/-- info: 'Implementation.leafOK_calldata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.leafOK_calldata

/-- info: 'Implementation.reduce_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.reduce_eq

/-- info: 'Implementation.run_calldata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.run_calldata

/-- info: 'Implementation.accepts_calldata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.accepts_calldata

/-- info: 'Implementation.isF192_primitives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.isF192_primitives

/-- info: 'Implementation.frobOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.frobOK
