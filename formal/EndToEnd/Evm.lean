-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Evm.PcsOpen
import Evm.Contract
import Evm.Calldata

/-!
# The deployed EVM contract is the Statement's verifier

The deployed verifier is an EVM contract (`crates/membership/evm`) compiled from an operation graph recorded
from the Rust verifier (`crates/membership/evm/src/record.rs`): it reads a statement and the reduction's proof
from calldata (`verify(bytes32,bytes32,bytes)`, packed: the four roots as words, eleven scalars, the index of
the transaction's frame of PCS claims), runs `quotient::protocol::reduce`, and checks that the transaction
declares the six PCS claims the reduction leaves (each claim's EIP encoding
`1 ‖ n ‖ root ‖ ood ‖ point ‖ value`, hashed with `KECCAK256`, is payload `k` of the frame), leaving them to
the block's proof. F5 (`formal/Implementation`) is that graph as Lean data and its interpreter, and proves
(`Implementation.run_calldata`) that on the calldata of a statement and a proof it checks declared exactly
the encodings `PcsQuotient.pcsClaimBytes` of the Statement's reduction's six claims on their commitments.

**What is proved**, for every statement `stmt`, proof `proof` (the reduction's proof and the six openings),
frame index and circuit commitment `index` (the contract's storage: the root's bytes, the out-of-domain
answer's word), with the deployed Keccak-256:

* **`evm_accepts_iff_verifyWith`** (`Evm/Contract.lean`): modelling what the block proves of declared claim
  `k` by the named definition `pcsOpen` (`Evm/PcsOpen.lean`: the claim's bytes read as the block reads them,
  `decodeClaim`, version `1`, `1 ≤ n ≤ 32`, `82 + 24 n` bytes, root, out-of-domain answer, point, value, which
  reads back exactly what `pcsClaimBytes` writes, `decodeClaim_pcsClaimBytes`; then the Statement's
  `PcsQuotient.pcsOpening`, i.e. `pcsOpeningWith` at Keccak-f[1600], of that claim on that commitment, with
  the proof's opening `k`), the contract accepts the calldata of `stmt` and `proof` exactly when
  `PcsQuotient.verifyWith` at Keccak-f[1600] accepts (`evm_accepts_eq_verify`: the two `Bool`s are equal, with
  `PcsQuotient.verify`);
* **`evm_accepts_iff_exists`** (`Evm/Calldata.lean`), over **all** calldata: with `pcsOpen` given openings
  `o`, the contract accepts `cd` exactly when `cd` is the calldata of a statement, a reduction proof and a
  frame index that, with those openings, `PcsQuotient.verify` accepts: the contract reverts on calldata of
  another length or selector (`accepts_of_not_wellFormed`), and every other calldata is a proof's
  (`calldata_surjective`, the inverse of `quotient.rs`'s `calldata`, the tests' `parse` in
  `crates/membership/evm/src/lean.rs`).

**What remains tested, not proved:**

* *Bytecode = graph*: that the deployed bytecode computes the recorded graph as F5's interpreter reads it
  (`Implementation.run`, `accepts`: `CALLDATALOAD`, `XOR`, `FIELD_MUL`, `KECCAK256` of `MSTORE`d words, the
  length and selector checks, the nonzero check, the storage reads, the claims' packing and their hashes
  compared with the frame's payloads, returning the word 1): `crates/membership/evm`'s parity tests
  (`quotient.rs`, `adversarial.rs`, `lean.rs`: `vectors_are_the_contracts_calls`) and
  `Implementation/Diff.lean` (the interpreter against the Rust verifier); `Implementation/Graph.lean` is
  generated from the recorded graph (`lean.rs`, `graph_lean_is_current`). That `FIELD_MUL` and the Rust's
  `F192` product are `mulE` (proved to be `Primitives.F192`'s product, `isF192_primitives`) and that the EVM's
  `KECCAK256` is the Statement's `keccak256` (`keccakBytes`) are assumptions of the same kind. How the frame of
  PCS claims is checked (its mode, its scheme byte, `FRAMEDATALOAD`) is not modelled: a claim is attested or
  not (`attest k`).
* *A declared claim = `pcsOpen`*: the frame of PCS claims is a mock (`crates/membership/evm/src/machine.rs`,
  `PcsFrame`) standing for a block that proves a declared claim by an opening that `pcs_claim::verify`
  accepts; that this is `PcsQuotient.pcsOpening` is `formal/Statement`'s differential test.
* *The stored commitment*: the contract reads the circuit's commitment from storage (constructor arguments
  that a fixed owner may change, `setIndexCommitment`); the theorems hold for whatever commitment `index` is
  stored (its out-of-domain answer as the word of an element), and are about the circuit's when that is what
  is stored.
-/

/-- info: 'Evm.evm_accepts_iff_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.evm_accepts_iff_verifyWith

/-- info: 'Evm.evm_accepts_eq_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.evm_accepts_eq_verify

/-- info: 'Evm.evm_accepts_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.evm_accepts_iff_exists

/-- info: 'Evm.calldata_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.calldata_surjective

/-- info: 'Evm.decodeClaim_pcsClaimBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.decodeClaim_pcsClaimBytes

/-- info: 'Evm.pcsOpen_pcsClaimBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.pcsOpen_pcsClaimBytes

/-- info: 'Implementation.run_calldata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.run_calldata
