# Design documents

Each document describes the deployed code (main); superseded protocols and figures are in [`HISTORY.md`](HISTORY.md).
The current figures are in [`../AGENTS.md`](../AGENTS.md), "Numbers"; the EIP draft is
[`../eip-draft_leanPCS.md`](../eip-draft_leanPCS.md).

- [`PCS_CLAIM.md`](PCS_CLAIM.md): the EIP draft's PCS claim as `crates/pcs_claim` implements it (version 1).
- [`PERF_PROVER.md`](PERF_PROVER.md): how the provers are measured, where their time goes, their speedups (the same
  proofs) and what was rejected.
- [`LEAN_PORT.md`](LEAN_PORT.md): what `formal/` needs to state the deployed protocols (it states those of `f96a7938`).
- [`HISTORY.md`](HISTORY.md): superseded protocols and figures, by line and commit.
- Membership (`crates/membership`):
  - [`membership/PROTOCOL.md`](membership/PROTOCOL.md): the protocol (circuit, tables, three claims), its soundness,
    its zero knowledge assuming a zero-knowledge PCS, its gas and how to integrate the contract.
- leanVM line, π1 (`crates/leanvm/univariate`):
  - [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md): the univariate PIOP, π1-rec4's transcript, the claims'
    points, soundness and gas;
  - [`leanvm/univariate/FLOCK.md`](leanvm/univariate/FLOCK.md): Flock's verifier as π1 runs it, and the Keccak-f[1600]
    block;
  - [`leanvm/univariate/KECCAK.md`](leanvm/univariate/KECCAK.md): the Keccak VM's statement, workloads, capacity and
    vectors;
  - [`leanvm/univariate/PROVER.md`](leanvm/univariate/PROVER.md): the prover.
- leanVM line, π2 (`crates/leanvm/rec`):
  - [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md): the recursion: π1-rec4's verifier as π2's circuit, the public
    inputs, soundness and gas;
  - [`leanvm/rec/PI2.md`](leanvm/rec/PI2.md): π2's PIOP, prover, verifier and contract.
