# Design documents

- [`membership/HIDING.md`](membership/HIDING.md): the hiding layouts that make the membership proof's commitments and
  openings zero knowledge.
- leanVM line, π1 (`crates/leanvm/univariate`):
  - [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md): the univariate PIOP;
  - [`leanvm/univariate/SPEC-FLOCK.md`](leanvm/univariate/SPEC-FLOCK.md): Flock's verifier as π1 runs it;
  - [`leanvm/univariate/PROVER.md`](leanvm/univariate/PROVER.md): the prover;
  - [`leanvm/univariate/KECCAK.md`](leanvm/univariate/KECCAK.md): the Keccak VM, its workloads, gas and measurements;
  - [`leanvm/flock/KECCAK.md`](leanvm/flock/KECCAK.md): the Keccak-f[1600] Flock block.
- leanVM line, π2 (`crates/leanvm/rec`):
  - [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md): the recursion;
  - [`leanvm/rec/PI2.md`](leanvm/rec/PI2.md): π2's PIOP, prover, verifier, contract;
  - [`leanvm/rec/SPEC-POINTS.md`](leanvm/rec/SPEC-POINTS.md): π1's claims' points on chain.

The EIP draft is [`../eip-draft_leanPCS.md`](../eip-draft_leanPCS.md); the status, [`../STATUS.md`](../STATUS.md).
