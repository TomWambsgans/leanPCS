# Design documents

- [`PCS_CLAIM.md`](PCS_CLAIM.md): the EIP draft's PCS claim as `crates/pcs_claim` implements it (version 1).
- Membership (`crates/membership`):
  - [`membership/PERF_GAS2.md`](membership/PERF_GAS2.md): the deployed protocol (three claims on two commitments and
    the circuit's, 273 B, 31,680 gas), its soundness and zero knowledge, on
    [`membership/PERF_GAS.md`](membership/PERF_GAS.md)'s (four claims, 36,520 gas); each says what the Lean needs;
  - [`membership/PERF_PROVER.md`](membership/PERF_PROVER.md): the prover's speedups (the same proofs);
  - [`membership/HIDING.md`](membership/HIDING.md): the membership proof's zero knowledge, assuming a zero-knowledge
    PCS opening (the reference openings are not yet ZK-WHIR);
  - [`membership/EIP_CLAIMS.md`](membership/EIP_CLAIMS.md): a record, superseded: the protocol of `f96a7938` (six
    claims on four commitments, 52,856 gas), the one `formal/` proves.
- leanVM line, π1 (`crates/leanvm/univariate`):
  - [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md): the univariate PIOP;
  - [`leanvm/univariate/SPEC-FLOCK.md`](leanvm/univariate/SPEC-FLOCK.md): Flock's verifier as π1 runs it;
  - [`leanvm/univariate/PROVER.md`](leanvm/univariate/PROVER.md): the prover;
  - [`leanvm/univariate/KECCAK.md`](leanvm/univariate/KECCAK.md): the Keccak VM, its workloads, gas and measurements;
  - [`leanvm/flock/KECCAK.md`](leanvm/flock/KECCAK.md): the Keccak-f[1600] Flock block.
- leanVM line, π2 (`crates/leanvm/rec`):
  - [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md): the recursion;
  - [`leanvm/rec/PI2.md`](leanvm/rec/PI2.md): π2's PIOP, prover, verifier, contract;
  - [`leanvm/rec/SPEC-POINTS.md`](leanvm/rec/SPEC-POINTS.md): π1's claims' points on chain;
  - [`leanvm/rec/PERF_GAS3.md`](leanvm/rec/PERF_GAS3.md): the deployed recursion's π2 (π2v4: the copy argument's sum
    forced by `Q`'s layout, seven claims, 63,328 gas), on [`leanvm/rec/PERF_GAS2.md`](leanvm/rec/PERF_GAS2.md)'s
    (π1-rec4, π1's three claims hashed in π2's circuit, 577 B, 66,376 gas), on
    [`leanvm/rec/PERF_GAS.md`](leanvm/rec/PERF_GAS.md)'s (`C1`'s claim alone, 89,672 gas); each says what the Lean
    needs;
  - [`leanvm/rec/PERF_PROVER.md`](leanvm/rec/PERF_PROVER.md): the recursion prover's speedups (the same proofs).

The EIP draft is [`../eip-draft_leanPCS.md`](../eip-draft_leanPCS.md); the status and provenance, [`../AGENTS.md`](../AGENTS.md).
