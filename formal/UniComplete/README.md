<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# UniComplete

The generic layers of the univariate verifier's honest prover (`crates/leanvm/univariate`),
which [`UniKeccakComplete`](../UniKeccakComplete/README.md) and [`RecCompose`](../RecCompose/README.md) import:
the prover's channel and polynomials, exact division, the domain facts, honest WHIR openings at the plain layouts, and
the completeness of π1-rec3's paired batch rounds. Nothing here is VM-specific; the Keccak VM's honest prover and its
completeness theorems are UniKeccakComplete's (`K/`). There is no end theorem and no differential runner here.

A library of `formal/EndToEnd` (`UniComplete`, `srcDir = "../UniComplete"`, `globs = ["UniComplete.+"]`, no root
file), plain (non-`module`) Lean files, since it imports `E2ECompleteness`. Sorry-free, no `native_decide`.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=10G lake build UniComplete     # the 13 modules
```

## The modules (`UniComplete/`)

| module | what | imported by |
|---|---|---|
| `Basic.lean` | the writer `Wr`/`WrM` (`leanvm_statement`'s `KeccakWriter`: `sendScalar`, `sendRoot`, `sendInteger`, `sampleW`), polynomials (`Poly` = CompPoly's computable `CPolynomial E`), the digits' `w_l` (`wPoly`), the novel basis (`ofNovel`), subset sums | UniKeccakComplete |
| `Div.lean` | exact division by a monic polynomial in quadratic time (`longDiv`, `divM`, `modM`), proved equal to Mathlib's `/ₘ`, `%ₘ` and CompPoly's `divByMonic`, `modByMonic` (`toPoly_divM`, `toPoly_modM`, `divM_eq`, `modM_eq`) | UniKeccakComplete |
| `Domain.lean` | the domain facts in one import (namespace `UniComplete.Domain`), of the modules below | UniKeccakComplete |
| `DomainBasis.lean` | the Cantor basis computed, not assumed: `beta_lanes` (its `32` words by `decide +kernel`), `beta_succ`, `basisK`, `basisE`, `omega_basisK`, `omega_basisE`, `pointE_injOn` | through `Domain`; RecCompose |
| `DomainDigits.lean` | `digits_eq`, `digits_getD`, `digits_pointE`, `vanishingRatio_digits` | through `Domain` |
| `DomainPoly.lean` | the subspace polynomials `wP` in `Polynomial E` (`wP_monic`, `wP_natDegree`, `wP_eval`, `wP_eq_prod`, `wP_dvd`), `linProd`, `eq_linProd` | through `Domain` |
| `DomainCount.lean` | `countBits`' checks on an honest count (`intBits_one`, `intBits_high`, `intBits_range`, `byteFold_wire`) | through `Domain` |
| `DomainPositions.lean` | the active rows' positions (`UniStatement.activePositions`: `mem_activePositions_iff`, `rowPosition_bijOn`, `isActive_rowPosition`) | through `Domain` |
| `DomainActive.lean` | the active rows' vanishing polynomials (`zActP`, `zPadP`, `activeVanishingFromBits_eq`, `zActP_mul_zPadP`) | through `Domain` |
| `DomainCoord.lean` | the coordinate functionals: `coordinatesAt_pointE` from their values on the basis | UniKeccakComplete |
| `DomainCoord18.lean` | the same at height `18` by kernel evaluation of the elimination cut into column steps on literal words (`coordinateFunctionals_18`, `coordinateFunctionalsBasis_18`, `coordinatesAt_pointE_18`); UniKeccakComplete's `K/AlgCDomain.lean` plays its role at the Keccak height `15` | UniKeccakComplete |
| `Whir.lean` | honest WHIR openings at the plain layouts: `stackEval`, `plain_holds`, `plain_multilinear`, `weightShape_plain`, `admissible_plain` (`24 ≤ vars ≤ 28`), **`pcsOpen_honest`**, **`pcsOpenWith_honest`** (the verifier's `UniStatement.pcsOpenWith` accepts every proof the honest opener produces, at the root read back from the halves the prover sends, `rootHalves`: **`rootOf_rootHalves`**, `rootWord_rootHalves`, the roots carried as their bytes since the EIP's PCS claims) | UniKeccakComplete, RecCompose |
| `Rec3Pairs.lean` | π1-rec3's paired batch rounds are complete (`sumcheck_pairs_drawn` against `batch.rs`'s `prove_pairs`; the language of `UniSound.Rec3.Pairs`) | UniKeccakComplete |

The prover these layers serve is mathematical, not an FFT implementation: columns are interpolated by the additive
transform (`PcsQuotient.Domain.coefficients`), numerators are products of CompPoly polynomials, quotients exact
divisions.

`scripts/gen_domain_coord18.py` regenerates `DomainCoord18.lean`'s literal certificate (`python3 -I
gen_domain_coord18.py path/to/DomainCoord18.lean`, between its `-- BEGIN GENERATED` and `-- END GENERATED` markers).
Nothing it writes is trusted: every literal is checked by the kernel (`decide +kernel`).
