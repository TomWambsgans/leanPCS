# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
"""The recursion of docs/leanvm/rec/SPEC-REC.md on the Keccak VM: pi2's sizes (D16v, N = 2^24) and its soundness round
by round after the union bounds over WHIR's level-0 Johnson lists, pi1-rec3's (from
params/leanvm_univariate_params.py), their composition, the arithmetizations SPEC-REC.md §3 compares, and the
batch's rounds of k variables (SPEC-POINTS.md §2.4).

    python3 -I params/leanvm_rec_params.py

MEASURED (crates/leanvm/rec: tests/counts.rs, tests/keccak_vm_rec.rs, tests/circuit.rs; SPEC-REC.md §1.2, §10.3):
pi1-rec3's verifier graph and pi2's positions at 128 and 400 signatures. MODELLED (here): every soundness figure, the
other arithmetizations' sizes, the k-variable rounds' permutations.

pi2's rounds are π2v2's (docs/leanvm/rec/PI2.md §2, §7; the Lean, formal/RecPiop/RecPiop/Rounds.lean `err`, states
π2v1, whose t has degree < 5N): the copy argument (alpha, beta, gamma) over W's list, the two identities at t, W's fold
and Q's claim at rho over W's and Q's lists. The
composition adds pi2's bound and pi1-rec3's (RecCompose's `RecKnowledgeSoundnessReduction`), each with its openings
charged once.
"""
from fractions import Fraction
import importlib.util
import math
import os
import sys

sys.dont_write_bytecode = True  # loading the other script must not write a __pycache__ next to it

HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


uni = _load("leanvm_univariate_params")
LOGQ = uni.LOGQ
CERTIFIED_L0 = uni.CERTIFIED_L0
bits, err = uni.bits, uni.err

# ---------------------------------------------------------------------------------------------------------------------
# MEASURED: pi1-rec3's verifier (Claims::Point; SPEC-REC.md §1.2) and pi2's D16v circuit of it (§2.4.5, §10.3).
PI1_REC3 = {
    128: dict(stream=9232, calls=70, perms=116, products=8476, linear=6633, challenges=14, values=3),
    400: dict(stream=9424, calls=71, perms=118, products=8673, linear=6887, challenges=14, values=3),
}
KECCAK_D16V = 130_944  # positions a Keccak-f[1600] (SPEC-REC.md §2.4.1; the design's 130,736)
REST = {128: 478_912, 400: 489_408}  # free bits, packings, later blocks' XORs, E units, ports
LOG_N = 24
ROW = 16  # D16v: 16 positions a row, 16 fold values and xi at t
PORT_DEGREES = 3  # the four-limb ports' fingerprints, degree 1 in gamma: the statement and pi1's two roots

# pi2's commitments (PI2.md §2, π2v2): W the witness, 2^24 K-words; Q: h (3N), q < 2N (6N), the pushes P (N, in K)
# and P's definition quotient q_P < 2N (2N, in K), 12N words (π2v1: h and q < 4N, 15N); the setup, kappa and
# kappa + sigma (honest: L = 1).
def pi2_stacks(log_n=LOG_N):
    n = 1 << log_n
    return dict(W=n, Q=12 * n, setup=2 * n)


def stack(words):
    return max(24, math.ceil(math.log2(words) - 1e-9))


def pi2_rounds(log_n=LOG_N, row=ROW):
    """pi2's rounds as RecPiop's `err`: (label, error numerator over 2^192, union)."""
    n = 1 << log_n
    s = pi2_stacks(log_n)
    lw, lq = CERTIFIED_L0[stack(s["W"])], CERTIFIED_L0[stack(s["Q"])]
    return lw, lq, [
        # π2v2 (PI2.md §7): the ports out of the copy argument, as an error term T. A dishonest port's hole x gives
        # h(x) a simple pole at α = w(x) + β x, which no other fraction has: Σ_V h is a nonzero rational function of
        # (α, β) with at most 2N linear factors, plus the vanishing denominators (4N), and the four-limb ports'
        # fingerprints, degree 1 in γ.
        ("copy argument (α, β, γ): 2N fractions, the ports' poles and fingerprints", 4 * n + PORT_DEGREES, lw),
        # π2v2: two identities at t, each of degree below 3N, which must both vanish: the copy identity
        # h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T = q Z_V (d_push of the committed P) and P's definition
        # P = P_v + Z_V q_P. The bound is the larger's, not the sum (π2v1: one identity below 5N).
        ("t: the copy identity and P's definition, each of degree < 3N", 3 * n - 1, lw * lq),
        (f"ρ: W's fold (degree {row - 1})", row - 1, lw * lq),
        # π2v2: Q's one claim combines h(t), q(t), P(t) = s and q_P's definition by ρ: degree 3 in ρ.
        ("ρ: Q's claim (the identity, P(t) = s, P's definition), degree 3", 3, lw * lq),
    ]


def pi2_bound():
    """pi2's weakest round after its lists, and its bits at Q = 2^64 with its three openings once (`pi2Bound`)."""
    _, _, rs = pi2_rounds()
    worst = max(err(num, LOGQ) * union for _, num, union in rs)
    return worst, uni.per_query(worst)


def recursion_bits(q=2 ** 64):
    """The recursion's bound at Q: pi2's `pi2Bound` + pi1-rec3's (the calculator's rounds, and the Lean's) + pi1-rec3's
    merge hazard (`hazard_probK`: 2^16 / |E| a query)."""
    pi2_worst, _ = pi2_bound()
    p = uni.pi1(uni.REFERENCE, "rec3")
    e_lean, _ = uni.lean_pi1("rec3")
    hazard = (2 ** 33 + q) * Fraction(2 ** 16, 2 ** LOGQ)
    pi2 = uni.uni_bound128(pi2_worst, q)
    calc = pi2 + uni.uni_bound128(p["weakest"][1], q) + hazard
    lean = pi2 + uni.uni_bound128(e_lean, q) + hazard
    return 64 + bits(calc), 64 + bits(lean)


# ---------------------------------------------------------------------------------------------------------------------
# The arithmetizations (SPEC-REC.md §2, §3): positions a Keccak-f, values at t, the quotient table's words a position.
ROUNDS = 24


def keccak_positions(design):
    if design == "B4":  # crates/membership/quotient's chi gate on bits, 4 cells a row (113,114 rows a Keccak-f, measured)
        return 4 * 113_114
    if design == "C16":  # cell outputs, 16-cell rows: chi5+theta rows (15 cells), 2 C (6) + 1 D (3) rows
        return ROUNDS * (320 + 192) * 16
    if design == "C64":  # cell outputs, slice rows: 25 b, 5 C, 5 C_prev, 25 a' (60 of 64)
        return ROUNDS * 64 * 64
    if design == "D16v":  # measured (the design: 130,736)
        return KECCAK_D16V
    if design == "D32v":  # slice rows: 25 b + 5 C_prev pulls, 30 expression pushes; and a theta prep
        return (ROUNDS + 1) * 64 * 32
    raise ValueError(design)


DESIGNS = {
    "B4": dict(values=5, qwords=13.75, note="the χ gate on bits, cell outputs"),
    "C16": dict(values=18, qwords=9 + 3 / 16, note="cell outputs, χ5+θ rows"),
    "C64": dict(values=66, qwords=9 + 3 / 64, note="cell outputs, slice rows"),
    # π2v2: Q 12N words; values at t: the row, ξ and s = P(t)
    "D16v": dict(values=18, qwords=12, note="virtual pushes, 16-position rows"),
    "D32v": dict(values=34, qwords=12, note="virtual pushes, slice rows"),
}


def design_size(design, xmss=128):
    """N for pi1-rec3 at `xmss` signatures: its permutations at the design's positions, plus D16v's measured rest
    (an approximation for the other designs)."""
    total = PI1_REC3[xmss]["perms"] * keccak_positions(design) + REST[xmss]
    log_n = math.ceil(math.log2(total))
    return dict(total=total, log_n=log_n, fill=total / 2 ** log_n, q=DESIGNS[design]["qwords"] * 2 ** log_n)


def c16_split_t(log_n):
    """C16's Q split into three proof commitments (h; then q and the gate's quotient): t over three lists."""
    n = 1 << log_n
    lw = CERTIFIED_L0[stack(n)]
    lh = CERTIFIED_L0[stack(3 * n)]
    lq = CERTIFIED_L0[stack((DESIGNS["C16"]["qwords"] - 3) * n)]
    e = err(3 * n + 2 * n // 16, LOGQ) * lw * lh * lq
    return lw, lh, lq, e


# ---------------------------------------------------------------------------------------------------------------------
# The batch in rounds of k variables (SPEC-POINTS.md §2.4).
BATCH_VARS = 27


def permutations_of(data_bytes):
    """Keccak-f permutations of one Keccak-256 of the 32-byte state and `data_bytes` (rate 136, pad10*1)."""
    return (32 + data_bytes) // 136 + 1


def grouped_rounds(k, vars_=BATCH_VARS, degree=2):
    """Rounds of k variables (the last the rest): challenges, scalars, permutations. A round of j variables sends the
    summand on V_j's coordinate-functional curve, of degree degree * j * 2^(j-1), its coefficients but one."""
    rounds = [k] * (vars_ // k) + ([vars_ % k] if vars_ % k else [])
    scalars = [degree * j * 2 ** (j - 1) for j in rounds]
    return dict(challenges=len(rounds), scalars=sum(scalars), perms=sum(permutations_of(24 * s) for s in scalars))


def main():
    print("== pi1-rec3's verifier (MEASURED, Claims::Point)")
    for xmss, p in PI1_REC3.items():
        used = p["perms"] * KECCAK_D16V + REST[xmss]
        print(f"  {xmss} signatures: stream {p['stream']:,} B, Keccak-256 {p['calls']}, Keccak-f {p['perms']}, E products"
              f" {p['products']:,}, linear {p['linear']:,}; claims at {p['challenges']} narrow challenges and"
              f" {p['values']} values; pi2 (D16v) {used:,} positions of 2^{LOG_N} ({100 * used / 2 ** LOG_N:.1f}%)")
    s = pi2_stacks()
    print(f"  pi2's stacks: W 2^{math.log2(s['W']):.2f} (list {CERTIFIED_L0[stack(s['W'])]}), Q 2^{math.log2(s['Q']):.2f}"
          f" (stack 2^{stack(s['Q'])}, list {CERTIFIED_L0[stack(s['Q'])]}), setup 2^{math.log2(s['setup']):.0f} (L = 1)")

    print("\n== pi2's rounds (N = 2^24, rows of 16): bits alone and after the lists")
    lw, lq, rs = pi2_rounds()
    for label, num, union in rs:
        print(f"   {label:72s} {bits(err(num, LOGQ)):6.1f} {bits(err(num, LOGQ) * union):6.1f}")
    worst, pi2_bits = pi2_bound()
    print(f"   weakest: t ({bits(worst):.2f} after W's and Q's lists, {lw} · {lq});"
          f" with the openings once: {pi2_bits:.2f} bits as Q / ε at Q = 2^64 (Lean `pi2Bound`)")

    print("\n== pi1-rec3 at 128 signatures (params/leanvm_univariate_params.py)")
    p = uni.pi1(uni.REFERENCE, "rec3")
    _, lean1 = uni.lean_pi1("rec3")
    print(f"   weakest round: {p['weakest'][0]}, {bits(p['weakest'][1]):.2f} bits after C1's and C2's lists;"
          f" {p['total']:.2f} bits with the openings (Lean: {lean1:.2f})")
    calc, lean = recursion_bits()
    print(f"   the recursion, pi2 + pi1-rec3 + the merge hazard (2^16/|E| a query): {calc:.2f} bits as Q / ε at"
          f" Q = 2^64 (with the Lean's pi1-rec3 bound: {lean:.2f})")

    print("\n== the arithmetizations (SPEC-REC.md §3), pi1-rec3 at 128 signatures (MODELLED: the rest as D16v's)")
    for design, d in DESIGNS.items():
        z = design_size(design)
        print(f"  {design:5s} [{d['note']}]: {keccak_positions(design):,} positions a Keccak-f, total"
              f" {z['total'] / 1e6:.2f}M -> N = 2^{z['log_n']} ({100 * z['fill']:.0f}%); Q 2^{math.log2(z['q']):.2f}"
              f" {'fits 2^28' if z['q'] <= 2 ** 28 else '** over 2^28 **'}; {d['values']} values at t")
    z = design_size("C16")
    lw, lh, lq, e = c16_split_t(z["log_n"])
    print(f"  C16 with Q split in three (lists W {lw}, h {lh}, q {lq}): t {bits(e):.1f} bits after the lists")

    print(f"\n== the batch over {BATCH_VARS} variables in rounds of k (SPEC-POINTS.md §2.4; pi2 at"
          f" {KECCAK_D16V:,} positions a Keccak-f)")
    plain = grouped_rounds(1)
    for k in (1, 2, 3, 4):
        g = grouped_rounds(k)
        extra = g["perms"] - plain["perms"]
        print(f"    k = {k}: {g['challenges']:>2} challenges, {g['scalars']:>3} scalars, {g['perms']:>2} Keccak-f"
              f" ({extra:+d}: {extra * KECCAK_D16V / 1e6:+.2f}M positions)")
    mixed = 3 * permutations_of(24 * 24) + 9 * permutations_of(24 * 8)
    print(f"    3 triples and 9 pairs: 12 challenges, {mixed} Keccak-f ({mixed - plain['perms']:+d}:"
          f" {(mixed - plain['perms']) * KECCAK_D16V / 1e6:+.2f}M positions)")


if __name__ == "__main__":
    main()
