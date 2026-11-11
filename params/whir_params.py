# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
"""Replicates leanVM's WHIR eta search (crates/pcs/src/whir_config.rs) at the stack sizes 2^24 ..= 2^28, rate 1/2,
the sizes of every commitment of both lines (the membership proof's 2^24, 2^24, 2^28; leanVM's up to 2^28), and
checks them against leanerVM's certified codes (formal/WhirBridge/WhirBridge/Large*.lean).

    python3 params/whir_params.py            # (`--large` is accepted and gives the same report)

Per stack size: the code's eta search, level by level (the counts the prover and the verifier's table use), then
leanerVM's certified codes (`Params/Deployed.lean`, certTable, rate 1/2 rows copied below) with every group's bound
computed exactly as the certificate's `Nat` check does (`Params/Check.lean`: listHi, thrHi, excHi, FoldOK, OodOK,
QueryOK, FinalOK), read as bits; the opening's query count QO (`largeQueries`) and `openingBoundAt QO (2^64)`; and the
list factors after one, two, three roots.
"""
import math
import struct

LOGQ = 192.0
RS_DEG = (1 << 31) + (1 << 15) + (1 << 7) + (1 << 3) + (1 << 1) + 1


def reduced_rate(r, c):
    return (2.0**c - 1) / 2.0 ** (c + r)


def mparam(r, c, eta):
    return max(math.ceil(math.sqrt(reduced_rate(r, c)) / eta), 3)


def log_a(r, eta, c):
    rho = reduced_rate(r, c)
    s = math.sqrt(rho)
    g = 1 - s - eta
    h = mparam(r, c, eta) + 0.5
    num = 2 * h**5 + 3 * h * g * rho
    den = 3 * rho**1.5
    n = 2.0 ** (c + r)
    return math.log2(num / den * n + h / s)


def per_q(r, c, eta):
    rho = reduced_rate(r, c)
    g = 1 - math.sqrt(rho) - eta
    return math.log2(1 / (1 - g))


def log_l(r, c, eta):
    rho = reduced_rate(r, c)
    return math.log2(1 / (2 * eta * math.sqrt(rho)))


def ood_bits(r, c, eta, mu, s):
    l, lm = log_l(r, c, eta), math.log2(mu)
    return LOGQ - l - lm if s == 0 else s * (LOGQ - lm) - (2 * l - 1)


def alg_bits(r, c, eta, prev, s):
    d = max(RS_DEG, prev + s, 2)
    return LOGQ - math.log2(d) - log_l(r, c, eta)


def next_up(x):
    return struct.unpack("d", struct.pack("q", struct.unpack("q", struct.pack("d", x))[0] + 1))[0]


def eta_for_m(r, c, m):
    eta = math.sqrt(reduced_rate(r, c)) / m
    while mparam(r, c, eta) > m:
        eta = next_up(eta)
    return eta


def optimize(level, r, c, ilv, target=128, grind=17, prev=0):
    qt, mu, bl, best = target - grind, c + ilv, 2 ** (c + r), None
    for m in range(3, 4097):
        eta = eta_for_m(r, c, m)
        if eta >= 1 - math.sqrt(reduced_rate(r, c)):
            continue
        pg = LOGQ - log_a(r, eta, c)
        if pg + 1e-12 < target:
            break
        pq = per_q(r, c, eta)
        q = math.ceil(qt / pq)
        if q > bl:
            continue
        if level == 0:
            s = 0
        else:
            s = next((s for s in range(1, 9) if ood_bits(r, c, eta, mu, s) + 1e-12 >= target), None)
            if s is None:
                continue
        if ood_bits(r, c, eta, mu, s) + 1e-12 < target or alg_bits(r, c, eta, prev, s) + 1e-12 < target:
            continue
        cand = dict(m=m, eta=eta, queries=q, ood=s, logL=log_l(r, c, eta), pg=pg, perq=pq,
                    ood_bits=ood_bits(r, c, eta, mu, s), alg=alg_bits(r, c, eta, prev, s), mu=mu)
        if best is None or q < best["queries"]:
            best = cand
    return best


def ladder(log_n, r0=1):
    rates, cols, ks = [r0], [log_n - 6], [6]
    n, red, fold, rate = log_n - 6, 3, 6, r0
    while n > 5:
        k = min(4, n)
        rate = rate + fold - red
        red = 1
        rates.append(rate)
        cols.append(n - k)
        ks.append(k)
        n -= k
        fold = k
    return rates, cols, ks, n


# ---------------------------------------------------------------------------------------------------------
# The stack sizes 2^24 ..= 2^28 (formal/WhirBridge/WhirBridge/Large*.lean)
# ---------------------------------------------------------------------------------------------------------

LARGE = range(24, 29)

# leanerVM `mumbai`, Params/Deployed.lean, certTable, rate exponent 1, stack sizes 24 ..= 28: per level (kappa, R, e, s),
# slack eta = e / 2^22, bracket s / 2^40 <= sqrt(rho_-) <= (s + 1) / 2^40.
CERT_R1 = {
    24: [(18, 1, 298, 777470645082), (14, 4, 96, 274869518207), (10, 7, 52, 97136551275),
         (6, 10, 60, 34090246063), (2, 13, 25, 10520478337)],
    25: [(19, 1, 375, 777471386538), (15, 4, 121, 274873712607), (11, 7, 65, 97160286535),
         (7, 10, 74, 34225257466), (3, 13, 21, 11363415354)],
    26: [(20, 1, 471, 777471757266), (16, 4, 152, 274875809783), (12, 7, 82, 97172151991),
         (8, 10, 91, 34292563839), (4, 13, 95, 11762252358)],
    27: [(21, 1, 663, 777471942630), (17, 4, 191, 274876858365), (13, 7, 103, 97178084176),
         (9, 10, 114, 34326167535), (5, 13, 109, 11956682925)],
    28: [(22, 1, 832, 777472035311), (18, 4, 240, 274877382655), (14, 7, 129, 97181050133),
         (10, 10, 142, 34342957053), (6, 13, 130, 12052722081), (2, 16, 42, 3719550786)],
}

# What the Lean decides (LargeParams.lean): `largeLadder` queries, `largeList`, `largeQueries`.
LEAN_QUERIES = {24: [224, 56, 32, 23, 17], 25: [224, 56, 32, 23, 17], 26: [224, 56, 32, 23, 18],
                27: [225, 56, 32, 23, 18], 28: [225, 56, 32, 23, 18, 14]}
LEAN_LIST = {24: 9952, 25: 7908, 26: 6296, 27: 4473, 28: 3564}
LEAN_QO = {24: 7183, 25: 7546, 26: 7928, 27: 8318, 28: 9018}
GRIND = 17
SQRT_DEN, SLACK_DEN = 2**40, 2**22


def log2_frac(num, den):
    """log2(num / den) for (big) positive integers."""
    return math.log2(num) - math.log2(den)


class Cert:
    """A level's certificate, with the bounds of `Params/Check.lean` (`Cert.thrHi`, ..., `Cert.excHi`), exactly."""

    def __init__(self, kappa, r, e, s):
        self.kappa, self.r, self.e, self.s = kappa, r, e, s
        self.n = 2 ** (kappa + r)
        self.d = 2**kappa - 1
        den = SQRT_DEN * SLACK_DEN
        self.thr_hi = (((s + 1) * SLACK_DEN + e * SQRT_DEN) * self.n + den - 1) // den
        self.thr_lo = ((s * SLACK_DEN + e * SQRT_DEN) * self.n + den - 1) // den
        self.list_hi = den // (2 * e * s)
        self.m_hi = max(((s + 1) * SLACK_DEN + 2 * e * SQRT_DEN - 1) // (2 * e * SQRT_DEN), 3)
        self.mu_hi = ((2 * self.m_hi + 1) * SQRT_DEN + 2 * s - 1) // (2 * s) - 1
        self.h_hi = ((2 * self.m_hi + 1) ** 2 * self.n + 12 * self.d - 1) // (12 * self.d) - 1
        n, d, mu, h = self.n, self.d, self.mu_hi, self.h_hi
        exc_num = ((2 * mu - 1) * h + (n - d - 1) * mu) * (self.thr_lo - d) + (n - d) * (h + mu + 4 * d * mu * h)
        self.exc_hi = exc_num // (self.thr_lo - d)

    def fold_bits(self, fold):
        """`FoldOK`: (2 listHi + 2^(l-1) excHi) / |E|, the fold group with the row-union factor."""
        return 192 - math.log2(2 * self.list_hi + 2 ** (fold - 1) * self.exc_hi)

    def ood_bits(self, nxt):
        """`OodOK`: listHi'^2 kappa / |E|."""
        return 192 - math.log2(nxt.list_hi**2 * self.kappa)

    def query_bits(self, nxt, t):
        """`QueryOK`: ((thrHi - 1)/n)^t + (t + 1) listHi' / |E|, after the 17 bits of grinding."""
        num = (self.thr_hi - 1) ** t * 2**192 + (t + 1) * nxt.list_hi * self.n**t
        return GRIND - log2_frac(num, self.n**t * 2**192)

    def final_bits(self, t):
        """`FinalOK`: ((thrHi - 1)/n)^t + t / |E|, after the 17 bits of grinding."""
        num = (self.thr_hi - 1) ** t * 2**192 + t * self.n**t
        return GRIND - log2_frac(num, self.n**t * 2**192)


def certified_levels(log_n):
    """Per level of the certified ladder at 2^log_n, rate 1/2: (fold, queries, fold bits, ood bits, query bits)."""
    rates, cols, ks, _ = ladder(log_n)
    certs = [Cert(*c) for c in CERT_R1[log_n]]
    queries = LEAN_QUERIES[log_n]
    assert [c.kappa for c in certs] == cols and [c.r for c in certs] == rates, "certificates follow the ladder"
    assert len(queries) == len(certs)
    out = []
    for i, (c, k, t) in enumerate(zip(certs, ks, queries)):
        if i + 1 < len(certs):
            out.append((k, t, c.fold_bits(k), c.ood_bits(certs[i + 1]), c.query_bits(certs[i + 1], t)))
        else:
            out.append((k, t, c.fold_bits(k), None, c.final_bits(t)))
    assert certs[0].list_hi == LEAN_LIST[log_n], "listHi = largeList (listHi_large)"
    return out


def opening_bound_bits(qo, qa=2**64):
    """openingBoundAt QO QA = (QA + QO)(2^-128 + 5 (QA + QO) / 2^256), in bits."""
    n = qa + qo
    return -log2_frac(n * (2**128 + 5 * n), 2**256)


def report_large():
    print("== the stack sizes 2^24 ..= 2^28, rate 1/2 (formal/WhirBridge/WhirBridge/Large*.lean)")
    print("\n-- the code's eta search (whir_config.rs), its own accounting:")
    for log_n in LARGE:
        rates, cols, ks, yr = ladder(log_n)
        prev, line = 0, []
        for i, (r, c, k) in enumerate(zip(rates, cols, ks)):
            o = optimize(i, r, c, k, prev=prev)
            assert o["queries"] == LEAN_QUERIES[log_n][i], "the code's search gives the tabulated queries"
            prev = o["queries"]
            line.append(f"L{i} q={o['queries']} L={2**o['logL']:.0f} pg={o['pg']:.2f}")
        print(f"   2^{log_n} (residual 2^{yr}): " + "; ".join(line))
    print("\n-- leanerVM's certified codes, each group exactly as the certificate's Nat check bounds it, in bits"
          " (fold / out-of-domain / queries after 17 bits of grinding):")
    weakest = {}
    for log_n in LARGE:
        levels = certified_levels(log_n)
        parts = []
        for i, (k, t, fb, ob, qb) in enumerate(levels):
            ood = "-" if ob is None else f"{ob:.1f}"
            fin = " (final)" if ob is None else ""
            parts.append(f"{i}{fin}: {fb:.2f} / {ood} / {qb:.2f}")
        weakest[log_n] = min(min(fb, qb, 1e9 if ob is None else ob) for (_, _, fb, ob, qb) in levels)
        print(f"   2^{log_n}: " + "; ".join(parts))
    print("\n-- per shape: queries, L0 (certified), QO, weakest group, the opening's bound openingBoundAt QO QA in bits"
          " at QA = 0 and 2^64 (with the uniform QV = 10122 of openingBound: "
          f"{opening_bound_bits(10122, 0):.2f}, {opening_bound_bits(10122):.2f})")
    print("   log_n | queries                   | L0    (log2)  | QO   | weakest group | QA = 0 | QA = 2^64")
    for log_n in LARGE:
        l0 = LEAN_LIST[log_n]
        print(f"   {log_n:5d} | {str(LEAN_QUERIES[log_n]):25s} | {l0:5d} ({math.log2(l0):5.2f}) | {LEAN_QO[log_n]:4d} |"
              f" {weakest[log_n]:8.2f} bits | {opening_bound_bits(LEAN_QO[log_n], 0):6.2f} |"
              f" {opening_bound_bits(LEAN_QO[log_n]):6.2f}")
    print("\n-- list factors (WHIR takes no OOD sample at level 0: a challenge drawn after roots 1..r and before the"
          " claims that pin a candidate is union-bounded over L1 ... Lr); bits left, 192 - log2(product):")
    print("   one root:    " + ", ".join(f"2^{m}: {192 - math.log2(LEAN_LIST[m]):.2f}" for m in LARGE))
    print("   two roots (L1 L2):")
    for m1 in LARGE:
        print("     " + "  ".join(f"2^{m1}x2^{m2}: {192 - math.log2(LEAN_LIST[m1] * LEAN_LIST[m2]):6.2f}"
                                for m2 in LARGE))
    worst = max(LEAN_LIST.values())
    print(f"   three roots: worst L1 L2 L3 = 9952^3 = 2^{math.log2(worst**3):.2f}, {192 - math.log2(worst**3):.2f} bits left")
    for k in (20, 24, 28, 29, 30):
        print(f"   a degree-2^{k} identity after two roots (worst lists, 9952^2): "
              f"{192 - math.log2(worst**2) - k:.2f} bits; the formal bound union_two_roots_le: {165 - k} bits")


if __name__ == "__main__":
    report_large()
