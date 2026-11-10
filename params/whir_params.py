# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
"""Replicates leanVM's WHIR eta search (crates/pcs/src/whir_config.rs) at this repository's three stack sizes,
and prints, per level, the Johnson list bound L the search assumes and every soundness term.

    python3 params/whir_params.py
    python3 params/whir_params.py --large     # the stack sizes 2^24 ..= 2^28 of a leanVM PIOP (below)

    python3 params/whir_params.py --recursion # a second ladder, a design alternative (below)

`--recursion`: a second ladder, once the leanVM recursion's openings (opening version 3, removed from the code: every
opening is now the EIP draft's PCS version 1, leanVM's ladder): the same level 0 (rate 1/2, a 6-variable fold), then
4-variable folds whose
rates fall one bit a level (1/4, 1/8, 1/16, ...; every block at least 2^8 positions) instead of three. Per stack size
2^15 ..= 2^28: the code's eta search on that ladder (the counts the prover and the verifier's table use), every term
of the code's accounting, and leanerVM's certificate groups (`Params/Check.lean`'s FoldOK, OodOK, QueryOK, FinalOK,
the row-union factor 2^(l-1) included) at slacks chosen here as `gen.py` chooses them: the largest level-0 slack
whose groups clear 128 bits, at deeper levels the slack that balances the fold group against the query group. These
ladders are not in leanerVM's `certTable` (its 56 ladders are the deployed schedule's), so the certificate figures
are this script's computation of the checks `shapeOK` would make, not a kernel-checked table. Then the trade-off
against the deployed ladder and two other schedules: queries, the deeper levels' committed words, and an estimate of
the proof's bytes.

`--large` (added for formal/WhirBridge/WhirBridge/Large*.lean): at every stack size 2^24 ..= 2^28, rate 1/2, the
code's eta search as above, then leanerVM's certified codes (`Params/Deployed.lean`, certTable, rate 1/2 rows
copied below) with every group's bound computed exactly as the certificate's `Nat` check does (`Params/Check.lean`:
listHi, thrHi, excHi, FoldOK, OodOK, QueryOK, FinalOK), read as bits; the opening's query count QO
(`largeQueries`) and `openingBoundAt QO (2^64)`; and the list factors after one, two, three roots.
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


def configs():
    out = {}
    for name, log_n in [("wiring", 24), ("witness", 25), ("quotient", 28)]:
        rates, cols, ks, yr = ladder(log_n)
        levels, prev = [], 0
        for i, (r, c, k) in enumerate(zip(rates, cols, ks)):
            o = optimize(i, r, c, k, prev=prev)
            o.update(rate=r, cols=c, k=k)
            levels.append(o)
            prev = o["queries"]
        out[name] = (log_n, yr, levels)
    return out


# ---------------------------------------------------------------------------------------------------------
# The reduction's rounds after the union over the level-0 Johnson lists (WHIR takes no OOD sample at level
# 0, so a root binds only to a list until the claims are opened).
# ---------------------------------------------------------------------------------------------------------

# leanerVM `mumbai`, LeanVM/Protocol/Whir/Params/Deployed.lean, certTable: level 0 of (mu, R = 1), eta = e / 2^22.
FORMAL_ETA_E = {24: 298, 25: 375, 28: 832}


def list_max(log_n, eta, r=1):
    c = log_n - 6
    return math.floor(1 / (2 * eta * math.sqrt(reduced_rate(r, c))))


def reduction_rounds(l_witness, l_quotient, n_cells=2**24, identity_degree=2**28 + 2**22 + 9230):
    """Bits of each round of the reduction, the round's error unioned over the lists it precedes."""
    q = 2.0**192
    copy_paper = (2 * n_cells**2 + 4 * n_cells + 8) / q  # main.tex / formal: 2N^2 + 4N + 8
    copy_tight = (6 * n_cells + 8) / q  # one uncancelled pole: 2N bad beta, 2N bad alpha, 2N for DD' on H
    ident = identity_degree / q
    lb = lambda e: -math.log2(e)
    return {
        "copy (alpha,beta,gamma), paper bound": (lb(copy_paper), lb(copy_paper * l_witness)),
        "copy (alpha,beta,gamma), tight bound": (lb(copy_tight), lb(copy_tight * l_witness)),
        "identities (t)": (lb(ident), lb(ident * l_witness * l_quotient)),
        "rho": (lb(3 / q), lb((3 * l_witness + l_quotient) / q)),
        "WHIR batching lambda on R2 (J = 2)": (None, lb(l_quotient / q)),
    }


def report_unions():
    code = configs()
    lists = {
        "whir_config.rs eta search (the code's accounting)": {
            name: math.floor(2 ** code[name][2][0]["logL"] + 1e-9) for name in code
        },
        "leanerVM certified eta (what F2 would import)": {
            name: list_max(log_n, FORMAL_ETA_E[log_n] / 2**22)
            for name, log_n in [("wiring", 24), ("witness", 25), ("quotient", 28)]
        },
    }
    for title, ls in lists.items():
        print(f"\n== level-0 lists, {title}: " + ", ".join(f"{k} L={v} (2^{math.log2(v):.2f})" for k, v in ls.items()))
        for name, (ideal, union) in reduction_rounds(ls["witness"], ls["quotient"]).items():
            ideal_s = "     -" if ideal is None else f"{ideal:6.1f}"
            print(f"   {name:40s} ideal commitments {ideal_s} bits, after the union {union:6.1f} bits")
    cap = (2 * 2**48 + 4 * 2**24 + 8) * 2**18 / 2**192
    print(f"\n   with leanerVM's generic cap L <= 2^18 instead, the copy round (paper bound): {-math.log2(cap):.1f} bits")


def split_opening_attack(queries=225, grinding=17, d=0.25):
    """Two separate openings of one root, each against a different list member half a code distance apart."""
    per_attempt = queries * -math.log2(1 - d)
    return per_attempt, per_attempt + grinding + 1


# ---------------------------------------------------------------------------------------------------------
# --large: the stack sizes 2^24 ..= 2^28 (formal/WhirBridge/WhirBridge/Large*.lean)
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


# ---------------------------------------------------------------------------------------------------------
# --recursion: the second ladder (once opening version 3, `RECURSION_SCHEDULE`; no longer in the code)
# ---------------------------------------------------------------------------------------------------------

DEPLOYED = (3, 1, 0)  # whir_config.rs: DEPLOYED_SCHEDULE (initial, subsequent, min_log_block)
RECURSION = (5, 3, 8)  # whir_config.rs: RECURSION_SCHEDULE
OTHERS = {"(5, 2, 8): 1/2, 1/4, 1/16, 1/64, ...": (5, 2, 8), "(6, 3, 8): 1/2, 1/2, 1/4, 1/8, ...": (6, 3, 8)}


def schedule_ladder(log_n, schedule, r0=1):
    """`derive_ladder_shape` on a `DomainSchedule`: (rates, cols, folds, residual)."""
    initial, subsequent, min_log_block = schedule
    rates, cols, ks = [r0], [log_n - 6], [6]
    n, fold, rate, red = log_n - 6, 6, r0, initial
    while n > 5:
        k = min(4, n)
        rate = max(rate + fold - red, min_log_block - (n - k))
        red = subsequent
        rates.append(rate)
        cols.append(n - k)
        ks.append(k)
        n -= k
        fold = k
    return rates, cols, ks, n


def schedule_config(log_n, schedule):
    """The code's eta search on the schedule's ladder, level by level (`derive_config_with_schedule`)."""
    rates, cols, ks, yr = schedule_ladder(log_n, schedule)
    levels, prev = [], 0
    for i, (r, c, k) in enumerate(zip(rates, cols, ks)):
        o = optimize(i, r, c, k, prev=prev)
        assert o is not None, f"2^{log_n}: level {i} infeasible"
        o.update(rate=r, cols=c, k=k)
        levels.append(o)
        prev = o["queries"]
    return levels, yr


def make_cert(kappa, r, e):
    """A certificate of the level code (kappa, r) at slack e / 2^22, with the tightest bracket of sqrt(rho_-)."""
    d = 2**kappa - 1
    return Cert(kappa, r, e, math.isqrt(d << (80 - kappa - r)))


def cert_groups(level, e, nxt):
    """(fold, ood, query) bits of a level at slack e, the next level's certificate `nxt` (None: the final level)."""
    c = make_cert(level["cols"], level["rate"], e)
    if c.thr_lo <= c.d:
        return None
    if nxt is None:
        return c.fold_bits(level["k"]), None, c.final_bits(level["queries"])
    return c.fold_bits(level["k"]), c.ood_bits(nxt), c.query_bits(nxt, level["queries"])


def worst(groups):
    return -1e9 if groups is None else min(g for g in groups if g is not None)


def choose_slack(level, nxt, largest):
    """gen.py's choice: the largest slack whose groups clear 128 bits (level 0), else the balancing one."""
    rho = (2 ** level["cols"] - 1) / 2 ** (level["cols"] + level["rate"])
    emax = int((1 - math.sqrt(rho)) * 2**22) - 2
    grid = sorted({max(1, int(1.05**j)) for j in range(int(math.log(emax) / math.log(1.05)) + 1)})
    scored = [(worst(cert_groups(level, e, nxt)), e) for e in grid]
    if largest and any(v >= 128 for v, _ in scored):
        lo = max(e for v, e in scored if v >= 128)
        hi = min([e for e in grid if e > lo] + [emax])
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lo, hi = (mid, hi) if worst(cert_groups(level, mid, nxt)) >= 128 else (lo, mid)
        return lo
    _, e = max(scored)
    lo, hi = max(1, int(e / 1.06)), int(e * 1.06) + 1
    while hi - lo > 2:
        m1, m2 = lo + (hi - lo) // 3, hi - (hi - lo) // 3
        if worst(cert_groups(level, m1, nxt)) < worst(cert_groups(level, m2, nxt)):
            lo = m1
        else:
            hi = m2
    return max(range(lo, hi + 1), key=lambda e: worst(cert_groups(level, e, nxt)))


def certify(levels):
    """Slacks from the last level up, and every level's (e, fold, ood, query) bits."""
    out, nxt = [None] * len(levels), None
    for i in reversed(range(len(levels))):
        e = choose_slack(levels[i], nxt, largest=(i == 0))
        out[i] = (e,) + cert_groups(levels[i], e, nxt)
        nxt = make_cert(levels[i]["cols"], levels[i]["rate"], e)
    return out


def deeper_words(levels):
    """The words the deeper levels commit (E elements): each level's block times its lanes."""
    return sum(2 ** (l["cols"] + l["rate"] + l["k"]) for l in levels[1:])


def proof_bytes(levels, lanes0=64):
    """An estimate of the opening's Merkle part: each level's rows (8 B a lane at level 0, 24 B a lane past it) and
    their pruned paths (about q (depth - log2 q + 1) hashes of 32 bytes)."""
    total = 0
    for i, l in enumerate(levels):
        depth, q = l["cols"] + l["rate"], l["queries"]
        row = lanes0 * 8 if i == 0 else 24 * 2 ** l["k"]
        total += q * row + q * max(depth - math.log2(q) + 1, 1) * 32
    return total


def report_recursion():
    print("== the second ladder (once opening version 3: 5 bits, then 3, blocks >= 2^8; no longer in the code)")
    print("   per level: rate, fold, queries | the code's accounting (whir_config.rs): pg / query+17 / ood / alg bits"
          " | leanerVM's groups at the chosen slack e/2^22: fold / ood / query+17 bits")
    for log_n in range(15, 29):
        levels, yr = schedule_config(log_n, RECURSION)
        certs = certify(levels)
        print(f"-- 2^{log_n} (residual 2^{yr}): queries {[l['queries'] for l in levels]}")
        for i, (l, (e, fb, ob, qb)) in enumerate(zip(levels, certs)):
            ood = "    -" if ob is None else f"{ob:5.1f}"
            code_ood = "    -" if i == 0 else f"{l['ood_bits']:5.1f}"
            print(f"   L{i}: 1/2^{l['rate']:<2d} fold {l['k']} q {l['queries']:3d} | code {l['pg']:6.2f} /"
                  f" {l['queries'] * l['perq'] + 17:6.2f} / {code_ood} / {l['alg']:5.1f} (L {2 ** l['logL']:.0f}) |"
                  f" cert e {e:6d}: {fb:6.2f} / {ood} / {qb:6.2f} (listHi {make_cert(l['cols'], l['rate'], e).list_hi})")
        weakest_code = min(min(l["pg"], l["queries"] * l["perq"] + 17, l["alg"], 1e9 if i == 0 else l["ood_bits"])
                           for i, l in enumerate(levels))
        weakest_cert = min(min(g for g in c[1:] if g is not None) for c in certs)
        print(f"   weakest term: code {weakest_code:.2f} bits, certificate groups {weakest_cert:.2f} bits")
    print("\n== the trade-off (rate 1/2 at level 0; the queries, the deeper levels' committed words, an estimate of the"
          " Merkle part of a proof at 64 lanes)")
    schedules = {"deployed (3, 1, 0): 1/2, 1/16, 1/128, ...": DEPLOYED,
                 "recursion (5, 3, 8): 1/2, 1/4, 1/8, ...": RECURSION, **OTHERS}
    for log_n in (23, 24, 25, 26, 27, 28):
        print(f"-- 2^{log_n}")
        base = None
        for name, schedule in schedules.items():
            levels, _ = schedule_config(log_n, schedule)
            words, size = deeper_words(levels), proof_bytes(levels)
            base = base or (words, size)
            weakest = min(min(g for g in c[1:] if g is not None) for c in certify(levels))
            print(f"   {name:42s} rates {str([l['rate'] for l in levels]):20s} queries"
                  f" {str([l['queries'] for l in levels]):28s} (sum {sum(l['queries'] for l in levels)}):"
                  f" deeper words 2^{math.log2(words):.2f} ({words / base[0]:.3f}x), proof ~{size / 1024:.0f} KiB"
                  f" ({size / base[1]:.2f}x), certificate groups >= {weakest:.2f} bits")


if __name__ == "__main__":
    import sys

    if "--large" in sys.argv:
        report_large()
        sys.exit(0)
    if "--recursion" in sys.argv:
        report_recursion()
        sys.exit(0)
    for name, (log_n, yr, levels) in configs().items():
        print(f"== {name}: stack 2^{log_n}, residual 2^{yr}")
        for i, o in enumerate(levels):
            print(
                f" L{i}: rate 1/2^{o['rate']} msg 2^{o['cols']} fold {o['k']} m={o['m']} eta={o['eta']:.6f}"
                f" queries={o['queries']} ood={o['ood']} log2L={o['logL']:.3f} (L={2**o['logL']:.1f})"
                f" pg={o['pg']:.2f} q-bits={o['queries'] * o['perq']:.2f}+17 ood-bits={o['ood_bits']:.2f}"
                f" alg={o['alg']:.2f}"
            )
    report_unions()
    bits, work = split_opening_attack()
    print("\n== split opening of the quotient table's two claims (f halfway between two list members):")
    print(f"   one opening passes its 225 level-0 queries with (3/4)^225 = 2^-{bits:.1f};"
          f" both, with 17-bit grinding: about 2^{work:.1f} Keccak-f calls")
    print(f"   the count was sized for words farther than the Johnson radius: (1 - 0.2896)^225 = "
          f"2^-{225 * -math.log2(1 - 0.2896):.1f}")
