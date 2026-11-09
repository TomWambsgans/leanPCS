# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
"""Soundness of pi1, the univariate PIOP of docs/leanvm/univariate/SPEC.md on the Keccak VM, round by round after
the union bounds over the level-0 Johnson lists of its two proof commitments, and the sizes of its commitments: the
main line (`KECCAK_MAIN`) and pi1-rec3 (`KECCAK_REC3`), at the workloads of crates/leanvm/statement/src/shapes.rs
(the reference: 128 signatures).

    python3 -I params/leanvm_univariate_params.py

Each challenge's error is the Schwartz-Zippel bound of the polynomial it must avoid, times the number of committed
tables it is drawn against: L1 (C1's list) for those drawn after C1 and before C2, L1 L2 after C2. The setup
commitment F is computed by anyone from the program: an honest codeword's list within the Johnson radius is itself
(L = 1). The lists are the certified level-0 lists of leanerVM's WhirBridge (`params/whir_params.py --large`, rate
1/2), which the Lean bound uses too.

As the code states them (crates/leanvm/univariate/src/verifier.rs; tables, flushes and counters from
crates/leanvm/statement/src/layout.rs):
- every degree at t is taken with each quotient's committed capacity (`verifier::chunks`, the third chunk rounded up
  to a power of two), sized for the height's fewest rows 2^(r-1) + 1 (SPEC.md §13, F1), since a cheating prover fills
  the whole capacity;
- a table's leaf identity is checked times Z_act(t), whose degree is the prover's row count (at most 2^r);
- the heap's blocks are `heap.rs`'s, the unused blocks included, each an identity of degree < 2^r;
- the bus's polynomial has degree 4 a tuple (one Schwartz-Zippel over E^5; 16 at pi1-rec3, alpha = (c, c^2, c^4,
  c^8)), with every table full (the counts are the prover's);
- Flock on the Keccak-f block (crates/vendor/flock-42422001/src/keccak.rs, docs/leanvm/flock/KECCAK.md):
  log_n = 17 + h_SHA3, a univariate skip of 3, seven fixed zerocheck coordinates then the drawn ones (at pi1-rec3 the
  squares of one), the lincheck's 11 rounds, the slices sent and the terminal computed from the block's structure (no
  matrix committed, no claim), the ring map in tower order (6/|E|, crates/leanvm/statement/src/ring_tower.rs);
- rho, lambda and every round of the batching sumcheck are rounds of their own; pi1-rec3's batch runs two variables
  a round (degree 8) with 160-bit challenges.

The Fiat-Shamir composition is the Lean's (formal/UniSound/UniSound/Fs128.lean, `uniBound128`): an adversary of Q
permutation queries breaks pi1 with probability about Q (eps_WHIR + max over rounds of the round's error times its
lists), the three openings charged once at WhirBridge's exact certified bound 269 * 2^-137. So the figure of merit
is the weakest round after its lists, not the sum of the rounds (printed too: the interactive protocol's error).
"""
from fractions import Fraction
import math

LOGQ = 192  # |E| = 2^192
NARROW = 160  # pi1-rec3's batch challenges: the hash's low 160 bits

# leanVM 42422001's five tables and the Keccak VM's SHA3 (layout.rs): per flush, the degree in the columns of its pull
# and push tuples (2 for an address fp*o or a product, 1 otherwise; `verifier::tuple_degree`); the counters; the
# factor columns sent (`verifier::factor_columns`); the fingerprints sent (`verifier::table_part`: a pull with an
# unsent column, a push that differs from its pull by one); the columns; the table's own constraints.
TABLES = {
    "XOR": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, factors=2, fingerprints=4, width=15),
    "MUL": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, factors=5, fingerprints=4, width=15),
    "SET": dict(pull=[1, 1, 2], push=[1, 1, 2], counters=2, factors=2, fingerprints=2, width=8),
    "DEREF": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, factors=5, fingerprints=4, width=15),
    "JUMP": dict(pull=[1, 1, 2, 2, 2], push=[2, 1, 2, 2, 2], counters=4, factors=3, fingerprints=6, width=14,
                 constraints=2),
    # the state step, the bytecode read, 13 cells read and 13 written (each at fp * o, degree 2)
    "SHA3": dict(pull=[1, 1] + [2] * 26, push=[1, 1] + [2] * 26, counters=27, factors=2, fingerprints=27, width=86,
                 lanes=50),
}

# The workloads (shapes.rs): rows per table in the order above, memory cells used. Memory 2^ceil(log2 cells).
WORKLOADS = {
    32: ([6956, 9877, 6578, 9652, 3995, 4440], 184_479),
    128: ([24260, 36229, 24626, 35812, 15509, 17712], 721_598),
    400: ([73288, 110893, 75762, 109932, 48157, 55316], 2_243_324),
    1000: ([181438, 275593, 188562, 273432, 120085, 138266], 5_600_312),
}
REFERENCE = 128
LOG_BYTECODE = 18  # the aggregation program, 2^17.54 instructions
FLOCK_LOG_SIZE = 17  # a Keccak-f block's slots: one permutation a SHA3 row, 2^11 words of q_flock
FLOCK_SKIP = 3
FLOCK_FIXED = 7  # leanVM's fixed zerocheck coordinates
PACKING = 6
QFLOCK_ROW_BITS = FLOCK_LOG_SIZE - PACKING  # 11: q_flock's words a SHA3 row, and the lincheck's rounds
LINCHECK_ROUNDS = QFLOCK_ROW_BITS
RING_MAP = 6

# Certified level-0 Johnson lists for public layouts at rate 1/2 (WhirBridge `largeShapes`, `params/whir_params.py
# --large`), by stack variables; the Lean bound takes the largest, 9,952, for every round.
CERTIFIED_L0 = {24: 9952, 25: 7908, 26: 6296, 27: 4473, 28: 3564}
LEAN_LIST = 9952
# WhirBridge.εExact: the exact certified per-group bound of an opening (the weakest group at 2^24 ..= 2^28 has
# 128.95 bits; the setup's 2^23 is certified in formal/UniKeccakSound/UniKeccakSound/Fs/Whir23.lean), charged once for
# all of a proof's openings in the query-bounded random-permutation model.
EPS_WHIR = Fraction(269, 2 ** 137)
# The Lean's cap on every round's error before the lists (formal/UniKeccakSound/README.md): 2^32/|E| on the main line,
# 2^35/|E| at pi1-rec3 (its narrow pairs: 8/2^160).
LEAN_ROUND = {"main": 32, "rec3": 35}


def log2_ceil(x):
    return max(0, (x - 1).bit_length())


def chunks(count):
    """verifier::chunks: at most three powers of two covering `count` coefficients."""
    sizes, left = [], count
    while left > 0:
        top = left.bit_length() - 1
        if len(sizes) == 2 and left != 1 << top:
            sizes.append(top + 1)
            break
        sizes.append(top)
        left -= 1 << top
    return sizes


def capacity(count):
    return sum(1 << e for e in chunks(count))


def degree(plus, minus):
    """verifier::degree: saturating."""
    return max(0, plus - minus)


def least_rows(r):
    return 0 if r == 0 else (1 << (r - 1)) + 1


def heap_blocks(lm, lb, heights):
    """heap.rs: the used blocks largest first (memory, bytecode, then the tables in order), then aligned unused ones."""
    used = [("memory", lm, 0), ("bytecode", lb, 1)] + [(name, h, 2 + i) for i, (name, h) in enumerate(zip(TABLES, heights))]
    used.sort(key=lambda b: (-b[1], b[2]))
    total = sum(1 << r for _, r, _ in used)
    d = (total - 1).bit_length()
    base = 1 << d
    blocks, offset = [], 0
    for name, r, _ in used:
        blocks.append((name, r))
        offset += 1 << r
    while offset < base:
        r = (offset & -offset).bit_length() - 1
        while offset + (1 << r) > base:
            r -= 1
        blocks.append(("unused", r))
        offset += 1 << r
    return d + 1, blocks


def stack_vars(words):
    """StackLayout::new: the placed words' log2, at least 15."""
    return max(15, log2_ceil(max(words, 2)))


def analyse(xmss):
    rows, cells = WORKLOADS[xmss]
    lm, lb = log2_ceil(cells), LOG_BYTECODE
    heights = [log2_ceil(r) for r in rows]
    h_sha3 = heights[-1]
    r_w = max(heights + [lm])
    h, blocks = heap_blocks(lm, lb, heights)
    # The identities at t, by degree.
    ids = {"tree": 1 << (h + 1)}
    c2_words = 3 * ((1 << h) + (1 << h) + 1)  # T, Q_tree's two chunks; E-valued, three K-limbs each
    caps = {}
    for name, r in blocks:
        n = 1 << r
        if name == "unused":
            ids[f"unused 2^{r}"] = n - 1
            continue
        if name in ("memory", "bytecode"):
            # R D_fin + w_r Q = D_init: the fingerprints have degree n - 1 (the setup's addresses, the final counts)
            cap = capacity(degree(2 * (n - 1), n) + 1)
            ids[f"leaf {name}"] = max(2 * (n - 1), n + cap - 1)
        else:
            t = TABLES[name]
            pull_deg, push_deg = 1 + sum(t["pull"]), sum(t["push"])  # the pull side carries R
            cap = capacity(degree(max(pull_deg, push_deg) * (n - 1) + (n - least_rows(r)), n) + 1)
            # R (P_pull w_r + Z_act^2) + Q w_r Z_act = P_push w_r + Z_act^2, deg Z_act <= n
            ids[f"leaf {name}"] = max(pull_deg * (n - 1) + n, 3 * n - 1, cap - 1 + 2 * n, push_deg * (n - 1) + n)
        caps[name] = cap
        c2_words += 3 * cap
    # Q_W (C1-only constraints lifted to V_{r_W}, batched by gamma): its degree as verifier.rs sizes it, and the
    # lifted constraints' degrees.
    qd, lifted, constraints = 0, 0, 0
    for (name, t), r in zip(TABLES.items(), heights):
        n = 1 << r
        lift = (1 << r_w) - n
        if t.get("constraints"):  # JUMP: b + v_cond w, v_cond (b + 1)
            qd = max(qd, degree(n, 2))
            lifted = max(lifted, 2 * (n - 1) + lift)
            constraints += t["constraints"]
        qd = max(qd, degree((n - 1) * (1 + t["counters"]), n))  # z_T prod c_j + 1, on every row
        lifted = max(lifted, (n - 1) * (1 + t["counters"]) + lift)
        constraints += 1
        if t.get("lanes"):  # copy_j - l_j(y(t)), l_j of degree <= r 2^(r-1)
            qd = max(qd, degree(r * (n // 2), n))
            lifted = max(lifted, max(n - 1, r * (n // 2)) + lift)
            constraints += t["lanes"]
    qd = max(qd, degree(1 << lm, 3))  # the public input: (mem_k - I_k) w_{r_W} / w_1, three limbs
    lifted = max(lifted, (1 << lm) - 1 + (1 << r_w) - 2)
    constraints += 3
    cap_w = capacity(qd + 1)
    c2_words += 3 * cap_w
    ids["Q_W"] = max(lifted, (1 << r_w) + cap_w - 1)
    # C1: q_flock (values, 2^11 words a SHA3 row), every column and one inverse a table, memory (3 limbs and the
    # final count), the bytecode's final count.
    c1_words = (1 << (h_sha3 + QFLOCK_ROW_BITS)) + sum((t["width"] + 1) << r for t, r in zip(TABLES.values(), heights)) \
        + (4 << lm) + (1 << lb)
    setup_words = (1 << (lb + 4)) + (1 << lm)  # the bytecode's 16 tuple slots, the memory's addresses
    # The bus: tuples a side, every table full, the memory, the bytecode, the boundary.
    side = sum(len(t["pull"]) << r for t, r in zip(TABLES.values(), heights)) + (1 << lm) + (1 << lb) + 1
    # The relations on each commitment (`Relations::combine`, by rho).
    c1_rel = sum(t["counters"] + t["factors"] + t["fingerprints"] for t in TABLES.values()) + 2 + 1 + 1 + 1
    c2_rel = 1 + 1 + 1 + len(blocks) + 1
    setup_rel = 2
    log_n = FLOCK_LOG_SIZE + h_sha3
    s1, s2, s3 = stack_vars(c1_words), stack_vars(c2_words), stack_vars(setup_words)
    return dict(xmss=xmss, lm=lm, heights=heights, h=h, blocks=blocks, ids=ids, caps=caps, cap_w=cap_w, qd=qd,
                constraints=constraints, c1=c1_words, c2=c2_words, setup=setup_words, s1=s1, s2=s2, s3=s3,
                side=side, rel=dict(C1=c1_rel, C2=c2_rel, setup=setup_rel), log_n=log_n,
                batch_vars=max(s1, s2, s3), values=values_at_t())


def values_at_t():
    """SPEC.md §8: counters, factors and fingerprints; memory 3, bytecode 2; T(t), Q_W(t)."""
    return sum(t["counters"] + t["factors"] + t["fingerprints"] for t in TABLES.values()) + 3 + 2 + 2


def lists(a):
    return CERTIFIED_L0.get(a["s1"]), CERTIFIED_L0.get(a["s2"])


def rounds(a, variant, l1, l2):
    """pi1's rounds: (label, error numerator, log2 of the field it is over, how many such rounds, the lists' union).
    Each round's error is numerator / 2^bits; a row of several rounds has that error each."""
    rec3 = variant == "rec3"
    drawn = a["log_n"] - FLOCK_SKIP - FLOCK_FIXED
    k = FLOCK_SKIP
    out = [
        ("bus (α, β): multisets, degree 16 a tuple in (c, β), every table full" if rec3 else
         "bus (α, β): multisets, degree 4 a tuple, every table full", (16 if rec3 else 4) * a["side"], LOGQ, 1, l1),
        (f"γ: {a['constraints']} C1-only constraints batched", a["constraints"] - 1, LOGQ, 1, l1),
        (f"Flock: the zerocheck's {drawn} drawn coordinates" + (" as squares of one" if rec3 else ""),
         (1 << drawn) - 1 if rec3 else drawn, LOGQ, 1, l1),
        (f"Flock: the skip's z (k = {k})", (1 << (k + 1)) - 1, LOGQ, 1, l1),
        (f"Flock: the zerocheck's {a['log_n'] - k} rounds, degree 3", 3, LOGQ, a["log_n"] - k, l1),
        ("Flock: the lincheck's α (4 claims)", 3, LOGQ, 1, l1),
        (f"Flock: the lincheck's {LINCHECK_ROUNDS} rounds, degree 2", 2, LOGQ, LINCHECK_ROUNDS, l1),
        ("Flock: the ring map in tower order", RING_MAP, LOGQ, 1, l1),
        ("t: every identity at its committed capacity", sum(a["ids"].values()), LOGQ, 1, l1 * l2),
        (f"ρ: C1's {a['rel']['C1']} relations combined", a["rel"]["C1"] - 1, LOGQ, 1, l1 * l2),
        ("λ: 3 claims", 2, LOGQ, 1, l1 * l2),
    ]
    v = a["batch_vars"]
    if rec3:
        out.append((f"batch: {v // 2} pairs, degree 8, narrow", 8, NARROW, v // 2, l1 * l2))
        if v % 2:
            out.append(("batch: the plain round, degree 2, narrow", 2, NARROW, 1, l1 * l2))
    else:
        out.append((f"batch: {v} rounds, degree 2", 2, LOGQ, v, l1 * l2))
    return out


def err(num, bits_):
    return Fraction(num, 2 ** bits_)


def bits(x):
    return -math.log2(x)


def weakest(rs):
    """The largest round error after its lists: (label, error)."""
    return max(((label, err(num, b) * union) for label, num, b, _, union in rs), key=lambda p: p[1])


def interactive(rs):
    return sum(err(num, b) * count * union for _, num, b, count, union in rs)


def uni_bound128(e, q):
    """formal/UniSound/UniSound/Fs128.lean's `uniBound128 e Q` (also RecCompose's `pi2BoundE`), in exact rationals:
    N (eps + 5N/2^256) + N (L^2 e + 8N/2^256) + 2N^2/2^256 + (2^81 + Q)^2/2^508, N = 2^33 + Q; here `e` already
    carries its lists."""
    n = 2 ** 33 + q
    return (n * (EPS_WHIR + Fraction(5 * n, 2 ** 256)) + n * (e + Fraction(8 * n, 2 ** 256))
            + Fraction(2 * n * n, 2 ** 256) + Fraction((2 ** 81 + q) ** 2, 2 ** 508))


def per_query(e):
    """Bits as Q / eps at Q = 2^64: 64 + the bound's bits."""
    return 64 + bits(uni_bound128(e, 2 ** 64))


def pi1(xmss, variant):
    """pi1's figures: the analysis, the rounds, the weakest round, the bits at Q = 2^64 (Q / eps)."""
    a = analyse(xmss)
    l1, l2 = lists(a)
    rs = rounds(a, variant, l1, l2)
    label, w = weakest(rs)
    return dict(a=a, rounds=rs, weakest=(label, w), total=per_query(w), interactive=interactive(rs))


def lean_pi1(variant):
    e = Fraction(LEAN_LIST ** 2 * 2 ** LEAN_ROUND[variant], 2 ** LOGQ)
    return e, per_query(e)


def main():
    print("== commitments (words) and the stacks (C1, C2: proof; F: setup, L = 1)")
    for xmss in WORKLOADS:
        a = analyse(xmss)
        flag = "  ** over 2^28 **" if max(a["s1"], a["s2"]) > 28 else (
            "  ** below 2^24: no certified list **" if min(a["s1"], a["s2"]) < 24 else "")
        print(f" {xmss:>5} signatures (heights {' '.join(map(str, a['heights']))}, memory 2^{a['lm']}): C1"
              f" 2^{math.log2(a['c1']):.2f} (stack 2^{a['s1']}), C2 2^{math.log2(a['c2']):.2f} (2^{a['s2']}),"
              f" F 2^{math.log2(a['setup']):.2f} (2^{a['s3']}); heap 2^{a['h']}; Flock log_n {a['log_n']};"
              f" bus side 2^{math.log2(a['side']):.2f}; Σ deg at t 2^{math.log2(sum(a['ids'].values())):.2f}{flag}")
    a = analyse(REFERENCE)
    print(f"\n== {REFERENCE} signatures: the identities at t (degrees), the quotients' capacities")
    for k, v in a["ids"].items():
        cap = a["caps"].get(k.split(" ", 1)[-1])
        print(f"   {k:16s} {v:>10,}" + (f"   (quotient capacity {cap:,})" if cap else ""))
    print(f"   {'Σ':16s} {sum(a['ids'].values()):>10,}   (Q_W: degree {a['qd']:,}, capacity {a['cap_w']:,})")
    print(f"   relations: C1 {a['rel']['C1']}, C2 {a['rel']['C2']}, F {a['rel']['setup']}; values at t"
          f" {a['values']}; batch over {a['batch_vars']} variables")

    for xmss in [32, 128, 400]:
        for variant in ("main", "rec3"):
            p = pi1(xmss, variant)
            a = p["a"]
            l1, l2 = lists(a)
            if l1 is None or l2 is None:
                print(f"\n== {xmss} signatures, {variant}: a stack outside 2^24 ..= 2^28, no certified list")
                continue
            print(f"\n== {xmss} signatures, {'pi1-rec3' if variant == 'rec3' else 'main line'}:"
                  f" L1 = {l1} (C1, 2^{a['s1']}), L2 = {l2} (C2, 2^{a['s2']}); bits a round, alone and after its lists")
            for label, num, b, count, union in p["rounds"]:
                e = err(num, b)
                print(f"   {label:72s} {bits(e):6.1f} {bits(e * union):6.1f}" + (f"   (x{count})" if count > 1 else ""))
            label, w = p["weakest"]
            print(f"   weakest round: {label} ({bits(w):.2f} bits after its lists);"
                  f" all rounds summed (interactive) {bits(p['interactive']):.2f}")
            print(f"   with WHIR's openings once (2^{-bits(EPS_WHIR):.2f}): {p['total']:.2f} bits as Q / ε at Q = 2^64")

    print("\n== against the Lean bound (formal/UniKeccakSound, uniBound128 at the reference shape)")
    for variant in ("main", "rec3"):
        p = pi1(REFERENCE, variant)
        e, lean = lean_pi1(variant)
        raw_max = max(err(num, b) for _, num, b, _, _ in p["rounds"])
        print(f"   {'pi1-rec3' if variant == 'rec3' else 'main line'}: Lean {lean:.2f} bits (every round"
              f" ≤ 2^{LEAN_ROUND[variant]}/|E|, lists 9952² for every round: 2^{-bits(e):.2f} a query);"
              f" the calculator {p['total']:.2f} (largest round before its lists 2^{192 - bits(raw_max):.2f}/|E|,"
              f" weakest after its lists 2^{-bits(p['weakest'][1]):.2f})")
    print("   WHIR's term, 2^-128.93 a query, is the same in both and dominates; the gap is the Lean's uniform round cap"
          "\n   and its uniform list 9,952² (the certified lists at C1's 2^27 and C2's 2^26 stacks are 4,473 and 6,296).")


if __name__ == "__main__":
    main()
