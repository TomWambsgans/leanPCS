#!/bin/sh
# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
# Reproduces the EIP draft's two benchmarks (eip-draft_leanPCS.md, "Benchmarks"): `sh bench.sh`.
#
# 1. Zero-knowledge Keccak-256 Merkle membership: the prover's time, then the contract's gas.
# 2. leanVM by recursion, at 128 leanXMSS signatures: the prover's time from leanVM's execution trace to the recursive
#    proof and its openings, then the contract's gas. The trace is written once, by leanVM at commit 9d50c92a3 (the
#    Keccak VM) patched by crates/leanvm/univariate/src/prover/dump_keccak/apply.sh, and kept in $BENCH_DIR.
#
# It ends with the figures of the EIP draft's table: the prover column (the measured prover time plus 0.1 s a PCS
# claim), the calldata, the PIOP column (the PIOP's frame alone: max(standard, floor) of its calldata and execution),
# the claims and the total.
#
# BENCH_DIR (default target/bench) keeps leanVM's tree, the trace and the runs' logs; LEANVM_REPO is where leanVM is
# fetched from; RUSTFLAGS defaults to -C target-cpu=native. REPEAT (default 1) runs the two provers that many times,
# interleaved (membership, leanVM, membership, ...), and reports their medians; each leanVM run is itself the median of
# 5 warm passes. BENCH_PIN prefixes the timed commands only (the builds run first, unpinned).
#
# The EIP draft's figures are medians of five interleaved runs on 8 physical cores of an idle AMD EPYC 9355P, with
# RUSTFLAGS as README.md gives them for Zen 5:
#   LEANVM_NUM_THREADS=8 BENCH_PIN="taskset -c 0-7" REPEAT=5 sh bench.sh
set -eu

root=$(cd "$(dirname "$0")" && pwd)
work=${BENCH_DIR:-$root/target/bench}
repo=${LEANVM_REPO:-https://github.com/leanEthereum/leanMultisig}
commit=9d50c92a34aabb4df6b0c4502f056e1f07b26bab
repeat=${REPEAT:-1}
pin=${BENCH_PIN:-}
export RUSTFLAGS="${RUSTFLAGS:--C target-cpu=native}"
cd "$root"
logs=$work/logs
mkdir -p "$logs"
rm -f "$logs"/membership.* "$logs"/pipeline.*

echo "== leanVM: execution trace of 128 signatures"
trace=$work/traces/xmss128
if [ ! -f "$trace/meta.txt" ]; then
    tree=$work/leanvm-9d50c92a3
    if [ ! -d "$tree" ]; then
        git init -q "$work/leanvm.git"
        git -C "$work/leanvm.git" fetch -q --depth 1 "$repo" "$commit"
        mkdir -p "$tree"
        git -C "$work/leanvm.git" archive "$commit" | tar -x -C "$tree"
        sh "$root/crates/leanvm/univariate/src/prover/dump_keccak/apply.sh" "$tree"
    fi
    (cd "$tree" && LEANVM_TRACE_DUMP="$trace" cargo leanvm aggregate --xmss 128 --log-inv-rate 1)
fi

echo "== Building"
cargo bench -p quotient --bench membership --no-run
cargo test --release -p leanvm_rec --test pipeline --no-run

run=1
while [ "$run" -le "$repeat" ]; do
    echo "== Membership: prover (run $run of $repeat)"
    $pin cargo bench -p quotient --bench membership | tee "$logs/membership.$run"
    echo "== leanVM: prover, median of 5 passes (run $run of $repeat)"
    LEANVM_TRACE="$trace" PIPELINE_REPEAT=5 $pin cargo test --release -p leanvm_rec --test pipeline -- --ignored \
        --nocapture | tee "$logs/pipeline.$run"
    run=$((run + 1))
done

echo "== Membership: gas"
cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report | tee "$logs/membership-gas"

echo "== leanVM: gas, of the real 128-signature proof's calldata"
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture --test-threads 1 real_end_to_end \
    | tee "$logs/leanvm-gas"

# The median of the numbers on standard input, one a line.
median() { sort -g | awk '{ v[NR] = $1 } END { if (NR % 2) print v[(NR + 1) / 2]; else print (v[NR / 2] + v[NR / 2 + 1]) / 2 }'; }

m_prover=$(cat "$logs"/membership.* | awk -F: '/^prover total/ { print $2 + 0 }' | median)
l_prover=$(cat "$logs"/pipeline.* | awk '$2 == "s" && $3 == "total" { print $1 }' | median)
# A value of the gas tests' `BENCH <name> key=value ...` lines (`bench <log> <name> <key>`), or a loud failure.
bench() {
    v=$(awk -v name="$2" -v key="$3" '$1 == "BENCH" && $2 == name {
        for (i = 3; i <= NF; i++) if (index($i, key "=") == 1) print substr($i, length(key) + 2) }' "$1" | head -n 1)
    [ -n "$v" ] || { echo "bench.sh: no BENCH $2 $3= in $1" >&2; exit 1; }
    echo "$v"
}
# A number with a comma every three digits.
grouped() { awk -v n="$1" 'BEGIN { s = ""; while (length(n) > 3) { s = "," substr(n, length(n) - 2) s; n = substr(n, 1, length(n) - 3) } print n s }'; }
m_claims=$(bench "$logs/membership-gas" membership claims)
m_calldata=$(bench "$logs/membership-gas" membership calldata)
m_piop=$(grouped "$(bench "$logs/membership-gas" membership piop)")
m_total=$(grouped "$(bench "$logs/membership-gas" membership total)")
l_claims=$(bench "$logs/leanvm-gas" leanvm claims)
l_calldata=$(bench "$logs/leanvm-gas" leanvm calldata)
l_piop=$(bench "$logs/leanvm-gas" leanvm piop)
l_total=$(bench "$logs/leanvm-gas" leanvm total)

echo
echo "== The EIP draft's table ($repeat run(s); prover = median + 0.1 s a claim)"
awk -v p="$m_prover" -v c="$m_claims" -v d="$m_calldata" -v g="$m_piop" -v t="$m_total" 'BEGIN {
    printf "membership: prover %.2f s (measured %.3f s), calldata %s bytes, PIOP %s gas, %s claims, total %s gas\n",
        p + 0.1 * c, p, d, g, c, t }'
awk -v p="$l_prover" -v c="$l_claims" -v d="$l_calldata" -v g="$l_piop" -v t="$l_total" 'BEGIN {
    printf "leanVM:     prover %.2f s (measured %.3f s), calldata %s bytes, PIOP %s gas, %s claims, total %s gas\n",
        p + 0.1 * c, p, d, g, c, t }'
