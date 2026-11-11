#!/bin/sh
# Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
# Reproduces the EIP draft's two benchmarks (eip-draft_leanPCS.md, "Benchmarks"): `sh bench.sh`.
#
# 1. Zero-knowledge Keccak-256 Merkle membership: the prover's time, then the contract's gas.
# 2. leanVM by recursion, at 128 leanXMSS signatures: the prover's time from leanVM's execution trace to the recursive
#    proof and its openings, then the contract's gas. The trace is written once, by leanVM at commit 9d50c92a3 (the
#    Keccak VM) patched by crates/leanvm/univariate/src/prover/dump_keccak/apply.sh, and kept in $BENCH_DIR.
#
# BENCH_DIR (default target/bench) keeps leanVM's tree and the trace; LEANVM_REPO is where leanVM is fetched from;
# RUSTFLAGS defaults to -C target-cpu=native.
# The EIP draft's prover figures: `LEANVM_NUM_THREADS=8 taskset -c 0-7 sh bench.sh` on an AMD EPYC 9355P (8 physical
# cores), with RUSTFLAGS as AGENTS.md gives them for Zen 5.
set -eu

root=$(cd "$(dirname "$0")" && pwd)
work=${BENCH_DIR:-$root/target/bench}
repo=${LEANVM_REPO:-https://github.com/leanEthereum/leanMultisig}
commit=9d50c92a34aabb4df6b0c4502f056e1f07b26bab
export RUSTFLAGS="${RUSTFLAGS:--C target-cpu=native}"
cd "$root"

echo "== Membership: prover"
cargo bench -p quotient --bench membership

echo "== Membership: gas"
cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report

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

echo "== leanVM: prover (median of 5 passes)"
LEANVM_TRACE="$trace" PIPELINE_REPEAT=5 cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture

echo "== leanVM: gas, of the real 128-signature proof's calldata"
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture --test-threads 1 real_end_to_end
