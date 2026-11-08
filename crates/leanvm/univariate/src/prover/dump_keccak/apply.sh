#!/bin/sh
# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
# Makes a leanVM (https://github.com/leanEthereum/leanVM) tree at commit 9d50c92a3 (the Keccak VM,
# docs/leanvm/univariate/KECCAK.md) write its execution trace for the univariate prover: `sh apply.sh <leanVM tree>`.
# Then any proof leanVM starts with `LEANVM_TRACE_DUMP=<dir>` set runs the program again without its fill blocks,
# writes that run to <dir> (trace_dump.rs) and exits, e.g.
#   LEANVM_TRACE_DUMP=<dir>/xmss128 cargo leanvm aggregate --xmss 128 --log-inv-rate 1
# A tree to apply it to: git -C <leanVM checkout> archive 9d50c92a3 | tar -x -C <dir>
set -e
here=$(cd "$(dirname "$0")" && pwd)
cd "$1"
cp "$here/trace_dump.rs" crates/leanvm_core/src/cpu/trace_dump.rs
python3 - <<'PY'
p = 'crates/leanvm_core/src/cpu/mod.rs'
s = open(p).read()
assert 'mod trace_dump;' not in s, 'already applied'
s = s.replace("mod trace;\n", "mod trace;\nmod trace_dump;\n", 1)
anchor = '    let exec = crate::stage!("Execute program", || program.execute(public_input)).map_err(ProveError::Execution)?;\n'
assert anchor in s, 'not leanVM 9d50c92a3'
s = s.replace(anchor, "    trace_dump::maybe_dump(program, public_input);\n" + anchor, 1)
open(p, 'w').write(s)
PY
grep -n "trace_dump" crates/leanvm_core/src/cpu/mod.rs
