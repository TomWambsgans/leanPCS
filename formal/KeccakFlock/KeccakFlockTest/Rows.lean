-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock

/-!
# The block's rows against the Rust's walk

The vectors are `crates/leanvm_flock_gas/tests/lean_keccak_block.rs`'s output (`cargo test --release -p
leanvm_flock_gas --test lean_keccak_block -- --nocapture`): the verifier's walk `keccak_flock::row_values` on column
weights `w[p] = (r_p, 0, 0)`, `r_p` the `p`-th output of xorshift64 from `0x9e3779b97f4a7c15 ⊕ seed`. The walk only
adds, so limb 0 of each row value is the XOR of the `r_p` over the row's positions: 64 random GF(2) column vectors
at once, which determine the rows' 0/1 matrices up to a negligible chance. Per seed, the digest of limb 0 of `A w`
and of `B w` over the `2^17` rows and twelve sample rows; here `KeccakFlock.r1cs.rows` (the forward walk of the
specification's R1CS, the lists `row k` summed in `E`) recomputes them. Run with
`lake env lean ../KeccakFlock/KeccakFlockTest/Rows.lean` from `formal/EndToEnd`; a `#guard` fails on any difference.
-/

open LeanVM.Parameters LeanVM.Protocol KeccakFlock CompPoly

namespace KeccakFlockTest.Rows

/-- The Rust test's xorshift64 stream from `0x9e3779b97f4a7c15 ⊕ seed`, `2^17` outputs. -/
def weights (seed : UInt64) : Array UInt64 := Id.run do
  let mut x : UInt64 := 0x9e3779b97f4a7c15 ^^^ seed
  let mut a : Array UInt64 := Array.mkEmpty 131072
  for _ in [0:131072] do
    x := x ^^^ (x <<< 13)
    x := x ^^^ (x >>> 7)
    x := x ^^^ (x <<< 17)
    a := a.push x
  return a

/-- The column weights `(r_p, 0, 0)`. -/
def column (seed : UInt64) : CMlPolynomialEval E m :=
  let a := weights seed
  (Vector.ofFn fun p : Pos ↦ E.ofLimbs (K.ofLane a[p.val]!) 0 0 : Vector E (2 ^ m))

/-- Limb 0 of entry `k`, as a lane. -/
def limb0 (v : CMlPolynomialEval E m) (k : ℕ) : UInt64 :=
  if h : k < 2 ^ m then (v[(⟨k, h⟩ : Fin (2 ^ m))].limb 0).lane else 0

/-- The Rust test's digest of limb 0 over the rows. -/
def digest (v : CMlPolynomialEval E m) : UInt64 :=
  (List.range (2 ^ m)).foldl (fun h k ↦ h * 0x100000001b3 ^^^ limb0 v k) 0xcbf29ce484222325

/-- The walk's digests and sample rows against the Rust's. -/
def check (seed dl dr : UInt64) (samples : List (ℕ × UInt64 × UInt64)) : Bool :=
  let w := r1cs.rows (column seed)
  digest w.1 == dl && digest w.2 == dr && samples.all fun (k, a, b) ↦ limb0 w.1 k == a && limb0 w.2 k == b

#guard check 1 0x2b99263ade42b812 0xf4cc534f63942896
  [(64, 0x78efd6aa782dd3a3, 0x78efd6aa782dd3a3), (69, 0, 0), (1805, 0x57fb99c79521b425, 0x78efd6aa782dd3a3),
    (936, 0x0bc1ee8332a25d44, 0x78efd6aa782dd3a3), (6399, 0x55b7ffd67171915e, 0x78efd6aa782dd3a3),
    (6401, 0x78efd6aa782dd3a3, 0x78efd6aa782dd3a3), (7817, 0, 0), (8209, 0x802603a0612076bb, 0xb6fae9b60964bb26),
    (10243, 0x1ec4cf02ddbb707b, 0x78efd6aa782dd3a3), (103986, 0x2754df56d16ca3c1, 0x6886c3e651f3f031),
    (30466, 0, 0), (100000, 0, 0)]

#guard check 2 0x855d382c7a7db033 0x5dd260bbccd163af
  [(64, 0x16be2bc4c86f750e, 0x16be2bc4c86f750e), (69, 0, 0), (1805, 0x633080debd609c10, 0x16be2bc4c86f750e),
    (936, 0xab16199768c921a2, 0x16be2bc4c86f750e), (6399, 0x7421bedb1d92ab97, 0x16be2bc4c86f750e),
    (6401, 0x16be2bc4c86f750e, 0x16be2bc4c86f750e), (7817, 0, 0), (8209, 0xad9653d660622b43, 0xfc4f24410cd413cc),
    (10243, 0xbdc3153a276b032c, 0x16be2bc4c86f750e), (103986, 0x62996298e52bdba6, 0x7f3031d304c5e95f),
    (30466, 0, 0), (100000, 0, 0)]

#guard check 3 0xc9c0e2dc359f2254 0x81ceebbfa96271d2
  [(64, 0xb6a2f678d34f8dde, 0xb6a2f678d34f8dde), (69, 0, 0), (1805, 0xf79c7916f1627251, 0xb6a2f678d34f8dde),
    (936, 0xf2226bfe954c5713, 0xb6a2f678d34f8dde), (6399, 0x5df06d5a84cc63f2, 0xb6a2f678d34f8dde),
    (6401, 0xb6a2f678d34f8dde, 0xb6a2f678d34f8dde), (7817, 0, 0), (8209, 0xa098aab7e13de966, 0xef9a4b94912e28a1),
    (10243, 0x8aae22d163101cf0, 0xb6a2f678d34f8dde), (103986, 0x49d3f76c2474aa8b, 0xeb70b6569559f70e),
    (30466, 0, 0), (100000, 0, 0)]

-- A wrong digest is rejected: the check is not vacuous.
#guard !check 1 0x2b99263ade42b813 0xf4cc534f63942896 []

end KeccakFlockTest.Rows
