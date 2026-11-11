<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# A univariate PIOP for the Keccak VM, for the EVM

This is the protocol of `crates/leanvm/univariate` (`verifier::reduce`), as the code runs it. The VM, its workloads
and its capacity are in [`KECCAK.md`](KECCAK.md); Flock's part is in [`FLOCK.md`](FLOCK.md); the prover is in
[`PROVER.md`](PROVER.md), its measurements in [`docs/PERF_PROVER.md`](../../PERF_PROVER.md). Figures marked
*measured* come from revm runs of the contract compiled from the recorded Rust verifier (`tests/keccak_vm.rs`,
`tests/prove_real.rs`); *modelled* ones are computed here.

## 0. Summary

The statement is the Keccak VM's: leanVM 42422001's five instruction tables and leanVM `9d50c92a3`'s `SHA3` table as
the sixth (§1). The proof of it is not leanVM's:

- **Two proof commitments**, `C1` and `C2`, and one fixed setup commitment `F`. `C1` holds the tables' columns
  (univariate: coefficients on Cantor subspaces) and Flock's packed witness `q_flock` (values). `C2` comes after the
  bus challenges and Flock. It holds a **product heap** (the bus's grand product as a committed binary tree on Cantor
  cosets) and the quotients.
- **No GKR and no table sumcheck.** Every identity is a quotient identity checked at **one random point `t`**. The
  proof sends only the evaluations that occur in nonlinear terms (118 field elements), and every linear relation
  among evaluations is folded into claims.
- **The bus is a grand product** (exact multisets), not logUp. In characteristic 2, `Σ 1/(β + f)` only proves the
  multisets equal modulo 2 (§5.1).
- **The hash argument** is Flock on a Keccak-f[1600] block, one permutation a `SHA3` row, with a univariate skip of 3
  and the lincheck's terminal computed from the block's structure (§7).
- **Claims.** On the main line (`machine.rs`'s claim encoding, point claims), one batching sumcheck over the three
  stacks turns every commitment's relations into one point claim: 3 claims, declared as 3 (`C1`, `C2`, `F`). Extension
  W (weighted claims) drops that sumcheck.
- **Three Fiat–Shamir shapes** (§4): `KECCAK_MAIN` (π1's own contract), `KECCAK_REC3` (π1-rec3, the recursion's
  inner proof as the Lean states it) and `KECCAK_REC4` (π1-rec4, the deployed recursion's inner proof). The last two
  run the batch two variables a round and π1-rec4 draws several challenges from one Keccak-f (§14).
- **Result** at the reference workload (128 signatures), measured, π1 alone as a contract (`KECCAK_MAIN`): 8,065 B of
  calldata, 231,489 gas of execution; as an EIP-8141 frame transaction, standard 360,169, EIP-7976 floor 516,160,
  without its frame of claims (§10). Under the recursion π1 is not on chain: π2 verifies it
  (`docs/leanvm/rec/SPEC-REC.md`).

## 1. Statement and workload

leanVM 42422001's `crates/verifier` is ported, generic over the scalar, in `crates/leanvm/statement`, with the
`SHA3` table of leanVM `9d50c92a3` as its sixth table, opcode 5 (`layout::tables`). The statement: the VM, run on
the stacked bytecode (the fixed program) from `pc = 1, fp = 1`, halts at `pc = g^(2^lb - 1)`, `fp = 1`, `2^lb` the
bytecode's instructions. The 32-byte public input is in memory cells 0 and 1, and every `SHA3` row is one Keccak-f
step of leanVM `9d50c92a3`'s sponge. In Lean (`formal/KeccakVm`) this is `KvHolds`: `M3Holds` of the six tables
together with the Keccak-f region `KeccakAux`.

- **Fields.** `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^3 + y + 1)`, with `g = x` (`GEN`).
- **Tables.** XOR (15 columns), MUL (15), SET (8), DEREF (15), JUMP (14), and `SHA3` (86: 9 operands, 25 input and
  25 output lanes, 27 counts; 28 flush pairs). Also memory (3 limbs and a final count, `2^lm` cells), bytecode (a
  final count, `2^lb` instructions) and `q_flock` (Flock's packed witness, `2^11` K-words a `SHA3` row).
- **Bus** (leanVM's). Tuples have up to 16 coordinates, with fingerprint `β + Σ_s eq(α, s) τ_s` and `α ∈ E^4`.
  There are three channels: state, bytecode with counters, and memory with counters. The counters are powers of
  `g`. The push and pull multisets are equal, and every counter is nonzero. Framework blocks: the state boundary,
  the memory image (counts 1, final counts), the bytecode (counts 1, final counts). Padding rows push what they pull.
- **Constraints.** JUMP has two (`b + v_cond·w` and `v_cond·(b + 1)`), of degree 2. The other tables' rows are
  constrained by the bus only; the `SHA3` permutation is Flock's.

**Reference workload**: 128 leanXMSS signatures (`leanvm_statement::shapes::reference()`, `leanvm_rec::REFERENCE`).
Table rows XOR 24,260, MUL 36,229, SET 24,626, DEREF 35,812, JUMP 15,509, `SHA3` 17,712 (log-heights 15 16 15 16 14
15); memory `2^20`, bytecode `2^18` instructions. The other workloads (32, 400 and 1,000 signatures) are in
`leanvm_statement::shapes::WORKLOADS` and `KECCAK.md`.

## 2. Domain and encodings

- **Cantor basis** of `K`: `β_0 = 1`, `s(β_{k+1}) = β_k`, `s(x) = x^2 + x` (`src/domain.rs`, as
  `crates/membership/quotient/src/domain.rs`). Let `ω_i = Σ_k i_k β_k` and `V_r = {ω_i : i < 2^r}`. The digits are
  `w_0(x) = x`, `w_{k+1} = s(w_k)`. Then `w_r` is `V_r`'s subspace polynomial, `w_l(ω_i) = ω_{i >> l}`, and
  `w_m / w_r = Π_{j=r}^{m-1} (w_j + 1)`, a product with no division.
- **Basis `B`.** A column of `2^r` rows is the polynomial of degree `< 2^r` whose value at `ω_i` is row `i`. It is
  committed as its coefficients in `B_k = Π_l (w_l if k_l else 1 + w_l)`, a triangular transform of the novel basis
  (`B_k = Σ_{S ⊇ k} X_S`). Then **`f(t) = ĉ(w_0(t), …, w_{r-1}(t))`**: the multilinear claim's point is the digits
  themselves, with no inversion (the novel basis needs `w/(1+w)`).
- **Restriction to a coset.** For `F` of `2^m` coefficients and an aligned coset `o + V_r`, let
  `R(z) = Σ_k c_k Π_(l<r) b_(k_l)(w_l(z)) Π_(l≥r) b_(k_l)(w_l(o))`, `b_1(x) = x`, `b_0(x) = 1 + x`: the low factors
  of `B_k` at `z`, the high ones at `o` (§13, F6). It has degree `< 2^r` and agrees with `F` on the coset, and
  `R(o + t)` is one claim on `F` at the *mixed point* `(w_{<r}(t) + w_{<r}(o), w_{≥r}(o))` (each `w_l` is
  GF(2)-linear). This is how one heap serves every block's identity.
- **Composition with values.** `q_flock`'s words are committed as values. Let `y_l` be the linearised polynomials
  `Σ_{m<r} a_{l,m} x^{2^m}` with `y_l(ω_i) = i_l` (the inverse Moore system, `domain::coordinate_functionals`). Then
  `ℓ(x) = ṽ(y_0(x), …, y_{r-1}(x))` agrees with a word's column on `V_r` and has degree `≤ r 2^(r-1)`. `ℓ(t)` is one
  claim on the values at `y(t)`, for `r^2` products.
- **Vanishing polynomials of the active rows.** The active rows of a table are the fixed cosets of its row count's
  set bits (§13, F1b). `Z_act(t)` is a product of one factor a bit, computed from the count's bits
  (`domain::active_vanishing_from_bits`); the padding rows' `Z_pad = w_r / Z_act` is never computed.

## 3. Commitments

| commitment | when | content | words at 128 signatures (placed / stack) |
|---|---|---|---:|
| setup `F` | once | the bytecode's 16 tuple slots on `V_18` (slot 0 `SEP_BYTECODE`, slot 1 the pc `g^i`, slot 2 zero, then the instruction); the memory's addresses `g^i` on `V_20` | `2^22.32` / `2^23` |
| `C1` | first | `q_flock` (values, `2^11` words a `SHA3` row: `2^26`); every table column (basis `B`), `SHA3`'s 50 lanes among them; one counter-inverse column `z_T` per table; memory (4 columns, `V_20`); bytecode final count (`V_18`) | `2^26.21` / `2^27` |
| `C2` | after `α, β, γ` and Flock | the heap `T` (`2^22` E), `Q_tree`, one leaf quotient `Q_b` per heap block, the constraint quotient `Q_W`, each E-valued as three K-limb columns | `2^25.35` / `2^26` |

The setup commitment is a constant in the code (no `SLOAD`). The `C1` and `C2` commitments (root and out-of-domain
answer) are in calldata. Each commitment's relations end as **one** declared claim (the batching sumcheck, §8). That
is a choice of cost, not of binding: the out-of-domain answer binds each root to one table
([`docs/PCS_CLAIM.md`](../../PCS_CLAIM.md)), so claims on one commitment could be declared and proven apart.
`src/stacks.rs` gives each column an aligned block, largest first. A claim reads only its column's block. Nothing relies on the stack's unused words, nor on the zero padding of
a column shorter than its lane, which leanVM's `Layout::new` does not force (`PROVER.md`, "The stacks' unused
words").

**Sizes over the workloads**: the largest proof stack is `2^25` at 32 signatures, `2^27` at 128, `2^28` at 400 and
`2^30` at 1,000; `q_flock` alone is `2^(h_SHA3 + 11)` words, which bounds the workloads ([`KECCAK.md`](KECCAK.md),
"Capacity").

**Two additions to `C1`, both keeping the statement.** First, the `SHA3` table's 50 lane columns equal `q_flock`'s
port words of the row's block on every row (a constraint of `Q_W`, §6); the bus reads the columns. Second,
`z_T · Π_j c_j = 1` on every row (a constraint of `Q_W`) proves `CountsNonzero`. leanVM proves it by a third product,
of all counters. The alternative here is count leaves in the heap, which doubles the heap for no fewer values.

## 4. Transcript and challenges

**The public input in calldata** (§13, F7) is four big-endian 64-bit words `(cell0.c0, cell0.c1, cell1.c0,
cell1.c1)`, the K-limbs of memory cells 0 and 1. leanVM's statement reads its 32-byte digest as little-endian words
(`Digest::words`), so a caller passes each of the digest's four 8-byte words byte-reversed. Accepting the digest
unchanged would cost the contract a byte swap of the four words, about 110 gas (modelled), while the convention costs
nothing. It is documented here and in `contract.rs`.

The transcript is a Keccak-256 chain (`leanvm_statement::transcript::KeccakChannel`). A challenge is one Keccak-256
of the state and the calldata bytes read since the last one. A scalar is 24 bytes, a root half 16 (big-endian, so
that a root's 32 bytes are its bytes as they are, the root a PCS claim encodes, which the contract passes as it is). A
commitment is the EIP draft's (`crates/pcs_claim`, `docs/PCS_CLAIM.md`): its root, then its out-of-domain answer
`f(z)` (a scalar), `z` derived from the root alone, which binds the root to one polynomial before any challenge. The
seed is the Keccak-256 of the name `leanVM-univar-v1`, the contract's IV (§13, F2: it binds the program, the setup
commitment, the shape and the variant) and the public input. There are no announced sizes beyond the row counts: one
shape class per contract. The order:

1. The six row counts (§13, F1), then `C1`'s commitment (root, out-of-domain answer). Then `α ∈ E^4` (the tuple
   weights), `β` (the fingerprint shift) and `γ` (the batching of `C1`-only constraints).
2. Flock (§7): its rounds, challenges and values.
3. `C2`'s commitment, then `t`.
4. The values at `t` (§8).
5. `ρ`, which combines each commitment's relations.
6. On the main line: `λ`, which batches the three commitments, then the batching sumcheck's rounds and its three
   end values.

**The Fiat–Shamir shapes** (`flock_min::Variant::fs`). `KECCAK_MAIN` (`FsShape::Main`) draws every challenge by
its own hash. `KECCAK_REC3` (`FsShape::Rec3`, π1-rec3, the recursion's inner proof as the Lean states it) draws `α`
as `(c, c², c⁴, c⁸)` of one challenge and Flock's zerocheck coordinates after the seven fixed ones as successive
squares of one challenge (`docs/leanvm/rec/SPEC-REC.md` §1.4), and runs the batching sumcheck two variables a round
with narrow (160-bit) challenges (§14.1). At 128 signatures π1-rec3's verifier makes 70 Keccak-256 calls (116
Keccak-f) over a 9,280-byte stream. `KECCAK_REC4` (`FsShape::Rec4`, π1-rec4, the deployed recursion's inner proof)
is π1-rec3 with the challenges no message separates drawn from one Keccak-f each, and the ring map drawn after `C2`'s
commitment (§14.4): 60 calls, 106 Keccak-f at the reference shape. It has no EVM contract of its own (`KECCAK256`
gives no sponge rate); π2's circuit runs it, and the Lean does not state it. π1's contract IV binds the shape (§13,
F2), so a proof of one shape is not a proof of another.

## 5. The bus as a product heap

### 5.1 Why not logUp

`Σ 1/(β + f)` over a multiset, in characteristic 2, sees each tuple's multiplicity modulo 2. Take two accesses at
one address with the same count, both reading the same fake value. They pull `(A, v', c)` twice and push
`(A, v', g c)` twice, and both pairs cancel. So a program that reads a cell twice can be made to read anything.

A sound logUp exists, but it is not used. Tag every push with its public position, and every pull with a committed
pointer to the push it consumes. Then the push side is a set, `#push = #pull`, and equality modulo 2 forces exact
equality (pigeonhole). It adds a column per flush and leaves leanVM's tuples.

### 5.2 Heap

`T` is one polynomial on `V_H` (`H = 22` at 128 signatures). Position `i` holds node `i` of a binary heap, with
children `2i` and `2i + 1` and the root at `1` (`ω_1 = 1`). The leaves are `[2^(H-1), 2^H)`. Since
`s(ω_i) = ω_{i>>1}`, the tree is one identity:

**Tree.** `w_1(t) (T(s(t)) + T(t) T(t+1)) + w_H(t) Q_tree(t) = 0`, where `Q_tree = Q_0 + w_H q_1` (degree
`2^H`). Here `T(s(t))` is at the digits `(w_1, …, w_H)` and `T(t + 1)` at `(w_0 + 1, w_1, …)`.

**Leaves.** The aligned blocks of `src/heap.rs`, largest first:

| block | leaves | leaf | at 128 signatures |
|---|---:|---|---|
| memory | `2^lm` | `D_init / D_fin` of cell `i` | `2^20`, first |
| bytecode | `2^lb` | `D_init / D_fin` of instruction `i` | `2^18`, next |
| each table | its height | `Π_j D'_j / Π_j D_j` over its row's flushes | MUL, DEREF `2^16`; XOR, SET, `SHA3` `2^15`; JUMP `2^14` |
| unused | the rest, in aligned blocks (one per set bit of the gap) | 1 | `2^14` and `2^19` |

**Leaf identities**, each with its own quotient `Q_b`. The heap restricted to block `b` is `R_b`, read at the mixed
point (§2):

- table: `(R_b P_b + P'_b) Z_pad + (R_b + 1) Z_act = Q_b w_r`, checked times `Z_act` (§13, F1). On an active row
  `Z_act` vanishes and `Z_pad` does not, so the leaf is the ratio. On a padding row `Z_pad` vanishes and `Z_act` does
  not, so the leaf is 1, whatever the row holds. Padding rows are exempt from the bus: no constraint is placed on
  them, and none is needed.
- memory and bytecode: `R_b D_fin + D_init ≡ 0` mod `w_r`.
- unused: `R_u(o_u + t) = 1`. This is degree `< 2^r`, an identity of polynomials, with no quotient.

**Root.** `T(1) (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^lb - 1), 1)`: the pushes' product equals the
pulls', the state boundary included. `T(1)` is a claim at the digits `(1, 0, …, 0)`. Read it as
`T(1) · fp(init) = fp(fin)`, a product, not as a division.

**Zero fingerprints need no exclusion.** Every heap identity only multiplies: a leaf is `R P = P'`, not `R = P'/P`.
So the bus's soundness argument (Balanced, the Lean heap proof `formal/Heap`) needs no event "a pull fingerprint
vanishes".

**The `SHA3` leaves read the lane columns.** So the bus's soundness for `SHA3` needs `Q_W`'s copy identities (§6):
they tie the columns the leaves read to `q_flock`, which Flock checks.

**One quotient per identity.** With two proof commitments, nothing drawn after `C2` can batch the identities that
involve `C2`. A batch drawn before `C2` lets the prover trade errors between them: perturb two leaves at one point
and solve for the product.

### 5.3 Degrees

Each fingerprint is linear in the columns, except addresses `fp·o` and the products in MUL's result, DEREF's store
and JUMP's next state, which are degree 2. A table's leaf quotient is sized for its height's fewest rows,
`2^(r-1) + 1` (§13, F1), so `deg Q_b ≈ (Σ_j deg D_j) n + n/2`: XOR, MUL, DEREF and JUMP `≈ 8.5 n`, SET `≈ 4.5 n`,
`SHA3` `≈ 54.5 n` (28 flush pairs, the 26 memory accesses with a degree-2 address), memory and bytecode `≈ n`
(`verifier::reduce`, step 6).

## 6. The constraint quotient `Q_W` (`C1` only, batched by `γ`)

Each constraint lives on its table's domain and is lifted to `V_{r_W}` (`r_W` the largest height or `lm`, 20 at 128
signatures) by `w_{r_W} / w_r = Π (w_j + 1)`:

- JUMP's two constraints, on all rows;
- the counters: `z_T Π_j c_j + 1`, on every row (§13, F1);
- the public input: `(mem_k - I_k) Π_{j=1}^{r_W - 1} (w_j + 1)`, where `I_k` is the line through limb `k`'s two
  public values (leanVM's public lines);
- the lane copies: `copy_j - ℓ_j`, with `ℓ_j` the composition (§2) of `q_flock`'s port word for lane `j` at the
  row's block (11 slot bits; input lane `l` at the block's input port, output lane `l` at its output port,
  `layout::keccak_slot`), and `copy_j - ℓ_j - END_BIT` for `in_16` (`layout::keccak_slot_offset`, `KECCAK.md`).

`Σ_i γ^i M_i W_i = Q_W w_{r_W}`. Its degree is the largest of its terms': at the workloads the public input's
`2^lm - 3`; `SHA3`'s 27 counters give about `27 n`. Padding rows have no constraint but the counters': the leaf
identity exempts them (§5.2).

## 7. Flock on the Keccak-f block (details in `FLOCK.md`)

**Interface.** Flock runs after `C1` and before `C2`, reading only `C1`'s `q_flock`. It draws its own challenges in
the transcript between `γ` and the `C2` root. The verifier runs it as
`flock_min::verify_walked_with::<_, keccak_flock::Keccak>` at `log_n = 17 + h_SHA3` variables (32 at 128 signatures).

- **The block** is `flock::keccak`'s ([`FLOCK.md`](FLOCK.md), "The block"): one Keccak-f[1600] per `2^17` slots,
  every round's state materialised, `C = I`. Block `i` sits at row `i` of the placed `SHA3` table.
- **The zerocheck** has a univariate skip of `k = 3`: `2^3` coset values, then `log_n - 3` rounds of 2 scalars, then
  `v_a` and `v_b`. **The lincheck** has 11 rounds of 2 scalars (the block's slot bits after its 6 packing bits).
- **The slices** `s_i = ẑ(i, p)`, `i < 64`, are sent. The lincheck's terminal is checked on them by the block's
  structured terminal (`keccak_flock::structured_terminal`: eq factors, ρ and θ as cyclic shifts, the rounds' shared
  factor; 3,019 `E` operations at a skip of 3), which equals the walk of the block's matrices. No matrix is committed
  and none is opened.
- **The ring switch**: six map challenges, the target `Σ_i x^i Φ(s_i)` computed with the map's stages in tower order
  (§13, entries 2 and 3), and one claim `⟨Φ(eq(p, ·)), q_flock⟩ = target` on `C1`. On the main line its weight is one
  term (`RING_TWIST`), evaluated at the batch's point (§13, entries 2 and 11); in weighted mode it is 64
  Frobenius-twisted eq terms.
- **Scalars**: `2^k + 2 (log_n - k) + 2 + 22 + 64 = 2 log_n + 90` at `k = 3`: 154 at 128 signatures.

## 8. The final check: values, relations, claims

**Values sent at `t`** (118, 24 bytes each, the same at every workload). These are the minimum that keeps every
relation linear in what is not sent:

- per table: its pull fingerprints `D_j(t)` whose tuple has an unsent column, and push fingerprints that differ from
  their pull by an unsent column; its counters `c_j(t)` (45 in all, 27 of them `SHA3`'s); and one factor of each
  product (`fp`, `pc`; MUL `va_k`, DEREF `f_pc, f_fp, ptr`, JUMP `b, v_cond`: `verifier::factor_columns`);
- memory: `D_fin(t)`, `c_fin(t)` and the address `addr(t)` (on `F`); bytecode: `D_fin(t)` and `c_fin(t)`;
- `C2`: `T(t)` (a factor of the tree identity) and `Q_W(t)` (so that `Q_W`'s relation is on `C1` alone).

A push fingerprint the sent values give is derived (`D'_j = D_j + eq(α, 2)(g + 1) c_j` for a counted flush).

**Linear relations.** Each is `Σ coefficient · evaluation = value`, with the values above among the coefficients.

- On `C1`: every sent column value; every sent fingerprint, as its tuple's columns at `t`; `Q_W`'s identity, with
  its `z_T`, JUMP `w`, lane copy, public-input and composition terms; Flock's ring-switch claim on `q_flock`.
- On `C2`: the tree (four terms), the root, each block's leaf identity (the heap at the mixed point and the quotient's
  chunks), the unused blocks, `T(t)` and `Q_W(t)`.
- On `F`: `addr(t)`, and the bytecode's fingerprint as **one** point, `(α, w_{<lb}(t))`, on the 16-slot block.

Each commitment's relations are combined by the powers of `ρ` (`Relations::combine`).

**Claims, main line: the claims' encoding** (`crates/evm_link/src/machine.rs`: point claims, `c` each). A batching
sumcheck takes `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack (27 variables at 128 signatures), the
others zero-extended. With `KECCAK_MAIN` it has two scalars a round; with `KECCAK_REC3` and `KECCAK_REC4` it runs
two variables a round (`transcript::sumcheck_pairs_drawn`, §14.1). Then come the three stacks' values at its point `r`. The verifier
evaluates every `W_k(r)` (`verifier::weight_at`): columns at one row point share their eq factor, selector factors
share their high bits, Frobenius twists are cached (`stacks::EqCache`), `q_flock`'s slot terms share the eq of their
instance coordinates, and the ring-switch term is evaluated by its map (§7). The result is one point claim per
commitment: 3 claims, declared as 3.

**What the contract itself checks.** The verifier is linearised: every relation it states is a claim it checks
declared. The checks it makes itself are the row counts' range (§13, F1), Flock's lincheck terminal and, in point
mode, the batching sumcheck's terminal; each is affine in the last scalar read before it. So with the openings
mocked, a stream solved for those scalars is accepted at any challenges (`tests/lean_keccak_vectors.rs` builds such
streams); that is expected, not a bug. The verdict means something only together with the openings.

**Extension W: weighted claims** (`Claims::Weighted`). A claim is `root, layout, k`, then per claim its points (each a
column's low coordinates), its terms (`column | point << 32 | twist << 48`, then the coefficient) and its value. The
block's opening evaluates the weight, as leanVM's own WHIR verifier does. No batching sumcheck. Price `c` a claim; the
opening's work grows with the terms. It is kept because the Lean vectors cover it (`tests/lean_keccak_vectors.rs`)
and the parity tests run it; the prover has no opening for it.

## 9. Soundness

Modelled round by round by `params/leanvm_univariate_params.py` (`python3 -I`), at every workload; proved in Lean at
the reference shape (below).

Each challenge's error is a Schwartz–Zippel bound times the number of committed tables it is drawn against: `L_1`
before `C2` and `L_1 L_2` after it, `L` the certified level-0 Johnson list of a stack's WHIR commitment (leanerVM's
`WhirBridge`, rate 1/2: 4,473 at `C1`'s `2^27` stack, 6,296 at `C2`'s `2^26`). The setup is honestly computed, and an
honest codeword's list within the Johnson radius is itself, so `L = 1` there. Stacks below `2^24` words have no
certified level-0 list. `|E| = 2^192`. The rounds at 128 signatures, as the code states them (§13, F8: committed
capacities, the unused blocks, degree 4 a tuple, `ρ`, `λ` and each round of the batch apart), in bits after the lists:

| round | error | main line | π1-rec3 | π1-rec4 |
|---|---|---:|---:|---:|
| bus `(α, β)`: if the push and pull multisets differ, `Π(β + fp)` differs: one Schwartz–Zippel over `E^5`, degree 4 a factor (π1-rec3/4, `α = (c, c², c⁴, c⁸)`: 16 in `(β, c)`), every table full (the counts are the prover's), `N = 2^21.62` tuples a side | `4N/|E|` (`16N/|E|`) | 156.3 | 154.3 | 154.1 (one query with `γ` and the zerocheck's point, their errors summed) |
| `γ`: the 61 `C1`-only constraints batched | `60/|E|` | 174.0 | 174.0 | in `α`'s query |
| Flock's zerocheck point: its 22 drawn coordinates (π1-rec3/4: the successive squares of one) | `22/|E|` (`(2^22 − 1)/|E|`) | 175.4 | 157.9 | in `α`'s query |
| Flock's other rounds: the skip (`(2^(k+1) − 1)/|E|`), 29 zerocheck rounds of degree 3, the lincheck's `α` (3) and 11 rounds of degree 2, the ring map in tower order (`6/|E|`) | at most `15/|E|` each | ≥ 176.0 | ≥ 176.0 | ≥ 176.0 (the map in `t`'s and `ρ`'s queries) |
| `t`: every identity at its committed capacity: the tree (`2^23`), the leaves times `Z_act` (memory `2^21`, `SHA3` `1.9M`, …), `Q_W` (`2^21`), the unused blocks; `Σ deg = 17,653,749 ≈ 2^24.07` | `Σ deg/|E|` (π1-rec4: + the map's `6/|E|`) | **143.2** | 143.2 | 143.2 |
| `ρ`: `C1`'s 116 relations combined (`C2` 14, `F` 2) | `115/|E|` (π1-rec4: + `λ`'s 2 + the map's 6) | 160.4 | 160.4 | 160.3 |
| `λ`: 3 claims | `2/|E|` | 166.3 | 166.3 | in `ρ`'s query |
| the batch: 27 rounds of degree 2 (π1-rec3/4: 13 pairs of degree 8 and one plain round, narrow challenges) | `2/|E|` each (`8/2^160`, `2/2^160`) | 166.3 | **132.3** | **132.3** |

The weakest round is `t` on the main line and the narrow pairs at π1-rec3 and π1-rec4 (§14.5 says why π1-rec4's
merged queries are charged their summed errors). At 32 and 400 signatures the main line's `t` keeps 143.3 and 142.5
bits; π1-rec3's and π1-rec4's pairs 131.1 and 133.4.

**Fiat–Shamir and the PCS (§13, F3).** WHIR is leanVM's, unchanged. In the query-bounded random-permutation model of
the end theorems an adversary of `Q` permutation queries breaks π1 with probability about `Q (ε_WHIR + ε_round)`,
`ε_round` the weakest round after its lists: the openings' Fiat–Shamir transcripts are domain-separated (each seeded
by its own PCS claim, `keccak256(PCS_claim)`) and share the adversary's queries, so the three openings (`C1`, `C2`, `F`) are
charged once, at `WhirBridge`'s exact certified bound `269 · 2^-137 = 2^-128.93` a query (the setup's `2^23` stack is
certified too). That is **128.93 bits** as `Q/ε` on the main line and **128.79** at π1-rec3 and π1-rec4
(`Q = 2^64`); 128.64 and 128.86 at their 32 and 400 signatures. The setup's `F` cannot join a proof commitment
without losing its `L = 1`. Under the recursion π1-rec4's bound enters the recursion's (127.86 bits,
`docs/leanvm/rec/SPEC-REC.md` §5).

**Lean.** `formal/UniKeccakSound` proves knowledge soundness of both variants at the reference shape, in one random
permutation and with an explicit extractor: **128.87 bits** (main line) and **128.49** (π1-rec3) as `Q/ε` at
`Q ≤ 2^64` (`uniBound128`); completeness is `formal/UniKeccakComplete`'s (`δ < 2^-169`). The calculator reproduces
`uniBound128` from its terms, and the gap to its own figures is the Lean's coarser rounds: it caps every round's error
before the lists at one bound, `2^32/|E|` on the main line (the largest is `t`'s `2^24.07/|E|`) and `2^35/|E|` at
π1-rec3 (its narrow pairs' `8/2^160`, exactly), and multiplies every round, those before `C2` included, by the largest
certified list squared, `9,952² ≈ 2^26.6` (against `4,473 · 6,296 ≈ 2^24.7`). WHIR's `2^-128.93` a query is the same
in both; the rounds cost the Lean 0.06 bits (main line) and 0.44 (π1-rec3), the calculator 0.00 and 0.14. The Lean
does not state π1-rec4; its uniform cap holds for π1-rec4's summed queries too (the largest is the batch's pairs,
`2^35/|E|`; `α`'s query sums to below `2^26/|E|`), so the 128.49 bits carry over once it is stated
([`docs/LEAN_PORT.md`](../../LEAN_PORT.md)).

## 10. Gas

Measured on revm (`tests/keccak_vm.rs`, `keccak_gas_report`, which prints every workload and the phases at 128
and 400 signatures), `KECCAK_MAIN`, point claims, π1 alone as a contract at 128 signatures: **8,065 B** of calldata,
**231,489** execution, 3 claims. As an EIP-8141 frame transaction (without the 21,000 base, `FRAME_TX_INTRINSIC_COST`
and the per-frame costs, and without its frame of claims and the PCS gas): standard (`16` a nonzero byte, `4` a zero
byte, plus execution) 360,169; EIP-7976's floor (`64` a byte) **516,160**, which binds.

**Calldata at 128 signatures** (no selector: the length and the value alone are checked): public input 32 B, row counts 24 B, `C1`'s and `C2`'s commitments
(root and out-of-domain answer) 112 B, Flock's 154 scalars 3,696 B, the 118 values at `t` 2,832 B, the batching
sumcheck (27 rounds of 2 scalars, 3 values) 1,368 B, the frame's index 1 B. The design is almost size-independent:
the values at `t` are fixed, and Flock's rounds and the batch grow only with the logarithms of the sizes. The gas is a
function of the shape: the real proofs run at the gas a sample stream of their shape gives (`tests/evm_vectors.rs`
replays them at their recorded gas). The recursion's contract is π2's (`docs/leanvm/rec/SPEC-REC.md` §6).

## 11. Prover

[`PROVER.md`](PROVER.md) describes the prover (`src/prover/`) phase by phase;
[`docs/PERF_PROVER.md`](../../PERF_PROVER.md) has its measurements.

## 12. Risks and open questions

1. **Capacity.** `C1` exceeds WHIR's `2^28` words past the workloads [`KECCAK.md`](KECCAK.md) ("Capacity") gives.
2. **The main line pays for faithfulness in execution.**
   - The point ABI forces a batching sumcheck, whose weight carries the ring switch's 64 Frobenius-twisted eq terms:
     the cost leanVM's verifier pays at WHIR's terminal point. Extension W moves it to the block's openings.
   - Execution binds on the main line, so `c` shows at once (+3c).
3. **Extension W changes what the block proves.** Its price per claim should grow with the terms, which the table
   does not charge.
4. **Faithfulness deltas** (the statement is the same):
   - `CountsNonzero` by inverse columns `z_T` instead of leanVM's count product;
   - the `SHA3` lanes committed twice, with `copy = ℓ(q_flock)` (and `END_BIT` on `in_16`) in `Q_W`;
   - padding rows unconstrained (the leaf identity forces their leaves to 1): the extracted witness is `C1` as
     committed, with the lanes read from `q_flock` (§13, F6);
   - the bus as a committed heap instead of a GKR;
   - the hash argument on a Keccak-f block of one permutation per `2^17` slots, not leanVM `9d50c92a3`'s block of
     three ([`KECCAK.md`](KECCAK.md), "The statement");
   - one shape class per contract.

   `Balanced` (a `List.Perm`) follows from the heap's root as leanVM's GKR root gives it.
5. **The soundness calculator** (§9) is an analysis, not a proof: it reads the degrees off the code, at every
   workload. The proof is the Lean's (§9), at the reference shape only, with a coarser bound.
6. **The gas is a function of the shape.** The code is straight-line with fixed-cost opcodes, so a valid proof costs
   what a sample stream of its length costs; the real proofs confirm it.
   - Each measuring build jumps over failed checks: one `JUMPDEST` a check and a call, subtracted.
   - The contract equals the Rust verifier word for word, straight and deployed
     (`keccak_contract_is_the_rust_verifier`; `prove_real`'s parity on real proofs).

## 13. Refinements of the design

The design's refinements, by the labels the code cites. Each entry states the rule as built.

1. **From the Lean heap proof** (`formal/Heap`):
   - §5.2 and §6: padding rows are exempt in the leaf identity `(R P + P') Z_pad + (R + 1) Z_act = Q w_r`; there is
     no `padRow` constraint.
   - §5: the root is `T(1) · fp(init) = fp(fin)`, a product; zero fingerprints need no exclusion, since every heap
     identity only multiplies.
   - §5.2: `HeapLayout::new` can leave several unused blocks.
   - §9: the bus error is `4N/|E|` (one Schwartz–Zippel over `E^5`, degree 4 a factor).
   - §5.2: the hash table's leaves read its copy columns, so the bus's soundness needs `Q_W`'s copy identities.

2. **Lever 1a: the ring map in tower order** (`leanvm_statement::ring_tower`). The map's six stages are applied
   shift 1 first, 32 last (leanVM: 32 first). The outermost stage is then `GF(2^32)`-linear, the next
   `GF(2^16)`-linear, and so on, so the target `Σ_i x^i Φ(s_i)` is computed through `K`'s subfields: 64 sums of
   slices (the coordinates of `x^i` in a tower basis, 1,938 slice terms), then six levels with `6 · 64` squarings and
   `3 · 63` products, against `64 · 63` squarings. On the main line the ring-switch term is one term of `C1`'s
   relations (`RING_TWIST`), whose weight at the batch's point is computed from the inside out (the 64 twisted eq
   products, then 63 products and the chains `f_j^(2^k)`; no coefficients `d_k`). Each eq factor is
   `(1 + r_k) + p_k`, with `1 + r_k` shared. The map's error is at most `6/|E|` (leanVM's order: `2^31/|E|` by
   Schwartz–Zippel): a node of the tower is `(A + θB) + f_j(A^q + θB^q)`, which vanishes for at most one `f_j` unless
   both children do. Prover: `Φ(a)` applies `a ← a + f_j a^(2^(2^j))` for `j = 0..5`, and the weight is
   `Φ(eq(p, u))` with that `Φ`.

3. **Lever 1b: the tower's leaves as an `XOR` network** (Paar's greedy common subexpressions, `ring_tower::Tower`):
   1,938 slice terms become 767 `XOR`s (251 shared).

4. **Lever 1c: the batch's weights share their work** (`verifier::weight_at`): a column's limbs share its row
   (`Σ_limb basis · selector` once per column), terms on one row add `coefficient · part` before the row multiplies
   them, and `q_flock`'s slot terms share the eq of their instance coordinates (only their 11 slot bits' factors
   differ).

5. **Lever 4a** (a matrices' reduction run inside the batching sumcheck) is not needed: it reduces a lincheck
   terminal to claims on committed matrices, and the Keccak-f block's terminal is computed from its structure in
   Flock (§7). No matrix is committed, and the batching sumcheck is the stacks' alone.

6. **F1: the row counts are announced.** The contract is built for the heights (one contract per shape class:
   heights, `log_memory`, `log_bytecode`), not for the row counts. The stream starts with the six tables' row counts,
   32-bit big-endian integers (24 bytes, `Channel::next_integer`), before `C1`'s root, in table order XOR, MUL, SET,
   DEREF, JUMP, `SHA3`; the first challenge's hash absorbs them with the root. The contract requires each count
   `c ≤ 2^r` (`c >> (r+1) = 0`, and `c`'s low `r` bits zero if bit `r` is set) and computes `Z_act(t)` from its bits
   (entry 10). `Z_pad` is not computed:
   - the leaf identity is checked times `Z_act(t)`: `R (P w_r + Z_act²) + Q w_r Z_act = P' w_r + Z_act²` (since
     `Z_pad Z_act = w_r`), a polynomial identity of degree `deg + 2^r`;
   - the counters' constraint `z_T Π_j c_j = 1` holds on **every** row, padding rows included (they are free, so the
     prover sets their counters nonzero).
   Each leaf quotient is sized for its height's fewest rows, `2^(r-1) + 1` (`Shape::least_rows`); with fewer rows an
   honest quotient does not fit (a smaller shape class), and soundness does not depend on it. Prover: write the six
   counts before `C1`'s root; set padding rows' counters to 1 and `z_T = (Π_j c_j)^(-1)` on every row.

7. **F5: small shapes.** Every quotient degree is `verifier::degree(plus, minus)`, saturating, so no height wraps.
   `Shape::validate` rejects only a memory of one cell, a height of 32 or more, and a `SHA3` height below 7 (Flock's
   seven fixed zerocheck coordinates; `VerifierError::InvalidShape`).

8. **F2: the IV, the setup commitment, the claims.**
   - `contract::SetupRoots`: the commitment the IV binds is a code constant, the setup commitment `F`'s root and
     out-of-domain answer (from the program and the shape, `prover::setup::shape_roots`; `REFERENCE` is the
     128-signature shape's, root `067244be…`). The gas reports use `REFERENCE` for every shape (the gas does not depend
     on it); a deployment for another shape takes its own `F`.
   - Each claim is the EIP draft's PCS claim (`crates/pcs_claim`): the stack in its `vars` variables (its `2^vars`
     words, the zero tail past its blocks included: the claim is a point of the whole stack, as the batching sumcheck
     leaves it, §8), committed as `(root, ood)`, at the batch's point, of the value the prover sends; its encoding
     `version || n || root || ood || point || value` hashed is a payload of the transaction's frame of PCS claims
     (`evm_link::declared_claims`). No layout word: a verifier knows the stack's size from `n`, and the commitment of
     a stack's leading lanes is the whole stack's (`pcs_claim::commit_words`).
   - The openings (`prover::opening`, `crates/pcs_claim`): one a claim, the PCS version 1's: leanVM's WHIR at rate
     `1/2` on its ladder (`pcs::whir::DEPLOYED_SCHEDULE`), its transcript seeded by `keccak256(PCS_claim)`, proving
     `f(z) = ood` and `f(point) = value` at one random combination.
   - `verifier::layouts(shape)` is public (and `Reduced::layouts`): the stacks depend on the shape alone.
   - The contract's IV is `keccak("leanVM-univar-iv" ‖ program IV ‖ F's root ‖ F's out-of-domain answer ‖ shape bytes
     ‖ variant bytes)` (`contract::contract_iv`; the variant bytes are `"keccak-vm"`, the skip and the Fiat–Shamir
     shape's code); the seed is `keccak(name ‖ IV ‖ public input)`. It costs no gas.
   - Prover: seed the transcript with `contract_iv(shape, variant, program IV, roots)`; send each commitment's root
     and out-of-domain answer; open each claim.

9. **F3, F6, F7, F8** (documentation):
   - F3: §9's PCS figure (the three openings charged once at `269 · 2^-137` a query, in the query-bounded model);
     proof stacks below `2^24` have no certified list.
   - F6: §2's restriction formula takes the high factors only (`B_(k - k mod 2^r)(o)` would add the constant
     `Π_(l<r)(1 + w_l(o))`); §12: the extracted witness is `C1` as committed.
   - F7: §4 and `contract.rs`: the public input's word order.
   - F8: §9 counts committed capacities, the unused blocks, degree 4 a tuple, and `ρ` and `λ` apart.

10. **F1b: the active rows at fixed cosets** (`domain::active_positions`, `is_active`,
    `active_vanishing_from_bits`). A count's bit `b < r` owns the rows `[2^r - 2^(b+1), 2^r - 2^b)` (an aligned coset
    with a constant offset `ω_(2^(r-b) - 2)`), bit `r` (a full table) all of `V_r`; the active rows are the cosets of
    the count's set bits, the highest first. So `Z_act(t) = Π_(b<r) (1 + c_b (w_b + K_b + 1)) · (1 + c_r (w_r + 1))`:
    one product and one selection a bit, the factors shared by the tables of one height. A count above `2^(r-1)`
    starts with the prefix `[0, 2^(r-1))`; the last row `2^r - 1` is active only in a full table. The rows' order is
    not part of the statement (the bus is a multiset; padding rows are free). Prover: place table `T`'s `c` active
    rows, in order, at `active_positions(c, r)`, padding rows everywhere else (`Trace::place`); the `SHA3` rows'
    Flock blocks are built after placement, block `i` at row `i`.

11. **Lever 3a: the ring weight as hand-scheduled code** (`leanvm_statement::evm::kernel`, `Scalar::ring_weight`).
    The generic compilation spends about 47 gas a twisted factor: the chain value `p_n^(2^k)` and `a_n` go to memory
    and back. The kernel keeps a block of 13 twists' products on the stack, the coordinates inner, so a coordinate's
    chain value and `a_n` stay on top for the block's squarings and factors, each factor multiplied into its product
    in place (`DUP`, `FIELD_MUL`, `SWAP`, `POP`): about 40 gas a factor, and half the code bytes. It uses the memory
    below the slots (the hashing's scratch, free between nodes). The parity tests check it word for word against the
    Rust (`ring_tower::weight_at`). The report's `FIELD_MUL` count is the graph's, without the kernel's.

12. **Lever 5a** (extension B, a bit-slice claim type on the ABI) is not built: no claim of the Keccak VM's π1 is on
    bit slices. A declared claim holds point claims, or weighted claims under extension W.

13. **The Lean transcription's findings** (documentation):
    - `weight_at` keys `q_flock`'s slot rows by their point (entry 4), not by the slot;
    - `Relations::combine` merges the 0-variable `TreeQuotient(1)` term into the first longest `C2` point: harmless
      (documented in `claims.rs`);
    - `flock_min`'s `log_n ≥ 17 + 7` is `Shape::validate`'s `SHA3` height of at least 7 (entry 7);
    - §8: what the contract checks itself, and why solved streams pass with mocked openings.

14. **Lever 1c: narrow batch challenges** (`FsShape::Rec2`'s, kept by `Rec3` and `Rec4`; `Channel::sample_narrow`,
    `transcript::NARROW_BITS`). The batching sumcheck's challenges are the hash's low 160 bits instead of 192 (limb 2
    below `2^32`). π1's verifier draws them with `sumcheck_pairs_drawn(.., narrow)`, its prover likewise, the recorder
    as `record::Node::Narrow` (an `AND` with 20 bytes of ones), π2's circuit packs limb 2 from 32 digest bits. A plain
    round of degree 2 errs with probability `2/2^160`, a pair `8/2^160`. They were made for a contract that carried
    π1's point in calldata (four zero bytes a coordinate); π2's circuit now hashes π1's claims, and the shape stays.

15. **Lever 1d: the paired batch** (π1-rec3, kept by π1-rec4; `FsShape::Rec3`): the batching sumcheck two variables a
    round on `V_2`'s coordinate functionals, one narrow challenge a pair: §14.1–§14.3.

16. **Lever 1a′: no claims on Flock's matrices.** The Keccak VM's π1 has none: its lincheck terminal is the structured
    one (`keccak_flock::structured_terminal`), computed by π1's verifier, so its claims are three (`C1`, `C2`, `F`),
    all at the batch's point.

17. **π1-rec4: the wide draws** (`FsShape::Rec4`): the challenges no message separates drawn from one Keccak-f, the
    ring map after `C2`'s commitment, 106 Keccak-f instead of 116: §14.4 and §14.5.

### The floor

The main line is execution-bound. Its largest part is the ring switch's weight at the batch's point: it needs the 64
conjugates of each of the coordinates of Flock's point (26 at 128 signatures: 1,638 squarings) and 64 products of
that many factors (1,664 products), whatever the map's coefficients, because a `K`-packed word's bits need all 64
Frobenius conjugates and the batch's point is random in `E`. The next is Flock's structured terminal (about 42K at
400 signatures). `keccak_gas_report` prints every phase at 128 and 400 signatures.

**Measured vs modelled.** Every gas and calldata figure is measured on revm (the measuring build's checks
subtracted). Modelled: the public input's byte swap (about 110 gas, not built). The soundness figures are §9's.

### Dropped levers

- The lincheck merged into the batch: circular (its point is the ring switch's, an input of the batch).
- Fewer coefficients a round: the batch's weight is a sum over many points, with no common eq factor to split off.
- A smaller skip (`k` 3 → 0–2): 2 scalars at most, and the prover's skip kernels start at 3
  (`flock::zerocheck::skip::MIN_SKIP`).
- Another tower basis for the target's `XOR` network: 400 random bases, the best 755 `XOR`s against 767.
- The public input in leanVM's byte order: about 110 gas; documented instead (F7).
- A looped ring-weight kernel: a loop costs about 30 gas an iteration.
- 32-bit packing of `q_flock` (32 twists instead of 64): not leanVM's witness, and `C1` would double.

## 14. The recursion's Fiat–Shamir shapes: the paired batch and the wide draws

π2's circuit runs π1's verifier (`docs/leanvm/rec/SPEC-REC.md`), so π1's transcript is what π2 pays for: a Keccak-f
is 130,944 of π2's `2^24` positions (SPEC-REC.md §2.4.1). π1-rec3 and π1-rec4 shape the transcript for π2 and keep
π1's stream, statement, relations and claims. π1-rec3 is `FsShape::Rec3`: the derived runs of `Rec` (`α` and Flock's
zerocheck point as successive squares, SPEC-REC.md §1.4), the narrow batch challenges of `Rec2` (§13, entry 14) and
the paired batch (§14.1). π1-rec4 is `FsShape::Rec4`: π1-rec3 with the wide draws (§14.4).

```sh
cargo test --release -p leanvm_statement --lib transcript -- --nocapture
cargo test --release -p leanvm_univariate --lib domain
```

### 14.1 The paired batch

π1's three claims (`C1`, `C2`, `F`) are at the batching sumcheck's point `r`, whose coordinates are the largest stack's
variables (27 at 128 signatures, 28 at 400). The batch runs two variables a round, so `r` is generated by 14
challenges instead of 27 (`transcript::{sumcheck_pairs, sumcheck_pairs_drawn, pair_point, cantor_beta1}`; π1's
verifier calls it in `verifier::batch`, its prover is `prover::batch::prove_pairs`).

- **The rounds** (`transcript::sumcheck_pairs`). A pair is `(u_(2j), u_(2j+1))`, low variables first. Its polynomial
  is `G_j(X) = Σ_rest Σ_k λ^k W_k(·) C_k(·)`, read at `(r_(<2j), y_0(X), y_1(X), rest)`. It has degree 8.
  - `V_2 = {0, 1, β_1, 1 + β_1}` is `GF(4)` (`β_1² + β_1 = 1`). So `Σ_(x ∈ V_2) x^e` is 1 for `e ∈ {3, 6}` and 0 for
    every other `e ≤ 8`.
  - The stream holds `c_0, c_1, c_2, c_4, …, c_8`, and `c_3 = claim + c_6`.
  - One challenge `z_j` gives `r_(2j) = y_0(z_j) = z_j + β_1 y_1` and `r_(2j+1) = y_1(z_j) = z_j² + z_j`.
  - 27 variables are 13 pairs, then one plain round, with `r_26 = z_13`; 28 variables are 14 pairs.
  - Every challenge is narrow, 160 bits (`Channel::sample_narrow`).
- **What stays.** The weights `W_k(r)`, the three values, and the claims at `r`'s prefixes. Only the rounds and their
  challenges change.
- **π2.** A pair's two call words are `y_0`, `y_1` of a port, not ports themselves (`CallWord::Pair`,
  `circuit::compile::pair_coordinate`); the map `z ↦ (y_0(z), y_1(z))` is injective (`y_0 + β_1 y_1 = z`), so
  binding the `z_j` binds `r`. `public_from_calls` recovers `z` and checks both coordinates; π2's verifier computes
  `pair_point` of its public scalars (`Reduced::pair_points`).
- **The prover** (`prover::batch::prove_pairs`). A pair round takes nine sums `Σ W(a, b, ·) C(a, b, ·)`,
  `a, b ∈ {0, 1, ∞}`, for each piece of the weights and each group of four words: the coefficients of `G̃`, and then
  `G = G̃(y_0, y_1)`. As built it reuses `Weight::round` and `Weight::fold`: each pair binds its low variable at 0, 1
  and `β_1` on clones of the weights (`Weight` and `Folded` are `Clone`), then takes one round on the high variable;
  four passes a pair instead of two (a two-variable kernel in `weight.rs` would read the stacks once a pair). `G̃`'s
  coefficients in `u_0` come by interpolation (`β_1² + β_1 = 1`: no inversion); each pair is checked against the
  claim (`c_3 + c_6`). A stack shorter than the batch with an odd number of variables zero-extends itself past its
  words' rounds. No extra memory, no new commitment.
- **Tested** (`leanvm_statement` `transcript::tests`, `leanvm_univariate` `domain::tests`): the paired sumcheck is
  complete on honest product sums of 1, 2 and 3 tables, at odd and even variable counts; a wrong claim, and each
  flipped scalar, ends on a claim the tables do not give; `pair_point` is `V_2`'s coordinate functionals, and
  `cantor_beta1` is `domain::beta()[1]`; recorded over 27 variables at degree 2: 27 Keccak-f either way, 14
  challenges against 27, and 278 `E` operations against 135. End to end, the real π1-rec3 and π1-rec4 proofs are
  accepted by π1's Rust verifier (and π1-rec3's by its contract) and by the recursion's contract through π2.

The pairs were made when the recursion's contract carried π1's point in calldata (14 challenges and 3 values, 408 B
against 720 B; [`docs/HISTORY.md`](../../HISTORY.md)). π2's circuit now hashes π1's claims, so the point is not in
calldata; the paired batch stays as π1-rec3's and π1-rec4's batch, at no Keccak-f more than plain rounds (§14.3).

### 14.2 Why the batch's point stays

`C1` carries Flock's ring switch (§7), one of `C1`'s relations:
`Σ_u Φ(eq(P, u)) q_flock(u) = target`, with `Φ(eq(P, ·)) = Σ_(k<64) c_k eq(P^(2^k), ·)` and `P` challenges of Flock's
rounds. A declared claim holds point claims (`E`-linear evaluations), and the 64 values `q̂(P^(2^k))` are unknown
(sending them would make 64 claims). So the claim is reduced by a sumcheck over `q_flock`'s variables, as Binius's ring
switch ends, and a sumcheck's challenges must be drawn after its rounds' messages. That sumcheck is the batch, whose
point every other relation shares at no extra coordinate. The alternatives give the coordinates back as claim values,
at least as many:

- **DEEP** could fold the univariate relations (columns at `t`, `t + 1`, `s(t)`; `Q_W`'s copies at `y(t)`; `F`'s point
  `(α, w(t))`) into one quotient in a new commitment, one point claim a height group. It saves no coordinate (the batch
  stays for `q_flock`); it needs every column's value at every point (about 90 more values, 2.1 KB of π1's stream,
  about 16 Keccak-f in π2, modelled); it costs a commitment, whose list joins the union bound, and a claim a height
  group. The heap's restrictions are multilinear claims at mixed points (§2), not univariate evaluations of `T`.
- **Gemini** in characteristic 2 (`F_(j+1)(s(x)) = F_j(x) + (x + r_j)(F_j(x) + F_j(x + 1))`) commits `F_1, …` and
  needs each `F_j` at `w_j(z)` and `w_j(z) + 1`: about two values on chain for each coordinate saved.
- **Zeromorph** (`q(x) − v = Σ_l (w_l(x) + r_l) Q_l(w_(l+1)(x))` in basis `B`) merges the `Q_l` through KZG's
  homomorphism, which WHIR's roots lack; one stack can hold every `Q_l`, but the weights `w_l(z) + r_l` carry `r`, so
  each `Q_l(w_(l+1)(z))` is its own claim.
- **The univariate sumcheck** over `q_flock`'s values needs an `E`-valued quotient of `2^n` points (a new commitment)
  and `E_r(z)`, a sum of `2^n` terms, for π2 to evaluate.

### 14.3 The challenges per round

A round of `k` variables on `V_k`'s coordinate functionals (`y_l(ω_i) = i_l`, §2) sends the summand restricted to the
curve `u = y(X)`: a polynomial `G` of degree `2 · k · 2^(k-1)` for a summand of degree 2 in each variable, whose sum
over `V_k` is the sum over the round's `2^k` corners. One challenge `z` gives the `k` coordinates `y_l(z)`. No curve
does better: a curve through the `2^k` corners on `2^k` points has coordinates of degree at least `2^(k-1)`.

π2 hashes that data. Over 27 variables (modelled, `params/leanvm_rec_params.py`; Keccak-256's rate is 136 bytes):

| rounds of | challenges | scalars | Keccak-f | in π2 |
|---|---:|---:|---:|---|
| 1 variable | 27 | 54 | 27 | |
| **2 variables (π1-rec3, π1-rec4)** | **14** | 106 | **27** | **+0 Keccak-f** |
| 3 variables | 9 | 216 | 45 | +18 (2.36M positions) |
| 4 variables | 7 | 408 | 77 | +50 |
| 3 triples, 9 pairs | 12 | 144 | 33 | +6 (0.79M positions) |

- **Pairs cost no permutation.** A plain round's 2 scalars and the 32-byte state are 80 bytes, one block. A pair's 8
  scalars and the state are 224 bytes: one hash of two blocks, where two plain rounds take two hashes of one block.
- **Triples do not pay**: each costs 2 more permutations against pairs and saves half a challenge; π2 has about 0.36M
  positions left at 128 signatures and 0.09M at 400 (SPEC-REC.md §2.4.5).
- **In π2** the pairs send more stream scalars (8 where two plain rounds send 4), fewer challenge packings, one later
  block a pair, and about twice the batch's `E` operations (278 against 135, recorded); π2's verifier has 13 fewer
  ports.

### 14.4 The wide draws (π1-rec4)

π1-rec3's transcript (`tests/counts.rs`, `transcript_shape`; bytes each call absorbs besides the 32-byte state):
`80 | 0 0 0 | 192 | 48 ×41 | 1536 | 0 ×5 | 56 | 2832 | 0 | 192 ×13 | 48`, plus the seed: 70 calls, 116 Keccak-f. Nine
calls absorb nothing (`β`, `γ`, the zerocheck's `c`; the ring map's `f_1 … f_5`; the batch's `λ`): a whole
permutation for 192 bits each, while a Keccak-f's rate holds 1,088.

**The wide draw** (`Channel::sample_wide`, `transcript::keccak256_rate`): one Keccak-256 of the state and the bytes
since the last challenge, as `sample` hashes them, but read past its digest: the sponge's whole rate after its last
permutation (136 bytes; its first 32 are `keccak256` of the input, which stays the chain's next state). Challenge `k`
is the rate's bytes `8 + 24k .. 32 + 24k` read as `challenge_of` reads the state's `8 .. 32`, so challenge 0 is
`sample`'s and a draw gives up to five (`WIDE_MAX`). In π2's circuit a challenge `k` is three more lanes of the same
permutation's output (lanes `1 + 3k … 3 + 3k`), packed as `Low`'s.

**π1-rec4's transcript** (the stream is π1-rec3's byte for byte; only the challenges' derivation changes):

| call | absorbs | Keccak-f | draws |
|---|---:|---:|---|
| the seed | name, IV, public input | 1 | — |
| after `C1`'s commitment | row counts, `C1`'s root and answer (80 B) | 1 | `α`'s `c`, `β`, `γ`, the zerocheck's `c` (wide, 4) |
| the skip, the zerocheck's and lincheck's rounds | as π1-rec3 (192 B, 41 × 48 B) | 2 + 41 | one each |
| after `C2`'s commitment | the slices (1,536 B) and `C2`'s root and answer (56 B) | 12 | `t`, the ring map's `f_0 … f_3` (wide, 5) |
| after the values at `t` | 2,832 B | 22 | `ρ`, the batch's `λ`, `f_4`, `f_5` (wide, 4) |
| the batch | 13 pairs × 192 B, 48 B | 26 + 1 | one each (narrow) |
| | | **106** (π1-rec3: 116) | 60 calls (70) |

Moving the slices into `t`'s call costs nothing (`32 + 1,592 + 1 = 1,625` bytes fill 12 blocks, as `32 + 1,536`
did alone) and saves the map's own call. At 400 signatures: 108 against 118. The minimum for any sponge on this
stream, every message absorbed before the challenge that follows it, is 105 (the values at `t` are 9 bytes past 21
blocks with the 32-byte state; a duplex sponge without it would save that one, at the cost of leaving Keccak-256's
chain, which π1's main line, its contract and the Lean's model share). Narrow ring-map challenges, six in one rate,
would save no permutation over drawing `f_4, f_5` with `ρ`, and would weaken the ring switch.

**Code.** `leanvm_statement`: `FsShape::Rec4` (its code 4 in π1's contract IV, which binds the variant), the channels'
`sample_wide` (`KeccakChannel`, `KeccakWriter`, the prover's `Replay`, the recorder: `record::Node::Wide(hash, k)`,
challenge 0 a `Node::Low`), `flock_min::verify_walked_deferred` (Flock without its map, the zerocheck's first
coordinate given) and `ring_end_at`. `leanvm_univariate`: `verifier::reduce` and the prover draw as the table says
(`KECCAK_REC4`); `batch` takes `λ` drawn. The EVM's `KECCAK256` gives the digest alone, so π1-rec4 has no contract of
its own (`codegen` refuses a `Wide` node): its vectors are checked against the Rust verifier (`tests/evm_vectors.rs`,
`tests/prove_real.rs`), and π2's circuit runs it. `leanvm_rec::PI1 = KECCAK_REC4`; π1-rec3 stays (the Lean's, its
vectors, its contract).

**Vectors.** `tests/vectors/keccak128_rec4.txt` (the reference trace) and `keccak_rec4.txt` (400 signatures), written
by `tests/prove_real.rs` (`WRITE_VECTORS`, `VECTOR_FILE`), not by hand ([`KECCAK.md`](KECCAK.md), "Vectors").

### 14.5 Soundness of the two shapes

**The pairs.** A pair's polynomial has degree 8, so its Schwartz–Zippel error with a narrow challenge is `8/2^160` (a
plain round's `2/2^160`), drawn after `C2`, over `C1`'s and `C2`'s lists (4,473 and 6,296 at 128 signatures): 157.0
bits alone and 132.3 after the lists, the weakest round of π1-rec3 and π1-rec4 (§9). Summed over the 14 rounds, as an
interactive protocol would count them, about 128.5; with Fiat–Shamir over `Q` queries the per-round figure is the one
that counts (§9). The Lean bound caps each round at `2^35/|E|`, a pair's `8/2^160` exactly. The point is not uniform
(each pair of coordinates lies on a curve); neither argument needs it: the sumcheck makes one Schwartz–Zippel step a
round, in `z_j`, and WHIR's openings are sound at every point. No new commitment, no new list.

**π1-rec4 against π1-rec3.** The stream, the statement, the relations, the claims and every challenge's role are
π1-rec3's; three things differ.

1. *Several challenges from one query.* In the random-permutation model a fresh Keccak-f query's output is uniform
   (up to `Q/2^1600`), so the five 192-bit challenges of a wide draw are uniform and independent, and independent of
   the digest that becomes the next state (other lanes); the capacity stays Keccak-256's 512 bits. The bus needs `c`
   and `β` independent and uniform (SPEC-REC.md §1.4), and they are. The Fiat–Shamir composition
   (`formal/UniSound/UniSound/Fs128.lean`, `uniBound128`) charges every query the error of the round it may hit; a wide
   query may hit any of its challenges, so its error is their sum (`params/leanvm_univariate_params.py`,
   `rounds(.., "rec4")`).
2. *The ring map after `C2`'s commitment, `f_0 … f_3` with `t` and `f_4, f_5` after the values at `t`.* The ring
   switch's relation is `Σ_u W_f(u) q_flock(u) = target_f(s)`, a function of `q_flock` (bound by `C1`'s root and
   answer before `α`), the slices `s` and the point `p` (in the stream before the map) and the map `f` alone, so
   drawing `f` later, and in two parts, leaves it a function of values fixed before `f`. For a dishonest `s` it is a
   nonzero polynomial `P(f_0, …, f_5)` of degree 1 in each `f_j`. Write `P = Σ_m c_m(f_0 … f_3) f_4^{m_4} f_5^{m_5}`:
   some `c_m` is nonzero of degree ≤ 4, so a `t`-query makes it vanish with probability ≤ 4/|E|, and otherwise a
   `ρ`-query makes `P` vanish with probability ≤ 2/|E|. The calculator charges the whole 6/|E| to both queries, over
   `C1`'s and `C2`'s lists. `t`'s identities do not involve the map.
3. *`λ` with `ρ`, `f_4`, `f_5`.* `ρ` combines relations that are all fixed when it is drawn but the ring relation's
   target, which `f_4, f_5` fix; those are independent of `ρ` (other lanes), so conditioned on them the combination
   errs with probability ≤ (relations − 1)/|E| as before. `λ` combines the three combined claims, fixed by `ρ`.

At 128 signatures, bits after the lists (`python3 -I params/leanvm_univariate_params.py`):

| query | error | π1-rec3 | π1-rec4 |
|---|---|---:|---:|
| `α`'s call | bus `16 · side`, `γ` 60, zerocheck `2^22 − 1` (summed in π1-rec4) | 154.3, 174.0, 157.9 | 154.1 |
| `t`'s call | the identities' `Σ deg` (+ the map's 6 in π1-rec4) | 143.2 | 143.2 |
| `ρ`'s call | `ρ` 115 (+ `λ` 2 + the map's 6) | 160.4 (`λ` 166.3, the map 177.3) | 160.3 |
| the batch's pairs | `8/2^160` | **132.3** | **132.3** |

With the three openings charged once (`269 · 2^-137` a query), **128.79 bits as `Q/ε` at `Q = 2^64`** for both (400
signatures: 128.86).
