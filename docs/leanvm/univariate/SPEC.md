<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# A univariate PIOP for the Keccak VM, for the EVM

This is the protocol of `crates/leanvm/univariate` (`verifier::reduce`), as the code runs it. The VM, its workloads,
the gas and the prover's measurements are in `KECCAK.md`; Flock's part is in `SPEC-FLOCK.md`; the prover is in
`PROVER.md`. Figures marked *measured* come from revm runs of the contract compiled from the recorded Rust verifier
(`tests/keccak_vm.rs`, `tests/prove_real.rs`); *modelled* ones are computed here.

## 0. Summary

The statement is the Keccak VM's: leanVM 42422001's VM with its BLAKE2S table replaced by leanVM `9d50c92a3`'s `SHA3`
table (§1). The proof of it is not leanVM's:

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
- **Claims.** On the main line (`PCS_OPEN`'s ABI, point claims), one batching sumcheck over the three stacks turns
  every commitment's relations into one point claim: 3 claims in 3 calls (`C1`, `C2`, `F`). Extension W (weighted
  claims) drops that sumcheck.
- **Result** at the reference workload (128 signatures), measured: 8,020 B of calldata, 230,985 gas of execution,
  358,957 transaction gas (EIP-7623, claim price 0, without the 21,000 base). §10 and `KECCAK.md` have the other
  workloads.

## 1. Statement and workload

leanVM 42422001's `crates/verifier` is ported, generic over the scalar, in `crates/leanvm/statement`, with the
`SHA3` table of leanVM `9d50c92a3` in BLAKE2S's place (`layout::tables`). The statement: the VM, run on the stacked
bytecode (the fixed program) from `pc = 1, fp = 1`, halts at `pc = g^(2^lb - 1)`, `fp = 1`, `2^lb` the bytecode's
instructions. The 32-byte public input is in memory cells 0 and 1, and every `SHA3` row is one Keccak-f step of
leanVM `9d50c92a3`'s sponge. In Lean (`formal/KeccakVm`) this is `KvHolds`: `M3Holds` of the six tables together with
the Keccak-f region `KeccakAux`.

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

The setup root is a constant in the code (no `SLOAD`). The `C1` and `C2` roots are in calldata. Each commitment is
opened by **one** `PCS_OPEN` call. WHIR takes no OOD sample at level 0, so a root binds only a list of tables and
all claims on it must be checked together (AGENTS.md). `src/stacks.rs` gives each column an aligned block, largest
first. A claim reads only its column's block. Nothing relies on the stack's unused words, nor on the zero padding of
a column shorter than its lane, which leanVM's `Layout::new` does not force (`PROVER.md`, "The stacks' unused
words").

**Sizes over the workloads**: the largest proof stack is `2^25` at 32 signatures, `2^27` at 128, `2^28` at 400 and
`2^30` at 1,000. `q_flock` alone is `2^(h_SHA3 + 11)` words, so `C1` reaches WHIR's `2^28` at `2^16` permutations,
about 470 signatures (`tests/keccak_vm.rs`, `keccak_stacks_against_whir`; `KECCAK.md`, "Capacity").

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
of the state and the calldata bytes read since the last one. A scalar is 24 bytes, a root half 16: one of the root's
two WHIR scalars (`hash_to_scalars`, the opening's first two), big-endian, so that a root's 32 bytes are its `PCS_OPEN`
root word `s_0 · 2^128 + s_1` (`crates/membership/evm/src/machine.rs`), which the contract passes as it is. The seed
is the Keccak-256 of the name `leanVM-univar-v1`, the contract's IV (§13, F2: it binds the program, the setup roots,
the shape, the layout words and the variant) and the public input. There are no announced sizes beyond the row
counts: one shape class per contract. The order:

1. The six row counts (§13, F1), then the `C1` root. Then `α ∈ E^4` (the tuple weights), `β` (the fingerprint shift)
   and `γ` (the batching of `C1`-only constraints).
2. Flock (§7): its rounds, challenges and values.
3. The `C2` root, then `t`.
4. The values at `t` (§8).
5. `ρ`, which combines each commitment's relations.
6. On the main line: `λ`, which batches the three commitments, then the batching sumcheck's rounds and its three
   end values.

**The Fiat–Shamir shapes** (`flock_min::Variant::fs`). `KECCAK_MAIN` (`FsShape::Main`) draws every challenge by
its own hash. `KECCAK_REC3` (`FsShape::Rec3`, π1-rec3, the recursion's inner proof: `docs/leanvm/rec/SPEC-REC.md`
§1.4, `SPEC-POINTS.md`) draws `α` as `(c, c², c⁴, c⁸)` of one challenge and Flock's zerocheck coordinates after the
seven fixed ones as successive squares of one challenge, and runs the batching sumcheck two variables a round with
narrow (160-bit) challenges. At 128 signatures π1-rec3's verifier makes 70 Keccak-256 calls over a 9,232-byte stream.

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

## 7. Flock on the Keccak-f block (details in `SPEC-FLOCK.md`)

**Interface.** Flock runs after `C1` and before `C2`, reading only `C1`'s `q_flock`. It draws its own challenges in
the transcript between `γ` and the `C2` root. The verifier runs it as
`flock_min::verify_walked_with::<_, keccak_flock::Keccak>` at `log_n = 17 + h_SHA3` variables (32 at 128 signatures).

- **The block** is `lv42_flock::keccak`'s (`docs/leanvm/flock/KECCAK.md`): one Keccak-f[1600] per `2^17` slots,
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

**Claims, main line: `PCS_OPEN`'s ABI** (`crates/membership/evm/src/machine.rs`: point claims, `c` each). A batching
sumcheck takes `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack (27 variables at 128 signatures), the
others zero-extended. With `KECCAK_MAIN` it has two scalars a round; with `KECCAK_REC3` it runs two variables a
round (`transcript::sumcheck_pairs_drawn`). Then come the three stacks' values at its point `r`. The verifier
evaluates every `W_k(r)` (`verifier::weight_at`): columns at one row point share their eq factor, selector factors
share their high bits, Frobenius twists are cached (`stacks::EqCache`), `q_flock`'s slot terms share the eq of their
instance coordinates, and the ring-switch term is evaluated by its map (§7). The result is one point claim per
commitment: 3 claims in 3 calls.

**What the contract itself checks.** The verifier is linearised: every relation it states is a claim handed to
`PCS_OPEN`. The checks it makes itself are the row counts' range (§13, F1), Flock's lincheck terminal and, in point
mode, the batching sumcheck's terminal; each is affine in the last scalar read before it. So with the openings
mocked, a stream solved for those scalars is accepted at any challenges (`tests/lean_keccak_vectors.rs` builds such
streams); that is expected, not a bug. The verdict means something only together with the openings.

**Extension W: weighted claims** (`Claims::Weighted`). A call is `root, layout, k`, then per claim its points (each a
column's low coordinates), its terms (`column | point << 32 | twist << 48`, then the coefficient) and its value. The
precompile evaluates the weight, as leanVM's own WHIR verifier does. No batching sumcheck. Price `c` a claim; the
precompile's work grows with the terms. It is kept because the Lean vectors cover it (`tests/lean_keccak_vectors.rs`)
and the parity tests run it; the prover has no opening for it.

## 9. Soundness

**The calculator is not yet updated for the Keccak VM.** `params/leanvm_univariate_params.py` still models the
BLAKE2s VM's π1 at 1,000 signatures, so its figures are not the Keccak VM's. The reasoning below does not depend on
the VM.

Each challenge's error is a Schwartz–Zippel bound times the number of committed tables it is drawn against: `L_1`
before `C2` and `L_1 L_2` after it, `L` the certified level-0 Johnson list of a stack's WHIR commitment
(`lean-whir-large`; e.g. 4,473 at a `2^27` stack). The setup is honestly computed, and an honest codeword's list
within the Johnson radius is itself, so `L = 1` there. Stacks below `2^24` words have no certified level-0 list.
`|E| = 2^192`. The rounds, as the code states them (§13, F8: committed capacities, the unused blocks, degree 4 a
tuple, `ρ` and `λ` apart):

| round | error |
|---|---|
| bus `(α, β)`: if the push and pull multisets differ, `Π(β + fp)` differs: one Schwartz–Zippel over `E^5`, degree 4 a factor, every table full (the counts are the prover's), `N` tuples | `4N/|E|` |
| `γ`: `C1`-only constraints batched | `(their number − 1)/|E|` |
| Flock, before `C2`: the skip (`(2^(k+1) - 1)/|E|`), the zerocheck's degree-3 and the lincheck's degree-2 rounds, the ring map in tower order (`6/|E|`) | about `2^7/|E|` |
| `t`: every identity at its committed capacity (tree, leaves times `Z_act`, unused blocks, `Q_W`) | `Σ deg/|E|` |
| `ρ`: each commitment's relations combined | `(their number)/|E|` |
| `λ` (3 claims) and the batching sumcheck's rounds | `(2 + 2 · vars)/|E|` on the main line |

The `t` round dominates: its degree sum, the largest, is multiplied by `L_1 L_2`.

**The PCS (§13, F3).** WHIR is leanVM's, unchanged, at about 128.97 certified bits an opening, and the main line
makes 3 openings (`C1`, `C2`, `F`): a plain union gives about 127.4 bits. In the query-bounded random-permutation
model of the end theorems, the openings' Fiat–Shamir transcripts are domain-separated (each seeded by its own layout
word and claims) and share the adversary's `Q` queries, so their total is about `(Q + 3)·ε` rather than `3·Q·ε`:
about 129 bits for `Q ≫ 3`. The setup's `F` cannot join a proof commitment without losing its `L = 1`.

Not counted: Fiat–Shamir (Keccak-256 as a random oracle) and Flock's fixed zerocheck coordinates (leanVM's).

**π1-rec3** (`KECCAK_REC3`; `docs/leanvm/rec/SPEC-REC.md` §1.4 and `SPEC-POINTS.md`, analysis there, not proven):
`α` as `(c, c², c⁴, c⁸)` puts the bus at degree 16 a factor in `(β, c)`; Flock's zerocheck coordinates as successive
squares of one `c` give a polynomial of degree about `2^(log_n - k - 7)` in `c`; the batching sumcheck's narrow
challenges make a round of degree `d` err with probability `d/2^160`.

**Lean.** `formal/UniKeccak` transcribes this verifier (main line and π1-rec3) and agrees with the Rust on the
differential vectors; its knowledge-soundness and completeness statements for the Keccak VM are stated, not proved
(`formal/README.md`, "The Keccak VM").

## 10. Gas

Measured on revm (`tests/keccak_vm.rs`, `keccak_gas_report`), `KECCAK_MAIN`, point claims; transaction gas is
EIP-7623's `max(16 B + execution, 40 B)` (zero bytes 4 and 10) without the 21,000 base; `c` the price of a claim.

| signatures | largest stack | calldata | execution | claims / calls | tx, `c` = 0 | tx, `c` = 5,000 |
|---:|---:|---:|---:|---:|---:|---:|
| 32 | `2^25` | 7,828 B | 222,928 | 3 / 3 | 347,840 | 362,840 |
| **128** | `2^27` | 8,020 B | 230,985 | 3 / 3 | **358,957** | 373,957 |
| 400 | `2^28` | 8,116 B | 236,976 | 3 / 3 | 366,484 | 381,484 |

The gas is a function of the shape: the real proofs run at these figures (`KECCAK.md`, "The real proofs' gas"),
and the design is almost size-independent (the values at `t` are fixed; Flock's rounds and the batch grow only with
the logarithms of the sizes).
**Calldata at 128 signatures**: selector and public input 36 B, row counts 24 B, two roots 64 B, Flock's 154 scalars
3,696 B, the 118 values at `t` 2,832 B, the batching sumcheck (27 rounds of 2 scalars, 3 values) 1,368 B. The
contract is execution-bound (`16 B + execution` above `40 B`). The deployable build, the per-phase report and the
recursion's contract are in `KECCAK.md`.

## 11. Prover

`PROVER.md` describes the prover (`src/prover/`) phase by phase; `KECCAK.md` has its measurements. At 128
signatures, `KECCAK_REC3`, on an Apple M4 Max: 3.65 s warm (median of 3), 6.86 GB peak.

## 12. Risks and open questions

1. **Capacity.** `C1` exceeds WHIR's `2^28` words above about 470 signatures (`KECCAK.md`, "What remains").
2. **The main line pays for faithfulness in execution.**
   - The point ABI forces a batching sumcheck, whose weight carries the ring switch's 64 Frobenius-twisted eq terms:
     the cost leanVM's verifier pays at WHIR's terminal point. Extension W moves it to the precompile.
   - Execution binds on the main line, so `c` shows at once (+3c).
3. **Extension W is a precompile change.** Its price per claim should grow with the terms, which the table does not
   charge.
4. **Faithfulness deltas** (the statement is the same):
   - `CountsNonzero` by inverse columns `z_T` instead of leanVM's count product;
   - the `SHA3` lanes committed twice, with `copy = ℓ(q_flock)` (and `END_BIT` on `in_16`) in `Q_W`;
   - padding rows unconstrained (the leaf identity forces their leaves to 1): the extracted witness is `C1` as
     committed, with the lanes read from `q_flock` (§13, F6);
   - the bus as a committed heap instead of a GKR;
   - the hash argument on a Keccak-f block of one permutation per `2^17` slots, not leanVM `9d50c92a3`'s block of
     three (`KECCAK.md`, "The statement");
   - one shape class per contract.

   `Balanced` (a `List.Perm`) follows from the heap's root as leanVM's GKR root gives it.
5. **The soundness calculator** models the BLAKE2s VM (§9) and is an analysis, not a proof: it assumes the batching
   sumcheck and `ρ` as standard and Fiat–Shamir over Keccak-256.
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

5. **Lever 4a** (a matrices' reduction run inside the batching sumcheck) belonged to the BLAKE2s block, whose
   lincheck terminal was reduced to claims on committed matrices. The Keccak-f block's terminal is computed from its
   structure in Flock (§7), so the batching sumcheck is the stacks' alone.

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

8. **F2: the IV, the layout words, the setup roots.**
   - `contract::SetupRoots`: the roots the IV binds are code constants: `F` (from the program and the shape,
     `prover::setup::f_root`; `REFERENCE.f` is the 128-signature shape's, `067244be…`) and two fixed words `a0`,
     `b0` (`93cd9a03…`, `c0755650…`), the roots of leanVM 42422001's BLAKE2s matrices, which no Keccak VM proof
     opens; they stay in the preimage so that the IV's bytes, the committed vectors and their Lean transcription are
     unchanged. The gas reports use `REFERENCE` for every shape (the gas does not depend on the roots); a deployment
     for another shape takes its own `F`.
   - `PCS_OPEN`'s layout word (`contract::layout_word`) is a 32-byte constant: the shape's 8 bytes (`log_memory`,
     `log_bytecode`, the six heights), the opening's code (`0x5501` `C1`, `0x5502` `C2`, `0x5503` the setup, bytes
     22..24), the stack's `vars` (byte 24) and `placed` (bytes 25..32, the words the blocks fill). WHIR's verifier
     reads `vars` and `placed` from it. `contract::layout_words` adds two fixed words (codes `0x5504`, `0x5505`,
     `vars` 28, `placed` `2^28`) after the three openings'.
   - `verifier::layouts(shape)` is public (and `Reduced::layouts`): the stacks depend on the shape alone.
   - The contract's IV is `keccak("leanVM-univar-iv" ‖ program IV ‖ F ‖ a0 ‖ b0 ‖ shape bytes ‖ the five layout
     words ‖ variant bytes)` (`contract::contract_iv`; the variant bytes are `"keccak-vm"`, the skip and the
     Fiat–Shamir shape's code); the seed is `keccak(name ‖ IV ‖ public input)`. It costs no gas.
   - Prover: seed the transcript with `contract_iv(shape, variant, program IV, roots)`; call `PCS_OPEN` with the
     layout words.

9. **F3, F6, F7, F8** (documentation):
   - F3: §9's PCS figure (WHIR openings at 128.97 bits, by a plain union and in the query-bounded model); shapes
     below `2^24` have no certified list.
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

12. **Lever 5a** (extension B, a bit-slice claim type on the ABI) was removed with the BLAKE2s VM; `PCS_OPEN` takes
    point claims, or weighted claims under extension W.

13. **The Lean transcription's findings** (documentation):
    - `weight_at` keys `q_flock`'s slot rows by their point (entry 4), not by the slot;
    - `Relations::combine` merges the 0-variable `TreeQuotient(1)` term into the first longest `C2` point: harmless
      (documented in `claims.rs`);
    - `flock_min`'s `log_n ≥ 17 + 7` is `Shape::validate`'s `SHA3` height of at least 7 (entry 7);
    - §8: what the contract checks itself, and why solved streams pass with mocked openings.

### The floor

The main line is execution-bound. Its largest part is the ring switch's weight at the batch's point: it needs the 64
conjugates of each of the coordinates of Flock's point (26 at 128 signatures: 1,638 squarings) and 64 products of
that many factors (1,664 products), whatever the map's coefficients, because a `K`-packed word's bits need all 64
Frobenius conjugates and the batch's point is random in `E`. The next is Flock's structured terminal (about 42K at
400 signatures). `keccak_gas_report` prints every phase at 128 and 400 signatures.

**Measured vs modelled.** Every gas and calldata figure is measured on revm (the measuring build's checks
subtracted). Modelled: the public input's byte swap (about 110 gas, not built) and the PCS's 128.97 bits an opening.

### Dropped levers

- The lincheck merged into the batch: circular (its point is the ring switch's, an input of the batch).
- Fewer coefficients a round: the batch's weight is a sum over many points, with no common eq factor to split off.
- A smaller skip (`k` 3 → 0–2): 2 scalars at most, and the prover's skip kernels start at 3
  (`lv42_flock::zerocheck::skip::MIN_SKIP`).
- Another tower basis for the target's `XOR` network: 400 random bases, the best 755 `XOR`s against 767.
- The public input in leanVM's byte order: about 110 gas; documented instead (F7).
- A looped ring-weight kernel: a loop costs about 30 gas an iteration.
- 32-bit packing of `q_flock` (32 twists instead of 64): not leanVM's witness, and `C1` would double.
