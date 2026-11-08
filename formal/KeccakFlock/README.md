<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# KeccakFlock: the Keccak-f block of the Keccak VM

The Flock block of `crates/lv42_flock/src/keccak.rs` (one Keccak-f[1600] permutation in `2^17` positions, every
round's state materialised, `C = I`; `crates/lv42_flock/KECCAK.md`), as the inhabitant of `KeccakVm.KeccakFlockSpec`
(`formal/KeccakVm/KeccakVm/Instance.lean`). It is a library of `formal/EndToEnd` (`KeccakFlock`,
`srcDir = "../KeccakFlock"`, `warningAsError`). Its files are not `module`s: they import `formal/Circuit`'s
`KeccakBits` and `formal/RecCircuit`'s `KeccakMath`, which are not either.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=10G lake build KeccakFlock     # #guard_msgs checks the axioms
lake env lean ../KeccakFlock/KeccakFlockTest/Rows.lean           # the rows against the Rust's walk (~30 s)
lake env lean ../KeccakFlock/KeccakFlockTest/Honest.lean         # the honest column, evaluated (~35 s)
```

The Rust side of `Rows.lean`: `cargo test --release -p leanvm_flock_gas --test lean_keccak_block -- --nocapture`
(`crates/leanvm_flock_gas/tests/lean_keccak_block.rs`).

## The R1CS (`KeccakFlock/Block.lean`)

- **Positions.** Position `z + 64 w` of a block is bit `z` of its 64-bit word `w` (`pos w z`). This is how
  `bitTable` and `BlockR1CS.batchBlock` read a column of `K`: the low six coordinates are the packing position
  (`Flock.kSkip`), the high eleven the word (`KeccakVm.kWords`).
- **The layout**, as `keccak.rs` and `keccak_flock.rs` have it:
  - the port quads `4q + r`, `q < 32`: `X` (`r = 0`) and `V` (`r = 3`) are output lane `q`, `Y` (`r = 1`) is the
    word 1, `C` (`r = 2`) is input lane `q`; quad 25 is `(2, 1, 0, 2)`, quads 26..31 are `(0, 1, 0, 0)`;
  - `tWord j l = 64 (j + 2) + l` holds χ's products `t_j[l]`, and `aWord j l = 64 (j + 2) + 32 + l` the state
    `A_j[l]` (`j < 23`);
  - `stWord j l` is the word of the state before round `j` (`state_word(j − 1, l)`);
  - `cpos`, position 64 (bit 0 of quad 0's `Y`), is the constant wire (`CONST_POS`, `CONSTANT_COLUMN`);
  - `inSlot l = 4l + 2` and `outSlot l = 4l`, as `UniStatement.keccakSlot` places the `SHA3` lanes.
- **The rows.** `row k` is the pair of position lists that row `k` of `A` and of `B` sum (`rowW`, `portRow`,
  `roundRow`), the five kinds of `keccak.rs`:
  - constant `([1], [1])`;
  - free input `([self], [1])` (the `C` words);
  - copy `([X], [1])` (the `V` words);
  - product `(1 + b[x+1], b[x+2])` (the `t` words);
  - lin-id `(b[l] + t + RC, [1])` (the states and the `X` words; ι on lane 0);
  - empty `([], [])`.

  Bit `z` of `b[i]` is the sum of eleven positions of the previous state (`bForm`): lane `src = piInv i` at
  `z' = z − rho src`, the five lanes of column `src − 1` at `z'`, and the five lanes of column `src + 1` at
  `z' − 1`. This is `b_forms` and `row_values`.
- **The matrices** `matA`, `matB` have entry `(k, j)` set when `j` occurs an odd number of times in row `k`'s list
  (`xorMem`). No list repeats a position, so this is the 0/1 matrix of the Rust's rows. In characteristic two,
  applying a row to a vector gives the sum of the list's entries (`sum_ite_xorMem`).
- **`r1cs : BlockR1CS E 17`** carries these matrices and two walks:
  - the forward walk `walkRows` sums each row's list, as `row_values_walk` does, in about `13 · 2^17` additions
    (`rows_fst`, `rows_snd` by `sum_ite_xorMem`);
  - the backward walk is the naive one (`2^34` terms, never evaluated).

## Soundness (`KeccakFlock/Sound.lean`)

```lean
theorem KeccakFlock.step_of_holds {κ : ℕ} (c : Column (KeccakVm.kWords + κ))
    (h : BlockR1CS.BatchHolds r1cs cpos (bitTable c)) (t : Fin (2 ^ κ)) :
    KeccakVm.kBlockState c t outSlot = keccakF1600 (KeccakVm.kBlockState c t inSlot)
```

This is exactly `KeccakFlockSpec.step_of_holds`. It has no hypothesis beyond the predicate, and `keccakF1600` is
leanerVM's (`Statement/Keccak.lean`). The proof:

1. The block the predicate reads is Boolean: bit `z` of word `w` sits at `z + 64 w` (`batchBlock_bitTable`). So each
   row's two sums are parities of bits (`sum_ofBool`), and every position holds the AND of its row's two parities
   (`holds_rows`).
2. Round by round (`state_of_rows`, the shape of `RecCircuit.d16_state`):
   - the eleven bits a form sums give `πρθ` of the previous state (`parity_bForm`);
   - the product rows give `t = ¬b[x+1] ∧ b[x+2]`;
   - the lin-id rows give `b ⊕ t ⊕ ι`, that is `KeccakBits.round` (`RecCircuit.round_apply`).
3. The output port therefore holds `KeccakBits.keccakF` of the input port, which is `keccakF1600` bit by bit
   (`PcsCircuit.keccakF_bits`).

## Completeness and the inhabitant (`KeccakFlock/Complete.lean`)

- **The honest block** `honestBlock s` is `build_block_witness`. Its states are `stateAfter s j`, leanerVM's
  `Keccak.round` folded over the first `j` round constants, computed once a block. Its words are built bit by bit
  (`honestBit`):
  - `tBit` is `¬b[x+1] ∧ b[x+2]`;
  - the ports are as in the layout above.

  `genColumn` places the honest block of state `t` at block `t`.
- **`holds_gen`**: the honest column satisfies `BatchHolds r1cs cpos`. Every row's AND of parities is the honest bit
  (`rows_honest`); the lin-id rows hold by `round_parity` (`stateAfter_succ`, `PcsCircuit.round_bits`).
- **`in_gen`**: block `t`'s input port holds state `t`.
- **`keccakFlockSpec : KeccakVm.KeccakFlockSpec`** assembles them:

  ```lean
  r1cs := r1cs; constPos := cpos; inSlot := inSlot; outSlot := outSlot
  step_of_holds := step_of_holds; gen := genColumn; holds_gen := holds_gen; in_gen := in_gen
  ```

The root file checks, with `#guard_msgs`, that `step_of_holds`, `holds_gen`, `in_gen` and `keccakFlockSpec` depend on
`[propext, Classical.choice, Quot.sound]` only. Everything is sorry-free, with no `native_decide`.

## Tests (`KeccakFlockTest/`, not part of the library)

- **`Rows.lean` checks the rows against the Rust.** It evaluates `r1cs.rows` (the specification's forward walk) on
  the column weights `(r_p, 0, 0)`, with `r_p` a xorshift64 stream. Limb 0 of each row value is then 64 independent
  GF(2) evaluations of the row's 0/1 form. For three seeds, it compares the digest over all `2^17` rows of `A w` and
  of `B w`, and twelve sample rows (one of each kind), with `keccak_flock::row_values`, the verifier's walk of
  `keccak.rs`'s block. All of them agree. A changed digest fails.
- **`Honest.lean` evaluates the honest column** of two states, as one batch:
  - every row's AND of parities holds and the constant wire is 1;
  - block 0, lifted to `E`, satisfies `r1cs.Holds`, decided by one walk;
  - the output port is `keccakF1600` of the input port;
  - Keccak-f of the zero state starts with `0xF1258F7940E1DDE7`;
  - a flipped output, `t`, state, input or empty bit breaks a row of its block, and only of its block.

## What is not done

- **The structured lincheck terminal** (`keccak_flock.rs::structured_terminal`, `KECCAK.md` M3), with its proof
  that it equals the matrices' bilinear form (the walked terminal). See the section below.
- **A fast backward walk.** `r1cs.cols` is the naive sum. `BlockR1CS.cols` is only read through `cols_fst` and
  `cols_snd`, so nothing here needs a fast one.
- The Keccak VM's relation over this block (`KeccakVm.KvHolds keccakFlockSpec`), its arithmetization and the
  univariate verifier's statement are other milestones (`formal/KeccakVm/README.md`).
