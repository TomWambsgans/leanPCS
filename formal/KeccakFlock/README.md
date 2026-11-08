<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# KeccakFlock: the Keccak-f block of the Keccak VM

The Flock block of `crates/vendor/flock-42422001/src/keccak.rs` (one Keccak-f[1600] permutation in `2^17` positions, every
round's state materialised, `C = I`; `docs/leanvm/flock/KECCAK.md`), as the inhabitant of `KeccakVm.KeccakFlockSpec`
(`formal/KeccakVm/KeccakVm/Instance.lean`). It is a library of `formal/EndToEnd` (`KeccakFlock`,
`srcDir = "../KeccakFlock"`, `warningAsError`). Its files are not `module`s: they import libraries that are not
either, namely `formal/Circuit`'s `KeccakBits`, `formal/RecCircuit`'s `KeccakMath`, `FlockSoundUni.Transcription`
and `UniSound.Ids.Facts`.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=10G lake build KeccakFlock     # #guard_msgs checks the axioms
lake env lean ../KeccakFlock/KeccakFlockTest/Rows.lean           # the rows against the Rust's walk (~30 s)
lake env lean ../KeccakFlock/KeccakFlockTest/Honest.lean         # the honest column, evaluated (~35 s)
lake env lean ../KeccakFlock/KeccakFlockTest/Terminal.lean       # both terminals against the Rust's (~9 min)
```

The Rust side of `Rows.lean` and `Terminal.lean`: `cargo test --release -p leanvm_statement --test lean_keccak_block --
--nocapture` (`crates/leanvm/statement/tests/lean_keccak_block.rs`).

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

## The lincheck terminal (`KeccakFlock/Terminal*.lean`)

- **Transcriptions** (`Terminal.lean`):
  - `Terminal.structuredTerminal` is `keccak_flock.rs::structured_terminal`, computable. It is split into the packing
    weights (`packingAt`), the correlations through partial correlations (`correlation`) and the body
    (`structuredCore`). The body is written in the Rust's named parts (`tOne`, `rcOne`, `constants`, `bOne`,
    `oneCoefficient`, `freeW`, `copiesW`, `aTMid`, `aTLast`, `diagonal`, `laneTerms`, `gAt`, `shifts`). The Rust's
    accumulations into arrays are written as the sums they compute.
  - `Terminal.walkedTerminal` is `flock_min.rs::walked_terminal_with::<_, KeccakWalked>`, run on the specification's
    forward walk `r1cs.rows`. The shared helpers (`eqKernel`, `eqEval`, `dot`, `lagrangeWeights`, `rowLowWeights`)
    are `formal/UniStatement`'s.
- **The walked terminal is the matrices' bilinear form**, for all inputs (`TerminalWalk.lean`):

  ```lean
  theorem Terminal.walkedTerminal_eq_bilinear (zSkip rowLow chiIn chiInPrime s alpha) :
      walkedTerminal zSkip rowLow chiIn chiInPrime s alpha =
        bilinear zSkip rowLow chiIn chiInPrime s alpha +
          alpha * alpha * eqEval chiIn chiInPrime * dot (rowLowWeights zSkip rowLow).2 s +
          alpha * alpha * alpha * eqEval constantBits chiInPrime * s.getD 0 0
  ```

  Here `bilinear = Σ_(k, j) e_k (A_kj + α B_kj) w_j` over the block's matrices `matA`, `matB`, with
  `e_k = lowWeights[k mod 64] · eq(chi_in)[k / 64]` and `w_j = s[j mod 64] · eq(chi_in')[j / 64]`.
- **The structured terminal equals the walked one** under the Rust's assertions (`TerminalMain.lean`):

  ```lean
  theorem Core.structuredTerminal_eq_walked (zSkip rowLow chiIn chiInPrime s α)
      (hrl : rowLow.length ≤ 6) (hz : zSkip = none → rowLow.length = 6)
      (hci : chiIn.length = 11) (hcp : chiInPrime.length = 11) :
      structuredTerminal zSkip rowLow chiIn chiInPrime s α = walkedTerminal zSkip rowLow chiIn chiInPrime s α
  ```

  `Core.structuredTerminal_eq_bilinear` combines the two theorems. The length of `s` is not needed: both sides read it
  through `getD`. The proof, file by file:
  - `TerminalCore.lean`, `WF_eq`: the walked form, row class by row class, for arbitrary tables. Summed over the
    packing position, a form of `b` gives two correlations `corr(off) = Σ_z E_z s_(z − off)` (`sum_bForm`).
  - `TerminalStruct.lean`: the constant column's coefficient (`tOne_eq`, `rcOne_eq`, `constants_eq`, `bOne_eq`) and
    the diagonal (`diagonal_eq`). `constants_eq` uses characteristic two, `kd[0] + kd[1] = 1`.
  - `TerminalShifts.lean`, `shifts_eq`: the offsets (`sum_shifts`), the lane bijections (`reindex1`, `reindex2`) and
    the rounds (`laneA_eq`, `laneB_eq`).
  - `TerminalEq.lean`, `structuredCore_eq`: the body is the walked form, given `Σ_z E_z = 1`.
  - `TerminalFront.lean` and `TerminalMain.lean`, the inputs:
    - the eq table of an 11-coordinate point factors into lane, kind and round (`eqKernel_factor`);
    - the eq table of a concatenation is the tensor product (`eqKernel_append`);
    - the split packing weights are `rowLowWeights` (`packingAt_eq`) and sum to 1 (`packing_sum`): an eq table does
      (`eqKernel_sum`), and so do Lagrange weights at distinct nodes (`lagrangeWeights_sum`, Mathlib's
      `Lagrange.sum_basis`, with `FlockSoundUni`'s `phi_injOn` and `lagrangeWeights_getD`);
    - the partial correlations are the correlations (`correlation_eq`);
    - the pin's weight is the eq table at word 1 (`eqEval_constantBits`).
- **Tested** (`KeccakFlockTest/Terminal.lean`). At every skip `0..6`, on inputs drawn as the Rust test draws them,
  `structuredTerminal` equals the Rust's `structured_terminal`, and `walkedTerminal` (at skips 0, 3, 6) equals the
  Rust's walked terminal. A changed slice changes the value.

The root file checks, with `#guard_msgs`, that `walkedTerminal_eq_bilinear`, `structuredTerminal_eq_walked` and
`structuredTerminal_eq_bilinear` depend on `[propext, Classical.choice, Quot.sound]` only. `KeccakFlock` imports
`FlockSoundUni.Transcription` and `UniSound.Ids.Facts` for these lemmas.

## Where it is used

- The terminal is used by π1's verifier and its soundness: `UniKeccak.structuredTerminal` is
  `KeccakFlock.Terminal.structuredTerminal` (`UniKeccakSound.KF.Br.structuredTerminal_eq`), and the catch of Flock's
  soundness on the block uses `structuredTerminal_eq_bilinear` ([`formal/UniKeccakSound`](../UniKeccakSound/README.md)).

## What is not done

- **A fast backward walk.** `r1cs.cols` is the naive sum. `BlockR1CS.cols` is only read through `cols_fst` and
  `cols_snd`, so nothing here needs a fast one.
