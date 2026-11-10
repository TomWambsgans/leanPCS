// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/membership/evm/src/machine.rs; new here: EIP-8141's frame introspection and a frame of PCS claims, and the `Chain` that deploys contracts and keeps
// their storage across transactions. MIT OR Apache-2.0; see AGENTS.md.
//! revm with `FIELD_MUL`, and with the frames of an EIP-8141 transaction, its frame of PCS claims among them.
//!
//! # PCS claims
//!
//! A transaction declares the claims its contract checks in a frame of PCS claims (the EIP draft,
//! `eip-draft_leanPCS.md`): an EIP-8288 dependency verification frame whose `data` is `PCS_SCHEME` then the
//! Keccak-256 of each claim, which the block's aggregated proof proves. The contract finds them with EIP-8141's
//! introspection, which this machine has: `FRAMEPARAM` (`0xb3`, 2 gas; the mode and the length of `data`) and
//! `FRAMEDATALOAD` (`0xb1`, 3 gas). [`PcsFrame`] is such a frame, standing for a block that proves its claims.
//!
//! **A claim** is the claims of one opening, on one commitment: an opening is of one random combination of its claims,
//! and that alone binds them to one table, leanVM's WHIR taking no out-of-domain sample at its first commitment (two
//! openings of one root could be of two tables). Its bytes ([`claim_input`]) are `3 + k (v + 1)` words of 32 bytes:
//!
//! 1. the commitment: its Merkle root `r` as the word `s_0 · 2^128 + s_1`, `s_h` the little-endian number of
//!    bytes `16 h .. 16 h + 16` of `r` (the two scalars of [`quotient::transcript::root_scalars`]);
//! 2. the layout's id ([`layout_id`]), which fixes `v`, the table's variables, and which lane of the WHIR stack
//!    holds which block of the table;
//! 3. `k ≥ 1`, the number of claims;
//! 4. each claim: its point's `v` coordinates, then its value. A field element of `GF(2^192)` is the low 192
//!    bits of its word, limb 0 lowest, and its top 64 bits are zero.
//!
//! The block proves it by an opening [`quotient::opening::verify`] accepts for the layout the id names: its
//! transcript's IV hashes that layout's prefix ([`quotient::opening::prefix`]: the label, the version, the layout's
//! hash, its size, WHIR's rate) then these claims, words 4 onwards as field elements, and its proof's first two
//! scalars are the root's, word 1's two halves (`formal/WhirBridge`, `family_sound`). The ids name distinct prefixes.
//!
//! **Why this encoding.** Every word is one the contract already holds as an EVM word, so writing a claim is an
//! `MSTORE` a word: a field element as `XOR` and `FIELD_MUL` work on it, a root as the calldata carries it and the
//! transcript absorbs it. Words of fixed width, with no offsets and no length but `k`, leave one way to parse a
//! claim, whose length the layout and `k` fix; with the top bits zero, a list of claims has one encoding, and its hash
//! names it. The layout is named, not sent: the protocol fixes it, and its lanes would be up to 64 more words.
//!
//! **Gas.** A transaction with `c` PCS claims pays `5,000 + 1,000 c` intrinsic gas for their share of the block's
//! aggregated proof ([`dependency_gas`]), apart from what this machine measures, and its frame of PCS claims is
//! `1 + 32 c` bytes of the transaction.

use std::cell::RefCell;

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::{Claim, Layout};
use quotient::protocol::{quotient_layout, wiring_layout, witness_layout};
use quotient::transcript::root_scalars;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Context, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{ExecuteCommitEvm, MainBuilder, MainContext};
use revm::interpreter::interpreter_types::{InterpreterTypes, MemoryTr, StackTr};
use revm::interpreter::{InstructionContext, InstructionResult, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256, keccak256};
use revm::state::AccountInfo;

/// The opcode of `FIELD_MUL`, unassigned on mainnet.
pub const FIELD_MUL: u8 = 0x0c;
pub const FIELD_MUL_GAS: u64 = 10;

/// EIP-8141's `FRAMEDATALOAD` and `FRAMEPARAM`, and their gas.
pub const FRAMEDATALOAD: u8 = 0xb1;
pub const FRAMEPARAM: u8 = 0xb3;
const FRAMEDATALOAD_GAS: u64 = 3;
const FRAMEPARAM_GAS: u64 = 2;
const KECCAK256: u8 = 0x20;
/// EIP-8288's mode of a dependency verification frame, and the scheme of PCS claims (the EIP draft's `PCS_SCHEME`).
pub const DEP_VERIFY_FRAME_MODE: u8 = 4;
pub const PCS_SCHEME: u8 = 0x12;

fn element(word: U256) -> F192 {
    let [c0, c1, c2, _] = word.into_limbs();
    F192::new(c0, c1, c2)
}

/// Pops two words and pushes the product of their low 192 bits as elements of `GF(2^192)`.
fn field_mul<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    gas!(context.interpreter, FIELD_MUL_GAS);
    let Some(([a], b)) = context.interpreter.stack.popn_top() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let product = element(a) * element(*b);
    *b = U256::from_limbs([product.c0, product.c1, product.c2, 0]);
}

/// A field element as a claim encodes it: limb 0 lowest, the top 64 bits zero.
pub fn element_word(x: F192) -> [u8; 32] {
    U256::from_limbs([x.c0, x.c1, x.c2, 0]).to_be_bytes()
}

/// A root as a claim encodes it: `s_0 · 2^128 + s_1`, its two scalars as the transcript carries them.
pub fn root_word(root: &Hash) -> [u8; 32] {
    let [s0, s1] = root_scalars(root);
    U256::from_limbs([s1.c0, s1.c1, s0.c0, s0.c1]).to_be_bytes()
}

/// The tables of the membership protocol (`quotient::protocol`), as claims name their layouts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableId {
    Witness = 1,
    Wiring = 2,
    Quotient = 3,
}

/// The rows, `2^log_rows`, for which the block proves claims on the protocol's layouts: where each of its three tables is
/// a stack leanVM's WHIR commits, of `2^15` to `2^28` words in at most 64 lanes, and the two secret ones have
/// hidden layouts (`quotient::protocol::MIN_LOG_ROWS`, `docs/membership/HIDING.md`).
pub const LOG_ROWS: std::ops::RangeInclusive<usize> = quotient::protocol::MIN_LOG_ROWS..=22;

/// The rows of the layouts a block proving claims on tables past WHIR's `2^28` words would know: every size the
/// reduction takes (`quotient::protocol::reduction_supported`).
pub const LARGE_LOG_ROWS: std::ops::RangeInclusive<usize> =
    quotient::protocol::MIN_LOG_ROWS..=quotient::protocol::MAX_REDUCTION_LOG_ROWS;

/// The id of the layout of `table` for a circuit of `2^log_rows` rows: `256 · table + log_rows`.
pub fn layout_id(table: TableId, log_rows: usize) -> u64 {
    assert!(LARGE_LOG_ROWS.contains(&log_rows), "no layout for 2^{log_rows} rows");
    256 * table as u64 + log_rows as u64
}

/// The layout an id names, if the block proves claims on it.
pub fn layout(id: U256) -> Option<Layout> {
    let id = u64::try_from(id).ok()?;
    let log_rows = (id % 256) as usize;
    let table = match id / 256 {
        1 => witness_layout,
        2 => wiring_layout,
        3 => quotient_layout,
        _ => return None,
    };
    LOG_ROWS.contains(&log_rows).then(|| table(log_rows))
}

/// [`layout`] for a block that also proves claims on the larger tables, to [`LARGE_LOG_ROWS`].
pub fn layout_large(id: U256) -> Option<Layout> {
    let id = u64::try_from(id).ok()?;
    let log_rows = (id % 256) as usize;
    let table = match id / 256 {
        1 => witness_layout,
        2 => wiring_layout,
        3 => quotient_layout,
        _ => return None,
    };
    LARGE_LOG_ROWS.contains(&log_rows).then(|| table(log_rows))
}

/// The claim the opening of `claims` on the table committed as `root`, under layout `id`, proves: its bytes.
pub fn claim_input(root: &Hash, id: u64, claims: &[Claim]) -> Vec<u8> {
    let vars = layout_large(U256::from(id)).expect("a layout the block knows").vars;
    assert!(!claims.is_empty() && claims.iter().all(|claim| claim.point.len() == vars));
    let mut input = root_word(root).to_vec();
    input.extend(U256::from(id).to_be_bytes::<32>());
    input.extend(U256::from(claims.len()).to_be_bytes::<32>());
    for claim in claims {
        for &x in claim.point.iter().chain([&claim.value]) {
            input.extend(element_word(x));
        }
    }
    input
}

/// A frame as EIP-8141's introspection shows it: its mode and its `data`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub mode: u8,
    pub data: Vec<u8>,
}

/// A transaction's frame of PCS claims, standing for a block that proves them: payload `j` of its `data` is the
/// Keccak-256 of the `j`-th claim declared. By default it is the transaction's first frame, as [`crate::quotient`]'s
/// calldata names it; [`PcsFrame::before`] puts frames before it, and [`PcsFrame::mode`] and [`PcsFrame::scheme`]
/// make it another kind of frame, for tests.
#[derive(Clone, Debug)]
pub struct PcsFrame {
    claims: Vec<Vec<u8>>,
    /// The transaction's frames before it.
    pub before: Vec<Frame>,
    /// Its mode, `DEP_VERIFY_FRAME_MODE`.
    pub mode: u8,
    /// Its first byte, `PCS_SCHEME`.
    pub scheme: u8,
    /// Every payload read is the hash of what the contract last hashed: a frame declaring whatever the contract
    /// checks, for runs on calldata of no proof.
    pub declare_all: bool,
}

impl Default for PcsFrame {
    fn default() -> Self {
        Self {
            claims: Vec::new(),
            before: Vec::new(),
            mode: DEP_VERIFY_FRAME_MODE,
            scheme: PCS_SCHEME,
            declare_all: false,
        }
    }
}

impl PcsFrame {
    /// A frame declaring whatever the contract checks ([`PcsFrame::declare_all`]).
    pub fn declaring_all() -> Self {
        Self {
            declare_all: true,
            ..Self::default()
        }
    }

    /// Declare, as its next payload, the claim the opening of `claims`, all together, on the table committed as
    /// `root`, under layout `id`, proves.
    pub fn declare(&mut self, root: &Hash, id: u64, claims: &[Claim]) {
        self.declare_input(claim_input(root, id, claims));
    }

    /// Declare a claim of these bytes as its next payload.
    pub fn declare_input(&mut self, input: Vec<u8>) {
        self.claims.push(input);
    }

    /// The claims declared, in order.
    pub fn claims(&self) -> &[Vec<u8>] {
        &self.claims
    }

    /// Its `data`: its scheme, then each claim's hash.
    pub fn data(&self) -> Vec<u8> {
        let mut data = vec![self.scheme];
        self.claims.iter().for_each(|claim| data.extend(keccak256(claim).0));
        data
    }

    /// The transaction's frames: those before it, then it.
    pub fn frames(&self) -> Vec<Frame> {
        let mut frames = self.before.clone();
        frames.push(Frame {
            mode: self.mode,
            data: self.data(),
        });
        frames
    }
}

/// A transaction's intrinsic gas for `claims` PCS claims (the EIP draft): `5,000` if it has any, and `1,000` a claim.
pub fn dependency_gas(claims: usize) -> u64 {
    if claims == 0 { 0 } else { 5_000 + 1_000 * claims as u64 }
}

/// The running transaction's frames, and what its contract hashed and checked.
#[derive(Default)]
struct Running {
    frames: Vec<Frame>,
    declare_all: bool,
    /// The bytes the last `KECCAK256` hashed.
    last: Vec<u8>,
    /// Before each read of a payload (a frame's `data` past its first byte), what the last `KECCAK256` hashed: the
    /// claims the contract checked.
    checked: Vec<Vec<u8>>,
}

thread_local! {
    static RUNNING: RefCell<Running> = RefCell::default();
}

/// `FRAMEPARAM`: the mode (`0x02`) or the length of `data` (`0x04`) of a frame of the transaction; another parameter,
/// or a frame it does not have, halts.
fn frame_param<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    gas!(context.interpreter, FRAMEPARAM_GAS);
    let Some(([index], param)) = context.interpreter.stack.popn_top() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let value = RUNNING.with_borrow(|running| {
        let frame = running.frames.get(usize::try_from(index).ok()?)?;
        match u8::try_from(*param).ok()? {
            0x02 => Some(U256::from(frame.mode)),
            0x04 => Some(U256::from(frame.data.len())),
            _ => None,
        }
    });
    match value {
        Some(value) => *param = value,
        None => context.interpreter.halt(InstructionResult::InvalidFEOpcode),
    }
}

/// `FRAMEDATALOAD`: the word of a frame's `data` at an offset, zero past its end, as `CALLDATALOAD`; a frame the
/// transaction does not have halts. A read past the first byte keeps what the last `KECCAK256` hashed, as a claim
/// checked; with [`PcsFrame::declare_all`], it reads that hash.
fn frame_data_load<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    gas!(context.interpreter, FRAMEDATALOAD_GAS);
    let Some(([offset], index)) = context.interpreter.stack.popn_top() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let offset = usize::try_from(offset).unwrap_or(usize::MAX);
    let word = RUNNING.with_borrow_mut(|running| {
        let data = &running.frames.get(usize::try_from(*index).ok()?)?.data;
        let mut word = [0u8; 32];
        if offset < data.len() {
            let n = 32.min(data.len() - offset);
            word[..n].copy_from_slice(&data[offset..offset + n]);
        }
        if offset >= 1 {
            let last = running.last.clone();
            if running.declare_all {
                word = keccak256(&last).0;
            }
            running.checked.push(last);
        }
        Some(U256::from_be_bytes(word))
    });
    match word {
        Some(word) => *index = word,
        None => context.interpreter.halt(InstructionResult::InvalidFEOpcode),
    }
}

/// `KECCAK256`, as revm's, keeping the bytes it hashed.
fn keccak256_keeping<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    let Some([offset, len]) = context.interpreter.stack.popn() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let Ok(len) = usize::try_from(len) else {
        context.interpreter.halt(InstructionResult::InvalidOperandOOG);
        return;
    };
    match gas::keccak256_cost(len) {
        Some(cost) if context.interpreter.gas.record_cost(cost) => {}
        _ => {
            context.interpreter.halt(InstructionResult::OutOfGas);
            return;
        }
    }
    let bytes = if len == 0 {
        Vec::new()
    } else {
        let Ok(from) = usize::try_from(offset) else {
            context.interpreter.halt(InstructionResult::InvalidOperandOOG);
            return;
        };
        if !context.interpreter.resize_memory(from, len) {
            context.interpreter.halt(InstructionResult::MemoryOOG);
            return;
        }
        context.interpreter.memory.slice_len(from, len).to_vec()
    };
    let hash = keccak256(&bytes);
    RUNNING.with_borrow_mut(|running| running.last = bytes);
    let _ = context.interpreter.stack.push(U256::from_be_bytes(hash.0));
}

/// What a transaction did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned (a creation: the code it deployed), or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of its execution: the transaction's without its base cost, its calldata, its frames' `data` and its
    /// claims' intrinsic gas ([`dependency_gas`]). A creation's includes its 32,000, its init code's 2 a word and its code's deposit, 200 a byte.
    pub execution: u64,
    /// The claims it checked against its frame of PCS claims, in order: what it hashed before each payload read.
    pub claims: Vec<Vec<u8>>,
}

/// A transaction's gas: its base cost, then the larger of its calldata at the standard rate plus `execution`, and
/// of its calldata at the floor rate, `floor` gas a nonzero byte. EIP-7623 has a floor of 40, and 10 for a zero
/// byte; EIP-7976 has 64 for every byte.
pub fn transaction_gas(calldata: &[u8], execution: u64, floor: u64) -> u64 {
    let zeros = calldata.iter().filter(|&&byte| byte == 0).count() as u64;
    let nonzeros = calldata.len() as u64 - zeros;
    let floor_gas = floor * nonzeros + if floor == 64 { 64 } else { floor / 4 } * zeros;
    21_000 + (16 * nonzeros + 4 * zeros + execution).max(floor_gas)
}

/// Who deploys contracts.
pub const DEPLOYER: Address = Address::with_last_byte(0xde);
/// Who calls them, unless said otherwise.
pub const CALLER: Address = Address::with_last_byte(0xca);

/// The accounts transactions run on: the senders' and the contracts deployed.
#[derive(Clone, Default)]
pub struct Chain {
    db: CacheDB<EmptyDB>,
}

impl Chain {
    /// Run a transaction from `from`, sending `value` wei, whose frame of PCS claims is `pcs`, and keep
    /// what it changes; and the address of the contract it created, if any. Each transaction starts cold
    /// (EIP-2929): its first `SLOAD` of a slot costs 2,100.
    pub(crate) fn run(
        &mut self,
        from: Address,
        to: TxKind,
        data: &[u8],
        value: U256,
        pcs: &PcsFrame,
    ) -> (Outcome, Option<Address>) {
        // Senders have funds for the value; gas is free.
        let nonce = self
            .db
            .cache
            .accounts
            .get(&from)
            .map_or(0, |account| account.info.nonce);
        let balance = U256::from(10u64.pow(18));
        self.db
            .insert_account_info(from, AccountInfo::from_balance(balance).with_nonce(nonce));
        // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
        let mut evm = Context::mainnet()
            .with_db(&mut self.db)
            .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
            .build_mainnet();
        evm.instruction.insert_instruction(FIELD_MUL, field_mul);
        evm.instruction.insert_instruction(FRAMEPARAM, frame_param);
        evm.instruction.insert_instruction(FRAMEDATALOAD, frame_data_load);
        evm.instruction.insert_instruction(KECCAK256, keccak256_keeping);
        RUNNING.set(Running {
            frames: pcs.frames(),
            declare_all: pcs.declare_all,
            ..Running::default()
        });
        let tx = TxEnv::builder()
            .caller(from)
            .nonce(nonce)
            .kind(to)
            .value(value)
            .data(Bytes::copy_from_slice(data))
            .gas_limit(10_000_000)
            .build()
            .expect("a transaction");
        let result = evm.transact_commit(tx).expect("a valid transaction");
        let claims = RUNNING.take().checked;
        let execution = result.gas_used() - transaction_gas(data, 0, 0);
        let (output, created) = match result {
            ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } => (Some(output.to_vec()), None),
            ExecutionResult::Success {
                output: Output::Create(output, created),
                ..
            } => (Some(output.to_vec()), created),
            _ => (None, None),
        };
        (Outcome { output, execution, claims }, created)
    }

    /// Deploy a contract by a transaction of `init_code` from [`DEPLOYER`]: its address, unless the creation
    /// failed, and the transaction's outcome.
    pub fn deploy(&mut self, init_code: &[u8]) -> (Option<Address>, Outcome) {
        let (outcome, created) = self.run(DEPLOYER, TxKind::Create, init_code, U256::ZERO, &PcsFrame::default());
        (created, outcome)
    }

    /// Send `calldata` and `value` wei from `from` to `to`, in a transaction whose frame of PCS claims is `pcs`, and
    /// keep what it changes.
    pub fn transact(
        &mut self,
        from: Address,
        to: Address,
        calldata: &[u8],
        value: U256,
        pcs: &PcsFrame,
    ) -> Outcome {
        self.run(from, TxKind::Call(to), calldata, value, pcs).0
    }

    /// The same from [`CALLER`] with no value, leaving the chain as it was.
    pub fn call(&self, to: Address, calldata: &[u8], pcs: &PcsFrame) -> Outcome {
        self.clone().transact(CALLER, to, calldata, U256::ZERO, pcs)
    }

    /// The code of the account at `address`.
    pub fn code(&self, address: Address) -> Vec<u8> {
        let account = self.db.cache.accounts.get(&address);
        let code = account.and_then(|account| account.info.code.as_ref());
        code.map_or_else(Vec::new, |code| code.original_byte_slice().to_vec())
    }

    /// The word in storage slot `slot` of the account at `address`.
    pub fn storage(&self, address: Address, slot: U256) -> U256 {
        let account = self.db.cache.accounts.get(&address);
        account
            .and_then(|account| account.storage.get(&slot).copied())
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every layout the block knows is a stack leanVM's WHIR commits, and the ids name distinct openings' prefixes
    /// (`quotient::opening::prefix`); ids outside the table name none.
    #[test]
    fn layouts_are_known_by_id() {
        let mut prefixes = std::collections::HashSet::new();
        for log_rows in LOG_ROWS {
            for table in [TableId::Witness, TableId::Wiring, TableId::Quotient] {
                let layout = layout(U256::from(layout_id(table, log_rows))).expect("a layout");
                assert!((15..=28).contains(&layout.log_n) && layout.lanes() <= 64);
                assert!(
                    prefixes.insert(quotient::opening::prefix(&layout)),
                    "{table:?}, 2^{log_rows} rows"
                );
            }
        }
        for id in [0u64, 12, 256 + 12, 256 + 23, 4 * 256 + 22, 1 << 40] {
            assert_eq!(layout(U256::from(id)), None, "{id}");
        }
        assert_eq!(layout(U256::MAX), None);
    }

    /// A frame of PCS claims: its scheme byte, then each claim's Keccak-256, after the frames before it.
    #[test]
    fn frame_data_is_the_claims_hashes() {
        let mut pcs = PcsFrame::default();
        pcs.declare_input(vec![1, 2, 3]);
        pcs.declare_input(Vec::new());
        let data = pcs.data();
        assert_eq!(data.len(), 1 + 64);
        assert_eq!(data[0], PCS_SCHEME);
        assert_eq!(&data[1..33], &keccak256([1, 2, 3]).0[..]);
        assert_eq!(&data[33..], &keccak256([]).0[..]);
        pcs.before.push(Frame { mode: 0, data: vec![7] });
        let frames = pcs.frames();
        assert_eq!(frames.len(), 2);
        assert_eq!(frames[1], Frame { mode: DEP_VERIFY_FRAME_MODE, data });
        assert_eq!((dependency_gas(0), dependency_gas(3)), (0, 8_000));
    }

    /// The root's word is its two scalars, the high one first.
    #[test]
    fn root_word_is_its_scalars() {
        let root: Hash = std::array::from_fn(|i| i as u8 + 1);
        let word = root_word(&root);
        let mut halves = [root[..16].to_vec(), root[16..].to_vec()];
        halves.iter_mut().for_each(|half| half.reverse());
        assert_eq!(word.to_vec(), halves.concat());
    }
}
