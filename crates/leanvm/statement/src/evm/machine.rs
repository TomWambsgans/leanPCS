// Adapted from this repository's crates/membership/evm/src/machine.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): revm with `FIELD_MUL`
// and EIP-8141's frame introspection over a frame of PCS claims, the same opcodes, claim encoding and transaction gas,
// and a `Chain` that deploys contracts and keeps them across transactions; here the frame may declare claims of any
// layout word, code may also be installed rather than deployed (it may pass EIP-170's limit), and an inspector gives
// every instruction's gas, in every contract a call runs. MIT OR Apache-2.0; see AGENTS.md.
//! revm with `FIELD_MUL`, EIP-8141's frame introspection over a transaction's frame of PCS claims, and
//! per-instruction gas.
//!
//! A contract checks that its transaction declares the claims it leaves: each claim's Keccak-256 is a payload of the
//! frame of PCS claims calldata names (the EIP draft, `eip-draft_leanPCS.md`; `crates/membership/evm/src/machine.rs`),
//! read with `FRAMEPARAM` (`0xb3`) and `FRAMEDATALOAD` (`0xb1`). A claim is this repository's: `3 + k (v + 1)` words,
//! the commitment's root word, the layout's id, `k`, then each claim's `v` coordinates and its value, a field element
//! being the low 192 bits of its word. It is every claim on its commitment, as one opening proves them.
//!
//! [`PcsFrame`] declares claims in two ways. **Byte strings** ([`PcsFrame::declare`]): what
//! `crates/leanvm/univariate`'s vectors use. **Openings** of known layouts ([`PcsFrame::decoding`],
//! [`PcsFrame::declare_opening`]): a registry keyed by the layout word, whose openings it encodes ([`Opening::input`]);
//! [`decode`] reads a claim back under that encoding (the root word `s_0 · 2^128 + s_1` of [`root_word`], a layout
//! word the registry knows, which fixes `v`, `k ≥ 1`, the exact length, every element's top 64 bits zero). A frame
//! declaring everything ([`PcsFrame::declaring_all`]), for measuring runs, then declares only claims that decode.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::field::E;
use revm::bytecode::Bytecode;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Context, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{ExecuteCommitEvm, MainBuilder, MainContext};
use revm::inspector::{InspectCommitEvm, Inspector};
use revm::interpreter::interpreter_types::{InputsTr, InterpreterTypes, Jumps, MemoryTr, StackTr};
use revm::interpreter::{CallInputs, CallOutcome, InstructionContext, InstructionResult, Interpreter, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256, keccak256};
use revm::state::AccountInfo;

/// The opcode of `FIELD_MUL`, the EIP draft's `MULFIELD` (`0x1f`, unassigned on mainnet).
pub const FIELD_MUL: u8 = 0x1f;
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
/// The index of the transaction's frame of PCS claims the contracts' calldata names: the first frame.
pub const PCS_FRAME: u8 = 0;

/// Where the contract is installed, and who calls it.
pub const VERIFIER: Address = Address::with_last_byte(0xc0);
pub const CALLER: Address = Address::with_last_byte(0xca);
/// Who deploys contracts.
pub const DEPLOYER: Address = Address::with_last_byte(0xde);

fn element(word: U256) -> E {
    let [c0, c1, c2, _] = word.into_limbs();
    E::new(c0, c1, c2)
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
pub fn element_word(x: E) -> [u8; 32] {
    U256::from_limbs([x.c0, x.c1, x.c2, 0]).to_be_bytes()
}

/// A claim's root word (`crates/membership/evm/src/machine.rs`): `s_0 · 2^128 + s_1`, `s_h` the little-endian number of the
/// root's bytes `16 h .. 16 h + 16`, that is each 16-byte half reversed. Its own inverse.
pub fn root_word(root: &[u8; 32]) -> [u8; 32] {
    let mut out = *root;
    out[..16].reverse();
    out[16..].reverse();
    out
}

/// The root a root word names ([`root_word`] is an involution).
pub fn root_of_word(word: &[u8; 32]) -> [u8; 32] {
    root_word(word)
}

/// A claim, decoded: the commitment's root (as its opening has it), the layout word, the claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub root: [u8; 32],
    pub layout: [u8; 32],
    pub claims: Vec<(Vec<E>, E)>,
}

impl Opening {
    /// The input that names this opening: [`decode`]'s inverse.
    pub fn input(&self) -> Vec<u8> {
        let mut out = root_word(&self.root).to_vec();
        out.extend(self.layout);
        out.extend(U256::from(self.claims.len()).to_be_bytes::<32>());
        for (point, value) in &self.claims {
            for &x in point.iter().chain([value]) {
                out.extend(element_word(x));
            }
        }
        out
    }
}

/// Decode `input` under the claims' encoding, the table's variables `vars(layout word)` (`None`: a layout the
/// registry does not know). `None` unless the input is exactly `3 + k (v + 1)` words with `1 ≤ k`, and every element's top 64 bits are
/// zero.
pub fn decode(input: &[u8], vars: impl Fn(&[u8; 32]) -> Option<usize>) -> Option<Opening> {
    let word = |k: usize| -> Option<[u8; 32]> { input.get(32 * k..32 * k + 32)?.try_into().ok() };
    let (root, layout, count) = (word(0)?, word(1)?, word(2)?);
    let v = vars(&layout)?;
    if count[..24].iter().any(|&b| b != 0) {
        return None;
    }
    let k = u64::from_be_bytes(count[24..].try_into().ok()?) as usize;
    if k == 0 || input.len() != 32 * (3 + k * (v + 1)) {
        return None;
    }
    let element = |w: [u8; 32]| -> Option<E> {
        if w[..8].iter().any(|&b| b != 0) {
            return None;
        }
        let [c0, c1, c2, _] = U256::from_be_bytes(w).into_limbs();
        Some(E::new(c0, c1, c2))
    };
    let mut claims = Vec::with_capacity(k);
    for c in 0..k {
        let at = 3 + c * (v + 1);
        let point = (0..v).map(|j| element(word(at + j)?)).collect::<Option<Vec<E>>>()?;
        claims.push((point, element(word(at + v)?)?));
    }
    Some(Opening {
        root: root_of_word(&root),
        layout,
        claims,
    })
}

/// A frame as EIP-8141's introspection shows it: its mode and its `data`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub mode: u8,
    pub data: Vec<u8>,
}

/// A transaction's frame of PCS claims, standing for a block that proves them: payload `j` of its `data` is the
/// Keccak-256 of the `j`-th claim declared. It is the transaction's first frame ([`PCS_FRAME`]) unless
/// [`PcsFrame::before`] puts frames before it.
#[derive(Clone, Debug)]
pub struct PcsFrame {
    claims: Vec<Vec<u8>>,
    /// The registry of layouts (layout word → the table's variables) whose openings it declares, and those openings.
    layouts: HashMap<[u8; 32], usize>,
    openings: Vec<Opening>,
    /// Every payload read is the hash of what the contract last hashed, if that decodes under a known layout (any,
    /// without a registry): a measuring run, whose claims are not those of a valid proof.
    pub declare_all: bool,
    /// The transaction's frames before it.
    pub before: Vec<Frame>,
    /// Its mode and its first byte: `DEP_VERIFY_FRAME_MODE` and `PCS_SCHEME`.
    pub mode: u8,
    pub scheme: u8,
}

impl Default for PcsFrame {
    fn default() -> Self {
        Self {
            claims: Vec::new(),
            layouts: HashMap::new(),
            openings: Vec::new(),
            declare_all: false,
            before: Vec::new(),
            mode: DEP_VERIFY_FRAME_MODE,
            scheme: PCS_SCHEME,
        }
    }
}

impl PcsFrame {
    /// A frame declaring whatever the contract checks: a measuring run.
    pub fn declaring_all() -> Self {
        Self {
            declare_all: true,
            ..Self::default()
        }
    }

    /// Declare a claim of these bytes as its next payload.
    pub fn declare(&mut self, input: Vec<u8>) {
        assert!(self.layouts.is_empty(), "a registry declares openings, not inputs");
        self.claims.push(input);
    }

    /// A frame that declares openings of these layouts (layout word, the table's variables).
    pub fn decoding(layouts: impl IntoIterator<Item = ([u8; 32], usize)>) -> Self {
        let layouts: HashMap<[u8; 32], usize> = layouts.into_iter().collect();
        assert!(!layouts.is_empty(), "a registry of at least one layout");
        Self {
            layouts,
            ..Self::default()
        }
    }

    /// Declare an opening, of a known layout, as its next payload: its root, layout word and claims.
    pub fn declare_opening(&mut self, opening: Opening) {
        let v = self.layouts.get(&opening.layout).expect("a layout the registry knows");
        assert!(!opening.claims.is_empty() && opening.claims.iter().all(|(p, _)| p.len() == *v));
        self.claims.push(opening.input());
        self.openings.push(opening);
    }

    /// `input` decoded as the registry's claims are encoded.
    pub fn decode(&self, input: &[u8]) -> Option<Opening> {
        decode(input, |w| self.layouts.get(w).copied())
    }

    /// Whether a contract checking the claim `input` as payload `index` finds it declared.
    pub fn declares(&self, input: &[u8], index: usize) -> bool {
        if self.declare_all {
            self.layouts.is_empty() || self.decode(input).is_some()
        } else {
            self.claims.get(index).is_some_and(|claim| claim == input)
        }
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

/// What declares a claim whatever it is, in a measuring run.
type DeclareAll = Box<dyn Fn(&[u8]) -> bool>;

/// The running transaction's frames, and what its contract hashed and checked.
#[derive(Default)]
struct Running {
    frames: Vec<Frame>,
    declare_all: Option<DeclareAll>,
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
/// checked; in a measuring run it reads that hash, if the run declares it.
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
            if running.declare_all.as_ref().is_some_and(|declares| declares(&last)) {
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

/// A call frame being run: whose code, and its last instruction started (its pc and the gas left then).
struct FrameGas {
    code: Address,
    last: Option<(usize, u64)>,
    /// The gas left after its last instruction ran (for the one that ends it).
    end: u64,
    /// Gas its finished calls' frames spent since its last instruction started, which that instruction's drop holds.
    children: u64,
    /// Gas attributed to its instructions and to its calls' frames.
    total: u64,
}

impl FrameGas {
    fn new(code: Address) -> Self {
        Self {
            code,
            last: None,
            end: 0,
            children: 0,
            total: 0,
        }
    }
}

/// The gas of each instruction, by the code it is in and its program counter: what its frame's gas left drops by
/// between the start of the instruction and the start of the next, less what the frames of its calls spent (a call
/// of a precompile runs no instructions: its gas is the call's).
#[derive(Default)]
struct GasByPc {
    sizes: Vec<(Address, usize)>,
    gas: Vec<(Address, Vec<u64>)>,
    frames: Vec<FrameGas>,
}

impl GasByPc {
    fn charge(&mut self, code: Address, pc: usize, gas: u64) {
        let at = match self.gas.iter().position(|(address, _)| *address == code) {
            Some(at) => at,
            None => {
                let size = self
                    .sizes
                    .iter()
                    .find(|(address, _)| *address == code)
                    .map_or(0, |s| s.1);
                self.gas.push((code, vec![0; size + 1]));
                self.gas.len() - 1
            }
        };
        let counts = &mut self.gas[at].1;
        if counts.len() <= pc {
            counts.resize(pc + 1, 0);
        }
        counts[pc] += gas;
    }

    /// The frame on top ended: its last instruction's gas, and its total to its caller's.
    fn finish(&mut self) {
        let frame = self.frames.pop().expect("a frame");
        let mut total = frame.total;
        if let Some((pc, before)) = frame.last {
            let gas = before - frame.end - frame.children;
            self.charge(frame.code, pc, gas);
            total += gas + frame.children;
        }
        if let Some(caller) = self.frames.last_mut() {
            caller.children += total;
        }
    }
}

impl<CTX, INTR: InterpreterTypes> Inspector<CTX, INTR> for GasByPc {
    fn step(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        let (pc, left) = (interp.bytecode.pc(), interp.gas.remaining());
        let code = interp
            .input
            .bytecode_address()
            .copied()
            .unwrap_or_else(|| interp.input.target_address());
        if self.frames.is_empty() {
            self.frames.push(FrameGas::new(code));
        }
        let frame = self.frames.last_mut().expect("a frame");
        frame.code = code;
        let previous = frame.last.replace((pc, left));
        let children = std::mem::take(&mut frame.children);
        if let Some((last, before)) = previous {
            let gas = before - left - children;
            frame.total += gas + children;
            self.charge(code, last, gas);
        }
    }

    fn step_end(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        if let Some(frame) = self.frames.last_mut() {
            frame.end = interp.gas.remaining();
        }
    }

    fn call(&mut self, _context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.frames.push(FrameGas::new(inputs.bytecode_address));
        None
    }

    fn call_end(&mut self, _context: &mut CTX, _inputs: &CallInputs, _outcome: &mut CallOutcome) {
        self.finish();
    }
}

/// What a call did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned, or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of its execution: the transaction's without its base cost, its calldata, its frames' `data` and its
    /// claims' intrinsic gas ([`dependency_gas`]).
    pub execution: u64,
    /// Each instruction's gas, by program counter, of the code called.
    pub gas_by_pc: Vec<u64>,
    /// The same, of every code that ran, by its address.
    pub gas_by_code: Vec<(Address, Vec<u64>)>,
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

/// Call `code`, installed at [`VERIFIER`] with storage `storage` (slot, word), with `calldata`, from [`CALLER`], in a
/// transaction whose frame of PCS claims is `pcs`; the transaction starts cold (EIP-2929).
pub fn call(code: &[u8], storage: &[(u8, [u8; 32])], calldata: &[u8], pcs: &PcsFrame) -> Outcome {
    let mut chain = Chain::default();
    chain.install(VERIFIER, code);
    for &(slot, word) in storage {
        chain.store(VERIFIER, slot, word);
    }
    chain.call(VERIFIER, calldata, pcs)
}

/// The accounts transactions run on, kept across them.
#[derive(Clone, Default)]
pub struct Chain {
    db: CacheDB<EmptyDB>,
}

/// A transaction's output (a creation's: the code), its execution gas (a creation's includes its 32,000, its init
/// code's 2 a word and its code's deposit, 200 a byte), and the address it created.
type Run = (Option<Vec<u8>>, u64, Option<Address>);

impl Chain {
    /// Put `code` at `address`, as if deployed.
    pub fn install(&mut self, address: Address, code: &[u8]) {
        let account = AccountInfo::default().with_code(Bytecode::new_raw(Bytes::copy_from_slice(code)));
        self.db.insert_account_info(address, account);
    }

    pub fn store(&mut self, address: Address, slot: u8, word: [u8; 32]) {
        self.db
            .insert_account_storage(address, U256::from(slot), U256::from_be_bytes(word))
            .expect("an account");
    }

    /// The code at `address`.
    pub fn code(&self, address: Address) -> Vec<u8> {
        let account = self.db.cache.accounts.get(&address);
        let code = account.and_then(|account| account.info.code.as_ref());
        code.map_or_else(Vec::new, |code| code.original_byte_slice().to_vec())
    }

    /// The word in storage slot `slot` of the account at `address`.
    pub fn storage(&self, address: Address, slot: u8) -> [u8; 32] {
        let account = self.db.cache.accounts.get(&address);
        let word = account.and_then(|account| account.storage.get(&U256::from(slot)).copied());
        word.unwrap_or_default().to_be_bytes()
    }

    /// Deploy `init_code` by a transaction from [`DEPLOYER`] (EIP-170's and EIP-3860's limits enforced): the address,
    /// unless the creation failed, and the transaction's execution gas.
    pub fn deploy(&mut self, init_code: &[u8]) -> (Option<Address>, u64) {
        let (_, execution, created) = self.transact(DEPLOYER, TxKind::Create, init_code, &PcsFrame::default(), None);
        (created, execution)
    }

    /// Call `to` with `calldata`, from [`CALLER`], in a transaction whose frame of PCS claims is `pcs`, leaving the
    /// chain as it was; each instruction's gas, by code.
    pub fn call(&self, to: Address, calldata: &[u8], pcs: &PcsFrame) -> Outcome {
        let mut chain = self.clone();
        let mut inspector = GasByPc::default();
        for (address, account) in &chain.db.cache.accounts {
            let size = account
                .info
                .code
                .as_ref()
                .map_or(0, |code| code.original_byte_slice().len());
            inspector.sizes.push((*address, size));
        }
        let mut claims = Vec::new();
        let (output, execution, _) = chain.transact(
            CALLER,
            TxKind::Call(to),
            calldata,
            pcs,
            Some((&mut inspector, &mut claims)),
        );
        while !inspector.frames.is_empty() {
            inspector.finish();
        }
        let gas_by_pc = inspector
            .gas
            .iter()
            .find(|(address, _)| *address == to)
            .map_or_else(Vec::new, |(_, gas)| gas.clone());
        Outcome {
            output,
            execution,
            gas_by_pc,
            gas_by_code: inspector.gas,
            claims,
        }
    }

    fn transact(
        &mut self,
        from: Address,
        to: TxKind,
        data: &[u8],
        pcs: &PcsFrame,
        inspect: Option<(&mut GasByPc, &mut Vec<Vec<u8>>)>,
    ) -> Run {
        let nonce = self
            .db
            .cache
            .accounts
            .get(&from)
            .map_or(0, |account| account.info.nonce);
        self.db.insert_account_info(
            from,
            AccountInfo::from_balance(U256::from(10u64.pow(18))).with_nonce(nonce),
        );
        let tx = TxEnv::builder()
            .caller(from)
            .nonce(nonce)
            .kind(to)
            .data(Bytes::copy_from_slice(data))
            .gas_limit(100_000_000)
            .build()
            .expect("a transaction");
        let declare_all: Option<DeclareAll> = pcs.declare_all.then(|| {
            let registry = pcs.clone();
            Box::new(move |input: &[u8]| registry.declares(input, 0)) as DeclareAll
        });
        RUNNING.set(Running {
            frames: pcs.frames(),
            declare_all,
            ..Running::default()
        });
        // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
        let context = Context::mainnet()
            .with_db(&mut self.db)
            .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
            .modify_block_chained(|block| block.gas_limit = u64::MAX);
        let result = match inspect {
            Some((inspector, calls)) => {
                let mut evm = context.build_mainnet_with_inspector(std::mem::take(inspector));
                evm.instruction.insert_instruction(FIELD_MUL, field_mul);
                evm.instruction.insert_instruction(FRAMEPARAM, frame_param);
                evm.instruction.insert_instruction(FRAMEDATALOAD, frame_data_load);
                evm.instruction.insert_instruction(KECCAK256, keccak256_keeping);
                let result = evm.inspect_tx_commit(tx).expect("a valid transaction");
                *inspector = std::mem::take(&mut evm.inspector);
                *calls = RUNNING.take().checked;
                result
            }
            None => {
                let mut evm = context.build_mainnet();
                evm.instruction.insert_instruction(FIELD_MUL, field_mul);
                evm.instruction.insert_instruction(FRAMEPARAM, frame_param);
                evm.instruction.insert_instruction(FRAMEDATALOAD, frame_data_load);
                evm.instruction.insert_instruction(KECCAK256, keccak256_keeping);
                let result = evm.transact_commit(tx).expect("a valid transaction");
                RUNNING.take();
                result
            }
        };
        let execution = result.gas_used() - transaction_gas(data, 0, 0);
        match result {
            ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } => (Some(output.to_vec()), execution, None),
            ExecutionResult::Success {
                output: Output::Create(output, created),
                ..
            } => (Some(output.to_vec()), execution, created),
            _ => (None, execution, None),
        }
    }
}
