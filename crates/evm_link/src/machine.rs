// Part of this repository; merged from crates/membership/evm/src/machine.rs (adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6: revm with `FIELD_MUL`)
// and crates/leanvm/statement/src/evm/machine.rs (adapted from it): EIP-8141's frame introspection over a frame of PCS
// claims, a `Chain` that deploys or installs contracts and keeps their storage across transactions, and every
// instruction's gas. MIT OR Apache-2.0; see AGENTS.md.
//! The EVM the contracts run on in tests: revm with `FIELD_MUL`, EIP-8141's frame introspection over a transaction's
//! frame of PCS claims, and per-instruction gas.
//!
//! # PCS claims
//!
//! A transaction declares the claims its contract checks in a frame of PCS claims (the EIP draft,
//! `eip-draft_leanPCS.md`): an EIP-8288 dependency verification frame whose `data` is `PCS_SCHEME` then the
//! Keccak-256 of each claim ([`crate::wire`]), which the block's aggregated proof proves. The contract finds them with
//! EIP-8141's introspection, which this machine has: `FRAMEPARAM` (`0xb3`, 2 gas; the mode and the length of `data`)
//! and `FRAMEDATALOAD` (`0xb1`, 3 gas). [`PcsFrame`] is such a frame, standing for a block that proves its claims.
//!
//! **Gas.** A transaction with `c` PCS claims pays `pcs_gas = 5,000 + 1,000 c` ([`dependency_gas`]), apart from what
//! this machine measures, and its frame of PCS claims is `1 + 32 c` bytes of the transaction. Under EIP-8141 a frame
//! transaction pays the larger of its standard gas (16 a nonzero byte and 4 a zero byte of its frames' data, plus
//! execution) and its floor (64 a byte, EIP-7976), the EIP draft adding `pcs_gas` to both ([`frame_tx_gas`]).

use std::cell::RefCell;

use primitives::field::F192;
use revm::bytecode::Bytecode;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Context, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{MainBuilder, MainContext};
use revm::inspector::{InspectCommitEvm, Inspector};
use revm::interpreter::interpreter_types::{InputsTr, InterpreterTypes, Jumps, MemoryTr, StackTr};
use revm::interpreter::{CallInputs, CallOutcome, InstructionContext, InstructionResult, Interpreter, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256, keccak256};
use revm::state::AccountInfo;

use crate::op::{DEP_VERIFY_FRAME_MODE, FIELD_MUL, FRAMEDATALOAD, FRAMEPARAM, FRAMEPARAM_MODE, KECCAK256, PCS_SCHEME};

/// The gas of `FIELD_MUL` (the EIP draft's `MULFIELD`), of EIP-8141's `FRAMEDATALOAD` and `FRAMEPARAM`.
pub const FIELD_MUL_GAS: u64 = 10;
const FRAMEDATALOAD_GAS: u64 = 3;
const FRAMEPARAM_GAS: u64 = 2;
/// `FRAMEPARAM`'s parameter of the length of a frame's `data`.
const FRAMEPARAM_LEN: u8 = 0x04;

/// The index of the transaction's frame of PCS claims the contracts' calldata names: the first frame.
pub const PCS_FRAME: u8 = 0;

/// Where [`call`] installs a contract.
pub const VERIFIER: Address = Address::with_last_byte(0xc0);
/// Who calls contracts, unless said otherwise.
pub const CALLER: Address = Address::with_last_byte(0xca);
/// Who deploys contracts.
pub const DEPLOYER: Address = Address::with_last_byte(0xde);

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

/// A frame as EIP-8141's introspection shows it: its mode and its `data`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub mode: u8,
    pub data: Vec<u8>,
}

/// A transaction's frame of PCS claims, standing for a block that proves them: payload `j` of its `data` is the
/// Keccak-256 of the `j`-th claim declared (an encoded PCS claim, [`crate::wire`]). It is the transaction's first frame
/// ([`PCS_FRAME`]) unless [`PcsFrame::before`] puts frames before it; [`PcsFrame::mode`] and [`PcsFrame::scheme`] make
/// it another kind of frame, for tests.
#[derive(Clone, Debug)]
pub struct PcsFrame {
    claims: Vec<Vec<u8>>,
    /// The payloads the contract reads as public data (π2's, of π1's claims hashed in its circuit), not as a claim's
    /// check: [`Outcome::claims`] leaves their reads out.
    pub read: Vec<usize>,
    /// The transaction's frames before it.
    pub before: Vec<Frame>,
    /// Its mode, `DEP_VERIFY_FRAME_MODE`.
    pub mode: u8,
    /// Its first byte, `PCS_SCHEME`.
    pub scheme: u8,
}

impl Default for PcsFrame {
    fn default() -> Self {
        Self {
            claims: Vec::new(),
            read: Vec::new(),
            before: Vec::new(),
            mode: DEP_VERIFY_FRAME_MODE,
            scheme: PCS_SCHEME,
        }
    }
}

impl PcsFrame {
    /// A frame declaring these claims (encoded), in order.
    pub fn of(claims: impl IntoIterator<Item = Vec<u8>>) -> Self {
        Self {
            claims: claims.into_iter().collect(),
            ..Self::default()
        }
    }

    /// Declare a claim (its encoding) as its next payload.
    pub fn declare(&mut self, claim: Vec<u8>) {
        self.claims.push(claim);
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

    /// The gas of a frame transaction of a verifying call of `calldata` and `execution` with this frame
    /// ([`frame_tx_gas`]).
    pub fn tx_gas(&self, calldata: &[u8], execution: u64) -> FrameTxGas {
        frame_tx_gas(calldata, execution, &self.data(), self.claims.len())
    }
}

/// A transaction's intrinsic gas for `claims` PCS claims (the EIP draft): `5,000` if it has any, and `1,000` a claim.
pub fn dependency_gas(claims: usize) -> u64 {
    if claims == 0 { 0 } else { 5_000 + 1_000 * claims as u64 }
}

/// Bytes at the standard rate: 16 gas a nonzero byte, 4 a zero byte.
pub fn calldata_gas(data: &[u8]) -> u64 {
    data.iter().map(|&byte| if byte == 0 { 4 } else { 16 }).sum()
}

/// A frame transaction's gas (EIP-8141, whose calldata floor is EIP-7976's), without `FRAME_TX_INTRINSIC_COST` and
/// the per-frame costs: the verifying frame's `calldata` and `execution`, and the frame of PCS claims' `data` with
/// its `claims` claims' gas (the EIP draft's `pcs_gas`, [`dependency_gas`], added to both sides).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameTxGas {
    /// Every frame's data at 16 gas a nonzero byte and 4 a zero byte, the execution, the PCS gas.
    pub standard: u64,
    /// Every frame's data at 64 gas a byte (EIP-7976's floor), the PCS gas.
    pub floor: u64,
    /// The larger: what the transaction pays.
    pub total: u64,
}

/// [`FrameTxGas`] of a verifying call: `calldata`, its `execution`, and its frame of PCS claims ([`PcsFrame::data`]
/// and the number of claims; an empty `pcs_data` and `claims = 0` for none).
pub fn frame_tx_gas(calldata: &[u8], execution: u64, pcs_data: &[u8], claims: usize) -> FrameTxGas {
    let pcs = dependency_gas(claims);
    let standard = calldata_gas(calldata) + calldata_gas(pcs_data) + execution + pcs;
    let floor = 64 * (calldata.len() + pcs_data.len()) as u64 + pcs;
    FrameTxGas {
        standard,
        floor,
        total: standard.max(floor),
    }
}

/// A legacy transaction's gas (a deployment, `setIndexCommitment`): its base cost, then the larger of its calldata at
/// the standard rate plus `execution`, and of its calldata at EIP-7976's floor, 64 gas a byte.
pub fn transaction_gas(calldata: &[u8], execution: u64) -> u64 {
    21_000 + (calldata_gas(calldata) + execution).max(64 * calldata.len() as u64)
}

/// The running transaction's frames, and what its contract hashed and checked.
#[derive(Default)]
struct Running {
    frames: Vec<Frame>,
    /// The payloads read as public data ([`PcsFrame::read`]).
    read: Vec<usize>,
    /// The bytes the last `KECCAK256` hashed.
    last: Vec<u8>,
    /// Before each read of a payload that is not public data, what the last `KECCAK256` hashed: the claims the
    /// contract checked.
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
            FRAMEPARAM_MODE => Some(U256::from(frame.mode)),
            FRAMEPARAM_LEN => Some(U256::from(frame.data.len())),
            _ => None,
        }
    });
    match value {
        Some(value) => *param = value,
        None => context.interpreter.halt(InstructionResult::InvalidFEOpcode),
    }
}

/// `FRAMEDATALOAD`: the word of a frame's `data` at an offset, zero past its end, as `CALLDATALOAD`; a frame the
/// transaction does not have halts. A read of a payload (a frame's `data` past its first byte) that is not public data
/// ([`PcsFrame::read`]) keeps what the last `KECCAK256` hashed, as a claim checked.
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
        if offset >= 1 && !running.read.contains(&((offset - 1) / 32)) {
            let last = running.last.clone();
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

/// What a transaction did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned (a creation: the code it deployed), or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of its execution: the transaction's without its base cost, its calldata, its frames' `data` and its
    /// claims' intrinsic gas ([`dependency_gas`]). A creation's includes its 32,000, its init code's 2 a word and its
    /// code's deposit, 200 a byte.
    pub execution: u64,
    /// Each instruction's gas, by program counter, of the code called.
    pub gas_by_pc: Vec<u64>,
    /// The same, of every code that ran, by its address.
    pub gas_by_code: Vec<(Address, Vec<u64>)>,
    /// The claims it checked against its frame of PCS claims, in order: what it hashed before each payload read.
    pub claims: Vec<Vec<u8>>,
}

impl Outcome {
    /// Whether it returned the word 1: a verifying contract's acceptance (`abi.encode(true)`).
    pub fn attests(&self) -> bool {
        self.output.as_deref() == Some(&crate::op::word([1, 0, 0])[..])
    }
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
    /// unless the creation failed, and the transaction's outcome.
    pub fn deploy(&mut self, init_code: &[u8]) -> (Option<Address>, Outcome) {
        let (outcome, created) = self.run(DEPLOYER, TxKind::Create, init_code, U256::ZERO, &PcsFrame::default());
        (created, outcome)
    }

    /// Send `calldata` and `value` wei from `from` to `to`, in a transaction whose frame of PCS claims is `pcs`, and
    /// keep what it changes.
    pub fn transact(&mut self, from: Address, to: Address, calldata: &[u8], value: U256, pcs: &PcsFrame) -> Outcome {
        self.run(from, TxKind::Call(to), calldata, value, pcs).0
    }

    /// The same from [`CALLER`] with no value, leaving the chain as it was.
    pub fn call(&self, to: Address, calldata: &[u8], pcs: &PcsFrame) -> Outcome {
        self.clone().transact(CALLER, to, calldata, U256::ZERO, pcs)
    }

    /// Run a transaction from `from`, sending `value` wei, whose frame of PCS claims is `pcs`, and keep what it
    /// changes; and the address of the contract it created, if any. Each transaction starts cold (EIP-2929): its
    /// first `SLOAD` of a slot costs 2,100.
    pub fn run(&mut self, from: Address, to: TxKind, data: &[u8], value: U256, pcs: &PcsFrame) -> (Outcome, Option<Address>) {
        // Senders have funds for the value; gas is free.
        let nonce = self.db.cache.accounts.get(&from).map_or(0, |account| account.info.nonce);
        let balance = U256::from(10u64.pow(18));
        self.db.insert_account_info(from, AccountInfo::from_balance(balance).with_nonce(nonce));
        let mut inspector = GasByPc::default();
        for (address, account) in &self.db.cache.accounts {
            let size = account.info.code.as_ref().map_or(0, |code| code.original_byte_slice().len());
            inspector.sizes.push((*address, size));
        }
        let tx = TxEnv::builder()
            .caller(from)
            .nonce(nonce)
            .kind(to)
            .value(value)
            .data(Bytes::copy_from_slice(data))
            .gas_limit(100_000_000)
            .build()
            .expect("a transaction");
        RUNNING.set(Running {
            frames: pcs.frames(),
            read: pcs.read.clone(),
            ..Running::default()
        });
        // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
        let mut evm = Context::mainnet()
            .with_db(&mut self.db)
            .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
            .modify_block_chained(|block| block.gas_limit = u64::MAX)
            .build_mainnet_with_inspector(inspector);
        evm.instruction.insert_instruction(FIELD_MUL, field_mul);
        evm.instruction.insert_instruction(FRAMEPARAM, frame_param);
        evm.instruction.insert_instruction(FRAMEDATALOAD, frame_data_load);
        evm.instruction.insert_instruction(KECCAK256, keccak256_keeping);
        let result = evm.inspect_tx_commit(tx).expect("a valid transaction");
        let mut inspector = std::mem::take(&mut evm.inspector);
        let claims = RUNNING.take().checked;
        while !inspector.frames.is_empty() {
            inspector.finish();
        }
        let gas_by_pc = match to {
            TxKind::Call(to) => inspector.gas.iter().find(|(address, _)| *address == to).map(|(_, gas)| gas.clone()),
            TxKind::Create => None,
        };
        // The base cost and the calldata at the standard rate (Cancun's intrinsic gas), the rest execution.
        let execution = result.gas_used() - 21_000 - calldata_gas(data);
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
        let outcome = Outcome {
            output,
            execution,
            gas_by_pc: gas_by_pc.unwrap_or_default(),
            gas_by_code: inspector.gas,
            claims,
        };
        (outcome, created)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A frame of PCS claims: its scheme byte, then each claim's Keccak-256, after the frames before it.
    #[test]
    fn frame_data_is_the_claims_hashes() {
        let mut pcs = PcsFrame::of([vec![1, 2, 3]]);
        pcs.declare(Vec::new());
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
}
