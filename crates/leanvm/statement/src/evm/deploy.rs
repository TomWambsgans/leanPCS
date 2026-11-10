// Part of this repository; the deployment follows this repository's crates/membership/evm/src/quotient.rs. MIT OR Apache-2.0;
// see AGENTS.md.
//! A [`Deployable`] verifier on revm: deployed by transactions ([`deploy`]) or installed ([`install`], for measuring
//! builds), and the gas of a verifier fragment measured alone ([`measure_fragment`]).

use evm_link::creation_code;
use revm::primitives::Address;

use crate::evm::codegen::{CALLS, Deployable, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile};
use crate::evm::machine::{Chain, PcsFrame, VERIFIER, call, transaction_gas};
use crate::evm::record::{Recorder, Sym, record};

/// The transcript's 16-byte name in [`measure_fragment`]'s builds.
const NAME: [u8; 16] = *b"leanVM-42422001K";

/// The contracts of a [`Deployable`] deployed, each by a transaction: the parts (no constructor), then the driver,
/// calling them at their addresses, its constructor storing the fixed commitments.
pub struct Deployed {
    pub chain: Chain,
    /// The driver's address: where a verifying call is sent.
    pub address: Address,
    /// Each contract: its address, code bytes, init code, the deployment's execution gas, and its code's tags (the
    /// driver last).
    pub contracts: Vec<DeployedContract>,
}

pub struct DeployedContract {
    pub address: Address,
    pub code_bytes: usize,
    pub init_code: Vec<u8>,
    pub execution: u64,
    pub tags: Vec<&'static str>,
}

impl DeployedContract {
    /// The deployment's transaction gas, without its 21,000 base, under a calldata floor of `floor` a byte.
    pub fn transaction(&self, floor: u64) -> u64 {
        transaction_gas(&self.init_code, self.execution, floor) - 21_000
    }
}

/// Deploy `deployable` on a fresh chain, its driver storing `roots` (slot, word).
pub fn deploy(deployable: &Deployable, roots: &[(u8, [u8; 32])]) -> Deployed {
    let mut chain = Chain::default();
    let mut contracts = Vec::new();
    let linked = &deployable.linked;
    for part in &linked.parts {
        let init_code = creation_code(&part.code.code, &[]);
        let (address, execution) = chain.deploy(&init_code);
        let address = address.expect("a part deploys");
        assert_eq!(chain.code(address), part.code.code);
        contracts.push(DeployedContract {
            address,
            code_bytes: part.code.code.len(),
            init_code,
            execution,
            tags: part.code.tags.clone(),
        });
    }
    let addresses: Vec<[u8; 20]> = contracts.iter().map(|c| c.address.into_array()).collect();
    let code = linked.driver_code(&addresses);
    let slots: Vec<u8> = roots.iter().map(|&(slot, _)| slot).collect();
    let mut init_code = creation_code(&code, &slots);
    roots.iter().for_each(|(_, word)| init_code.extend(word));
    let (address, execution) = chain.deploy(&init_code);
    let address = address.expect("the driver deploys");
    assert_eq!(chain.code(address), code);
    for &(slot, word) in roots {
        assert_eq!(chain.storage(address, slot), word);
    }
    contracts.push(DeployedContract {
        address,
        code_bytes: code.len(),
        init_code,
        execution,
        tags: linked.driver.code.tags.clone(),
    });
    Deployed {
        chain,
        address,
        contracts,
    }
}

/// Where a measuring build's parts are installed: `0x7a..` and the part's number.
fn part_address(k: usize) -> Address {
    let mut bytes = [0u8; 20];
    bytes[0] = 0x7a;
    bytes[18..].copy_from_slice(&(k as u16).to_be_bytes());
    Address::from(bytes)
}

/// `deployable` installed rather than deployed (a measuring build may pass EIP-170's limit by its `JUMPDEST`s): the
/// driver at [`VERIFIER`], storing `roots`, its parts at addresses of their own.
pub fn install(deployable: &Deployable, roots: &[(u8, [u8; 32])]) -> Deployed {
    let mut chain = Chain::default();
    let linked = &deployable.linked;
    let mut contracts = Vec::new();
    for (k, part) in linked.parts.iter().enumerate() {
        chain.install(part_address(k), &part.code.code);
        contracts.push(DeployedContract {
            address: part_address(k),
            code_bytes: part.code.code.len(),
            init_code: Vec::new(),
            execution: 0,
            tags: part.code.tags.clone(),
        });
    }
    let addresses: Vec<[u8; 20]> = (0..linked.parts.len()).map(|k| part_address(k).into_array()).collect();
    let code = linked.driver_code(&addresses);
    chain.install(VERIFIER, &code);
    roots.iter().for_each(|&(slot, word)| chain.store(VERIFIER, slot, word));
    contracts.push(DeployedContract {
        address: VERIFIER,
        code_bytes: code.len(),
        init_code: Vec::new(),
        execution: 0,
        tags: linked.driver.code.tags.clone(),
    });
    Deployed {
        chain,
        address: VERIFIER,
        contracts,
    }
}

/// One phase's share of a call.
#[derive(Clone, Debug)]
pub struct PhaseGas {
    pub phase: &'static str,
    pub gas: u64,
}

/// A fragment's calldata: the selector, a public input of four words, then the stream.
fn calldata(public_input: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], public_input, stream].concat()
}

/// What a part of a verifier costs measured alone: the same compilation and run, of a graph `f` records on a fresh
/// transcript (its outputs kept live by returning them), less the entry checks and the returned words.
#[derive(Clone, Debug)]
pub struct FragmentGas {
    /// Execution of the part itself: its arithmetic, its transcript hashing and its calldata reads.
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub stream_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub memory_words: usize,
}

pub fn measure_fragment(f: impl FnOnce(&mut Recorder) -> Vec<Sym>) -> FragmentGas {
    let ((outputs, stream_len), graph) = record(|| {
        let mut recorder = Recorder::new();
        let outputs = f(&mut recorder);
        (outputs, recorder.cursor as usize)
    });
    let entry = Entry {
        name: NAME,
        iv: [0x77; 32],
        stream_len,
        measure: true,
    };
    let words: Vec<Word> = outputs.iter().map(|sym| Word::Node(sym.0)).collect();
    let contract = compile(&graph, &words, &Ending::Return, &entry);
    let mut state = 0x9E37_79B9u64;
    let stream: Vec<u8> = (0..stream_len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect();
    let outcome = call(
        &contract.code,
        &[],
        &calldata(&[0x5a; 32], &stream),
        &PcsFrame::default(),
    );
    assert!(outcome.output.is_some(), "the measuring build returns");
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in outcome.gas_by_pc.iter().enumerate() {
        let phase = contract.phase_of.get(pc).copied().unwrap_or(CALLS);
        if gas == 0 || [MEASURE, CALLS, ENTRY].contains(&phase) {
            continue;
        }
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    FragmentGas {
        execution: phases.iter().map(|p| p.gas).sum(),
        phases,
        stream_bytes: stream_len,
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        memory_words: contract.memory_words,
    }
}
