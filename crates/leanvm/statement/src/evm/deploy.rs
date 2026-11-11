// Part of this repository; the deployment follows this repository's crates/membership/evm/src/quotient.rs. MIT OR Apache-2.0;
// see AGENTS.md.
//! The gas of a verifier fragment measured alone ([`measure_fragment`]).

use crate::evm::codegen::{CALLS, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile};
use crate::evm::machine::{PcsFrame, call};
use crate::evm::record::{Recorder, Sym, record};

/// The transcript's 16-byte name in [`measure_fragment`]'s builds.
const NAME: [u8; 16] = *b"leanVM-42422001K";

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
        selector: true,
        frame: Vec::new(),
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
