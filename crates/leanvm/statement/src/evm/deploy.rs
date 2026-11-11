// Part of this repository; the deployment follows this repository's crates/membership/evm/src/quotient.rs. MIT OR Apache-2.0;
// see AGENTS.md.
//! What a contract's call costs: its gas by phase ([`phases`]), on sample calldata ([`sample_stream`],
//! [`sample_tx_gas`]), and the gas of a verifier fragment measured alone ([`measure_fragment`]).

use crate::evm::codegen::{CALLS, ENTRY, Ending, Entry, MEASURE, Word, compile};
use crate::evm::machine::{FrameTxGas, PcsFrame, call, frame_tx_gas};
use crate::evm::record::{Recorder, Sym, record};

/// The transcript's 16-byte name in [`measure_fragment`]'s builds.
const NAME: [u8; 16] = *b"leanVM-42422001K";

/// One phase's share of a call.
#[derive(Clone, Debug)]
pub struct PhaseGas {
    pub phase: &'static str,
    pub gas: u64,
}

/// The gas of each phase: each instruction's (`gas_by_pc`) summed by the phase of its code (`phase_of`; `past` past
/// its end), in the order the phases first take gas.
pub fn phases(gas_by_pc: &[u64], phase_of: &[&'static str], past: &'static str) -> Vec<PhaseGas> {
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in gas_by_pc.iter().enumerate().filter(|&(_, &gas)| gas > 0) {
        let phase = phase_of.get(pc).copied().unwrap_or(past);
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    phases
}

/// A stream of `len` bytes, pseudo-random as a proof's are (a contract's gas does not depend on them; the
/// transaction's does, on its zero bytes only).
pub fn sample_stream(len: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect()
}

/// Calldata of `bytes` bytes, `zeros` of them zero, at the standard rate (16 gas a nonzero byte, 4 a zero byte).
pub fn sample_calldata_gas(bytes: usize, zeros: usize) -> u64 {
    16 * (bytes - zeros) as u64 + 4 * zeros as u64
}

/// The frame transaction's gas ([`frame_tx_gas`]) of a call of sample calldata of `bytes` bytes, `zeros` of them
/// zero, and `execution`; with `claims` claims (none: `0`), a frame of PCS claims of `1 + 32` bytes a claim (their
/// hashes counted nonzero) and their PCS gas.
pub fn sample_tx_gas(bytes: usize, zeros: usize, execution: u64, claims: usize) -> FrameTxGas {
    let calldata: Vec<u8> = std::iter::repeat_n(1u8, bytes - zeros).chain(std::iter::repeat_n(0u8, zeros)).collect();
    let frame = if claims == 0 { Vec::new() } else { vec![1u8; 1 + 32 * claims] };
    frame_tx_gas(&calldata, execution, &frame, claims)
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
        frame: Vec::new(),
    };
    let words: Vec<Word> = outputs.iter().map(|sym| Word::Node(sym.0)).collect();
    let contract = compile(&graph, &words, &Ending::Return, &entry);
    let stream = sample_stream(stream_len, 0x9E37_79B9);
    // A fragment's calldata: a public input of four words, then the stream (and no frame's index: it returns).
    let outcome = call(&contract.code, &[], &[&[0x5a; 32][..], &stream].concat(), &PcsFrame::default());
    assert!(outcome.output.is_some(), "the measuring build returns");
    let mut phases = phases(&outcome.gas_by_pc, &contract.phase_of, CALLS);
    phases.retain(|p| ![MEASURE, CALLS, ENTRY].contains(&p.phase));
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
