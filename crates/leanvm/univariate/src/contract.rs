// Part of this repository; the contract's assembly and measurement follow crates/membership/evm/src/quotient.rs. MIT OR
// Apache-2.0; see AGENTS.md.
//! The verifier as a contract (straight-line code compiled from the recorded verifier, `leanvm_statement::evm`), its
//! calldata, and what a call costs.
//!
//! **Calldata**: selector, the public input (four 64-bit words, each big-endian: `(cell0.c0, cell0.c1, cell1.c0,
//! cell1.c1)`; leanVM's 32-byte digest has its words little-endian, so a caller reverses each word's 8 bytes, SPEC.md
//! §4), then the stream: the six row counts, `C1`'s commitment (its root, its out-of-domain answer), Flock's messages,
//! `C2`'s commitment, the values at `t`, the batching sumcheck (SPEC.md §8, §13), then a byte, the index of the
//! transaction's frame of PCS claims. The contract is built for one shape class (the heights), which the transcript's
//! IV binds with the setup commitment.
//!
//! **Claims**: one per commitment, each the EIP draft's PCS claim (`crates/pcs_claim`, `docs/PCS_CLAIM.md`): the
//! stack in its `n` variables, committed as `(root, ood)`, at the batch's point, which the contract checks its
//! transaction declares (a payload of its frame of PCS claims is the claim's Keccak-256,
//! `evm_link::declared_claims`). `C1`'s and `C2`'s roots are the stream's 32 bytes as they are (the prover sends a
//! root's bytes, `KeccakWriter::send_root`), their out-of-domain answers the stream's elements after them; the setup
//! commitment `F` is a constant of the code ([`SetupRoots`]: no `SLOAD`).

use leanvm_statement::evm::codegen::{CALLS, Claim, Contract, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile, word};
use leanvm_statement::evm::machine::{FrameTxGas, Outcome, PCS_FRAME, PcsFrame, call, element_word, frame_tx_gas};
use leanvm_statement::evm::record::{Graph, Recorder, Sym, record};
use leanvm_statement::field::E;
use leanvm_statement::transcript::{Checks, KeccakChannel, keccak_seed, statement_words};

use crate::claims::Commitment;
use crate::verifier::{Reduced, Shape, Variant, reduce};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanVM-univar-v1";

/// The setup commitment the contract's IV binds, a constant of the code (SPEC.md §13, F2): `F`'s root and
/// out-of-domain answer, from the program and the shape (`prover::setup::shape_roots`). [`SetupRoots::REFERENCE`]'s
/// is the reference shape's (128 signatures, `leanvm_statement::shapes::reference`), which the gas reports use for
/// every shape (the gas does not depend on it).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SetupRoots {
    pub f: [u8; 32],
    /// `F`'s out-of-domain answer (`crates/pcs_claim`).
    pub f_ood: E,
}

const fn digit(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        _ => c - b'a' + 10,
    }
}

const fn hex32(text: &[u8; 64]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = digit(text[2 * i]) << 4 | digit(text[2 * i + 1]);
        i += 1;
    }
    out
}

impl SetupRoots {
    pub const REFERENCE: Self = Self {
        f: hex32(b"067244bea80942b5cacaa61c28ca748d0ae4ba6c106739ab109c9c07296e1ca5"),
        f_ood: E::new(REFERENCE_F_OOD[0], REFERENCE_F_OOD[1], REFERENCE_F_OOD[2]),
    };
}

/// [`SetupRoots::REFERENCE`]'s out-of-domain answer, limb 0 first (`tests/prove_real.rs` checks it against the
/// reference trace's `F`).
const REFERENCE_F_OOD: [u64; 3] = [0x20e3_e5ce_a967_4063, 0x56b4_7388_a81d_6fff, 0x1667_157a_1c2b_0b6b];

/// The shape's bytes: `log_memory`, `log_bytecode`, then the six heights.
pub fn shape_bytes(shape: &Shape) -> [u8; 8] {
    let heights = shape.heights();
    let mut bytes = [0u8; 8];
    bytes[0] = shape.log_memory as u8;
    bytes[1] = shape.log_bytecode as u8;
    for (k, &h) in heights.iter().enumerate() {
        bytes[2 + k] = h as u8;
    }
    bytes
}

/// The bytes the IV's preimage ends with: the tag `"keccak-vm"`, Flock's skip and the Fiat–Shamir shape's code.
pub fn variant_bytes(variant: Variant) -> Vec<u8> {
    let mut out = b"keccak-vm".to_vec();
    out.extend([variant.skip as u8, variant.fs as u8]);
    out
}

/// The IV the transcript's seed hashes (SPEC.md §13, F2): the Keccak-256 of a tag, the program's IV, the setup
/// commitment ([`SetupRoots`]: `F`'s root and its out-of-domain answer, as a claim encodes them), the shape and
/// [`variant_bytes`]. The seed then adds the public input. A constant of the code: it costs no gas.
pub fn contract_iv(shape: &Shape, variant: Variant, program_iv: &[u8; 32], roots: &SetupRoots) -> [u8; 32] {
    let mut data = b"leanVM-univar-iv".to_vec();
    data.extend_from_slice(program_iv);
    data.extend_from_slice(&roots.f);
    data.extend_from_slice(&element_word(roots.f_ood)[8..]);
    data.extend_from_slice(&shape_bytes(shape));
    data.extend_from_slice(&variant_bytes(variant));
    leanvm_statement::transcript::keccak256(&data)
}

/// The verifier for one shape, recorded.
pub struct Recorded {
    pub shape: Shape,
    /// Flock's variant (and so the Fiat–Shamir shape) it was recorded for: the IV binds it ([`contract_iv`]).
    pub variant: Variant,
    pub roots: SetupRoots,
    pub graph: Graph,
    pub reduced: Reduced<Sym>,
    pub stream_len: usize,
    pub roots_at: [usize; 2],
    pub reads: Vec<(&'static str, u32)>,
}

impl Recorded {
    /// The contract's IV for the program's `program_iv` ([`contract_iv`] of the shape, the variant and the root it
    /// was recorded with).
    pub fn iv(&self, program_iv: &[u8; 32]) -> [u8; 32] {
        contract_iv(&self.shape, self.variant, program_iv, &self.roots)
    }
}

pub fn record_verifier(shape: &Shape, variant: Variant) -> Recorded {
    record_verifier_with(shape, variant, &SetupRoots::REFERENCE)
}

/// [`record_verifier`] for a contract that binds `setup` (another shape's `F`, say): the graph is the same, the
/// roots are the code's constants.
pub fn record_verifier_with(shape: &Shape, variant: Variant, setup: &SetupRoots) -> Recorded {
    let ((reduced, stream_len, roots, reads), graph) = record(|| {
        let mut recorder = Recorder::new();
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut recorder, variant).expect("a recorder rejects nothing");
        (reduced, recorder.cursor as usize, recorder.roots.clone(), recorder.reads)
    });
    assert_eq!(roots.len(), 2, "two commitments in the stream");
    Recorded {
        shape: *shape,
        variant,
        roots: *setup,
        graph,
        reduced,
        stream_len,
        roots_at: [roots[0] as usize, roots[1] as usize],
        reads,
    }
}

fn scalar(sym: Sym) -> Word {
    Word::Node(sym.0)
}

/// The claims the contract checks declared (point claims), in order: each commitment's root and out-of-domain answer
/// (the stream's for `C1` and `C2`, the code's constants for `F`), the point and the value, in any word type.
fn claims_with<T: Copy, W: Clone>(
    recorded: &Recorded,
    reduced: &Reduced<T>,
    stream: impl Fn(usize) -> W,
    constant: impl Fn([u8; 32]) -> W,
    scalar: impl Fn(T) -> W + Copy,
) -> Vec<(W, W, Vec<W>, W)> {
    reduced
        .openings
        .iter()
        .map(|(commitment, opening)| {
            let (root, ood) = match commitment {
                Commitment::C1 => (stream(recorded.roots_at[0]), scalar(reduced.oods[0])),
                Commitment::C2 => (stream(recorded.roots_at[1]), scalar(reduced.oods[1])),
                Commitment::Setup => (constant(recorded.roots.f), constant(element_word(recorded.roots.f_ood))),
            };
            (root, ood, opening.point.iter().map(|&x| scalar(x)).collect(), scalar(opening.value))
        })
        .collect()
}

/// The claims the contract checks declared, as words of the contract.
pub fn calls(recorded: &Recorded) -> Vec<Claim> {
    claims_with(recorded, &recorded.reduced, Word::Stream, Word::Const, scalar)
        .into_iter()
        .map(|(root, ood, point, value)| Claim { root, ood, point, value })
        .collect()
}

/// `program_iv` is the program's (leanVM's digest of the bytecode and the R1CS); the contract's IV is derived from it
/// ([`contract_iv`]), as in every function here that takes one.
pub fn compile_verifier(recorded: &Recorded, program_iv: &[u8; 32], measure: bool) -> Contract {
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(program_iv),
        stream_len: recorded.stream_len,
        measure,
        selector: true,
        frame: Vec::new(),
    };
    compile(&recorded.graph, &[], &Ending::Claims(calls(recorded)), &entry)
}

/// The proof's calldata: the selector, the public input, the stream (what the committed vectors hold).
pub fn proof_calldata(public_words: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], public_words, stream].concat()
}

/// Calldata verifying a proof: [`proof_calldata`], then the index of the transaction's frame of PCS claims
/// ([`PCS_FRAME`]).
pub fn calldata(public_words: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&proof_calldata(public_words, stream)[..], &[PCS_FRAME]].concat()
}

/// A stream of the shape's length, its bytes pseudo-random as a proof's are (the contract's gas does not depend on
/// them; the transaction's does, on its zero bytes only).
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

/// The Rust verifier on the same calldata: the claims, and the values it requires to be zero, then nonzero.
pub fn rust_verifier(
    shape: &Shape,
    iv: &[u8; 32],
    public_words: &[u8; 32],
    stream: &[u8],
    variant: Variant,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), leanvm_statement::VerifierError> {
    rust_verifier_with(shape, iv, &SetupRoots::REFERENCE, public_words, stream, variant)
}

/// [`rust_verifier`] for a contract that binds `setup` in its IV.
pub fn rust_verifier_with(
    shape: &Shape,
    iv: &[u8; 32],
    setup: &SetupRoots,
    public_words: &[u8; 32],
    stream: &[u8],
    variant: Variant,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), leanvm_statement::VerifierError> {
    let seed = keccak_seed(&NAME, &contract_iv(shape, variant, iv, setup), public_words);
    let mut channel = KeccakChannel::new(seed, stream, Checks::collect());
    let reduced = reduce(shape, statement_words(public_words), &mut channel, variant)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

/// One phase's share of a call.
#[derive(Clone, Debug)]
pub struct PhaseGas {
    pub phase: &'static str,
    pub gas: u64,
}

/// What a verifying call costs.
#[derive(Clone, Debug)]
pub struct GasReport {
    pub calldata_bytes: usize,
    pub calldata_zero_bytes: usize,
    pub stream_bytes: usize,
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    pub calls: usize,
    /// Terms of each claim, and words written for it.
    pub terms: Vec<(String, usize, usize)>,
    pub pcs_words: usize,
    pub relations: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
    pub stream_by_phase: Vec<(&'static str, u32)>,
}

impl GasReport {
    /// The frame transaction's gas (EIP-8141 with EIP-7976's floor, without `FRAME_TX_INTRINSIC_COST` and the
    /// per-frame costs): this calldata and execution, and a frame of PCS claims of `claims` claims, or none.
    pub fn transaction(&self, claims: bool) -> FrameTxGas {
        let calldata = vec![1u8; self.calldata_bytes - self.calldata_zero_bytes]
            .into_iter()
            .chain(vec![0u8; self.calldata_zero_bytes])
            .collect::<Vec<u8>>();
        let (data, count) = if claims {
            (vec![1u8; 1 + 32 * self.calls], self.calls)
        } else {
            (Vec::new(), 0)
        };
        frame_tx_gas(&calldata, self.execution, &data, count)
    }

    pub fn calldata_gas(&self) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        16 * nonzero + 4 * self.calldata_zero_bytes as u64
    }
}

/// Measure the verifier for `shape`: build it, run it on sample calldata with every claim declared, and check the
/// phases against the total.
pub fn measure(shape: &Shape, iv: &[u8; 32], variant: Variant) -> GasReport {
    let recorded = record_verifier(shape, variant);
    let contract = compile_verifier(&recorded, iv, true);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let all_calls = calls(&recorded);
    let claims = recorded.reduced.openings.len();
    let calls_count = all_calls.len();
    let outcome: Outcome = call(&contract.code, &[], &data, &PcsFrame::declaring_all());
    assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "the measuring run returns 1");
    assert_eq!(outcome.claims.len(), calls_count, "one claim per commitment");
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in outcome.gas_by_pc.iter().enumerate() {
        if gas == 0 {
            continue;
        }
        let phase = contract.phase_of.get(pc).copied().unwrap_or(CALLS);
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    let total: u64 = phases.iter().map(|p| p.gas).sum();
    assert_eq!(total, outcome.execution, "the instructions' gas is the execution's");
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    assert_eq!(measured, contract.checks as u64 + calls_count as u64, "one JUMPDEST a check and a claim");
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    let terms: Vec<(String, usize, usize)> = recorded
        .reduced
        .openings
        .iter()
        .zip(&all_calls)
        .map(|((commitment, _), claim)| (format!("{commitment:?}"), 1, claim.words().len()))
        .collect();
    let _ = ENTRY;
    GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims,
        calls: calls_count,
        pcs_words: all_calls.iter().map(|c| c.words().len()).sum(),
        terms,
        relations: recorded.reduced.relations,
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
        stream_by_phase: recorded.reads.clone(),
    }
}

/// The words `calls` writes, for the Rust verifier's claims on `stream`: what the contract must write.
fn expected_words(reduced: &Reduced<E>, recorded: &Recorded, stream: &[u8]) -> Vec<[u8; 32]> {
    let root = |at: usize| -> [u8; 32] { stream[at..at + 32].try_into().unwrap() };
    claims_with(recorded, reduced, root, |b| b, element_word)
        .into_iter()
        .flat_map(|(root, ood, point, value)| [root, ood].into_iter().chain(point).chain([value]))
        .collect()
}

/// The PCS claims a proof's stream gives (the Rust verifier's reduction of it), in the contract's order: what its
/// transaction must declare, and what the block's openings must prove.
pub fn expected_claims(recorded: &Recorded, reduced: &Reduced<E>, stream: &[u8]) -> Vec<pcs_claim::PcsClaim> {
    reduced
        .openings
        .iter()
        .map(|(commitment, opening)| {
            let at = |k: usize| -> [u8; 32] { stream[recorded.roots_at[k]..recorded.roots_at[k] + 32].try_into().unwrap() };
            let (root, ood) = match commitment {
                Commitment::C1 => (at(0), reduced.oods[0]),
                Commitment::C2 => (at(1), reduced.oods[1]),
                Commitment::Setup => (recorded.roots.f, recorded.roots.f_ood),
            };
            pcs_claim::PcsClaim {
                n: opening.point.len() as u8,
                root,
                ood: ood.into(),
                point: opening.point.iter().map(|&x| x.into()).collect(),
                value: opening.value.into(),
            }
        })
        .collect()
}

/// The contract, built to return the claims it would check declared and every value it checks, against the Rust verifier
/// on the same calldata: word for word.
pub fn parity(shape: &Shape, iv: &[u8; 32], public_words: &[u8; 32], stream: &[u8], variant: Variant) {
    parity_with(shape, iv, &SetupRoots::REFERENCE, public_words, stream, variant);
}

/// [`parity`] for a contract that binds `setup`.
pub fn parity_with(
    shape: &Shape,
    iv: &[u8; 32],
    setup: &SetupRoots,
    public_words: &[u8; 32],
    stream: &[u8],
    variant: Variant,
) {
    let recorded = record_verifier_with(shape, variant, setup);
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(iv),
        stream_len: recorded.stream_len,
        measure: true,
        selector: true,
        frame: Vec::new(),
    };
    let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
    let outputs: Vec<Word> = calls(&recorded)
        .iter()
        .flat_map(Claim::words)
        .chain(checks.map(|&(id, _)| Word::Node(id)))
        .collect();
    let contract = compile(&recorded.graph, &outputs, &Ending::Return, &entry);
    let (reduced, zero, nonzero) =
        rust_verifier_with(shape, iv, setup, public_words, stream, variant).expect("the stream's length");
    let mut expected = expected_words(&reduced, &recorded, stream);
    expected.extend(zero.iter().chain(&nonzero).map(|&x| element_word(x)));
    let outcome = call(&contract.code, &[], &calldata(public_words, stream), &PcsFrame::default());
    let output = outcome.output.expect("the measuring build does not revert");
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(&expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
}

