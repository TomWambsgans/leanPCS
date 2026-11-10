// Part of this repository. The recording, compilation, measurement and parity follow
// crates/leanvm/univariate/src/contract.rs (itself after crates/membership/evm/src/quotient.rs). MIT OR Apache-2.0; see
// AGENTS.md.
//! π2's verifier as a contract: [`super::verifier::reduce`] recorded on `leanvm_statement`'s symbol, compiled to
//! straight-line EVM code (`leanvm_statement::evm::codegen`, `crates/evm_link`), run on revm with `FIELD_MUL` and
//! EIP-8141's frame introspection over a frame of PCS claims (`leanvm_statement::evm::machine`, point claims: `root,
//! layout, k, k × (point, value)`).
//!
//! **Calldata**: the selector, π1's public input (32 bytes, which the seed hashes), the stream: π1's roots and its
//! claims' elements, `W`'s root, `Q`'s root, the `2^r + 2` values; then a byte, the index of the transaction's frame of
//! PCS claims. **Claims**, checked declared in that frame in order: π1's (their words from calldata and constants:
//! `circuit::spec::Circuit::calls`), then π2's three: `W` (one claim), the setup (one; its root a constant of the
//! code), `Q` (two). Each is written at the region's start just before it is hashed, only where the one before left
//! another word (`Ending::DeclaredReusing`, `PI2.md` §9): π1's at the batch's point write it once, the setup's reuses
//! `W`'s digits.
//!
//! **One encoding for the six claims**: `machine.rs`'s, `root word, layout word, k, k × (point,
//! value)`. Every root word is a claim's (`s_0 · 2^128 + s_1`, the two WHIR scalars of the root: each 16-byte half
//! of the hash reversed). π1's roots are in calldata so, as π1's stream carries them (its prover sends a root as its
//! two scalars), π2's `W` and `Q` likewise, and the setup roots are constants so (the root word of
//! π1's setup hash, of π2's setup root); every layout word names its stack (π1's
//! `leanvm_univariate::contract::layout_word`, π2's `prover::layout_word`: the code, the variables, the words placed).
//! The block's prover is a registry keyed by the layout word ([`registry`]): π1's three layouts are checked by
//! `leanvm_univariate`'s opening, π2's three by `quotient::opening`, and `Q`'s two claims are one, as one opening
//! (AGENTS.md: two openings of one root could be of two tables). The tests declare openings of the registry
//! (`machine::PcsFrame::decoding`).

use fiat_shamir::merkle::Hash;
use leanvm_statement::evm::codegen::{CALLS, Contract, Ending, Entry, MEASURE, VERIFY, Word, compile, word};
use leanvm_statement::evm::machine::{self, Chain, Opening, Outcome, PCS_FRAME, PcsFrame, call, decode, element_word};
use leanvm_statement::evm::record::{Graph, Recorder, Sym, record};
use leanvm_statement::field::E;
use leanvm_statement::transcript::{Checks, KeccakChannel, keccak_seed};

use super::circuit::{Circuit, Read};
use super::prover::{layout_words, layouts};
use super::verifier::{NAME, Reduced, Spec, reduce, statement_words};
use crate::circuit::spec::CallWord;

/// What the contract is built for: the circuit's verifier, its IV, the setup's root, and π1's calls. Built by
/// [`Instance::new`] from the validated circuit, which derives the IV.
pub struct Instance<'a> {
    pub spec: &'a Spec,
    pub iv: [u8; 32],
    pub setup_root: Hash,
    pub pi1: &'a [Vec<CallWord>],
}

impl<'a> Instance<'a> {
    /// The instance of `circuit` (validated here), its verifier `spec` (`Spec::of(circuit)`), the setup's root (the
    /// commitment of `circuit`'s `σ`, `κ`: `prover::Setup::new(circuit).root()`), π1's contract IV (the circuit
    /// compiler's, `Compiled::pi1_iv`, derived from π1's recorded verifier) and π1's calls (the circuit's,
    /// `spec::Circuit::calls`). The IV is `prover::iv` of them.
    pub fn new(
        circuit: &Circuit,
        spec: &'a Spec,
        setup_root: Hash,
        pi1_iv: &[u8; 32],
        pi1: &'a [Vec<CallWord>],
    ) -> Self {
        circuit.validate().unwrap_or_else(|e| panic!("the circuit is not valid: {e}"));
        assert!(
            spec.log_n == circuit.log_n
                && spec.log_row == circuit.log_row
                && spec.pairs.len() == circuit.pairs.len()
                && spec.ports == circuit.public.len()
                && spec.reads == circuit.reads,
            "the spec is the circuit's"
        );
        Self {
            spec,
            iv: super::prover::iv(pi1_iv, &circuit.digest(), &setup_root, circuit.log_n),
            setup_root,
            pi1,
        }
    }
}

/// The verifier, recorded.
pub struct Recorded {
    pub graph: Graph,
    pub reduced: Reduced<Sym>,
    pub stream_len: usize,
    /// Where each root starts in the stream: π1's, then `W`'s and `Q`'s.
    pub roots_at: Vec<usize>,
    pub reads: Vec<(&'static str, u32)>,
}

pub fn record_verifier(spec: &Spec) -> Recorded {
    let ((reduced, stream_len, roots_at, reads), graph) = record(|| {
        let mut recorder = Recorder::new();
        let statement = Recorder::statement();
        let reduced = reduce(spec, statement, &mut recorder).expect("a recorder rejects nothing");
        (
            reduced,
            recorder.cursor as usize,
            recorder.roots.iter().map(|&r| r as usize).collect(),
            recorder.reads,
        )
    });
    Recorded {
        graph,
        reduced,
        stream_len,
        roots_at,
        reads,
    }
}

/// The public scalars' indices of the reads: each root's first half, each element.
fn read_indices(spec: &Spec) -> (Vec<usize>, Vec<usize>) {
    let (mut roots, mut elements, mut at) = (vec![], vec![], 4);
    for r in &spec.reads {
        match r {
            Read::Root => roots.push(at),
            Read::Scalar => elements.push(at),
            Read::Integer(_) => {}
        }
        at += r.scalars();
    }
    (roots, elements)
}

/// The number `n` as a word.
pub fn number(n: u64) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&n.to_be_bytes());
    bytes
}

/// A commitment as a claim encodes it (`machine::root_word`): `s_0 · 2^128 + s_1`, the two scalars of
/// `quotient::transcript::root_scalars` (the words π2's stream encodes its roots as), each half of the hash reversed.
pub fn root_word(root: &Hash) -> [u8; 32] {
    machine::root_word(root)
}

/// The layouts the block must prove claims on for this contract, with each table's variables: π1's (the layout words of
/// its calls, each call's variables read off its length) and π2's three ([`layout_words`]).
pub fn registry(inst: &Instance) -> Vec<([u8; 32], usize)> {
    let l = layouts(inst.spec.log_n);
    let mut out: Vec<([u8; 32], usize)> = layout_words(inst.spec.log_n)
        .into_iter()
        .zip([l.witness.vars, l.quotient.vars, l.setup.vars])
        .collect();
    for call in inst.pi1 {
        let (CallWord::Const(layout), CallWord::Const(k)) = (call[1], call[2]) else {
            panic!("π1's layout words and claim counts are constants")
        };
        let k = u64::from_be_bytes(k[24..].try_into().expect("8 bytes")) as usize;
        assert!(k >= 1 && (call.len() - 3) % k == 0, "a call of k claims");
        let vars = (call.len() - 3) / k - 1;
        if !out.iter().any(|(w, _)| *w == layout) {
            out.push((layout, vars));
        }
    }
    out
}

/// π2's three openings, in the order the contract checks their claims (`W`, the setup, `Q`): the roots the proof
/// commits, the layout words, the claims of the reduction (not the contract's call words, which must decode to these).
pub fn openings(inst: &Instance, reduced: &Reduced<E>, roots: &[Hash; 2]) -> Vec<Opening> {
    let [w, q, s] = layout_words(inst.spec.log_n);
    vec![
        Opening {
            root: roots[0],
            layout: w,
            claims: vec![reduced.witness.clone()],
        },
        Opening {
            root: inst.setup_root,
            layout: s,
            claims: vec![reduced.setup.clone()],
        },
        Opening {
            root: roots[1],
            layout: q,
            claims: vec![reduced.quotient.clone(), reduced.sum.clone()],
        },
    ]
}

/// π1's opening of a claim of π1's own contract (`leanvm_univariate`'s vectors: the layout word π1's, its variables at
/// byte 24) on the commitment whose root the prover committed, `root` (the vector's `whir_root`, from the prover's
/// output): what the block proves, whatever word 0 of the claim says.
pub fn pi1_opening(input: &[u8], root: &Hash) -> Opening {
    let opening = decode(input, |layout| Some(layout[24] as usize)).expect("π1's call is well formed");
    Opening { root: *root, ..opening }
}

/// The openings a block must hold for the contract to accept `stream`: π1's (its calls the Rust verifier's reduction
/// gives, decoded under the registry) and π2's ([`openings`], from the reduction and the proof's roots).
pub fn expected_openings(
    inst: &Instance,
    recorded: &Recorded,
    reduced: &Reduced<E>,
    roots: &[Hash; 2],
    stream: &[u8],
) -> Vec<Opening> {
    let registry = block(inst, &[]);
    let calls = expected_calls(inst, recorded, reduced, stream);
    let mut out: Vec<Opening> = calls[..inst.pi1.len()]
        .iter()
        .map(|words| registry.decode(&words.concat()).expect("π1's call decodes"))
        .collect();
    out.extend(openings(inst, reduced, roots));
    out
}

/// The frame of PCS claims for this contract: its registry, and the openings it declares, in order.
pub fn block(inst: &Instance, openings: &[Opening]) -> PcsFrame {
    let mut block = PcsFrame::decoding(registry(inst));
    for o in openings {
        block.declare_opening(o.clone());
    }
    block
}

/// The words of the eight calls, in order, for any word type.
fn call_words<T: Copy, W: Clone>(
    inst: &Instance,
    reduced: &Reduced<T>,
    roots_at: &[usize],
    stream: impl Fn(usize) -> W,
    constant: impl Fn([u8; 32]) -> W,
    scalar: impl Fn(T) -> W,
) -> Vec<Vec<W>> {
    let (_, elements) = read_indices(inst.spec);
    let roots = inst.spec.reads.iter().filter(|r| **r == Read::Root).count();
    let mut out: Vec<Vec<W>> = inst
        .pi1
        .iter()
        .map(|c| {
            c.iter()
                .map(|w| match *w {
                    CallWord::Const(bytes) => constant(bytes),
                    CallWord::Root(i) => stream(roots_at[i as usize]),
                    CallWord::Element(i) => scalar(reduced.public[elements[i as usize]]),
                    CallWord::Pair { element, coordinate } => {
                        scalar(reduced.pair_points[elements[element as usize]][coordinate as usize])
                    }
                })
                .collect()
        })
        .collect();
    let [lw, lq, ls] = layout_words(inst.spec.log_n);
    let claim = |(point, value): &(Vec<T>, T)| -> Vec<W> { point.iter().chain([value]).map(|&x| scalar(x)).collect() };
    let head = |root: W, id: [u8; 32], k: u64| vec![root, constant(id), constant(number(k))];
    // W, then the setup (its point's `w_4 … w_{m-1}` where W's are: the contract writes them once, PI2.md §9, lever
    // 3b), then Q.
    out.push([head(stream(roots_at[roots]), lw, 1), claim(&reduced.witness)].concat());
    out.push([head(constant(root_word(&inst.setup_root)), ls, 1), claim(&reduced.setup)].concat());
    out.push(
        [
            head(stream(roots_at[roots + 1]), lq, 2),
            claim(&reduced.quotient),
            claim(&reduced.sum),
        ]
        .concat(),
    );
    out
}

/// The calls as the contract's output words.
pub fn calls(inst: &Instance, recorded: &Recorded) -> Vec<Vec<Word>> {
    call_words(
        inst,
        &recorded.reduced,
        &recorded.roots_at,
        Word::Stream,
        Word::Const,
        |s: Sym| Word::Node(s.0),
    )
}

/// The claims the Rust verifier's reduction of `stream` gives: what the contract must check declared.
pub fn expected_calls(inst: &Instance, recorded: &Recorded, reduced: &Reduced<E>, stream: &[u8]) -> Vec<Vec<[u8; 32]>> {
    call_words(
        inst,
        reduced,
        &recorded.roots_at,
        |at| stream[at..at + 32].try_into().unwrap(),
        |b| b,
        element_word,
    )
}

fn entry(inst: &Instance, recorded: &Recorded, measure: bool) -> Entry {
    Entry {
        name: NAME,
        iv: inst.iv,
        stream_len: recorded.stream_len,
        measure,
    }
}

/// The contract: it reverts unless its transaction declares every claim, and returns the word 1.
pub fn compile_verifier(inst: &Instance, recorded: &Recorded, measure: bool) -> Contract {
    let calls = calls(inst, recorded);
    let ending = Ending::DeclaredReusing(calls.iter().map(Vec::len).collect());
    compile(
        &recorded.graph,
        &calls.concat(),
        &ending,
        &entry(inst, recorded, measure),
    )
}

/// The outputs and ending: the claims checked (`verify`), or their words then every checked value returned (parity).
fn ends(inst: &Instance, recorded: &Recorded, verify: bool) -> (Vec<Word>, Ending) {
    let calls = calls(inst, recorded);
    if verify {
        let ending = Ending::DeclaredReusing(calls.iter().map(Vec::len).collect());
        (calls.concat(), ending)
    } else {
        let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
        let outputs = calls
            .concat()
            .into_iter()
            .chain(checks.map(|&(id, _)| Word::Node(id)))
            .collect();
        (outputs, Ending::Return)
    }
}

/// Calldata verifying a proof: the selector, π1's public input, the stream, then the index of the transaction's frame
/// of PCS claims ([`PCS_FRAME`]).
pub fn calldata(public_input: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], public_input, stream, &[PCS_FRAME]].concat()
}

/// The Rust verifier's reduction, and the values it required to be zero, then nonzero.
pub type Checked = (Reduced<E>, Vec<E>, Vec<E>);

/// The Rust verifier on the same calldata, every check collected.
pub fn rust_verifier(
    inst: &Instance,
    public_input: &[u8; 32],
    stream: &[u8],
) -> Result<Checked, leanvm_statement::VerifierError> {
    let seed = keccak_seed(&NAME, &inst.iv, public_input);
    let mut channel = KeccakChannel::new(
        seed,
        stream,
        Checks::Collect {
            zero: vec![],
            nonzero: vec![],
        },
    );
    let reduced = reduce(inst.spec, statement_words(public_input), &mut channel)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

fn expected_return(inst: &Instance, recorded: &Recorded, public_input: &[u8; 32], stream: &[u8]) -> Vec<[u8; 32]> {
    let (reduced, zero, nonzero) = rust_verifier(inst, public_input, stream).expect("the stream's length");
    let mut out = expected_calls(inst, recorded, &reduced, stream).concat();
    out.extend(zero.iter().chain(&nonzero).map(|&x| element_word(x)));
    out
}

fn compare(output: &[u8], expected: &[[u8; 32]]) {
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
}

/// The contract, built to return the claims it would check declared and every value it checks, against the Rust verifier
/// on the same calldata: word for word. Returns the words compared.
pub fn parity(inst: &Instance, recorded: &Recorded, public_input: &[u8; 32], stream: &[u8]) -> usize {
    let (outputs, ending) = ends(inst, recorded, false);
    let contract = compile(&recorded.graph, &outputs, &ending, &entry(inst, recorded, true));
    let outcome = call(
        &contract.code,
        &[],
        &calldata(public_input, stream),
        &PcsFrame::default(),
    );
    let expected = expected_return(inst, recorded, public_input, stream);
    compare(&outcome.output.expect("the measuring build does not revert"), &expected);
    expected.len()
}

/// The verifying contract on `calldata`, its frame of PCS claims declaring exactly `openings`, in order ([`block`]):
/// whether it returned the word 1, and the claims it checked.
pub fn run(inst: &Instance, recorded: &Recorded, calldata: &[u8], openings: &[Opening]) -> (bool, Vec<Vec<u8>>) {
    let contract = compile_verifier(inst, recorded, false);
    let block = block(inst, openings);
    let outcome = call(&contract.code, &[], calldata, &block);
    (
        outcome.output.as_deref() == Some(&word([1, 0, 0])[..]),
        outcome.claims,
    )
}

/// The verifying contract's execution gas on `calldata` (without the claims' frame and intrinsic gas), and whether
/// it accepted.
pub fn verifying_execution(inst: &Instance, recorded: &Recorded, calldata: &[u8], openings: &[Opening]) -> (bool, u64) {
    let contract = compile_verifier(inst, recorded, false);
    let outcome = call(&contract.code, &[], calldata, &block(inst, openings));
    (outcome.output.as_deref() == Some(&word([1, 0, 0])[..]), outcome.execution)
}

/// Transaction gas without the 21,000 base for `calldata` and `execution`: EIP-7623 (`floor` 40, 10 a zero byte) or
/// EIP-7976 (`floor` 64, 64 a zero byte), against the standard `16` a byte (`4` a zero byte). With the claims, pass
/// the frame of PCS claims' `data` after the calldata and add their intrinsic gas (`machine::dependency_gas`).
pub fn transaction_of(calldata: &[u8], execution: u64, floor: u64) -> u64 {
    let zero = calldata.iter().filter(|&&b| b == 0).count() as u64;
    let nonzero = calldata.len() as u64 - zero;
    let standard = 16 * nonzero + 4 * zero + execution;
    let floor_gas = floor * nonzero + if floor == 64 { 64 } else { floor / 4 } * zero;
    standard.max(floor_gas)
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
    /// Without the claims' frame and intrinsic gas.
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    pub calls: usize,
    pub pcs_words: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
    /// The verifying contract's deployment: its code bytes, the execution, and the transaction gas under EIP-7623
    /// without the base.
    pub deployment: (usize, u64, u64),
}

impl GasReport {
    /// Transaction gas without its 21,000 base: `floor` 40 for EIP-7623 (10 a zero byte), 64 for EIP-7976; with
    /// `claims`, the frame of PCS claims too (`1 + 32` bytes a claim, counted nonzero) and their intrinsic gas.
    pub fn transaction(&self, claims: bool, floor: u64) -> u64 {
        let frame = if claims { 1 + 32 * self.calls as u64 } else { 0 };
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64 + frame;
        let zero = self.calldata_zero_bytes as u64;
        let standard = 16 * nonzero + 4 * zero + self.execution;
        let floor_gas = floor * nonzero + if floor == 64 { 64 } else { floor / 4 } * zero;
        let intrinsic = if claims { machine::dependency_gas(self.calls) } else { 0 };
        standard.max(floor_gas) + intrinsic
    }

    pub fn calldata_gas(&self) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        16 * nonzero + 4 * self.calldata_zero_bytes as u64
    }

    /// The report's table, as text.
    pub fn table(&self, name: &str) -> String {
        let mut s = String::new();
        let line = |s: &mut String, t: String| {
            s.push_str(&t);
            s.push('\n');
        };
        line(&mut s, format!("== {name}"));
        line(
            &mut s,
            format!(
                "calldata {} B ({} zero, stream {} B), calldata gas {}; code {} B; {} FIELD_MUL, {} XOR, {} hashes ({} B), {} checks, memory {} words",
                self.calldata_bytes,
                self.calldata_zero_bytes,
                self.stream_bytes,
                self.calldata_gas(),
                self.code_bytes,
                self.field_muls,
                self.xors,
                self.hashes,
                self.hashed_bytes,
                self.checks,
                self.memory_words
            ),
        );
        line(
            &mut s,
            format!(
                "execution: {}; {} claims in {} declared, {} words hashed",
                self.execution,
                self.claims,
                self.calls,
                self.pcs_words
            ),
        );
        for p in &self.phases {
            line(&mut s, format!("   {:>7}  {}", p.gas, p.phase));
        }
        line(
            &mut s,
            format!(
                "   deployment: {} B of code, {} execution, {} tx (EIP-7623, no base)",
                self.deployment.0, self.deployment.1, self.deployment.2
            ),
        );
        line(
            &mut s,
            format!(
                "EIP-7623 (no base): {}, with the claims' frame and intrinsic gas {}; EIP-7976: {} / {}",
                self.transaction(false, 40),
                self.transaction(true, 40),
                self.transaction(false, 64),
                self.transaction(true, 64)
            ),
        );
        s
    }
}

/// A stream of the right length, its bytes pseudo-random as a proof's are (the contract's gas does not depend on them;
/// the transaction's does, on its zero bytes only).
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

fn phases_of(codes: &[&[u64]], tags: &dyn Fn(usize, usize) -> &'static str) -> Vec<PhaseGas> {
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (code, gas_by_pc) in codes.iter().enumerate() {
        for (pc, &gas) in gas_by_pc.iter().enumerate() {
            if gas == 0 {
                continue;
            }
            let phase = tags(code, pc);
            match phases.iter_mut().find(|p| p.phase == phase) {
                Some(p) => p.gas += gas,
                None => phases.push(PhaseGas { phase, gas }),
            }
        }
    }
    phases
}

/// Measure the contract: run its measuring build on sample calldata with every claim declared, and check the phases
/// against the total; and deploy the verifying build.
pub fn measure(inst: &Instance, recorded: &Recorded) -> GasReport {
    let contract = compile_verifier(inst, recorded, true);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let calls = calls(inst, recorded);
    let claims: usize = inst.pi1.len() + 4;
    // A frame declaring every claim that is well formed under the registry (the format is checked even in a
    // measuring run).
    let mut attesting = PcsFrame::decoding(registry(inst));
    attesting.declare_all = true;
    let outcome: Outcome = call(&contract.code, &[], &data, &attesting);
    assert_eq!(
        outcome.output.as_deref(),
        Some(&word([1, 0, 0])[..]),
        "the measuring run returns 1"
    );
    assert_eq!(outcome.claims.len(), calls.len(), "one claim per commitment");
    let mut phases = phases_of(&[&outcome.gas_by_pc], &|_, pc| {
        contract.phase_of.get(pc).copied().unwrap_or(CALLS)
    });
    let total: u64 = phases.iter().map(|p| p.gas).sum();
    assert_eq!(total, outcome.execution, "the instructions' gas is the execution's");
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    assert_eq!(
        measured,
        contract.checks as u64 + calls.len() as u64,
        "one JUMPDEST a check and a claim"
    );
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    let report = GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims,
        calls: calls.len(),
        pcs_words: calls.iter().map(Vec::len).sum(),
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
        deployment: deployment(&compile_verifier(inst, recorded, false)),
    };
    report
}

/// `contract` deployed by a transaction (no constructor arguments): its code bytes, the deployment's execution, and
/// its transaction gas under EIP-7623 without the base.
fn deployment(contract: &Contract) -> (usize, u64, u64) {
    let init = evm_link::creation_code(&contract.code, &[]);
    let mut chain = Chain::default();
    let (address, execution) = chain.deploy(&init);
    let address = address.expect("the contract deploys");
    assert_eq!(chain.code(address), contract.code);
    (contract.code.len(), execution, machine::transaction_gas(&init, execution, 40) - 21_000)
}
