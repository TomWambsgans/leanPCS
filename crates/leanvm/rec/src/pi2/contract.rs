// Part of this repository. The recording, compilation, measurement and parity follow
// crates/leanvm/univariate/src/contract.rs (itself after crates/membership/evm/src/quotient.rs). MIT OR Apache-2.0; see
// AGENTS.md.
//! π2's verifier as a contract: [`super::verifier::reduce`] recorded on `leanvm_statement`'s symbol, compiled to
//! straight-line EVM code (`leanvm_statement::evm::codegen`, `crates/evm_link`), run on revm with `FIELD_MUL` and
//! EIP-8141's frame introspection over a frame of PCS claims (`leanvm_statement::evm::machine`).
//!
//! **Calldata** (no selector: the verifier is the only entry): π1's public input (32 bytes, which the seed hashes), the
//! stream: `W`'s commitment (root, out-of-domain answer), `Q`'s, the values at `t`; then a byte, the index of the
//! transaction's frame of PCS claims. **Claims**, each the EIP draft's PCS claim (`crates/pcs_claim`,
//! `docs/PCS_CLAIM.md`), declared in that frame in order: π1's three, whose Keccak-256s (payloads 0 … 2) the contract
//! reads into the seed and π2's circuit computes from π1's run (`docs/leanvm/rec/SPEC-REC.md` §2.4.6); then π2's five,
//! checked declared at payloads 3 … 7 (`evm_link::declared_claims`): `W`, the setup (its commitment a constant of the
//! code), `Q`'s identity, pushes and sum (`verifier::Reduced::claims`). A claim's fields are written once each (the
//! setup's point `W`'s digits, `Q`'s claims their `u`), packed and hashed where it is checked.
//!
//! Every root is a commitment's 32 bytes as they are: π2's `W` and `Q` in calldata as its stream carries them, the
//! setup's a constant; the out-of-domain answers are calldata's elements (after their roots) or a constant (the
//! setup's).

use std::sync::{Arc, Mutex, OnceLock};

use evm_link::Claim as Fields;
use fiat_shamir::merkle::Hash;
use leanvm_statement::evm::codegen::{CALLS, Claim, Contract, Ending, Entry, MEASURE, Word, compile};
pub use leanvm_statement::evm::deploy::{PhaseGas, sample_stream};
use leanvm_statement::evm::deploy::{phases, sample_calldata_gas, sample_tx_gas};
use leanvm_statement::evm::machine::{
    Chain, FrameTxGas, Outcome, PCS_FRAME, PcsFrame, call, element_word, frame_tx_gas, transaction_gas,
};
use leanvm_statement::evm::record::{Graph, Recorder, Sym, record};
use leanvm_statement::field::E;
use leanvm_statement::transcript::{Checks, KeccakChannel};
use pcs_claim::PcsClaim;
use primitives::field::F192;

use super::circuit::{Circuit, Read};
use super::verifier::{NAME, Reduced, Spec, reduce, statement_words};
use crate::circuit::spec::CallWord;

/// What the contract is built for: the circuit's verifier, its IV, the setup's commitment, and π1's calls. Built by
/// [`Instance::new`] from the validated circuit, which derives the IV.
pub struct Instance<'a> {
    pub spec: &'a Spec,
    pub iv: [u8; 32],
    pub setup_root: Hash,
    pub setup_ood: F192,
    pub pi1: &'a [Vec<CallWord>],
}

impl<'a> Instance<'a> {
    /// The instance of `circuit` (validated here), its verifier `spec` (`Spec::of(circuit)`), the setup's commitment
    /// (of `circuit`'s `σ`, `κ`: `prover::Setup::new(circuit)`'s `root()` and `ood()`), π1's contract IV (the circuit
    /// compiler's, `Compiled::pi1_iv`, derived from π1's recorded verifier) and π1's calls (the circuit's,
    /// `spec::Circuit::calls`). The IV is `prover::iv` of them.
    pub fn new(
        circuit: &Circuit,
        spec: &'a Spec,
        setup_root: Hash,
        setup_ood: F192,
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
        // `pi1` are π1's claims the circuit does not hash, the frame payloads it reads its hashed ones: together π1's
        // claims, each once, as [`payloads`] numbers them (`pi1.len() + hashed`).
        let hashed = frame_payloads(spec);
        let total = pi1.len() + hashed.len();
        assert!(
            hashed.windows(2).all(|p| p[0] < p[1]) && hashed.iter().all(|&p| (p as usize) < total),
            "π1's calls are the circuit's claims it does not hash: {} calls, hashed payloads {hashed:?}",
            pi1.len()
        );
        Self {
            spec,
            iv: super::prover::iv(pi1_iv, &circuit.digest(), &setup_root, setup_ood, circuit.log_n),
            setup_root,
            setup_ood,
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
            Read::Scalar | Read::Narrow => elements.push(at),
            Read::Integer(_) | Read::Frame(_) => {}
        }
        at += r.scalars();
    }
    (roots, elements)
}

/// The frame's payloads the verifier reads as public words (`Read::Frame`: π1's claims hashed in the circuit), in
/// order: what the seed hashes after the public input.
pub fn frame_payloads(spec: &Spec) -> Vec<u8> {
    spec.reads
        .iter()
        .filter_map(|r| match r {
            Read::Frame(p) => Some(*p),
            _ => None,
        })
        .collect()
}

/// Each claim the contract encodes ([`calls`]), its payload's index in the frame of PCS claims: π1's claims are
/// payloads `0, 1, …` (those hashed in the circuit the verifier reads instead), then π2's five.
pub fn payloads(inst: &Instance) -> Vec<usize> {
    let hashed: Vec<usize> = frame_payloads(inst.spec).iter().map(|&p| p as usize).collect();
    let pi1 = inst.pi1.len() + hashed.len();
    (0..pi1).filter(|p| !hashed.contains(p)).chain(pi1..pi1 + 5).collect()
}

/// The number `n` as a word.
pub fn number(n: u64) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&n.to_be_bytes());
    bytes
}

/// The claims' fields, in order (π1's the circuit does not hash, then π2's five), each the payload of its index in
/// [`payloads`], for any word type.
fn claim_words<T: Copy, W: Clone>(
    inst: &Instance,
    reduced: &Reduced<T>,
    roots_at: &[usize],
    stream: impl Fn(usize) -> W,
    constant: impl Fn([u8; 32]) -> W,
    scalar: impl Fn(T) -> W,
) -> Vec<Fields<W>> {
    let (_, elements) = read_indices(inst.spec);
    let roots = inst.spec.reads.iter().filter(|r| **r == Read::Root).count();
    let word = |w: &CallWord| match *w {
        CallWord::Const(bytes) => constant(bytes),
        CallWord::Root(i) => stream(roots_at[i as usize]),
        CallWord::Element(i) => scalar(reduced.public[elements[i as usize]]),
        CallWord::Pair { element, coordinate } => scalar(reduced.pair_points[elements[element as usize]][coordinate as usize]),
    };
    let payloads = payloads(inst);
    let mut out: Vec<Fields<W>> = inst
        .pi1
        .iter()
        .map(|c| {
            assert!(c.len() >= 3, "a claim's root, out-of-domain answer, point and value");
            let point = c[2..c.len() - 1].iter().map(word).collect();
            Fields { root: word(&c[0]), ood: word(&c[1]), point, value: word(&c[c.len() - 1]), index: 0 }
        })
        .collect();
    let field = |root: W, ood: W, (point, value): &(Vec<T>, T)| -> Fields<W> {
        Fields { root, ood, point: point.iter().map(|&x| scalar(x)).collect(), value: scalar(*value), index: 0 }
    };
    let [w_ood, q_ood] = reduced.oods;
    let (w_root, q_root) = (|| stream(roots_at[roots]), || stream(roots_at[roots + 1]));
    // W, the setup (its point's `w_4 … w_{m-1}` W's: written once), then Q's three.
    out.push(field(w_root(), scalar(w_ood), &reduced.witness));
    out.push(field(
        constant(inst.setup_root),
        constant(element_word(E::new(inst.setup_ood.c0, inst.setup_ood.c1, inst.setup_ood.c2))),
        &reduced.setup,
    ));
    out.push(field(q_root(), scalar(q_ood), &reduced.quotient));
    out.push(field(q_root(), scalar(q_ood), &reduced.pushes));
    out.push(field(q_root(), scalar(q_ood), &reduced.sum));
    assert_eq!(out.len(), payloads.len(), "a payload a claim");
    out.iter_mut().zip(payloads).for_each(|(claim, index)| claim.index = index);
    out
}

/// The claims as the contract's words (each the payload of its index in [`payloads`]).
pub fn calls(inst: &Instance, recorded: &Recorded) -> Vec<Claim> {
    claim_words(
        inst,
        &recorded.reduced,
        &recorded.roots_at,
        Word::Stream,
        Word::Const,
        |s: Sym| Word::Node(s.0),
    )
}

/// The claims the Rust verifier's reduction of `stream` gives, as words: what the contract must write.
pub fn expected_calls(inst: &Instance, recorded: &Recorded, reduced: &Reduced<E>, stream: &[u8]) -> Vec<Fields<[u8; 32]>> {
    claim_words(
        inst,
        reduced,
        &recorded.roots_at,
        |at| stream[at..at + 32].try_into().unwrap(),
        |b| b,
        element_word,
    )
}

/// The claims the Rust verifier's reduction of `stream` gives, as PCS claims: what the transaction must declare, in
/// order, and the block's openings prove.
pub fn expected_claims(inst: &Instance, recorded: &Recorded, reduced: &Reduced<E>, stream: &[u8]) -> Vec<PcsClaim> {
    expected_calls(inst, recorded, reduced, stream).iter().map(PcsClaim::of_words).collect()
}

/// A PCS claim from its words in order (root, out-of-domain answer, point, value; elements with their top 64 bits
/// zero).
pub fn claim_of_words(words: &[[u8; 32]]) -> PcsClaim {
    let n = words.len() - 3;
    PcsClaim::of_words(&Fields {
        root: words[0],
        ood: words[1],
        point: words[2..2 + n].to_vec(),
        value: words[2 + n],
        index: 0,
    })
}

/// A frame of PCS claims declaring `claims`, in order.
pub fn block(claims: &[PcsClaim]) -> PcsFrame {
    PcsFrame::of(claims.iter().map(PcsClaim::encode))
}

fn entry(inst: &Instance, recorded: &Recorded, measure: bool) -> Entry {
    Entry {
        name: NAME,
        iv: inst.iv,
        stream_len: recorded.stream_len,
        measure,
        frame: frame_payloads(inst.spec),
    }
}

/// The contract: it reverts unless its transaction declares every claim, and returns the word 1.
pub fn compile_verifier(inst: &Instance, recorded: &Recorded, measure: bool) -> Contract {
    let ending = Ending::Claims(calls(inst, recorded));
    compile(&recorded.graph, &[], &ending, &entry(inst, recorded, measure))
}

/// Calldata verifying a proof: π1's public input, the stream, then the index of the transaction's frame of PCS claims
/// ([`PCS_FRAME`]). No selector: the verifier is the contract's only entry (`docs/leanvm/rec/SPEC-REC.md` §12).
pub fn calldata(public_input: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [public_input, stream, &[PCS_FRAME]].concat()
}

/// Where π2's calldata holds the stream.
pub const STREAM_AT: usize = 32;

/// The Rust verifier's reduction, and the values it required to be zero, then nonzero.
pub type Checked = (Reduced<E>, Vec<E>, Vec<E>);

/// The Rust verifier on the same calldata, every check collected; `frame` the words its frame payloads hold
/// ([`frame_payloads`], in order).
pub fn rust_verifier(
    inst: &Instance,
    public_input: &[u8; 32],
    frame: &[[u8; 32]],
    stream: &[u8],
) -> Result<Checked, leanvm_statement::VerifierError> {
    let seed = super::verifier::seed(&inst.iv, public_input, frame);
    let mut channel = KeccakChannel::new(
        seed,
        stream,
        Checks::Collect {
            zero: vec![],
            nonzero: vec![],
        },
    );
    channel.frame = frame.to_vec();
    let reduced = reduce(inst.spec, statement_words(public_input), &mut channel)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

fn expected_return(
    inst: &Instance,
    recorded: &Recorded,
    public_input: &[u8; 32],
    frame: &[[u8; 32]],
    stream: &[u8],
) -> Vec<[u8; 32]> {
    let (reduced, zero, nonzero) = rust_verifier(inst, public_input, frame, stream).expect("the stream's length");
    let mut out: Vec<[u8; 32]> = expected_calls(inst, recorded, &reduced, stream).iter().flat_map(Fields::words).collect();
    out.extend(zero.iter().chain(&nonzero).map(|&x| element_word(x)));
    out
}

fn compare(output: &[u8], expected: &[[u8; 32]]) {
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
}

/// Sample claims for the payloads the verifier reads ([`frame_payloads`]): a measurement's or a parity's on a sample
/// stream, which no claim of π1's is.
pub fn sample_hashed(inst: &Instance) -> Vec<Vec<u8>> {
    (0..frame_payloads(inst.spec).len()).map(|j| vec![0x33 + j as u8; 8]).collect()
}

/// A frame whose payloads [`frame_payloads`] declare `hashed` (encoded claims, in order), the others any claim.
pub fn frame_declaring(inst: &Instance, hashed: &[Vec<u8>]) -> PcsFrame {
    let payloads = frame_payloads(inst.spec);
    assert_eq!(payloads.len(), hashed.len(), "a claim a frame payload read");
    let len = payloads.iter().map(|&p| p as usize + 1).max().unwrap_or(0);
    let mut frame = PcsFrame::of((0..len).map(|i| match payloads.iter().position(|&p| p as usize == i) {
        Some(j) => hashed[j].clone(),
        None => vec![0x5a; 8],
    }));
    frame.read = payloads.iter().map(|&p| p as usize).collect();
    frame
}

/// The contract, built to return the claims it would check declared and every value it checks, against the Rust verifier
/// on the same calldata: word for word. `hashed` are the claims the frame declares at the payloads the verifier reads
/// ([`frame_payloads`]; any bytes). Returns the words compared.
pub fn parity(
    inst: &Instance,
    recorded: &Recorded,
    public_input: &[u8; 32],
    hashed: &[Vec<u8>],
    stream: &[u8],
) -> usize {
    let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
    let outputs: Vec<Word> = (calls(inst, recorded).iter().flat_map(Claim::words))
        .chain(checks.map(|&(id, _)| Word::Node(id)))
        .collect();
    let contract = compile(&recorded.graph, &outputs, &Ending::Return, &entry(inst, recorded, true));
    let outcome = call(
        &contract.code,
        &[],
        &calldata(public_input, stream),
        &frame_declaring(inst, hashed),
    );
    let frame: Vec<[u8; 32]> = hashed.iter().map(|c| leanvm_statement::transcript::keccak256(c)).collect();
    let expected = expected_return(inst, recorded, public_input, &frame, stream);
    compare(&outcome.output.expect("the measuring build does not revert"), &expected);
    expected.len()
}

/// A verifying contract compiled, and the IV of its instance.
type CachedCode = ([u8; 32], Arc<Vec<u8>>);

/// The verifying contract's call on `calldata`, its frame of PCS claims declaring exactly `claims`, in order
/// ([`block`]; the payloads [`frame_payloads`] public data). The contract is compiled once per instance (the last one
/// asked for).
fn verifying_call(inst: &Instance, recorded: &Recorded, calldata: &[u8], claims: &[PcsClaim]) -> Outcome {
    // The contract is a function of the instance, which its IV binds (π1's IV, the circuit's digest, the setup).
    static CODE: OnceLock<Mutex<Option<CachedCode>>> = OnceLock::new();
    let code = {
        let mut cache = CODE.get_or_init(Default::default).lock().expect("the cached contract");
        match &*cache {
            Some((iv, code)) if *iv == inst.iv => code.clone(),
            _ => {
                let code = Arc::new(compile_verifier(inst, recorded, false).code);
                *cache = Some((inst.iv, code.clone()));
                code
            }
        }
    };
    let mut frame = block(claims);
    frame.read = frame_payloads(inst.spec).iter().map(|&p| p as usize).collect();
    call(&code, &[], calldata, &frame)
}

/// The verifying contract on `calldata`, its frame of PCS claims declaring exactly `claims`, in order ([`block`]):
/// whether it returned the word 1, and the claims it checked.
pub fn run(inst: &Instance, recorded: &Recorded, calldata: &[u8], claims: &[PcsClaim]) -> (bool, Vec<Vec<u8>>) {
    let outcome = verifying_call(inst, recorded, calldata, claims);
    (outcome.attests(), outcome.claims)
}

/// The verifying contract's execution gas on `calldata` (without the claims' frame and PCS gas), and whether it
/// accepted.
pub fn verifying_execution(inst: &Instance, recorded: &Recorded, calldata: &[u8], claims: &[PcsClaim]) -> (bool, u64) {
    let outcome = verifying_call(inst, recorded, calldata, claims);
    (outcome.attests(), outcome.execution)
}

/// A verifying call's frame-transaction gas (EIP-8141, EIP-7976's floor; without `FRAME_TX_INTRINSIC_COST` and the
/// per-frame costs): its `calldata` and `execution`, and its frame of PCS claims declaring `claims` (or none).
pub fn transaction_of(calldata: &[u8], execution: u64, claims: &[PcsClaim]) -> FrameTxGas {
    let data = if claims.is_empty() { Vec::new() } else { block(claims).data() };
    frame_tx_gas(calldata, execution, &data, claims.len())
}

/// What a verifying call costs.
#[derive(Clone, Debug)]
pub struct GasReport {
    pub calldata_bytes: usize,
    pub calldata_zero_bytes: usize,
    pub stream_bytes: usize,
    /// Without the claims' frame and PCS gas.
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    /// The claims its frame declares: those it encodes, and π1's hashed in the circuit, whose hashes it reads.
    pub declared: usize,
    pub pcs_words: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
    /// The verifying contract's deployment: its code bytes, the execution, and the creation transaction's gas without
    /// its base (EIP-7976's floor).
    pub deployment: (usize, u64, u64),
}

impl GasReport {
    /// The frame transaction's gas (EIP-8141, EIP-7976's floor; without `FRAME_TX_INTRINSIC_COST` and the per-frame
    /// costs), this sample calldata's zero bytes and the execution; with `claims`, a frame of PCS claims of
    /// `self.claims` claims (`1 + 32` bytes a claim, their hashes counted nonzero) and their PCS gas.
    pub fn transaction(&self, claims: bool) -> FrameTxGas {
        let claims = if claims { self.declared } else { 0 };
        sample_tx_gas(self.calldata_bytes, self.calldata_zero_bytes, self.execution, claims)
    }

    pub fn calldata_gas(&self) -> u64 {
        sample_calldata_gas(self.calldata_bytes, self.calldata_zero_bytes)
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
                "execution: {}; {} claims declared, {} encoded, {} words written for them",
                self.execution, self.declared, self.claims, self.pcs_words
            ),
        );
        for p in &self.phases {
            line(&mut s, format!("   {:>7}  {}", p.gas, p.phase));
        }
        line(
            &mut s,
            format!(
                "   deployment: {} B of code, {} execution, {} tx (EIP-7976 floor, no base)",
                self.deployment.0, self.deployment.1, self.deployment.2
            ),
        );
        let (alone, with) = (self.transaction(false), self.transaction(true));
        line(
            &mut s,
            format!(
                "frame transaction (EIP-8141, EIP-7976 floor; sample calldata): standard {} / floor {}; with the frame of \
                 PCS claims and pcs_gas: standard {} / floor {}, paid {}",
                alone.standard, alone.floor, with.standard, with.floor, with.total
            ),
        );
        s
    }
}

/// Measure the contract: run its measuring build on sample calldata with every claim declared, and check the phases
/// against the total; and deploy the verifying build.
pub fn measure(inst: &Instance, recorded: &Recorded) -> GasReport {
    let contract = compile_verifier(inst, recorded, true);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let calls = calls(inst, recorded);
    // The measuring build never reverts: a frame of sample claims at the payloads it reads will do (its gas is the
    // same).
    let outcome = call(&contract.code, &[], &data, &frame_declaring(inst, &sample_hashed(inst)));
    assert!(outcome.attests(), "the measuring run returns 1");
    assert_eq!(outcome.claims.len(), calls.len(), "one claim per commitment");
    let mut phases = phases(&outcome.gas_by_pc, &contract.phase_of, CALLS);
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
    GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims: calls.len(),
        declared: calls.len() + frame_payloads(inst.spec).len(),
        pcs_words: calls.iter().map(|c| c.words().len()).sum(),
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
        deployment: deployment(&compile_verifier(inst, recorded, false)),
    }
}

/// `contract` deployed by a transaction (no constructor arguments): its code bytes, the deployment's execution, and
/// its transaction gas with EIP-7976's floor, without the base.
fn deployment(contract: &Contract) -> (usize, u64, u64) {
    let init = evm_link::creation_code(&contract.code, &[], None);
    let mut chain = Chain::default();
    let (address, outcome) = chain.deploy(&init);
    let address = address.expect("the contract deploys");
    assert_eq!(chain.code(address), contract.code);
    (contract.code.len(), outcome.execution, transaction_gas(&init, outcome.execution) - 21_000)
}
