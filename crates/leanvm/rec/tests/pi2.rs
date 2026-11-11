// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2's PIOP (`src/pi2`, `PI2.md`), end to end on synthetic circuits built with the interface, D16v:
//!
//! - `small_*`: the honest proof's four claims hold and their openings verify (`pcs_claim::verify_claim`, what the
//!   block proves); a witness that breaks one copy, one formula or one public element leaves a false claim; a
//!   flipped byte of the stream gives claims the openings do not prove;
//! - `the_copy_sum_from_the_layout`: no claim reads the copy argument's sum (`PI2.md` §7): a dishonest port, the
//!   identity kept at its hole, leaves the identity's claim false whatever the prover does with `x h`'s coefficient `N`;
//!   the negative control: the same cheat meets the relation of a layout reading `G` through `Z_V`; `G` or `S` filled
//!   in an honest `Q`: a false claim;
//! - `the_interface_example`: the circuit compiler's own example (`circuit::spec::example`), padded, through the
//!   adapter;
//! - `contract_*`: the verifier compiled to EVM is the Rust verifier word for word, and
//!   accepts the honest proof with its frame of PCS claims declaring them, and rejects a flipped byte;
//! - `gas_report` (ignored): the contract at the D16v target shape (`N = 2^24`);
//! - `prove_target` (ignored): the prover at the target shape.
//!
//! `cargo test --release -p leanvm_rec --test pi2 -- --nocapture` (and `--ignored gas_report`).

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use leanvm_statement::evm::machine::element_word;
use leanvm_statement::field::E;
use pcs_claim::PcsClaim;
use leanvm_rec::circuit::spec::{self, CallWord};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::{Circuit, NONE};
use leanvm_rec::pi2::contract::{self, Instance, calldata, record_verifier, sample_stream};
use leanvm_rec::pi2::prover::{
    self, Cheat, PublicValue, Proved, Setup, claims_hold, open, prove, prove_cheating, prove_with, public_scalars,
    verify_openings,
};
use leanvm_rec::pi2::synth::{self, Built, Design};
use leanvm_rec::pi2::verifier::{Spec, to_f192};
use primitives::field::{F64, F192};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

const PI1_IV: [u8; 32] = [0x11; 32];

struct Fixture {
    circuit: Circuit,
    witness: Vec<F64>,
    public_input: [u8; 32],
    values: Vec<PublicValue>,
    spec: Spec,
    setup: Setup,
    iv: [u8; 32],
}

fn fixture(circuit: Circuit, witness: Vec<F64>, public_input: [u8; 32], values: Vec<PublicValue>) -> Fixture {
    let public = public_scalars(&public_input, &values);
    circuit
        .check(&witness, &public, F192::new(0x1234, 0x5678, 0x9abc))
        .expect("the witness satisfies the circuit");
    let spec = Spec::of(&circuit);
    let setup = Setup::new(&circuit);
    let iv = prover::iv(&PI1_IV, &circuit.digest(), &setup.root(), setup.ood(), circuit.log_n);
    Fixture {
        circuit,
        witness,
        public_input,
        values,
        spec,
        setup,
        iv,
    }
}

fn built(design: &Design) -> Fixture {
    let Built {
        circuit,
        witness,
        public_input,
        values,
        ..
    } = synth::build(design, 0x5eed);
    fixture(circuit, witness, public_input, values)
}

/// Positions whose value nothing constrains: pull-less ones, and spare self-loops no formula reads.
fn unconstrained(circuit: &Circuit) -> Vec<bool> {
    let pair_of = circuit.pair_of();
    let pulls = circuit.pulls();
    let width = circuit.width();
    let mut read = vec![false; circuit.n()];
    for (i, &p) in pair_of.iter().enumerate() {
        if p != NONE {
            let row = i & !(width - 1);
            for c in circuit.formulas[circuit.pairs[p as usize].formula].cells() {
                read[row + c] = true;
            }
        }
    }
    (0..circuit.n())
        .map(|i| !pulls[i] || (pair_of[i] == NONE && circuit.sigma[i] as usize == i && !read[i]))
        .collect()
}

fn honest_and_mutated(f: &Fixture, mutations: usize) {
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    assert_eq!(
        claims_hold(&proved, &f.setup),
        [true; 4],
        "the honest proof's claims hold"
    );
    let stream = proved.stream.clone();
    println!(
        "2^{} positions, rows of {}: {} pairs, {} groups, {} public terms; stream {} B; prover {:?}",
        f.circuit.log_n,
        f.circuit.width(),
        f.circuit.pairs.len(),
        f.spec.groups.len(),
        f.circuit.public.len(),
        stream.len(),
        proved.timings
    );
    let (reduced, roots, openings) = open(proved, &f.setup);
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), f.setup.ood(), &openings),
        Ok(())
    );

    // A flipped byte of the stream: the claims are not the ones the openings prove.
    for at in [0, stream.len() / 2, stream.len() - 1] {
        let mut bad = stream.clone();
        bad[at] ^= 0x20;
        let other = leanvm_rec::pi2::verifier::verify(&f.spec, &f.iv, &f.public_input, &[], &bad).expect("the length");
        assert!(
            verify_openings(f.circuit.log_n, &other, &roots, &f.setup.root(), f.setup.ood(), &openings).is_err(),
            "byte {at} flipped"
        );
    }

    // Witnesses that break one push: some claim is false.
    let free = unconstrained(&f.circuit);
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut tried = 0;
    while tried < mutations {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let i = (state % f.circuit.n() as u64) as usize;
        if free[i] {
            continue;
        }
        tried += 1;
        let mut bad = f.witness.clone();
        bad[i] += F64(1 + (state >> 40));
        let proved = prove_with(
            &f.circuit,
            &f.spec,
            &f.setup,
            &f.iv,
            &f.public_input,
            &f.values,
            &bad,
            false,
        );
        let holds = claims_hold(&proved, &f.setup);
        assert!(holds.contains(&false), "position {i} changed: {holds:?}");
    }
    // A public element changed.
    let mut values = f.values.clone();
    let k = values
        .iter()
        .position(|v| matches!(v, PublicValue::Scalar(_)))
        .expect("an element");
    if let PublicValue::Scalar(x) = &mut values[k] {
        *x += F192::new(0, 1, 0);
    }
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &values,
        &f.witness,
        false,
    );
    // The prover keeps the identity a polynomial one (`h = T / (d_pull d_push)` at the dishonest hole): the copy
    // argument's sum is not zero (PI2.md §7), so `x h` does not fit `H`'s slot, and the identity's claim is the false
    // one (`PI2.md` §7).
    assert_eq!(
        claims_hold(&proved, &f.setup),
        [true, true, false, true],
        "a public element changed"
    );
    let mut public_input = f.public_input;
    public_input[3] ^= 4;
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &public_input,
        &f.values,
        &f.witness,
        false,
    );
    assert_eq!(
        claims_hold(&proved, &f.setup),
        [true, true, false, true],
        "the public input changed"
    );
}

#[test]
fn small_d16v() {
    honest_and_mutated(&built(&synth::small_d16v(11)), 24);
}

/// The circuit compiler's example (`N = 32`), on `2^log_n` positions: the rows past it in no block (forwards, self-loops
/// of 0), the ports' tags moved past the new `N`.
fn padded_example(log_n: u8) -> (spec::Circuit, spec::Witness, spec::PublicInputs) {
    let (mut c, mut w, public) = spec::example();
    let (old, n) = (c.n(), 1usize << log_n);
    c.sigma = c
        .sigma
        .iter()
        .map(|&s| {
            if (s as usize) < old {
                s
            } else {
                s - old as u32 + n as u32
            }
        })
        .chain(old as u32..n as u32)
        .collect();
    c.log_n = log_n;
    w.resize(n, leanvm_statement::field::K(0));
    (c, w, public)
}

#[test]
fn the_interface_example() {
    let (c, w, public) = padded_example(11);
    assert_eq!(c.check(&w, &public), Ok(()));
    let circuit = adapt::adapt(&c);
    let (public_input, values) = adapt::public_values(&public);
    let f = fixture(circuit, adapt::witness(&w), public_input, values);
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    assert_eq!(claims_hold(&proved, &f.setup), [true; 4]);
    let (reduced, roots, openings) = open(proved, &f.setup);
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), f.setup.ood(), &openings),
        Ok(())
    );
    // The value the port binds, changed: the copy sum is not zero, and the identity's claim is false (PI2.md §7).
    let mut other = public.clone();
    other.elements[0] = leanvm_statement::field::E::new(1, 0, 0);
    let (_, values) = adapt::public_values(&other);
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &values,
        &f.witness,
        false,
    );
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, false, true]);
}

/// `Q`'s identity at `t`, read off the stack slot by slot: the relation the identity's claim checks, and the one a
/// layout reading `G` through `Z_V` alone would (the negative control). With `F_s` the slot `s` at `t`'s position
/// coordinates (`(t / Z_V) f_s(t)`), `E_jk = Σ_{l<3} Y^l F_(j + 2k + 4l)`, `K_jk = F_(j + 2k + 12)` and the identity's
/// ratios `a = z_0 / (1 + z_0) = t Z_V / c_h`, `b = a Z_V`: the claim holds iff `E_00 + a E_10 + b E_01 + a b E_11 =
/// target`, `target` its value over `(1 + z_0)(1 + z_1) scale` less the limb code 3's share `Y³ (K_00 + a K_10 + b
/// K_01 + a b K_11)`. The other layout (`H`, `G` at one kind, `q`'s digits at the other: `G` weighs `Z_V` against `H`)
/// checks `E_00 + Z_V E_11 + a E_10 + b E_01 = target`. Returns whether each holds: (this layout's, the other's).
fn identity_relations(proved: &Proved) -> (bool, bool) {
    let (point, value) = leanvm_rec::pi2::verifier::claim(&proved.reduced.quotient);
    let q = &proved.quotient.0;
    let m = point.len() - 4;
    // `u_0 = t / (1 + t)`.
    let t = point[0] * (F192::ONE + point[0]).inv();
    let z = (0..m).fold(t, |x, _| x * x + x);
    let ratio = |c: F192| c * (F192::ONE + c).inv();
    let (a, b) = (ratio(point[m]), ratio(point[m + 1]));
    assert_eq!(b, a * z, "the identity's digit ratio");
    let at = |slot: usize| {
        let bits: Vec<F192> = (0..4).map(|k| F192::from(F64(((slot >> k) & 1) as u64))).collect();
        pcs_claim::evaluate_lanes(q, &[&point[..m], &bits[..]].concat())
    };
    let f: Vec<F192> = (0..16).map(at).collect();
    let y = F192::Y;
    let y3 = y * y * y;
    let e = |j: usize, k: usize| f[j + 2 * k] + y * f[j + 2 * k + 4] + y * y * f[j + 2 * k + 8];
    let kp = |j: usize, k: usize| f[j + 2 * k + 12];
    let (_, scale) = leanvm_rec::pi2::verifier::extension();
    let weights = (F192::ONE + point[m]) * (F192::ONE + point[m + 1]) * scale;
    let target = value * weights.inv() + y3 * (kp(0, 0) + a * kp(1, 0) + b * kp(0, 1) + a * b * kp(1, 1));
    let this = e(0, 0) + a * e(1, 0) + b * e(0, 1) + a * b * e(1, 1);
    let other = e(0, 0) + z * e(1, 1) + a * e(1, 0) + b * e(0, 1);
    (this == target, other == target)
}

/// No claim reads the copy argument's sum (`PI2.md` §7): `H = x h` in one slot of `N` words, the identity's
/// claim reading `G` through `t² Z_V³ / c_h` (as the polynomial `x² Z_V³` after its product by `d_pull d_push`), force
/// `H(0) = 0`, so `h = H / x` has degree below `N - 1` and sums to zero on `V_m`.
///
/// - A dishonest port (a public element changed), the identity kept at its hole (`h = T / (d_pull d_push)`): the sum
///   is not zero, and whatever the prover does with `x h`'s coefficient `N` (drops it, which moves `h(0)`; keeps it in
///   `q`; drops it and puts the sum in `G`), the identity's claim is false and the other three hold.
/// - The negative control: the last cheat (`Cheat::AbsorbInG`) meets the identity's relation of a layout that reads `G`
///   through `Z_V` (`H` and `G` at one kind, `q`'s two digits at the other): there `D Z_V G` cancels `σ D Z_V`, `x h`'s
///   overflow, as polynomials. Here it does not. On a witness (`σ = 0`) the cheat is the honest proof: every claim holds.
/// - An honest `Q` with `G` filled: the identity's claim is false; with `S` filled: the identity's and the pushes'
///   (which reads `S` at `ρ²`). And `s` sent off `P(t)`: the pushes' claim is false. A constant added to `H`: the
///   identity's claim false; `S = c` with `G = Y³ c` (cancelling in the identity's claim): the pushes' claim alone false;
///   `P`'s constant moved after `q_P`: both of `Q`'s claims false.
#[test]
fn the_copy_sum_from_the_layout() {
    let f = built(&synth::small_d16v(11));
    let prove_as = |values: &[PublicValue], cheat: Cheat| {
        prove_cheating(
            &f.circuit,
            &f.spec,
            &f.setup,
            &f.iv,
            &f.public_input,
            values,
            &f.witness,
            false,
            cheat,
        )
    };
    // On a witness: the cheats that act on the sum are the honest proof.
    for cheat in [Cheat::None, Cheat::AbsorbInG, Cheat::OverflowInQ] {
        let proved = prove_as(&f.values, cheat);
        assert_eq!(claims_hold(&proved, &f.setup), [true; 4], "{cheat:?} on a witness");
        assert_eq!(identity_relations(&proved), (true, true), "{cheat:?} on a witness");
    }
    // A dishonest port.
    let mut values = f.values.clone();
    let k = values
        .iter()
        .position(|v| matches!(v, PublicValue::Scalar(_)))
        .expect("an element");
    if let PublicValue::Scalar(x) = &mut values[k] {
        *x += F192::new(7, 0, 1);
    }
    for cheat in [Cheat::None, Cheat::AbsorbInG, Cheat::OverflowInQ] {
        let proved = prove_as(&values, cheat);
        assert_eq!(
            claims_hold(&proved, &f.setup),
            [true, true, false, true],
            "{cheat:?}: a dishonest port"
        );
        let (this, other) = identity_relations(&proved);
        assert!(!this, "{cheat:?}: the identity's relation");
        assert_eq!(other, cheat == Cheat::AbsorbInG, "{cheat:?}: the other layout's relation (the negative control)");
    }
    // Slots an honest `Q` leaves zero, filled.
    let proved = prove_as(&f.values, Cheat::FillG(F192::new(1, 2, 3)));
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, false, true], "G filled");
    let proved = prove_as(&f.values, Cheat::FillS(F64(5)));
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, false, false], "S filled");
    // `s` off `P(t)`: the pushes' claim, of degree 2 in `ρ` drawn after `s`, is false.
    let proved = prove_as(&f.values, Cheat::ShiftS(F192::new(0, 0, 9)));
    assert!(!claims_hold(&proved, &f.setup)[3], "s shifted");
    // `H(0) ≠ 0` (a constant added to `H`): the identity's claim is false.
    let proved = prove_as(&f.values, Cheat::ConstH(F192::new(3, 0, 1)));
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, false, true], "H's constant moved");
    assert!(!identity_relations(&proved).0, "H's constant moved");
    // `S = c` and `G = Y³ c`, which cancel in the identity's claim: only the pushes' claim (`S(t) = 0` at `ρ²`) sees it.
    let proved = prove_as(&f.values, Cheat::SinG(F64(5)));
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, true, false], "S in G");
    // `P`'s constant moved after `q_P` (`P ≠ P_v` on `V_m`): the identity's claim and the pushes' are false.
    let proved = prove_as(&f.values, Cheat::ConstP(F64(5)));
    assert_eq!(claims_hold(&proved, &f.setup), [true, true, false, false], "P's constant moved");
    // The same cheats with the dishonest port: a false claim each.
    for cheat in [Cheat::ConstH(F192::new(3, 0, 1)), Cheat::SinG(F64(5)), Cheat::ConstP(F64(5))] {
        let proved = prove_as(&values, cheat);
        assert!(claims_hold(&proved, &f.setup).contains(&false), "{cheat:?}: a dishonest port");
    }
}

/// π1's claims for a small circuit: five claims of the real ones' kinds (each its root, out-of-domain answer, point
/// and value: the two roots, constants, elements).
fn small_pi1() -> Vec<Vec<CallWord>> {
    let c = |b: u8| CallWord::Const([b; 32]);
    let e = |k: u64| CallWord::Const(element_word(E::new(k, 0, 0)));
    let x = CallWord::Element;
    vec![
        vec![CallWord::Root(0), x(0), x(1), x(2), x(1)],
        vec![CallWord::Root(1), x(2), x(1), x(0), x(1)],
        vec![c(9), e(3), x(0), x(2), x(2)],
        vec![c(8), e(4), x(2), e(0), x(1)],
        vec![c(7), e(5), x(2), e(0), x(0)],
    ]
}

fn contract_checks(design: Design) {
    deep(move || {
        let f = built(&design);
        let pi1 = small_pi1();
        let inst = Instance::new(&f.circuit, &f.spec, f.setup.root(), f.setup.ood(), &PI1_IV, &pi1);
        assert_eq!(inst.iv, f.iv, "the instance's IV is the prover's");
        let recorded = record_verifier(&f.spec);
        let proved = prove(
            &f.circuit,
            &f.spec,
            &f.setup,
            &f.iv,
            &f.public_input,
            &f.values,
            &f.witness,
        );
        let stream = proved.stream.clone();
        assert_eq!(stream.len(), recorded.stream_len);
        // Word for word, on the honest stream and on a random one.
        let words = contract::parity(&inst, &recorded, &f.public_input, &[], &stream);
        contract::parity(&inst, &recorded, &[0x5a; 32], &[], &sample_stream(stream.len(), 7));
        println!("parity: {words} words");

        // The honest proof: the contract checks π1's claims and those the openings prove, declared.
        let (reduced, roots, openings) = open(proved, &f.setup);
        assert_eq!(
            verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), f.setup.ood(), &openings),
            Ok(())
        );
        let block = contract::expected_claims(&inst, &recorded, &reduced, &stream);
        let data = calldata(&f.public_input, &stream);
        let (accepted, calls) = contract::run(&inst, &recorded, &data, &block);
        assert!(accepted, "the contract accepts the honest proof");
        assert_eq!(calls, block.iter().map(PcsClaim::encode).collect::<Vec<_>>());
        // π2's claims are those `pcs_claim::verify_claim` accepted.
        let pi2 = prover::claims(f.circuit.log_n, &reduced, &roots, &f.setup.root(), f.setup.ood());
        assert_eq!(block[pi1.len()..], pi2[..]);
        assert_eq!(pi2[0].value, to_f192(reduced.witness.1));
        for at in [contract::STREAM_AT, data.len() / 2, data.len() - 2, data.len() - 1] {
            let mut bad = data.clone();
            bad[at] ^= 1;
            assert!(
                !contract::run(&inst, &recorded, &bad, &block).0,
                "calldata byte {at} flipped"
            );
        }
    });
}

#[test]
fn contract_d16v() {
    contract_checks(synth::small_d16v(11));
}

/// The contract at a target shape: built from the synthetic circuit's verifier (its gas depends on the shape alone:
/// the pairs, the formulas, the public side), π1-rec's real calls appended.
fn target_report(name: &str, design: Design) {
    let name = name.to_string();
    deep(move || {
        let built = synth::build(&design, 0x7a);
        let circuit = &built.circuit;
        let spec = Spec::of(circuit);
        let pi1 = leanvm_rec::pi2::pi1::pi1_calls();
        println!(
            "{name}: 2^{} positions ({:.1}% of the rows used), rows of {}: {} pairs ({} pull-less), {} groups, {} formulas, blocks up to 2^{} rows, {} public terms, {} reads; π1: {} calls, {} roots, {} elements",
            circuit.log_n,
            100.0 * built.used_rows as f64 / circuit.rows() as f64,
            circuit.width(),
            circuit.pairs.len(),
            spec.pull_less.len(),
            spec.groups.len(),
            circuit.formulas.len(),
            spec.max_log_rows(),
            circuit.public.len(),
            circuit.reads.len(),
            pi1.calls.len(),
            pi1.roots,
            pi1.elements
        );
        assert!(
            pi1.roots <= 2 && pi1.elements <= 51,
            "the synthetic circuit's public data hold π1's"
        );
        let inst = Instance::new(circuit, &spec, [0x44; 32], F192::new(5, 6, 7), &[0x33; 32], &pi1.calls);
        let recorded = record_verifier(&spec);
        let report = contract::measure(&inst, &recorded);
        print!("{}", report.table(&name));
        let stream = sample_stream(recorded.stream_len, 11);
        contract::parity(&inst, &recorded, &[0x5a; 32], &[], &stream);
        println!("{name}: parity");
    });
}

#[test]
#[ignore]
fn gas_report() {
    target_report("D16v, N = 2^24 (pi1-rec)", synth::target_d16v());
}

fn peak_memory() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
        .unwrap_or_default()
}

/// The prover at the D16v target shape, scaled to `2^PI2_LOG_N` positions if set (the same pairs, formulas and public
/// side, smaller blocks).
#[test]
#[ignore]
fn prove_target() {
    let target = synth::target_d16v();
    let design = match std::env::var("PI2_LOG_N").ok().and_then(|v| v.parse().ok()) {
        Some(log_n) => synth::scaled(&target, log_n),
        None => target,
    };
    let start = std::time::Instant::now();
    let f = built(&design);
    println!(
        "2^{} positions, {} pairs, {} groups: built, checked, setup committed in {:.1} s; {}",
        f.circuit.log_n,
        f.circuit.pairs.len(),
        f.spec.groups.len(),
        start.elapsed().as_secs_f64(),
        peak_memory()
    );
    let start = std::time::Instant::now();
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    let proving = start.elapsed().as_secs_f64();
    for (step, s) in &proved.timings {
        println!("   {s:>7.2} s  {step}");
    }
    let start = std::time::Instant::now();
    let (reduced, roots, openings) = open(proved, &f.setup);
    let opening = start.elapsed().as_secs_f64();
    println!("prove {proving:.1} s, open {opening:.1} s; {}", peak_memory());
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), f.setup.ood(), &openings),
        Ok(())
    );
}
