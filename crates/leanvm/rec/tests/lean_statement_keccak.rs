// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2's circuit as `formal/RecStatement` transcribes it, for the Keccak VM's π1-rec3 at the 128-signature reference
//! workload (`KECCAK_128`, the graph of `formal/RecGraphKeccak/RecGraphKeccak/Emitted.lean`), D16v. Self-contained: the
//! renderer ([`render`], the circuit's tables and the instance's constants as Lean data) is here.
//!
//! - `keccak_statement_data_is_current` (ignored: it compiles the circuit twice and commits its setup): the checked-in
//!   `formal/RecStatement/RecStatement/Data.lean` is what [`render`] writes now; `UPDATE_LEAN=1` rewrites it.
//!
//! **The data** is what π2's verifier is built from (`pi2::verifier::Spec::of`): the circuit's shape, its formulas, its
//! (block, role) pairs, the reads of the public data, the public terms and their holes (each term's hole position,
//! whose row and role π2v2's verifier reads: `Spec::phi`), then the instance's constants (π1's contract
//! IV, the setup's root, the circuit's digest) and π1's claims as the circuit names their words
//! (`spec::CallWord`). Not `σ` and not `κ`: the setup commits them, the digest and the root bind them, and the verifier
//! reads neither.
//!
//! The circuit is compiled on synthetic streams (as `tests/lean_circuit_keccak128.rs`): the test checks that the
//! adapted circuit (its formulas, pairs, reads, public terms, `σ`, `κ`, hence its digest and setup root), π1's calls and
//! π1's contract IV do not depend on the stream or the public input. π1's contract IV is
//! `contract_iv(KECCAK_128, KECCAK_REC3, PROGRAM_IV, SetupRoots::REFERENCE)`: `record_verifier` binds the
//! code's reference root (the setup call's constant `F` in `Emitted.lean`'s `call2` is `SetupRoots::REFERENCE.f`).
//!
//! `RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_rec --test lean_statement_keccak -- --ignored --nocapture`

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use std::fmt::Write;

use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_rec::circuit::compile::{Inputs, pi2};
use leanvm_rec::circuit::spec::CallWord;
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::{Circuit, Coeff, Formula, Lin, Read};
use leanvm_rec::pi2::prover::Setup;
use leanvm_rec::pi2::verifier::Spec;
use leanvm_rec::REFERENCE;
use leanvm_univariate::contract::{Recorded, SetupRoots, contract_iv, record_verifier};
use leanvm_univariate::{KECCAK_REC3, Shape};

/// The reference workload: leanVM 9d50c92a3's Keccak VM at 128 signatures (`leanvm_rec::REFERENCE`,
/// `leanvm_statement::shapes::reference()`; Lean's `RecGraphKeccak.Pi1.keccak128`).
const KECCAK_128: Shape = REFERENCE;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn data_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../formal/RecStatement/RecStatement/Data.lean")
}

/// The instance's constants the data carries.
struct Constants {
    /// π1's contract IV (`Compiled::pi1_iv`).
    pi1_iv: [u8; 32],
    /// The setup's root (`prover::Setup::new(circuit).root()`).
    setup_root: [u8; 32],
    /// `circuit.digest()`.
    digest: [u8; 32],
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn coeff_text(c: &Coeff) -> String {
    format!(
        "⟨0x{:x}, 0x{:x}, 0x{:x}, {}⟩",
        c.value[0], c.value[1], c.value[2], c.gamma
    )
}

fn lin_text(l: &Lin) -> String {
    let terms: Vec<String> = l
        .terms
        .iter()
        .map(|(c, cell)| format!("({}, {cell})", coeff_text(c)))
        .collect();
    let constant = match &l.constant {
        None => "none".to_string(),
        Some(c) => format!("some {}", coeff_text(c)),
    };
    format!("⟨[{}], {constant}⟩", terms.join(", "))
}

fn formula_text(f: &Formula) -> String {
    let products: Vec<String> = f
        .products
        .iter()
        .map(|(c, a, b)| format!("({}, {}, {})", coeff_text(c), lin_text(a), lin_text(b)))
        .collect();
    format!("⟨{}, [{}]⟩", lin_text(&f.lin), products.join(", "))
}

fn read_text(r: &Read) -> String {
    match r {
        Read::Integer(b) => format!(".integer {b}"),
        Read::Root => ".root".to_string(),
        Read::Scalar => ".scalar".to_string(),
        Read::Narrow => ".narrow".to_string(),
        Read::Frame(p) => format!(".frame {p}"),
    }
}

fn call_word_text(w: &CallWord) -> String {
    match *w {
        CallWord::Const(bytes) => format!(".const (hexBytes \"{}\")", hex(&bytes)),
        CallWord::Root(i) => format!(".root {i}"),
        CallWord::Element(i) => format!(".element {i}"),
        CallWord::Pair { element, coordinate } => format!(".pair {element} {coordinate}"),
    }
}

/// The formulas per Lean definition: the file's definitions stay small enough to elaborate quickly.
const CHUNK: usize = 16;

/// The Lean file of the circuit's tables and the instance's constants.
fn render(circuit: &Circuit, calls: &[Vec<CallWord>], c: &Constants) -> String {
    let mut out = String::new();
    let w = &mut out;
    let spec = Spec::of(circuit);
    writeln!(w, "-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.").unwrap();
    writeln!(
        w,
        "-- Generated by `crates/leanvm/rec/tests/lean_statement_keccak.rs` (`render`) from π2's circuit for the Keccak VM's"
    )
    .unwrap();
    writeln!(
        w,
        "-- π1-rec3. Do not edit: `UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement_keccak -- --ignored`"
    )
    .unwrap();
    writeln!(w, "-- rewrites it, and the test fails while it is stale.").unwrap();
    writeln!(w, "import RecStatement.Basic").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "/-!").unwrap();
    writeln!(w, "# π2's circuit for π1-rec3, as its verifier reads it").unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "`pi2::circuit::Circuit` of `circuit::compile::pi2(record_verifier(KECCAK_128, KECCAK_REC3, Point), D16v)` through"
    )
    .unwrap();
    writeln!(
        w,
        "`pi2::adapt`: `2^{}` positions, rows of `2^{}`, {} formulas, {} (block, role) pairs ({} pull-less) in {} groups, {} reads,",
        circuit.log_n,
        circuit.log_row,
        circuit.formulas.len(),
        circuit.pairs.len(),
        spec.pull_less.len(),
        spec.groups.len(),
        circuit.reads.len()
    )
    .unwrap();
    writeln!(
        w,
        "{} public terms ({} of them of value zero, in no `Φ`); π1's {} claims. Not `σ`, not `κ` (the setup's root and",
        circuit.public.len(),
        spec.ports - spec.phi.iter().map(|(_, terms)| terms.len()).sum::<usize>(),
        calls.len()
    )
    .unwrap();
    writeln!(
        w,
        "the circuit's digest bind them; the verifier reads neither). Data only."
    )
    .unwrap();
    writeln!(w, "-/").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "namespace RecStatement.Data").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "open RecStatement").unwrap();
    writeln!(w).unwrap();
    let chunks: Vec<&[Formula]> = circuit.formulas.chunks(CHUNK).collect();
    for (k, chunk) in chunks.iter().enumerate() {
        writeln!(w, "/-- Formulas {}..{}. -/", k * CHUNK, k * CHUNK + chunk.len()).unwrap();
        writeln!(w, "def formulas{k} : List Formula := [").unwrap();
        let items: Vec<String> = chunk.iter().map(|f| format!("  {}", formula_text(f))).collect();
        writeln!(w, "{}]", items.join(",\n")).unwrap();
        writeln!(w).unwrap();
    }
    let names: Vec<String> = (0..chunks.len()).map(|k| format!("formulas{k}")).collect();
    writeln!(w, "/-- The formulas (`Circuit::formulas`). -/").unwrap();
    writeln!(w, "def formulas : List Formula := {}", names.join(" ++ ")).unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- The (block, role) pairs (`Circuit::pairs`): first row, rows' log, role, formula, pulls. -/"
    )
    .unwrap();
    writeln!(w, "def pairs : List Pair := [").unwrap();
    let items: Vec<String> = circuit
        .pairs
        .iter()
        .map(|p| {
            format!(
                "  ⟨{}, {}, {}, {}, {}⟩",
                p.first_row, p.log_rows, p.role, p.formula, p.pulls
            )
        })
        .collect();
    writeln!(w, "{}]", items.join(",\n")).unwrap();
    writeln!(w).unwrap();
    writeln!(w, "/-- The public data read from the stream (`Circuit::reads`). -/").unwrap();
    writeln!(
        w,
        "def reads : List Read := [{}]",
        circuit.reads.iter().map(read_text).collect::<Vec<_>>().join(", ")
    )
    .unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- The public side (`Circuit::public`): each term's tag and value. -/"
    )
    .unwrap();
    writeln!(w, "def publicTerms : List PublicTerm := [").unwrap();
    let items: Vec<String> = circuit
        .public
        .iter()
        .map(|t| format!("  ⟨{}, {}⟩", t.tag, lin_text(&t.value)))
        .collect();
    writeln!(w, "{}]", items.join(",\n")).unwrap();
    writeln!(w).unwrap();
    // Each public term's hole, the position `σ` sends to its tag (`Spec::of`'s `hole`): π2v2's verifier reads its row
    // and role (`Spec::phi`).
    let hole: std::collections::HashMap<u32, usize> = (0..circuit.n())
        .filter(|&i| circuit.sigma[i] as usize >= circuit.n())
        .map(|i| (circuit.sigma[i], i))
        .collect();
    writeln!(
        w,
        "/-- Each public term's hole (`σ`'s preimage of its tag): `Spec::phi` reads its row and role. -/"
    )
    .unwrap();
    writeln!(
        w,
        "def holes : List ℕ := [{}]",
        circuit.public.iter().map(|t| hole[&t.tag].to_string()).collect::<Vec<_>>().join(", ")
    )
    .unwrap();
    writeln!(w).unwrap();
    writeln!(w, "/-- **π2's circuit** as its verifier reads it. -/").unwrap();
    writeln!(
        w,
        "def circuit : Circuit := ⟨{}, {}, formulas, pairs, reads, publicTerms, holes⟩",
        circuit.log_n, circuit.log_row
    )
    .unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- π1's contract IV (`Compiled::pi1_iv`: π1-rec3's at the reference setup root). -/"
    )
    .unwrap();
    writeln!(w, "def pi1Iv : List UInt8 := hexBytes \"{}\"", hex(&c.pi1_iv)).unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- The setup's root (`prover::Setup::new(circuit).root()`: the commitment of `κ`, `κ + σ`). -/"
    )
    .unwrap();
    writeln!(w, "def setupRoot : List UInt8 := hexBytes \"{}\"", hex(&c.setup_root)).unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- The circuit's digest (`Circuit::digest`: its encoding with `σ`'s and `κ`'s hashes). -/"
    )
    .unwrap();
    writeln!(w, "def digest : List UInt8 := hexBytes \"{}\"", hex(&c.digest)).unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "/-- π1's claims as the circuit names their words (`spec::Circuit::calls`). -/"
    )
    .unwrap();
    writeln!(w, "def pi1Calls : List (List CallWord) := [").unwrap();
    let items: Vec<String> = calls
        .iter()
        .map(|call| {
            format!(
                "  [{}]",
                call.iter().map(call_word_text).collect::<Vec<_>>().join(",\n   ")
            )
        })
        .collect();
    writeln!(w, "{}]", items.join(",\n")).unwrap();
    writeln!(w).unwrap();
    writeln!(w, "end RecStatement.Data").unwrap();
    out
}

/// The adapted circuit, π1's calls and contract IV, compiled on one synthetic (stream, public input).
struct Made {
    circuit: Circuit,
    calls: Vec<Vec<CallWord>>,
    pi1_iv: [u8; 32],
}

fn make(recorded: &Recorded, seed: usize, public: [u8; 32]) -> Made {
    let stream: Vec<u8> = (0..recorded.stream_len).map(|i| (i * (37 + 2 * seed) + 11 + seed) as u8).collect();
    let c = pi2(
        recorded,
        &Inputs {
            program_iv: PROGRAM_IV,
            public,
            stream: &stream,
        },
    );
    Made {
        circuit: adapt::adapt(&c.finished.circuit),
        calls: c.finished.circuit.calls.clone(),
        pi1_iv: c.pi1_iv,
    }
}

fn summary(circuit: &Circuit, calls: &[Vec<CallWord>], c: &Constants) -> String {
    let spec = Spec::of(circuit);
    format!(
        "log_n {} log_row {}, {} formulas, {} pairs ({} pull-less) in {} groups, {} reads, {} public terms ({} of value zero), \
         {} calls of {:?} words, |σ| {}, |κ| {}\npi1_iv {}\nsetup_root {}\ndigest {}",
        circuit.log_n,
        circuit.log_row,
        circuit.formulas.len(),
        circuit.pairs.len(),
        spec.pull_less.len(),
        spec.groups.len(),
        circuit.reads.len(),
        circuit.public.len(),
        spec.ports - spec.phi.iter().map(|(_, terms)| terms.len()).sum::<usize>(),
        calls.len(),
        calls.iter().map(Vec::len).collect::<Vec<_>>(),
        circuit.sigma.len(),
        circuit.kappa.len(),
        hex(&c.pi1_iv),
        hex(&c.setup_root),
        hex(&c.digest),
    )
}

/// The checked-in Lean data is π2's circuit for the Keccak VM's π1-rec3: `UPDATE_LEAN=1` rewrites it.
#[test]
#[ignore = "compiles π2's circuit for the Keccak VM's π1-rec3 twice (2^24 positions) and commits its setup"]
fn keccak_statement_data_is_current() {
    let rendered = deep(|| {
        let recorded = record_verifier(&KECCAK_128, KECCAK_REC3);
        // π1's contract IV binds the code's reference root.
        assert_eq!(KECCAK_128.log_memory, 20);
        assert_eq!(KECCAK_128.log_bytecode, 18);
        assert_eq!(KECCAK_128.table_rows, [24260, 36229, 24626, 35812, 15509, 17712]);
        let iv = contract_iv(
            &KECCAK_128,
            KECCAK_REC3,
            &PROGRAM_IV,
            &SetupRoots::REFERENCE,
        );
        assert_eq!(recorded.iv(&PROGRAM_IV), iv);
        eprintln!("SetupRoots::REFERENCE: f {}", hex(&SetupRoots::REFERENCE.f));
        let a = make(&recorded, 0, [3; 32]);
        let placeholder = |m: &Made| Constants {
            pi1_iv: m.pi1_iv,
            setup_root: [0; 32],
            digest: m.circuit.digest(),
        };
        let text_a = render(&a.circuit, &a.calls, &placeholder(&a));
        // Another stream and public input: the same circuit, calls and IV.
        {
            let b = make(&recorded, 1, [0x5a; 32]);
            assert_eq!(a.pi1_iv, iv, "π1's contract IV");
            assert_eq!(b.pi1_iv, iv, "π1's contract IV does not depend on the stream");
            assert_eq!(a.calls, b.calls, "π1's calls do not depend on the stream");
            assert_eq!(a.circuit.sigma, b.circuit.sigma, "σ does not depend on the stream");
            assert_eq!(a.circuit.kappa, b.circuit.kappa, "κ does not depend on the stream");
            assert_eq!(a.circuit.digest(), b.circuit.digest(), "the digest does not depend on the stream");
            assert!(
                text_a == render(&b.circuit, &b.calls, &placeholder(&b)),
                "the circuit's tables do not depend on the stream"
            );
        }
        let setup_root = Setup::new(&a.circuit).root();
        let constants = Constants {
            pi1_iv: a.pi1_iv,
            setup_root,
            digest: a.circuit.digest(),
        };
        eprintln!("{}", summary(&a.circuit, &a.calls, &constants));
        render(&a.circuit, &a.calls, &constants)
    });
    let path = data_path();
    if std::env::var_os("UPDATE_LEAN").is_some() {
        std::fs::write(&path, &rendered).expect("the Lean data written");
        return;
    }
    let current = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        current == rendered,
        "{} is stale: run `UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement_keccak -- --ignored`",
        path.display()
    );
}
