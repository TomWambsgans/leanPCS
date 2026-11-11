// Part of this repository. The zerocheck, lincheck and slices are leanVM 42422001's Flock prover
// (crates/vendor/flock-42422001, its `prove_reduction_skip`, this repository's, on the Keccak-f block of
// `flock::keccak`, docs/leanvm/flock/KECCAK.md), on the witness the trace's `SHA3` rows give. With π1-rec3
// (`FsShape::Rec3`) the zerocheck's eq point is the skip module's, as squares. MIT OR Apache-2.0; see AGENTS.md.
//! Flock's prover (SPEC-FLOCK.md), behind one call ([`prove`]): the zerocheck (a skip of 3 to 6), the lincheck and
//! the 64 slices, written to the contract's Keccak-256 chain through [`Chain`], then the ring map's challenges, as
//! `flock_min::verify_walked` and `flock_min::ring_end` read them.

use flock::zerocheck::skip::EqPoint;
use leanvm_statement::field::E;
use leanvm_statement::flock::N_FIXED_CHALLENGES;
use leanvm_statement::flock_min::{PACKING, RING_MAP_LEN, Variant};
use leanvm_statement::transcript::{FsShape, KeccakWriter};
use primitives::field::F192;

/// Flock's prover inputs, as leanVM's witness build leaves them.
pub struct FlockWitness {
    pub n_blocks: usize,
    pub z: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub z_lincheck: Vec<u8>,
}

/// The contract's chain as leanVM's flock prover's transcript: a scalar sent is 24 calldata bytes, a challenge one
/// Keccak-256 of the state and the bytes since the last; every challenge is kept, in order.
pub struct Chain<'a> {
    pub writer: &'a mut KeccakWriter,
    pub samples: Vec<E>,
    /// π1-rec4: the zerocheck's first eq coordinate, drawn before Flock (with the bus's challenges): the first
    /// challenge Flock's prover asks for.
    pub drawn: Option<E>,
}

impl flock::transcript::Transcript for Chain<'_> {
    fn add_scalar(&mut self, x: F192) {
        self.writer.send(x.into());
    }

    fn sample(&mut self) -> F192 {
        let e = match self.drawn.take() {
            Some(e) => e,
            None => self.writer.sample(),
        };
        self.samples.push(e);
        e.into()
    }
}

/// What Flock leaves: the slices' point and values.
pub struct FlockOut {
    pub point: Vec<E>,
    pub slices: Vec<E>,
    /// The zerocheck and the lincheck's seconds.
    pub reduction_secs: f64,
}

/// The zerocheck's eq point for the variant's Fiat–Shamir shape.
fn eq_point(variant: Variant) -> EqPoint {
    match variant.fs {
        FsShape::Main => EqPoint::Sampled,
        FsShape::Rec3 | FsShape::Rec4 => EqPoint::Squares,
    }
}

/// The reduction `reduce` runs (the zerocheck and the lincheck of a block with `lincheck_rounds` rounds, on the chain),
/// checked against the challenges the verifier draws.
fn reduction(
    writer: &mut KeccakWriter,
    variant: Variant,
    log_n: usize,
    lincheck_rounds: usize,
    drawn: Option<E>,
    reduce: impl FnOnce(&mut Chain) -> flock::slice::SliceClaim,
) -> Result<FlockOut, String> {
    let k = variant.skip;
    let mut chain = Chain {
        writer: &mut *writer,
        samples: Vec::new(),
        drawn,
    };
    let started = std::time::Instant::now();
    let claim = reduce(&mut chain);
    if chain.drawn.is_some() {
        return Err("Flock's prover did not take the eq coordinate drawn before it".into());
    }
    let samples = chain.samples;
    // The challenges, as the verifier draws them: the zerocheck's sampled eq coordinates (with π1-rec3 only the first,
    // the others its squares), the skip's point, its rounds', the lincheck's batching and rounds'.
    let n_r = match eq_point(variant) {
        EqPoint::Sampled => log_n - k - N_FIXED_CHALLENGES,
        EqPoint::Squares => usize::from(log_n > k + N_FIXED_CHALLENGES),
    };
    let rounds = log_n - k;
    if samples.len() != n_r + 1 + rounds + 1 + lincheck_rounds {
        return Err(format!("Flock's prover drew {} challenges", samples.len()));
    }
    let chi = &samples[n_r + 1..n_r + 1 + rounds];
    let lincheck = &samples[n_r + 2 + rounds..];
    let (_row_low, rest) = chi.split_at(PACKING - k);
    let (_chi_in, chi_rest) = rest.split_at(lincheck_rounds);
    let chi_in_prime: Vec<E> = lincheck.iter().rev().copied().collect();
    let point: Vec<E> = [&chi_in_prime[..], chi_rest].concat();
    let theirs: Vec<E> = claim.suffix_point.iter().map(|&x| x.into()).collect();
    if theirs != point {
        return Err("Flock's slices are not at the point the verifier derives".into());
    }
    Ok(FlockOut {
        point,
        slices: claim.s_hat_v.iter().map(|&x| x.into()).collect(),
        reduction_secs: started.elapsed().as_secs_f64(),
    })
}

/// Flock on the Keccak-f block (`flock::keccak`, `k_log = 17`: 11 lincheck rounds) at `log_n = 17 +
/// log(blocks)` variables, written to `writer` as `flock_min::verify_walked::<_, keccak_flock::Keccak>` reads it, then
/// the ring map's challenges (`flock_min::ring_end`; π1-rec4: none, the map is drawn after `C2`'s commitment, and the
/// zerocheck's first eq coordinate is `drawn`, drawn before). `witness` is
/// `flock::keccak::generate_witness_with_ab_packed_and_lincheck`'s.
pub fn prove(
    writer: &mut KeccakWriter,
    witness: &FlockWitness,
    variant: Variant,
    log_n: usize,
    drawn: Option<E>,
) -> Result<FlockOut, String> {
    use flock::keccak::{K_LOG, KeccakSetup};
    let k = variant.skip;
    if !(flock::zerocheck::skip::MIN_SKIP..=PACKING).contains(&k) {
        return Err(format!("Flock {variant:?}: a prover for a skip of 3 to 6"));
    }
    parallel::init();
    let setup = KeccakSetup::new(witness.n_blocks);
    if setup.m() != log_n {
        return Err(format!("Flock's witness has {} variables, the verifier's shape {log_n}", setup.m()));
    }
    let eq = eq_point(variant);
    // The drawn coordinate is the zerocheck's first sampled one; with none sampled (`log_n = k + 7`) the verifier
    // reads none either.
    let drawn = drawn.filter(|_| log_n > k + N_FIXED_CHALLENGES);
    let out = reduction(writer, variant, log_n, K_LOG - PACKING, drawn, |chain| {
        setup.prove_reduction_skip(k, eq, &witness.z, &witness.a, &witness.b, &witness.z_lincheck, chain)
    })?;
    if !variant.fs.wide() {
        for _ in 0..RING_MAP_LEN {
            writer.sample();
        }
    }
    Ok(out)
}
