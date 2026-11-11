// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
use super::*;
use primitives::test_rng::Rng;

/// Words that look random: a hash of their place and a seed.
fn words(n: usize, seed: u64) -> Vec<F64> {
    (0..1u64 << n)
        .map(|i| {
            F64((i ^ seed.rotate_left(29))
                .wrapping_add(1)
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .rotate_left(17))
        })
        .collect()
}

/// `f(x)` written out: `Σ_i f_i Π_j (x_j if bit j of i, else 1 - x_j)`.
fn naive(words: &[F64], point: &[F192]) -> F192 {
    words.iter().enumerate().fold(F192::ZERO, |acc, (i, &w)| {
        let weight = point.iter().enumerate().fold(F192::ONE, |e, (j, &x)| {
            e * if (i >> j) & 1 == 1 { x } else { F192::ONE + x } // 1 - x = 1 + x in characteristic 2
        });
        acc + weight * F192::from(w)
    })
}

fn opens(committed: &Committed, claim: &PcsClaim) -> bool {
    verify(&claim.encode(), &wire_proof(&open(committed, claim)))
}

#[test]
fn encoding_round_trips_and_rejects_malformed_claims() {
    let mut rng = Rng::new(1);
    for n in [1usize, 2, 15, 28, 32] {
        let claim = PcsClaim {
            n: n as u8,
            root: std::array::from_fn(|i| i as u8 ^ 0xa5),
            ood: rng.ext(),
            point: rng.ext_vec(n),
            value: rng.ext(),
        };
        let bytes = claim.encode();
        assert_eq!(bytes.len(), claim_len(n));
        assert_eq!(bytes.len(), 82 + 24 * n);
        assert_eq!(&bytes[..2], &[VERSION, n as u8]);
        assert_eq!(&bytes[2..34], &claim.root);
        assert_eq!(PcsClaim::decode(&bytes), Some(claim.clone()));
        assert_eq!(claim.hash(), keccak256(&bytes));
        // Wrong version, a length off by one either way, a truncated claim.
        let mut wrong = bytes.clone();
        wrong[0] = 2;
        assert_eq!(PcsClaim::decode(&wrong), None);
        assert_eq!(PcsClaim::decode(&bytes[..bytes.len() - 1]), None);
        assert_eq!(PcsClaim::decode(&[&bytes[..], &[0]].concat()), None);
        assert_eq!(PcsClaim::decode(&bytes[..1]), None);
    }
    // n = 0 and n = 33: not well-formed, whatever the length.
    for n in [0usize, 33] {
        let mut bytes = vec![VERSION, n as u8];
        bytes.resize(claim_len(n), 7);
        assert_eq!(PcsClaim::decode(&bytes), None);
    }
    assert_eq!(PcsClaim::decode(&[]), None);
}

#[test]
fn elements_are_the_low_24_bytes_of_the_evm_word() {
    let x = F192::new(0x0102030405060708, 0x1112131415161718, 0x2122232425262728);
    let bytes = element_bytes(x);
    assert_eq!(
        bytes.to_vec(),
        hex(&["2122232425262728", "1112131415161718", "0102030405060708"].concat())
    );
    // The EVM word `c0 | c1 << 64 | c2 << 128` (`evm_link::op::word`): its top 8 bytes zero, then these 24.
    let word = evm_link::op::word([x.c0, x.c1, x.c2]);
    assert_eq!(&word[..8], &[0; 8]);
    assert_eq!(&word[8..], &bytes);
    assert_eq!(element_of(&bytes), x);
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn the_variable_order_is_bit_j_for_x_j() {
    let mut rng = Rng::new(2);
    let f = words(10, 3);
    let point = rng.ext_vec(10);
    assert_eq!(evaluate(&f, &point), naive(&f, &point));
    // At a vertex of the cube, f is the word there: bit j of the index is coordinate j.
    let i = 0b10_0110_1001usize;
    let vertex: Vec<F192> = (0..10)
        .map(|j| if (i >> j) & 1 == 1 { F192::ONE } else { F192::ZERO })
        .collect();
    assert_eq!(evaluate(&f, &vertex), F192::from(f[i]));
}

#[test]
fn the_ood_point_is_its_derivation() {
    let root = [0x5a; 32];
    let z = ood_point(15, &root);
    assert_eq!(z.len(), 15);
    let digest = keccak256(&[b"leanPCS-ood".as_slice(), &[1, 15], &root, &[3]].concat());
    assert_eq!(z[3], element_of(digest[8..].try_into().unwrap()));
    // Each coordinate, each n and each root give another point.
    assert_ne!(z[0], z[1]);
    assert_ne!(ood_point(16, &root)[0], z[0]);
    assert_ne!(ood_point(15, &[0x5b; 32])[0], z[0]);
}

/// Changing one word of f changes the root, and its out-of-domain answer.
#[test]
fn the_ood_answer_changes_with_any_word() {
    let f = words(15, 4);
    let a = commit(f.clone());
    let mut g = f;
    g[12345] = F64(g[12345].0 ^ 1);
    let b = commit(g);
    assert_ne!(a.root, b.root);
    assert_ne!(a.ood, b.ood);
    assert_eq!(a.ood, naive(a.words(), &ood_point(15, &a.root)));
}

#[test]
fn claims_open_at_15_16_and_20_variables() {
    let mut rng = Rng::new(5);
    for n in [15, 16, 20] {
        let committed = commit(words(n, n as u64));
        let claim = committed.claim_at(rng.ext_vec(n));
        assert!(opens(&committed, &claim), "n = {n}");
        // A second claim on the same commitment opens on its own.
        let other = committed.claim_at(rng.ext_vec(n));
        assert!(opens(&committed, &other), "n = {n}");
    }
}

/// The value is the naive formula's: the opening reads the words in `f`'s variable order.
#[test]
fn an_opening_proves_the_naive_value() {
    let mut rng = Rng::new(6);
    let committed = commit(words(15, 6));
    let point = rng.ext_vec(15);
    let claim = committed.claim(point.clone(), naive(committed.words(), &point));
    assert!(opens(&committed, &claim));
}

#[test]
fn false_claims_and_altered_proofs_are_rejected() {
    let mut rng = Rng::new(7);
    let committed = commit(words(16, 7));
    let claim = committed.claim_at(rng.ext_vec(16));
    let proof = wire_proof(&open(&committed, &claim));
    assert!(verify(&claim.encode(), &proof));
    let rejects = |claim: &PcsClaim| !verify(&claim.encode(), &proof);
    // A wrong value, point, out-of-domain answer or root, against the honest proof.
    let mut wrong = claim.clone();
    wrong.value += F192::ONE;
    assert!(rejects(&wrong));
    let mut wrong = claim.clone();
    wrong.point[3] += F192::ONE;
    assert!(rejects(&wrong));
    let mut wrong = claim.clone();
    wrong.ood += F192::ONE;
    assert!(rejects(&wrong));
    let mut wrong = claim.clone();
    wrong.root[0] ^= 1;
    assert!(rejects(&wrong));
    // A false claim cannot be opened by the honest prover: its proof does not verify.
    let mut false_claim = claim.clone();
    false_claim.value += F192::ONE;
    let forged = std::panic::catch_unwind(|| wire_proof(&open(&committed, &false_claim)));
    if let Ok(forged) = forged {
        assert!(!verify(&false_claim.encode(), &forged));
    }
    // Altered proofs: a scalar of the stream, a word of an opened row, a sibling hash.
    let base = open(&committed, &claim);
    for k in [2, 7, base.stream.len() / 2, base.stream.len() - 1] {
        let mut altered = base.clone();
        altered.stream[k] += F192::ONE;
        assert!(!verify(&claim.encode(), &wire_proof(&altered)), "stream scalar {k}");
    }
    let mut altered = base.clone();
    altered.merkle[0].leaf_data[0][0] = F64(altered.merkle[0].leaf_data[0][0].0 ^ 1);
    assert!(!verify(&claim.encode(), &wire_proof(&altered)), "a row word");
    let mut altered = base.clone();
    altered.merkle[0].sibling_hashes[0][0] ^= 1;
    assert!(!verify(&claim.encode(), &wire_proof(&altered)), "a sibling hash");
    // Unsupported n, and malformed bytes.
    let mut small = claim.clone();
    small.n = 14;
    small.point.truncate(14);
    assert!(!verify(&small.encode(), &proof));
    assert!(!verify(&claim.encode()[1..], &proof));
}

/// A commitment of the leading lanes alone is the whole stack's (its root and out-of-domain answer), and its openings
/// of claims at points of the whole stack are accepted by the verifier, which knows only `n`, with or without the
/// codeword kept.
#[test]
fn leading_lanes_commit_and_open_as_the_whole_stack() {
    let n = 16;
    let lane = 1usize << (n - LANE_FOLD);
    let mut rng = Rng::new(7);
    for lanes in [1usize, 10, 33, 64] {
        let mut full = words(n, lanes as u64);
        full[lanes * lane..].iter_mut().for_each(|w| *w = F64::ZERO);
        let whole = commit(full.clone());
        let point = rng.ext_vec(n);
        for keep in [false, true] {
            let leading = full[..lanes * lane].to_vec();
            let committed = if keep {
                commit_lanes_keeping_codeword(leading, n)
            } else {
                commit_lanes(leading, n)
            };
            assert_eq!(committed.root, whole.root, "the root at {lanes} lanes");
            assert_eq!(committed.ood, whole.ood, "the out-of-domain answer at {lanes} lanes");
            let claim = committed.claim_at(point.clone());
            assert_eq!(claim.value, naive(&full, &point));
            assert_eq!(claim, whole.claim_at(point.clone()));
            assert!(opens(&committed, &claim), "an opening at {lanes} lanes (codeword kept: {keep})");
            let mut wrong = claim.clone();
            wrong.value += F192::ONE;
            assert!(!verify(&wrong.encode(), &wire_proof(&open(&committed, &claim))));
        }
    }
}

/// Interior all-zero lanes (as π2's `Q` has four slots of them) are left out of the encodes, of a kept codeword and
/// of the openings' lane passes: the root, the out-of-domain answer and every proof, alone and batched, from the kept
/// codeword or encoded again, are those of a commitment that leaves out nothing.
#[test]
fn zero_lanes_left_out_change_no_proof() {
    // A stack the two-sweep encode takes (which a kept codeword of skipped lanes needs).
    let n = 20;
    let lane = 1usize << (n - LANE_FOLD);
    let mut rng = Rng::new(11);
    let mut full = words(n, 5);
    for slot in [1usize, 5, 9, 12] {
        full[4 * slot * lane..4 * (slot + 1) * lane].fill(F64::ZERO);
    }
    // The reference: no lane flagged, the whole codeword kept.
    let (commitment, data) = pcs::whir::commit(&full, n, LANE_FOLD, LOG_INV_RATE);
    let z = ood_point(n, &commitment.root);
    let ood_lanes = lane_products(&full, &z, None);
    let reference = Commitment {
        n,
        root: commitment.root,
        ood: combine_lanes(&ood_lanes, &z[n - LANE_FOLD..]),
        tree: data.merkle_tree,
        codeword: Mutex::new(Some(data.codeword)),
        ood_lanes,
        zero_lanes: vec![false; 1 << LANE_FOLD],
    };
    let claims: Vec<PcsClaim> = (0..3)
        .map(|_| {
            let point = rng.ext_vec(n);
            let value = evaluate(&full, &point);
            reference.claim(point, value)
        })
        .collect();
    let want: Vec<Proof> = claims
        .iter()
        .map(|claim| open_words_keeping(&full, &reference, claim))
        .collect();
    for keep in [true, false] {
        let committed = commit_words(&full, n, keep);
        assert_eq!((committed.root, committed.ood), (reference.root, reference.ood));
        assert_eq!(
            committed.zero_lanes.iter().filter(|&&z| z).count(),
            16,
            "the empty slots' lanes flagged"
        );
        if keep {
            let kept = committed.codeword.lock().expect("the codeword").as_ref().map(Vec::len);
            assert_eq!(
                kept,
                Some(48 << (n - LANE_FOLD + LOG_INV_RATE)),
                "the nonzero lanes' codeword alone"
            );
        }
        for (claim, want) in claims.iter().zip(&want) {
            assert_eq!(
                &open_words_keeping(&full, &committed, claim),
                want,
                "alone (kept: {keep})"
            );
        }
        // Batched: from the kept codeword, which the batch frees, then encoded again.
        assert_eq!(
            open_words_batch(&full, &committed, &claims),
            want,
            "batched (kept: {keep})"
        );
        assert_eq!(
            open_words_batch(&full, &committed, &claims),
            want,
            "batched again (kept: {keep})"
        );
        assert!(
            claims
                .iter()
                .zip(&want)
                .all(|(claim, proof)| verify(&claim.encode(), &wire_proof(proof)))
        );
    }
}

/// The prover's time at a large stack (`PCS_CLAIM_BENCH_N`, default 26): the commitment, then a claim opened twice
/// (both reading the kept codeword), and the weights' construction alone.
#[test]
#[ignore]
fn opening_time() {
    let n: usize = std::env::var("PCS_CLAIM_BENCH_N").ok().map_or(26, |v| v.parse().expect("n"));
    if std::env::var_os("PCS_CLAIM_TRACING").is_some() {
        bench::init_tracing();
    }
    parallel::init();
    let mut rng = Rng::new(3);
    let words: Vec<F64> = (0..1usize << n).map(|i| F64(i as u64 ^ 0x5555)).collect();
    let started = std::time::Instant::now();
    let committed = commit_lanes_keeping_codeword(words, n);
    println!("commitment 2^{n}: {:.3} s", started.elapsed().as_secs_f64());
    let point = rng.ext_vec(n);
    let started = std::time::Instant::now();
    let claim = committed.claim_at(point.clone());
    println!("evaluate: {:.3} s", started.elapsed().as_secs_f64());
    let started = std::time::Instant::now();
    let _w = [eq_tensor(&ood_point(n, &committed.root), F192::ONE), eq_tensor(&point, F192::ONE)];
    println!("weights: {:.3} s", started.elapsed().as_secs_f64());
    for pass in 0..3 {
        let started = std::time::Instant::now();
        let proof = tracing::info_span!("opening", pass)
            .in_scope(|| open_words_keeping(committed.words(), committed.commitment(), &claim));
        println!("open {pass}: {:.3} s", started.elapsed().as_secs_f64());
        assert!(verify(&claim.encode(), &wire_proof(&proof)));
    }
}
