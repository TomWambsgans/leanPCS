<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows formal/UniStatement/README.md. -->

# RecStatement

The recursion's outer proof π2 (`crates/leanvm/rec`, `PI2.md` §2, §8–§9), **π2v3** (`leanvm-rec-pi2v3`: the ports
out of the copy argument, checked by the ports' term `T = Σ_{port pairs} I_p (E_p + Φ_k)` with `Φ_k` by rows
(`Data.holes`: each public term's hole); `P`, the internal pushes, committed in `Q` with its definition
`P = P_v + Z_V q_P`; `q`, `q_P` below `2N`; `s = P(t)` sent; `Q` the plain sixteen-slot stack (`m + 4` variables,
slots `1, 5, 9, 12` the prover's) and three claims: the identity's at `(u, ρ', y_0, y_1)`, weighing `P`, `q_P` by
`c_3`, the pushes' at `(u, ρ, 1, 1)`, `ρ` drawn after `s`, the sum at `(1^m, 0, 0, y_0, y_1)`; one inversion of
`R_d Y w_{m+1} B c_h D_n`), **on the EIP draft's PCS claims** (`crates/pcs_claim`, version 1: every commitment a root
and its out-of-domain answer, read after the root; every claim one point; one opening a claim; no layout words), **for
the recursion of the Keccak VM**: π1 is [`UniKeccak`](../UniKeccak/README.md)'s verifier (leanVM 9d50c92a3's Keccak
VM) at π1-rec3's Fiat–Shamir shape (`keccakRec3`) on the same PCS claims, at the 128-signature reference shape
(`RecGraphKeccak.Pi1.keccak128`), its recorded graph [`RecGraphKeccak`](../RecGraphKeccak/README.md)'s `pi1GraphK`.
In the files a reviewer reads:

* **π2's verifier as computable Lean**, step by step as `pi2/verifier.rs` and the contract's order;
* the circuit's tables as **data the Rust emits** (`Data.lean`, with a staleness test; never `σ`);
* **the eight declared claims** word for word (`contract::claim_words`) and their openings (`WhirBridge`'s
  transcription of `pcs_claim::verify_claim`);
* the **verifier-arithmetic lemmas** that `RecPiop`'s rounds and copy argument consume, proved;
* the **end statements** of the whole recursive verifier, stated here and proved in
  [`RecCompose`](../RecCompose/README.md): π2's part, in the random-permutation model (`RecKnowledgeSoundness2`,
  `RecCompleteness2`: the contract accepts only if the Keccak π1-rec3's recorded graph, run with the real
  Keccak-f[1600] as π2's circuit runs it, accepts the stream π2's extractor outputs); end-to-end knowledge soundness
  against the Keccak VM's relation (`KeccakVm.KvHolds`) as an **explicit reduction** (`RecKnowledgeSoundnessReduction`,
  `Reduction.lean`: the break is bounded by π2's error plus π1-rec3's and the merge hazard's experiments at
  Keccak-f[1600] for two explicit adversaries derived from the attacker, of its queries); and the end-to-end forms
  (`RecKnowledgeSoundness`, `RecCompleteness`) under named hypotheses about π1-rec3 at Keccak-f[1600]. The soundness
  ones (`Pi1FsKeccak`, `Pi1HazardKeccak`) are false as stated for computationally unbounded adversaries, which grind
  Keccak-f[1600] offline for free: read them as the Fiat–Shamir heuristic for adversaries of bounded Keccak-f[1600]
  work, which Lean does not model.

No `sorry`, no `native_decide`, every headline definition and theorem on Lean's three axioms (`RecStatement.lean`'s
`#guard_msgs`). It is a library of `formal/EndToEnd` (`RecStatement`, `srcDir = "../RecStatement"`, `warningAsError`),
as `UniStatement` is, whose definitions it reuses (the channel, `E`, the element words, the extractor's pieces), with
`UniKeccak`'s for π1 (the deployment `KDeployment`, the setup commitment `SetupRootsK` (`F`'s root and out-of-domain
answer), the setup `setupTreeKWith` and its answer `setupOodK`, the contract IV `contractIvKWith … keccakRec3`, the run
`runK`, a claim's opening `pcsOpenK`, the extractor `uniExtractorK`, the relation `KvHolds`), `WhirBridge.Pcs`'s for the
openings (`pcsVerifyWithHash`, `pcsVerifyWithHashO`, `oodPoint`) and `RecGraphKeccak`'s for π1-rec3's recorded graph and
merge hazard.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build RecStatement            # the library; the axiom guards
# the data (from the repository root, on h1: π2's circuit for the Keccak π1-rec3 compiled twice, its setup committed):
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement_keccak -- --ignored
```
(`RUSTFLAGS="-C target-cpu=native"` for the Rust; without `UPDATE_LEAN` the first command fails when `Data.lean` is
stale.)

## Reading order

1. [`Basic.lean`](RecStatement/Basic.lean): the circuit as the verifier reads it (`Coeff`, `Lin`, `Formula`, `Pair`,
   `Read`, `PublicTerm`, `Circuit` with each public term's hole) and π1's call words (`CallWord`).
2. [`Data.lean`](RecStatement/Data.lean) (generated): π2's circuit for the Keccak π1-rec3's graph at `KECCAK_128`,
   D16v: `2^24` positions, rows of 16, 55 formulas, 134 (block, role) pairs (5 pull-less) in 66 groups, 21 reads, 38
   public terms (16 of value zero, in no `Φ`) and their holes; π1's contract IV, the setup's root, the circuit's
   digest; π1's three claims (`30`, `29`, `26` words).
3. [`Core.lean`](RecStatement/Core.lean): **the arithmetic at `t`, over any field** (`CoreSpec.run`), every
   intermediate value a field of `Out`; the stacks' variables (`stackVars`).
4. [`Spec.lean`](RecStatement/Spec.lean): `Spec::of` (the blocks' constants in `K`, the groups, the ports' `Φ` by
   role, `phiOf`, the highest power of `γ`).
5. [`Verifier.lean`](RecStatement/Verifier.lean): the norm's inverse, the extension, `Spec.core` (the constants over
   `E`), `Q`'s slots (`quotientSlots`, `emptySlots`), **the IV** (`ivWith`, v3), `pairPoint`, `Reduced` and its five
   claims (`witness`, `setup`, `quotient`, `pushes`, `sum`), **`reduceWith`**, `runWith`/`run`.
6. [`Calls.lean`](RecStatement/Calls.lean): **the eight claims word for word** (`pcsCalls`: `callWord`,
   `claimWords`, `rootsAt`), the stream's length, the Keccak π1-rec3's contract IV (`pi1IvWith`,
   `UniKeccak.contractIvKWith … keccakRec3`).
7. [`Security.lean`](RecStatement/Security.lean): π2's circuit with `σ`, `κ` (`Pi2Circuit`: its digest, setup table
   over `F` and the setup's out-of-domain answer `setupOod`), the deployment and `RecDeployment.Real`, the setup's
   commitments (`RecSetupRoots`: π1's `F` and π2's, each a root and its answer), a declared claim decoded
   (`claimOfWords`) and opened (`pcsOpenWords`: `pcsOpenKO` or `UniKeccak.pcsOpenK` by `oodRead`;
   `pcsOpenKO_keccakF1600`), the proof (`RecProof`: the stream and eight opening proofs), the contract, the Keccak
   π1-rec3 at Keccak-f[1600] (its verifier and its recorded graph), the extractors, the experiments,
   **`RecKnowledgeSoundness2`**, **`RecCompleteness2`** (π2's part), the merge hazard on accepted streams
   (`Pi1HazardAccepted`), the hypotheses (`Pi1FsKeccak`, `Pi1HazardKeccak`, `Pi1CompletenessKeccak`,
   `Pi1HazardKeccakHonest`), **`RecKnowledgeSoundness`**, **`RecCompleteness`** (end to end, Prop-premise forms).
   [`Reduction.lean`](RecStatement/Reduction.lean): the derived adversaries (`pi1Adversary`, `hazardAdversary`) and
   **`RecKnowledgeSoundnessReduction`** (end to end, as an explicit reduction).
8. [`Lemmas/`](RecStatement/Lemmas): `Arith` (fractions, digits, the fold, the siblings' fold), `Side` (the pushes'
   sums, `Φ`'s fractions), `Subspace` (the indicators' closed form), `SpecOf` (the transcription's hypothesis, with
   `Φ`'s terms and their ports), `Push` (`push_side`), `Phi` (`phiPoly`, `V_{m−r}`'s Lagrange basis by rows,
   **`phiAt_eq`**), **`Main`** (`checks_claims_iff`, the claims' values), `SpecLink` (`Spec::of`'s constants are
   `SpecOf`'s).

## Rust → Lean

| Rust (`crates/leanvm/rec/src/pi2`, π2v3 on the PCS claims since `2775f816`) | Lean (`RecStatement.`) |
|---|---|
| `circuit.rs`: `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (but `σ`, `κ`), `max_gamma`, `coset_constants`, `vanishing`, `pair_constants`, `digest` | `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (with `holes`), `Circuit.maxGamma`, `cosetConstants` (`cosetConstantsF`), `vanishing` (`vanishingF`), `pairConstants`, `Pi2Circuit.digestWith` |
| `verifier.rs`: `NAME`, `SpecPair`, `Group`, `Spec`, `Spec::of`, `is_zero`, `normalised_constants`, `frobenius`, `inverse`, `extension`, `reduce`, `Reduced`, `verify`, `statement_words` | `name`, `SpecPair`, `Group`, `Spec`, `Spec.of` (`groupsOf`, `phiOf`), `PublicTerm.isZero`, `normalisedConstants`, `frobenius`, `normInverse`, `extension`, `reduceWith` (+ `CoreSpec.run`), `Reduced`, `runWith`/`run`, `UniStatement.publicWordsOf` |
| `verifier.rs` (`reduce`'s steps) | `digitsList`, `cellsList`/`foldLevel`, `zHat`, `fraction`, `groupDens`, `phiFrac`, `addFrac`, `pushStep`/`pushSums`, `wInvsList`, `foldW` |
| `prover.rs`: `stack_vars`, `QUOTIENT_SLOTS`, `EMPTY_SLOTS`, `iv`, `Setup::new`'s table and out-of-domain answer | `stackVars`, `quotientSlots`, `emptySlots`, `ivWith`/`iv`, `Pi2Circuit.setupStack`, `Pi2Circuit.setupOod` |
| `contract.rs`: `read_indices`, `element_word`, `claim_words`/`expected_calls`, `claim_of_words` | `elementIndices`, `UniStatement.elementWord`, `claimWords`/`pcsCalls`, `claimOfWords` (`elementOfWord`, `rootOfWord`) |
| `pcs_claim`: `verify_claim`, `ood_point` | `WhirBridge.Pcs.pcsVerifyWithHash` (at `WhirBridge.Pcs.oodPoint`, through `UniKeccak.pcsOpenK`), `WhirBridge.Pcs.pcsVerifyWithHashO` (the point computed over `F`, through `pcsOpenKO`); `pcsOpenWords` |
| `transcript.rs`: `cantor_beta1`, `pair_point`; `circuit/spec.rs`: `CallWord` | `cantorBeta1` (`UniStatement.cantorBeta1`), `pairPoint`, `CallWord` |
| `leanvm_univariate/contract.rs`: `variant_bytes`, `contract_iv_for` (at `KECCAK_REC3`) | `rec3VariantBytes`, `pi1IvWith` (`UniKeccak.variantBytesK`, `contractIvKWith`) |

**Deviations, none changing a value**: a `List` stands for a `Vec`, an out-of-range read gives a default (the Rust
would panic; it never does on the circuits tested); the Rust skips a product by a coefficient equal to one and, for a
one-pair group, its numerator `1` (here the products are taken); `γ^0` is read from the powers (`gammas[0] = 1`); the
arithmetic's inverse is the field's (the Rust's is the norm's, `normInverse`, transcribed); a port role's fraction of
no term (which `Spec::of` never makes) is `(0, 1)`.

## The data

`crates/leanvm/rec/tests/lean_statement_keccak.rs` (`render`) writes `Data.lean` from π2's
circuit for the Keccak VM's π1-rec3 at the 128-signature reference (`circuit::compile::pi2(record_verifier(KECCAK_128,
Keccak(KECCAK_REC3), Point), D16v)`, then `pi2::adapt`; the graph of `RecGraphKeccak/Emitted.lean`): the shape, the
formulas, the pairs, the reads, the public terms and their holes; π1's contract IV (`Compiled::pi1_iv`), the setup's
root (`Setup::new(circuit).root()`), the circuit's digest (`Circuit::digest`); π1's three calls
(`spec::Circuit::calls`). **Not `σ`, not `κ`**: the verifier reads neither; the setup's root and the digest bind them
(`RecDeployment.Real`); the setup's out-of-domain answer is computed from them (`Pi2Circuit.setupOod`). π1's contract
IV there is `contract_iv(KECCAK_128, KECCAK_REC3, PROGRAM_IV, SetupRoots::REFERENCE)`: at the reference setup
commitment (the Keccak 128 setup's `F` and its out-of-domain answer, the real `keccak128_rec3.txt` proof's), the same
as Lean's `RecGraphKeccak.Pi1.referenceRootsK` (the graph's setup call's constants). `keccak_statement_data_is_current`
fails when the file is stale; it also checks that the adapted circuit, π1's calls and π1's contract IV do not depend on
the stream or the public input.

## The statements (`Security.lean` and `Reduction.lean`, abridged: docstrings, `claimOfWords`' body and a proof left out)

**Two models, which do not compose formally.** π2's circuit computes π1-rec3's Fiat–Shamir challenges with the real
Keccak-f[1600] (a circuit is a fixed function: `RecCircuit.compile_sound`, `keccak_out`; for the Keccak graph
`RecGraphKeccak.pi1rec3K_end`); the Keccak π1-rec3's knowledge soundness is proved in the random-permutation model
(`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`: `uniBound128 (2^35/|E|) Q`, at most `2^-64` for `Q ≤ 2^64`).
No circuit computes a random permutation, which is inherent to recursion, so the statements come in two parts (as on
the membership line, where the random-permutation theorems and the EVM one do not formally compose):

1. **π2's part, in the random-permutation model** (provable): one random permutation `π` for π2's own Fiat–Shamir, the
   circuit's digest, the commitments and the eight openings.
2. **End to end against the Keccak VM's `KvHolds`, as an explicit reduction** (`RecKnowledgeSoundnessReduction`): for
   every adversary `A` of `Q` queries, the break's probability is at most `ε2 Q` plus the Keccak π1-rec3's
   Keccak-f[1600] soundness experiment for `pi1Adversary D A` plus the merge hazard's experiment for
   `hazardAdversary D A`. Both derived adversaries are `def`s: `A`, its queries logged, then π2's explicit extractor;
   they make `A`'s queries (at most `Q`, a conjunct of the Prop) and run in `A`'s time plus the extractor's (preimage
   replay, `W`'s inversion and decoding, Guruswami–Sudan at `2^24`, π1's graph's checks: polynomial; Lean does not
   model time). The Fiat–Shamir heuristic is applied by the reader to these two adversaries, in their Keccak-f[1600]
   work (`A`'s offline evaluations plus the extractor's graph checks per candidate), the resource it bounds and `Q`
   does not count.
3. **The Prop-premise corollaries**, under named hypotheses about π1-rec3 **at Keccak-f[1600]**, motivated by π1-rec3's
   random-permutation statements, and RecGraphKeccak's target `Pi1GraphIsVerifierK` (graph = verifier off the merge
   hazard, proved: `RecGraphKeccak.Sim.pi1GraphIsVerifierK`). `Pi1FsKeccak` and `Pi1HazardKeccak` quantify over every
   `OracleComp` adversary and count only its calls of `π`; such an adversary computes Keccak-f[1600] for free and
   grinds π1's challenges offline, so **they are false as stated**: the Fiat–Shamir heuristic for adversaries of
   bounded Keccak-f[1600] work, which Lean does not model. `Pi1CompletenessKeccak` and `Pi1HazardKeccakHonest` are
   about one fixed honest prover, the statement chosen before `π`: no adversary grinds there.

**The Keccak-f block** is the deployment's field `flock : KeccakVm.KeccakFlockSpec`: the relation is
`D.pi1.Relation D.flock` (`KvHolds D.flock prog s input q`), π1's extractor `uniExtractorK D.flock D.pi1`, the honest
relation `D.pi1.HonestRelation D.flock`. A field rather than a parameter of every statement: the verifier does not read
it, so π2's part and every definition the contract runs are unchanged, the statements keep their arity, and
`RecDeployment.Real` pins it to `KeccakFlock.keccakFlockSpec`, the block `uniKnowledgeSoundnessKeccakRec3_closed` is
proved at, as it pins the shape and the program IV (for any block, `KvHolds` means Keccak-f[1600] at the ports: the
block's `step_of_holds`).

**The merge hazard** (`RecGraphKeccak.MergeHazardK`) asks that the Keccak π1-rec3's run draw `t` (challenge 52) and that
`t` be a root of `Z_bad(p_0)` (`p_0` challenge 45; at most `2^16` hazardous `t`, `RecGraphKeccak.hazard_probK`); a run
that stops early, the empty stream included, is off it. The soundness hazard (`Pi1HazardAccepted`) also asks that
π1-rec3's graph accept the stream (`pi1GraphChecks`).

```lean
structure Pi2Circuit where
  circuit : Circuit
  sigma : ℕ → ℕ
  kappa : ℕ → K

def Pi2Circuit.setupOod (c : Pi2Circuit) (root : Digest) : E :=   -- the setup stack's value at oodPoint
  let vars := (stackVars c.circuit.logN).2.2
  let words := c.setupStack.toList.map ofK
  UniStatement.multilinearEval (words ++ List.replicate (2 ^ vars - words.length) 0)
    (WhirBridge.Pcs.oodPoint vars root).toList

structure RecDeployment where
  pi1 : UniKeccak.KDeployment             -- the Keccak VM's program, shape, program IV
  pi2 : List UInt8 → Pi2Circuit          -- π2's circuit for π1's contract IV (κ's constants)
  pi1Calls : List (List CallWord)
  pi1Stream : (ℕ → K) → Array UInt8     -- π1's stream as π2's witness holds it (RecCircuit's decodeStream)
  flock : KeccakVm.KeccakFlockSpec       -- the Keccak-f block of the relation KvHolds

def RecDeployment.pi1IvAt (D : RecDeployment) (roots : UniKeccak.SetupRootsK) : List UInt8 :=
  pi1Iv D.pi1.shape D.pi1.programIv roots     -- = UniKeccak.contractIvK D.pi1.shape keccakRec3 D.pi1.programIv roots

def RecDeployment.Real (D : RecDeployment) : Prop :=
  (∀ iv, (D.pi2 iv).circuit = Data.circuit) ∧ D.pi1Calls = Data.pi1Calls ∧ D.pi1.shape = RecGraphKeccak.Pi1.keccak128 ∧
    D.pi1.programIv = UniStatement.programIv ∧
    Id.run ((D.pi2 Data.pi1Iv).digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest ∧
    digestBytes (Id.run ((D.pi2 Data.pi1Iv).setupTreeWith (m := Id)
      fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root = Data.setupRoot ∧
    D.SetupFromCompiler ∧ D.flock = KeccakFlock.keccakFlockSpec

structure RecSetupRoots where                  -- the setup's commitments
  pi1 : UniKeccak.SetupRootsK                  -- F's root and out-of-domain answer
  pi2 : Digest
  pi2Ood : E

structure RecSetupTrees where                  -- π1's one tree, π2's tree, their answers
  pi1 : LeanVM.Prover.Tree
  pi2 : LeanVM.Prover.Tree
  pi1Ood : E
  pi2Ood : E

def RecDeployment.setupTreesWith (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← UniKeccak.setupTreeKWith F D.pi1
  let r1 := D.pi1.setupRoots t1
  let t2 ← (D.circuitAt r1).setupTreeWith F
  return ⟨t1, t2, r1.fOod, (D.circuitAt r1).setupOod t2.root⟩

-- the declared claims' openings
def claimOfWords (words : List (List UInt8)) : Option (Digest × E × List E × E)   -- root, ood, point, value

def oodRead (n : ℕ) : Bool := n == 24 || n == 28          -- W's and Q's sizes: the proof's commitments

def pcsOpenKO {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (n : ℕ) (root : Digest) (ood : E)
    (pt : List E) (v : E) (p : Compile.Proof) : m Bool :=
  if h : pt.length = n then
    WhirBridge.Pcs.pcsVerifyWithHashO (keccak256With F) F ⟨root, ood, pt, v, h⟩ p
  else pure false

def pcsOpenWords {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (words : List (List UInt8))
    (proof : Compile.Proof) : m Bool :=
  match claimOfWords words with
  | none => pure false
  | some (root, ood, point, value) =>
    if oodRead point.length then pcsOpenKO F point.length root ood point value proof
    else UniKeccak.pcsOpenK F point.length root ood point value proof

theorem pcsOpenKO_keccakF1600 (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    pcsOpenKO (m := Id) keccakF1600 n root ood pt v p =
      UniKeccak.pcsOpenK (m := Id) keccakF1600 n root ood pt v p

structure RecProof where       -- the stream and the eight opening proofs, in claim order
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  f : Compile.Proof
  w : Compile.Proof
  setup : Compile.Proof
  qId : Compile.Proof
  qPush : Compile.Proof
  qSum : Compile.Proof

def RecDeployment.ivWith (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let c := D.circuitAt roots.pi1
  let digest ← c.digestWith F
  RecStatement.ivWith F (D.pi1IvAt roots.pi1) (digestBytes roots.pi2) roots.pi2Ood digest c.circuit.logN

def RecDeployment.contractWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let iv ← D.ivWith F roots
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood
      proof.stream r
    if calls.length ≠ 8 then return (false, calls) else
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenWords F words p)
    return (ok, calls)

-- π2's part, in the random-permutation model
def Pi1GraphAccepts (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Prop :=
  ∃ out gops, RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK iv1 input.toList s = some out ∧
    (∀ z ∈ out.zeros, z = 0) ∧ (∀ z ∈ out.nonzeros, z ≠ 0) ∧ out.calls.mapM decodePi1Call = some gops ∧
    gops.map (·.2.2) = ops.map (·.2.2) ∧
      (gops.take 2).map (fun o ↦ (o.1, o.2.1)) = (ops.take 2).map (fun o ↦ (o.1, o.2.1))

def RecBreaksKnowledgeSoundness2 (D : RecDeployment) (ext : RecExtractor2) (z : RecOutcome2) : Prop :=
  z.1.2 = true ∧ ¬ ∃ s ops, ext z.2.2.2.1 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some s ∧
    contractPi1Openings z.2.2.2.2 = some ops ∧
    Pi1GraphAccepts (D.pi1IvAt z.2.2.2.1.pi1) z.1.1.1 s ops

def RecKnowledgeSoundness2With (D : RecDeployment) (ext : RecExtractor2) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D ext z] ≤ ε2 Q

def RecKnowledgeSoundness2 (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundness2With D (recExtractor2 D) ε2

def RecCompleteness2 (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤ δ2

-- the merge hazard: the run draws t (challenge 52), t a root of Z_bad(p_0) (RecGraphKeccak/Main.lean)
def MergeHazardK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Prop :=
  let ch := (Id.run (UniKeccak.runWithK (m := Id) (fun s ↦ pure (π s)) keccak128 iv publicInput stream
    UniKeccak.keccakRec3 .point)).chan.challenges
  53 ≤ ch.size ∧ HazardK (ch.getD 45 0) (ch.getD 52 0)

def Pi1HazardAccepted (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) : Prop :=
  pi1GraphChecks iv1 input s = true ∧ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 iv1 input.toList s

-- the hypotheses about π1-rec3 at Keccak-f[1600] (the soundness ones false as stated for unbounded adversaries)
def Pi1FsKeccak (D : RecDeployment) (ε1 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Pi1Adversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (A roots evals) permutationCallCost Q) →
    Pr{let z ← pi1KeccakSoundnessExperiment D A}[
      UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z] ≤ ε1 Q

def Pi1HazardKeccak (D : RecDeployment) (εh : ℕ → ℝ≥0∞) : Prop :=
  ∀ (B : Pi1StreamAdversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (B roots evals) permutationCallCost Q) →
    Pr{let z ← pi1HazardExperiment D B}[Pi1HazardAccepted z.1 z.2.1 z.2.2] ≤ εh Q

def Pi1CompletenessKeccak (D : RecDeployment) (P1 : Pi1Prover D) (δ1 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← pi1KeccakCompletenessExperiment D P1 input rows q}[v = false] ≤ δ1

def Pi1HazardKeccakHonest (D : RecDeployment) (P1 : Pi1Prover D) (δh : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let z ← pi1HonestHazardExperiment D P1 input rows q}[
      ∃ iv s, z = some (iv, s) ∧ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 iv input.toList s] ≤ δh

-- the end-to-end corollaries, against the Keccak VM's KvHolds
def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.2.2.2 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some w ∧ D.pi1.Relation D.flock w.1 z.1.1.1 w.2

def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

-- end to end, as an explicit reduction (Reduction.lean)
def hazardAdversary (D : RecDeployment) (A : RecAdversary) : Pi1StreamAdversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, (recExtractor2 D roots z.1 evals T z.2).getD #[])

def pi1Adversary (D : RecDeployment) (A : RecAdversary) : Pi1Adversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, z.2.pi1Proof ((recExtractor2 D roots z.1 evals T z.2).getD #[]))

def RecKnowledgeSoundnessReduction (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D (recExtractor D) z] ≤
      ε2 Q +
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z] +
        Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2]

-- the Prop-premise corollary
def RecKnowledgeSoundness (D : RecDeployment) (ε2 ε1 εh : ℕ → ℝ≥0∞) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK → Pi1FsKeccak D ε1 → Pi1HazardKeccak D εh →
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ ε2 Q + ε1 Q + εh Q

def RecCompletenessWith (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← recCompletenessExperiment D P input rows q}[v = false] ≤ δ

def RecCompleteness (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ1 δh δ2 : ℝ≥0∞) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK → Pi1CompletenessKeccak D P1 δ1 → Pi1HazardKeccakHonest D P1 δh →
    RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)
```

* **The contract** `D.contractWith F roots input proof`: π2's IV over `F` (`D.ivWith`, v3:
  `keccak("leanvm-rec-iv-v3" ‖ π1's contract IV ‖ π2's setup root ‖ its out-of-domain answer ‖ the circuit's digest ‖
  log_n)`, π1's contract IV the Keccak π1-rec3's at π1's setup commitment **over Keccak-f[1600]** (`pi1IvAt`)), the
  run of π2's verifier for the circuit `D.circuitAt roots.pi1 = D.pi2 (pi1IvAt roots.pi1)` (its verdict `all ≠ 0`),
  then **the eight declared claims** (`pcsCalls`), each the EIP draft's PCS claim in its words (the root's 32 bytes,
  the out-of-domain answer, the point's coordinates, the value, each element its `element_word`): π1's three (`C1`,
  `C2` from the stream, `F`'s root and answer the setup's, `pi1CallsWith`; their points the coordinates the contract
  derives from π1-rec3's pair challenges; `2^27`, `2^26`, `2^23` words), then π2's five (`W`'s root and answer from the
  stream, the setup's the deployment's, `Q`'s three on `Q`'s root and answer; `2^24`, `2^25`, `2^28` words). Each is
  decoded (`claimOfWords`: every element's top 64 bits zero) and opened on its point's length (`pcsOpenWords`).
  **The out-of-domain point**: `W`'s and `Q`'s claims (`oodRead`: sizes `24`, `28`) by `pcsOpenKO`, which computes the
  point over `F` (`WhirBridge.Pcs.pcsVerifyWithHashO`: `n` calls of `keccak256With F` at `oodInput n root j`), so in
  the random-permutation model it is read off the permutation, which `Q`'s three claims on one commitment need (the
  answer binds the root: `WhirBridge.Pcs.ood_binding_coords`); the claims on the deployment's commitments, π1's three
  and π2's setup's, by `UniKeccak.pcsOpenK` (`WhirBridge.Pcs.pcsVerifyWithHash` at the fixed `WhirBridge.Pcs.oodPoint`,
  as π1's own verifier and theorems take them; each is one claim on its commitment, so no binding is needed). **At the
  real Keccak-f[1600] the two agree** (`pcsOpenKO_keccakF1600`: both are the deployed `ood_point`). Its verdict and the
  claims' words; `verifierWith` its verdict. π1's verifier itself never runs: π2 proves its graph accepted.
* **The setup** (`D.setupTreesWith`): π1's one tree (`UniKeccak.setupTreeKWith`, the Keccak setup stack) with its
  out-of-domain answer (`UniKeccak.setupOodK`; π1's commitment `KDeployment.setupRoots`) and π2's (`PcsQuotient.commitWith`
  of `κ`, `κ + σ` in the basis `B`, for the circuit at π1's IV) with its answer (`Pi2Circuit.setupOod`); the answers are
  the stacks' values at the roots' out-of-domain points (the deployed Keccak-256), constants of the verifiers. The
  Keccak-f block's matrices are never committed. Its evaluations are π1's tree's, then π2's.
* **π1-rec3 at Keccak-f[1600]**: `pi1KeccakVerifierWith F` (`UniKeccak.verifyWithK` at `keccakRec3` with its IV and run
  over Keccak-f[1600], `UniKeccak.runK … keccakRec3 .point`; its three claims opened over `F` by `UniKeccak.pcsOpenK` on
  their stacks' variables `stackVarsK`) for the soundness and completeness hypotheses, whose experiments run on the
  recursive setup; `pi1GraphVerifierWith F` (the recorded graph `pi1GraphK` over Keccak-f[1600], its three claims, `F`'s
  commitment the setup's, opened the same way) for π2's completeness.
* **The extractors** (explicit, computable): `recExtractor2` decodes π2's `W` under the root the stream names (fast
  path, unique decoder, list decoder, at `W`'s stack), reads each candidate's witness values (the stack's leading `N`
  words, `basisValue`) and π1's stream off them (`D.pi1Stream`), the first on which the Keccak π1-rec3's graph accepts at
  Keccak-f[1600] with the contract's π1 openings (`pi1GraphAcceptsB`, `pi1OpsOf`); `recExtractor` then runs the Keccak
  π1's own extractor (`UniKeccak.uniExtractorK D.flock`) on that stream and the proof's three π1 opening proofs
  (`RecProof.pi1Proof`, a `UniKeccak.KeccakProof`), its row counts the stream's. The extractors take the setup's
  commitments.
* `RecDeployment.Real`: `∀ iv, (D.pi2 iv).circuit = Data.circuit`, π1's calls, the reference shape
  (`RecGraphKeccak.Pi1.keccak128`) and program IV, at π1's reference IV (`Data.pi1Iv`) the digest and setup root the
  Rust computed (which bind `σ`, `κ`), `SetupFromCompiler` (σ, κ the Lean compiler's on the Keccak graph `pi1GraphK`
  at `RecGraphKeccak.Emitted.rootsAt`, at every **32-byte** IV; π1's contract IV is a Keccak-256 digest), and the
  Keccak-f block `KeccakFlock.keccakFlockSpec`. The program `D.pi1.prog` is not pinned: the end theorems hold for every
  program of the reference shape.
* **The deployed bytecode** is linked to this model by transcription and the Rust's tests (`contract.rs`'s `parity`,
  `parity_deployable`), not by a Lean proof.

## The verifier-arithmetic lemmas (`Lemmas/`, proved)

Over any field of characteristic two, for `RecPiop`'s circuit `G` on a Cantor basis `B` (`ω = Heap.omega B`), under
**`SpecOf S G B pairOf portOf pubOf`** (the arithmetic's constants are `Spec::of` of `G`: the shape, the normalised
recursion's constants, the pairs enumerating `G.pairs` with their `s` and `Ẑ_s(c_p)`, the groups partitioning them with
their role, pull flag and formula, the ports' `Φ` by role, its terms distinct ports, each term's role and row its port's
hole's and its value the port's public fingerprint, the ports in no term of zero fingerprint):

* **`ind_eval_closed`** (`Subspace`): at `t ∉ V_m`, `Ẑ_s(t) + Ẑ_s(c_p) ≠ 0` and
  `(G.ind ω p).eval t = w_m(t)/(Ẑ_s(t) + Ẑ_s(c_p))`;
* **`phiAt_eq`** (`Phi`): the verifier's `Φ_k(t) = w_m G_n/G_d` is `phiPoly`'s value, `phiPoly` of degree below
  `N` taking each port's public fingerprint at its hole (`phiPoly_eval_port`);
* **`cellsList_eq_cellsOf`** (`Arith`): the siblings' fold is `RecPiop.cellsOf` (`ω_{2k+1} = ω_{2k} + 1`);
  **`foldW_eq_foldAt`**: `W`'s fold is `RecPiop.foldAt`;
* **`push_side`** (`Push`): at `t ∉ V_m`, `B ≠ 0`, `R_d ≠ 0`, the internal pushes `P_v(t) = v_0 + w_m A/B`, and the
  ports' fraction `1_S(t) Δ + T(t) = w_m R_n/R_d`, for any `Φ` taking the verifier's `Φ_k(t)`;
* **`all_ne_zero_iff`** (`Main`): the one inversion carries the nonzero conditions: `all ≠ 0` iff `t ∉ V_{m+1}`,
  `c_h ≠ 0`, `Y = c_h + c_q ≠ 0` and `α + P_v(t) + ξ ≠ 0`;
* **`checks_claims_iff`** (`Main`):
  ```lean
  ((S.run inp).all ≠ 0 ∧
      idEq (S.run inp) (c3Of S) (S.run inp).rhoQ ht qt pt qpt (sq^[G.logN] inp.t) inp.s ∧
      pushEq (S.run inp) inp.ρ pt qpt (sq^[G.logN] inp.t) inp.s ∧
      sumH = 0 ∧ inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
    (sq^[G.logN + 1] inp.t ≠ 0 ∧
      inp.α + G.pvAt (Heap.omega B) v inp.γ inp.t + inp.ξ ≠ 0 ∧
      G.QClaim (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ) (c3Of S) v inp.ξ inp.s inp.α inp.β inp.γ inp.t
        inp.ρ ht qt pt qpt ∧
      sumH = 0 ∧ inp.ξ = κt + inp.β * σt ∧ foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ = foldTrue)
  ```
  (`v = cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t`; `idEq`, `pushEq` `Q`'s identity and pushes'
  claims normalised, at the true values `h(t)`, `q(t)`, `P(t)`, `q_P(t)`): the verifier's check passes and its claims
  hold iff `t ∉ V_{m+1}`, `α + P_v(t) + ξ ≠ 0` and `RecPiop`'s claims hold (`QClaim` at `c_3`, the sum, the setup's
  claim, the fold); **`checks_claims_iff_post2`** states the right side with `RecPiop.Post2` itself, for any tables'
  model `Mo` whose `Φ` is `phiPoly` and whose constant is `c_3`, `P`'s share of the claims read as
  `P(t) + S(t)/Z_V(t)` and the sum `Σ_V (h + c_3 S)` (`Q`'s slot `12`, `S`, the prover's);
* the claims' values and points (`Main`): `run_quotientValue`, `run_pushesValue`, `run_u` (`u_l = w_l/(1 + w_l)`),
  `digitsScale_eq` (`t/w_{m+1} = Π_{l ≤ m} (1 + w_l)^{-1}`), for the tables' layer;
* **`normConsts_of_spec`**, **`pairZ_eq_zHat`** (`SpecLink`): `Spec::of`'s constants (`coset_constants`,
  `normalised_constants`, `pair_constants`) are `SpecOf`'s; they commute with a field homomorphism (`K → E`).

## Where the statements are proved

In [`RecCompose`](../RecCompose/README.md), at `D.Real` and the run-checked inputs (`Pi2Circuits D`, `GraphsAgree`,
`Pi2ViewChecked`), and at the real deployment (`RecCompose.realDeployment prog hprog`) from the evaluated checks
`GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked`:

* **`RecKnowledgeSoundnessReduction D pi2Bound`**, `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64` (`2^-64.93` at `2^64`):
  `RecCompose.recKnowledgeSoundness_reduction`, `recKnowledgeSoundness_reduction_real`. No Fiat–Shamir premise. The
  eight openings are charged once (`WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`, the point read off the permutation
  at `W`'s and `Q`'s sizes), and `Q`'s three claims are bound to one candidate by its out-of-domain answer
  (`RecCompose.qOodBinding`, from `WhirBridge.Pcs.ood_binding_coords` at `n = 28`): `pi2OpenErr = 269 · 2^-137 +
  2^-156`; π2's round 1 `(4N − 1)/|F|` with `Q`'s empty slots (`pi2RoundErr`, `2^-140.92` with the lists).
* **`RecKnowledgeSoundness2 D pi2Bound`**: `recKnowledgeSoundness2_closed`; **`RecKnowledgeSoundness D pi2Bound ε1
  εh`**: `recKnowledgeSoundness_closed` (premises `Pi1FsKeccak`, `Pi1HazardKeccak`, false as stated: above).
* **`RecCompleteness2`** at the concrete π1-rec3 prover (`RecCompose.Pi1K.pi1Rec3ProverK`, UniKeccakComplete's with its
  Fiat–Shamir over Keccak-f[1600]), `δ2 ≤ 2^-164`: `Pi1K.recCompleteness2_pi2_rec3_K`; **`RecCompletenessWith`** end to
  end, error `δ1 + δh + 2^-164` under `Pi1CompletenessKeccak δ1` and `Pi1HazardKeccakHonest δh`:
  `Pi1K.recCompleteness_real_K_fs_bits`.

## What is tested, what is defined

**Tested**: `Data.lean` against the Rust (`tests/lean_statement_keccak.rs`'s `keccak_statement_data_is_current`: the
file is what `render` writes for the Keccak π1-rec3's circuit; the circuit, π1's calls and π1's contract IV do not
depend on the stream or the public input). **No Lean differential run of π2's verifier on Keccak vectors exists.**
π2's verifier on the PCS claims (`Core`, `Spec`, `Verifier`, `Calls`, `claimOfWords`, the IV v3) is a transcription;
what runs against the Rust is π2's Lean prover (`RecComposeTest/Pi2Prover.lean`: on 2/2 regenerated vectors it writes
the Rust's setup, `W` and `Q` roots, their out-of-domain answers and its stream byte for byte, and recomputes the
Rust's IV v3), the evaluated `viewCheck` (`pi2::adapt` transcribed, at two IVs) and π1's contract IV and claim words
(`UniKeccak`'s, checked against the Rust there: [`../UniKeccak/README.md`](../UniKeccak/README.md)).

**Evaluated** (in `RecCompose`, by running Lean): the digest and the setup root of the Lean compiler's `σ`, `κ` at π1's
reference IV are `Data.digest`, `Data.setupRoot` (`DigestChecked`, `SetupRootChecked`, `rec-real-check`).

**Defined, not tested**: the extractors, the experiments, the Props. The claims' openings are `WhirBridge`'s
transcription of `verify_claim`, tested there (`Test/CheckPcs.lean`); the Rust mocks the block's frame.

## Open points

1. **The random-permutation theorems do not formally compose with the circuit's Keccak-f[1600]**. The Props at
   Keccak-f[1600] are premises whose readings are heuristic, not theorems. For soundness the meeting point is the
   reduction `RecKnowledgeSoundnessReduction`: the reader applies the Fiat–Shamir heuristic to its two explicit derived
   adversaries (motivated by `UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed` and
   `RecGraphKeccak.hazard_probK`). The Props `Pi1FsKeccak`, `Pi1HazardKeccak` are false as stated for unbounded
   adversaries (they grind Keccak-f[1600] offline for free); `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest` (about
   the honest prover) are not provable in this model. `Pi1CompletenessKeccak`'s random-permutation reading at the
   concrete prover is proved (`RecCompose.Pi1K.pi1CompletenessFs_rpm`, from
   `UniKeccakComplete.uniCompletenessKeccakRec3_closed`: `deltaK < 2^-169`). **`Pi1HazardKeccakHonest`'s
   random-permutation reading is not proved**: it is motivated only by `hazard_probK`, a count (at most `2^16`
   hazardous `t` per `p_0`, so `2^-176` for a uniform `t` with `p_0` fixed), not a game.
2. **`pi1Stream`** is a field of the deployment: where π2's witness holds π1's stream is the circuit compiler's (the
   stream's hashed bytes are free bits of π2's witness, `RecCircuit.Compiled.decodeStream`); the composition instantiates
   it. **`pi2`** is π2's circuit for π1's contract IV (the seed's constants): at the real deployment, the Lean
   compiler's at every IV (`SetupFromCompiler`); that it compiles, passes `viewCheck` and decodes π1's stream as at the
   reference IV, at every 32-byte IV, is `IvChecked`, evaluated at three IVs only ([`../RecCompose/README.md`](../RecCompose/README.md), "Remaining"). **`flock`** is the
   Keccak-f block of the relation, pinned by `Real`.
3. **π1's setup commitment** (`F`'s root and answer) is the setup's in the model's contract (π1's IV derived at the
   setup's own commitment); the Rust's `Data.pi1Iv` is at `SetupRoots::REFERENCE` (= `referenceRootsK`).
4. **The out-of-domain point by size.** The contract reads the point off the permutation at `W`'s and `Q`'s sizes
   (`24`, `28`) and takes the fixed `oodPoint` at the deployment's (`27`, `26`, `23`, `25`; the two sets are disjoint
   at the reference); at the real Keccak-f[1600] the two are the same function (`pcsOpenKO_keccakF1600`).
5. **The degenerate events** (`all = 0`: `t ∈ V_{m+1}`, `c_h = 0`, `c_h + c_q = 0`, `α + P_v(t) + ξ = 0`) reject;
   they matter for completeness only (`all_ne_zero_iff` names them).
