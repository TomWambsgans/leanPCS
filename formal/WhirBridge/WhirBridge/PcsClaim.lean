/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

The EIP's PCS opening, version 1 (`crates/pcs_claim/src/lib.rs`, `docs/PCS_CLAIM.md`), as a program of
leanerVM `mumbai`'s verifier language, and its Fiat-Shamir soundness in the random-oracle model. The
construction (the seedings naming the statement, the program of every statement, its certificate) is
`Family.lean`'s, adapted from mumbai's for leanVM (https://github.com/Verified-zkEVM/leanerVM, commit
6175f1a0, MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/EndToEnd/Sound/Statements.lean`).
-/
import WhirBridge.Verifier

/-!
# The PCS claim and its opening (version 1)

A PCS claim (`PcsClaim`, `crates/pcs_claim/src/lib.rs`) states that the multilinear polynomial `f`
over `K` in `n` variables committed to as `(root, ood)` takes the value `value` at `point`:

```
PCS_claim = version (1) ‖ n (1) ‖ root (32) ‖ ood (24) ‖ point (24 n) ‖ value (24)
```

each element of `E` 24 bytes, its limbs `c2, c1, c0` big-endian (`element_bytes`). `ood` is
`f(z)`, `z` the out-of-domain point derived from the root (`ood_point`): `z_j` the element the low 24
bytes of `keccak256("leanPCS-ood" ‖ 1 ‖ n ‖ root ‖ j)` encode.

`pcs::verify_claim` (`lib.rs:290-330`), which `pcsVerifyWithHash` transcribes:

1. reject unless `15 ≤ n ≤ 28` and the point has `n` coordinates;
2. the IV `keccak256(PCS_claim)` (`iv`, the dependency's payload), the public digest zero
   (`Transcript::new(proof, iv, PUBLIC_DIGEST, true)`);
3. the proof's first two scalars are the root, read (absorbed) and checked equal to the claim's;
4. `λ` sampled; WHIR (`verify_whir`, leanVM's deployed ladder at rate `1/2`) on the target
   `ood + λ · value` and the weight `eq(z, ·) + λ · eq(point, ·)`, `eq` the Rust's closure (`eqZ`).

As mumbai's stacked opening this is the opening of two claims, `(z, ood)` and `(point, value)`, on the
stacking `stacking n` whose stack **is** the table (`n` variables, `64` lanes of `2^(n-6)` words in
the order of `f`'s variables): `check_eq`, `prog_eq`.

The out-of-domain point enters the program as `zOf root` for a function `zOf : Digest → Vector E n`
fixed for the verifier (deployed: `oodPoint`, with mumbai's Keccak-256, as `opening.rs`'s layout id
is). Soundness holds for every such function; the binding of `PcsBinding.lean` models it as a random
oracle.

* `claimBytes_injective`: the claim's bytes name the claim (at one `n`);
* `seeds`: the seeding of a claim, its IV `H(claimBytes x)` (no other prefix: the claim's first two
  bytes are the prefix the verifier fixes), the public digest zero, the root history the claims'
  reads (`Family.lean`'s `famHistory`);
* `pcsVerify_imp`: acceptance by the transcription implies acceptance by the proven program;
* **`pcs_family_sound`**, **`pcs_sound`**: an adversary of at most `QA` queries outputs a claim and a
  proof; the verifier accepts while every candidate of the word extracted for the root violates
  `f(z) = ood` or `f(point) = value` with probability at most
  `openingBound QA = (QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)`, `≤ 2^-63` for
  `QA ≤ 2^64`.
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound (commitStack_after_ret extractedFrom_eq boundary_append_of)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Constants (`lib.rs:38-62`) -/

/-- `VERSION`: the PCS version. -/
def pcsVersion : ℕ := 1

/-- `MIN_VARIABLES`, `MAX_VARIABLES`: the variables version `1` opens, WHIR's stacks of `2^15` to
`2^28` words. -/
def minVars : ℕ := 15
def maxVars : ℕ := 28

/-- `MAX_PCS_VARIABLES`: the EIP's bound on `n` in a well-formed claim. -/
def maxPcsVariables : ℕ := 32

/-! ## Bytes -/

/-- A `K` word's eight big-endian bytes (`u64::to_be_bytes`). -/
def kBytesBE (a : K) : Bytes := (kBytes a).reverse

/-- **`element_bytes`** (`lib.rs:72-78`): the limbs `c2, c1, c0`, each big-endian, 24 bytes. -/
def elemBytes (x : E) : Bytes := kBytesBE (x.limb 2) ++ kBytesBE (x.limb 1) ++ kBytesBE (x.limb 0)

theorem kBytesBE_length (a : K) : (kBytesBE a).length = 8 := by
  simp [kBytesBE, kBytes_length]

theorem kBytesBE_injective : Function.Injective kBytesBE := fun a b h ↦
  LeanVM.Protocol.Compile.Rom.kBytes_injective (List.reverse_injective h)

theorem elemBytes_length (x : E) : (elemBytes x).length = 24 := by
  simp [elemBytes, kBytesBE_length]

theorem elemBytes_injective : Function.Injective elemBytes := by
  intro x y h
  unfold elemBytes at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [kBytesBE_length])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [kBytesBE_length])
  apply E.ext
  intro i
  fin_cases i
  · exact kBytesBE_injective h3
  · exact kBytesBE_injective h2
  · exact kBytesBE_injective h1

theorem length_flatMap_elemBytes : ∀ l : List E, (l.flatMap elemBytes).length = 24 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, elemBytes_length, length_flatMap_elemBytes l,
      List.length_cons]
    ring

theorem digestBytes_length' (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

/-! ## The claim (`PcsClaim`, `lib.rs:94-150`) -/

/-- **A PCS claim on `n` variables**: the root, the out-of-domain answer, the point (`n`
coordinates) and the value. -/
structure Claim1 (n : ℕ) where
  root : Digest
  ood : E
  point : List E
  value : E
  wide : point.length = n

theorem Claim1.ext' {n : ℕ} {x x' : Claim1 n} (h1 : x.root = x'.root) (h2 : x.ood = x'.ood)
    (h3 : x.point = x'.point) (h4 : x.value = x'.value) : x = x' := by
  cases x; cases x'; cases h1; cases h2; cases h3; cases h4; rfl

/-- **`PCS_claim`** (`PcsClaim::encode`, `lib.rs:108-118`): `VERSION ‖ n ‖ root ‖ ood ‖ point ‖
value`. -/
def claimBytes {n : ℕ} (x : Claim1 n) : Bytes :=
  [pcsVersion.toUInt8, n.toUInt8] ++ digestBytes x.root ++ elemBytes x.ood ++
    x.point.flatMap elemBytes ++ elemBytes x.value

theorem claimBytes_length {n : ℕ} (x : Claim1 n) : (claimBytes x).length = 82 + 24 * n := by
  simp only [claimBytes, List.length_append, digestBytes_length', elemBytes_length,
    length_flatMap_elemBytes, x.wide, List.length_cons, List.length_nil]
  ring

/-- **The claim's bytes name the claim** (at one `n`): fixed-width fields. -/
theorem claimBytes_injective {n : ℕ} {x x' : Claim1 n} (h : claimBytes x = claimBytes x') :
    x = x' := by
  unfold claimBytes at h
  have hp : (x.point.flatMap elemBytes).length = (x'.point.flatMap elemBytes).length := by
    rw [length_flatMap_elemBytes, length_flatMap_elemBytes, x.wide, x'.wide]
  obtain ⟨h4, h5⟩ := List.append_inj h (by
    simp only [List.length_append, digestBytes_length', elemBytes_length, hp])
  obtain ⟨h3, h3'⟩ := List.append_inj h4 (by
    simp only [List.length_append, digestBytes_length', elemBytes_length])
  obtain ⟨h2, h2'⟩ := List.append_inj h3 (by simp only [List.length_append, digestBytes_length'])
  obtain ⟨-, h1'⟩ := List.append_inj h2 rfl
  refine Claim1.ext' (digestBytes_injective h1') (elemBytes_injective h2') ?_
    (elemBytes_injective h5)
  exact LeanVM.Protocol.Compile.Rom.flatMap_inj_of_length elemBytes_length elemBytes_injective
    (by rw [x.wide, x'.wide]) h3'

/-! ## The out-of-domain point (`ood_point`, `lib.rs:83-91`) -/

/-- `OOD_TAG`: the ASCII bytes of `leanPCS-ood`. -/
def oodTag : Bytes := [0x6c, 0x65, 0x61, 0x6e, 0x50, 0x43, 0x53, 0x2d, 0x6f, 0x6f, 0x64]

/-- The input of coordinate `j`: `OOD_TAG ‖ VERSION ‖ n ‖ root ‖ j`, one byte each but the root. -/
def oodInput (n : ℕ) (r : Digest) (j : ℕ) : Bytes :=
  oodTag ++ [pcsVersion.toUInt8, n.toUInt8] ++ digestBytes r ++ [j.toUInt8]

/-- A `K` word from eight big-endian bytes (`u64::from_be_bytes`). -/
def beK (bs : Bytes) : K := K.ofLane (leLane bs.reverse 0)

/-- **`element_of`** (`lib.rs:80-85`): the element 24 bytes encode, limbs `c2, c1, c0` big-endian. -/
def elemOf (bs : Bytes) : E :=
  E.ofLimbs (beK ((bs.drop 16).take 8)) (beK ((bs.drop 8).take 8)) (beK (bs.take 8))

/-- **The out-of-domain point** of a root on `n` variables, with a Keccak-256 `h`: coordinate `j`
the element the low 24 bytes of `h(oodInput n root j)` encode. -/
def oodPointWith (h : Bytes → Digest) (n : ℕ) (r : Digest) : Vector E n :=
  Vector.ofFn fun j ↦ elemOf ((digestBytes (h (oodInput n r j))).drop 8)

/-- The deployed out-of-domain point: with Keccak-256. -/
def oodPoint (n : ℕ) (r : Digest) : Vector E n := oodPointWith keccak256 n r

/-! ## The stacking: the stack is the table -/

/-- **Version 1's stacking**: a table of `n` variables committed as itself, a claim's weight the
Rust's `eq(point, ·)` (`verify_claim`'s closure, `lib.rs:316-321`), no stack claim of its own. -/
def stacking (n : ℕ) : Stacking :=
  ⟨n, n, fun c ↦ eqZ c.point, fun c ↦ isMultiaffine_eqZ c.point n, [], fun _ h ↦ by cases h⟩

/-- **`f(p)`**: the multilinear polynomial of the stack `q`, `Σ_i q_i · eq(p, bits of i)` (the EIP's
`f(x) = Σ_i f_i Π_j ℓ_j(i, x)`, bit `0` the least significant). -/
noncomputable def colEval {n : ℕ} (q : Column n) (p : List E) : E :=
  ∑ x : Fin (2 ^ n), eqEval p (boolPoint n x) * ofK (q.values.getD x 0)

/-- **A claim holds of a stack exactly when its polynomial has the value at the point.** -/
theorem holds_iff {n : ℕ} (q : Column n) (c : Claim) :
    StackClaim.Holds n ((stacking n).weight c, c.value) q ↔ colEval q c.point = c.value := by
  show (∑ x : Fin (2 ^ n), eqZ c.point (boolPoint n x) * ofK (q.values.getD x 0)) = c.value ↔ _
  simp only [eqZ_eq_eqEval]
  rfl

/-- The two claims one opening proves: `f(z) = ood`, then `f(point) = value`. -/
def claimsOf {n : ℕ} (z : Vector E n) (x : Claim1 n) : List Claim :=
  [⟨z.toList, x.ood⟩, ⟨x.point, x.value⟩]

/-- They as a statement on the stacking (`Family.lean`'s `Stmt`). -/
def toStmt {n : ℕ} (z : Vector E n) (x : Claim1 n) : Stmt (stacking n) where
  claims := claimsOf z x
  short := by simp [claimsOf, stacking]
  wide c hc := by
    simp only [claimsOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp [stacking]
    · simpa [stacking] using x.wide

/-! ## The opening check (`verify_claim`, `lib.rs:300-330`) -/

/-- **The check past the root** (`lib.rs:309-326`): `λ`, the target `ood + λ · value`, the weight
`eq(z, ·) + λ · eq(point, ·)`, then WHIR at the stack's `n` variables and rate `2^-R`. -/
def check (n R : ℕ) (z : List E) (x : Claim1 n) : Prog Unit := do
  let lam ← Prog.sampleChallenge
  verifyWhir n R (x.ood + lam * x.value) fun pt ↦ eqZ z pt + lam * eqZ x.point pt

theorem dot_two (lam a b : E) : dot (powers lam 2) [a, b] = a + lam * b := by
  simp [dot, powers, powersFrom]

/-- **The check is mumbai's stacked opening** of the two claims on `stacking n`. -/
theorem check_eq {n R : ℕ} (z : List E) (hz : z.length = n) (x : Claim1 n) :
    check n R z x = (stacking n).check R [⟨z, x.ood⟩, ⟨x.point, x.value⟩] := by
  rw [Stacking.check_eq_ite, if_pos (by
    intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hz
    · exact x.wide)]
  unfold check verifyStackedOpening
  have hv : ∀ lam : E, verifyWhir n R (x.ood + lam * x.value)
        (fun pt ↦ eqZ z pt + lam * eqZ x.point pt) =
      verifyWhir (stacking n).logN R
        (dot (powers lam ((stacking n).claims [⟨z, x.ood⟩, ⟨x.point, x.value⟩]).length)
          (((stacking n).claims [⟨z, x.ood⟩, ⟨x.point, x.value⟩]).map (·.2)))
        (fun point ↦ dot (powers lam ((stacking n).claims [⟨z, x.ood⟩, ⟨x.point, x.value⟩]).length)
          (((stacking n).claims [⟨z, x.ood⟩, ⟨x.point, x.value⟩]).map fun c ↦ c.1 point)) :=
    fun lam ↦ by
      simp only [Stacking.claims, stacking, List.map_cons, List.map_nil, List.append_nil,
        List.length_cons, List.length_nil]
      rw [show (0 + 1 + 1 : ℕ) = 2 from rfl, dot_two]
      simp only [dot_two]
  simp only [hv]

/-- **The program past the transcript's start**: the root read as commitment `0`, the check, then
accept. -/
def prog (n R : ℕ) (z : List E) (x : Claim1 n) : Prog Bool := do
  commitStack n R
  check n R z x
  return true

theorem prog_eq {n R : ℕ} (z : Vector E n) (x : Claim1 n) :
    prog n R z.toList x = variantProg (stacking n) R (claimsOf z x) := by
  simp only [prog, variantProg, check_eq z.toList (by simp) x, claimsOf]
  rfl

/-! ## The verifier -/

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **`verify_claim`** (`lib.rs:300-330`) over a hash `H` and a permutation `F`, the out-of-domain
point `zOf root`: a claim outside `15 ≤ n ≤ 28` is rejected first (its point has `n` coordinates by
`Claim1`). -/
def pcsVerifyWithHash {n : ℕ} (zOf : Digest → Vector E n) (x : Claim1 n) (π : Proof) : m Bool :=
  if minVars ≤ n ∧ n ≤ maxVars then do
    let iv ← H (claimBytes x)
    let seed ← F (seedInput iv publicDigest)
    if rootOf π = some x.root then
      runProofWithHash H F (prog n logInvRate (zOf x.root).toList x) seed π
    else pure false
  else pure false

end Run

/-! ## The seedings -/

/-- A claim's seeding: the IV `H(PCS_claim)`, then the permutation of the IV and zero. -/
def seed1 {n : ℕ} (x : Claim1 n) : Seed where
  hs := [fun _ ↦ claimBytes x]
  fin ds := seedInput (ds.getD 0 default) default

variable {n : ℕ}

/-- **The seedings of the claims**, the out-of-domain point `zOf root`: the root history of a claim
is its two claims' reads (`famHistory`). -/
def seeds (zOf : Digest → Vector E n) : Seeds (Claim1 n) where
  seed := seed1
  root x := famHistory (toStmt (zOf x.root) x)
  offs := []
  refs x ds hds i hi := by
    have hl : (seed1 x).hs.length = 1 := rfl
    rw [hl] at hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds]
    rw [hds] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) default) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj H hH x x' ds ds' ha ha' he := by
    have hl : ds.length = 1 := ha.1
    have hl' : ds'.length = 1 := ha'.1
    have hiv : ds.getD 0 default = ds'.getD 0 default := by
      have := congrArg laneDigest he
      simpa [seed1, laneDigest_seedInput] using this
    obtain ⟨f0, hf0, hH0⟩ := ha.2 0 (by omega)
    obtain ⟨f0', hf0', hH0'⟩ := ha'.2 0 (by omega)
    simp only [seed1, List.getElem?_cons_zero, Option.some.injEq] at hf0 hf0'
    subst hf0 hf0'
    have e0 : ds[0] = ds'[0] := by
      simpa [List.getD_eq_getElem?_getD, hl, hl'] using hiv
    rw [e0] at hH0
    exact claimBytes_injective (hH _ _ _ hH0 hH0')

/-! ## The theorem for the proven program -/

section Sound

variable {R : ℕ} (hw : Whir.Admissible n R) (zOf : Digest → Vector E n)

theorem verifierFam_seeds (z : Claim1 n × Proof) :
    verifierFam (seeds zOf) (famProgram (stacking n) R) z =
      verifierComp (seed1 z.1) (variantProg (stacking n) R (claimsOf (zOf z.1.root) z.1)) z.2 := by
  simp only [verifierFam, seeds, nodeAt_famHistory]
  rfl

theorem isTotalQueryBound_seeds (z : Claim1 n × Proof) :
    IsTotalQueryBound (verifierFam (seeds zOf) (famProgram (stacking n) R) z) variantQueries := by
  rw [verifierFam_seeds]
  exact isTotalQueryBound_verifierComp (costLE_variant (stacking n) R _) (seed1 z.1) z.2

/-- **The event**: for the root the proof's first two scalars encode, every candidate of the word
extracted for it violates `f(z) = ood` or `f(point) = value`, `z = zOf root` of the claim's root. -/
def Doomed1 (R : ℕ) (zOf : Digest → Vector E n) (z : Claim1 n × Proof)
    (c : KeccakCalls.QueryCache) : Prop :=
  ∀ r, rootOf z.2 = some r →
    ∀ q ∈ Candidates n R (code₀ n R).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight n R) (2 ^ laneFold)),
      ∃ cl ∈ claimsOf (zOf z.1.root) z.1, ¬ StackClaim.Holds n ((stacking n).weight cl, cl.value) q

include hw in
/-- **Fiat-Shamir soundness of version 1's opening for the proven program**: an adversary of at
most `QA` queries outputs a claim and a proof; the seeded verifier accepts while every candidate of
the word extracted for the proof's root violates one of the opening's two claims with probability
at most `(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`. -/
theorem pcs_family_sound (A : OracleComp KeccakCalls (Claim1 n × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam (seeds zOf) (famProgram (stacking n) R))}[
        z.1.2 = true ∧ Doomed1 R zOf z.1.1 z.2] ≤
      (QA + variantQueries : ℕ) * (εWhir + failBound (seeds zOf) (QA + variantQueries)) := by
  refine romSound_of_imp (famProgram (stacking n) R) (famCert (stacking n) R hw) (seeds zOf)
    (fun x ↦ rootOk_famHistory _) εWhir (famCert_bound (stacking n) R hw) A QA hA variantQueries
    (isTotalQueryBound_seeds zOf) (Doomed1 R zOf) fun z c hv hbad ↦ ?_
  set x := toStmt (zOf z.1.root) z.1 with hx
  have hseed : (seeds zOf).seed z.1 = seed1 z.1 := rfl
  have hroot : (seeds zOf).root z.1 = famHistory x := rfl
  rw [hseed, hroot, nodeAt_famHistory] at hv
  obtain ⟨e, rest, hhist, hce⟩ := extracted_root (L := stacking n) (R := R) (claims := x.claims) hv
  obtain ⟨r, rest', hr, hhist'⟩ := extracted_root_word (L := stacking n) hw hv
  have he : e = Ev.commit (rootHeight n R) (2 ^ laneFold)
      (extract (fun x ↦ c (.inl x)) r (rootHeight n R) (2 ^ laneFold)) :=
    (List.cons.inj (hhist.symm.trans hhist')).1
  have hws := (Sound.after_extractedHistory _ _ hv).2
  rw [hhist] at hws
  unfold Doomed
  rw [hseed, hroot, nodeAt_famHistory]
  refine ⟨famHistory x ++ [e], ?_, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [extractedFrom_eq _ _ _ _ _ _ hv, hhist]
    exact (List.prefix_append_right_inj _).mpr ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    exact boundary_append_of (h := []) trivial
  · refine (famD_iff (stacking n) R hw x [e]).2 (variantCert_D_root (stacking n) R hw x.claims
      x.short hce ⟨shapeOK_root (stacking n) R hw hce fun ht w W he ↦
        hws ht w W (he ▸ List.mem_cons_self ..), fun q hq ↦ ?_⟩)
    have hq' : q ∈ Candidates n R (code₀ n R).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight n R) (2 ^ laneFold)) := by
      rw [he] at hq
      simp [LeanVM.Protocol.Whir.Sound.wordOf, commits] at hq
      exact hq
    obtain ⟨cl, hcl, hn⟩ := hbad r hr q hq'
    exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cl, hcl, rfl⟩), hn⟩

end Sound

end WhirBridge.Pcs
