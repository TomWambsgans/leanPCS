-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `formal/RecStatement` (`Verifier.lean`:
-- `ivWith`, `reduceWith`, `runWith`; `Security.lean`: `Pi2Circuit.digestWith`, `Pi2Circuit.setupTreeWith`,
-- `RecDeployment.ivWith`, `pcsOpenWords`, `RecDeployment.contractWith`, `RecDeployment.verifierWith`,
-- `RecDeployment.setupTreesWith`, `pi1GraphVerifierWith`) and `RecCompose.Couplings` (`openAt`, `openSeq`), with
-- Keccak-256 an explicit call, as `formal/UniComplete/UniComplete/VerifierH.lean` rewrites `formal/UniStatement`.
import RecCompose.Pi2Run
import RecCompose.Couplings
import UniKeccakComplete.K.VerifierH

/-!
# π2's verifier, contract and setup with Keccak-256 an explicit call

`formal/RecStatement`'s contract and setup are written over a permutation `F`, every Keccak-256 the sponge over it
(`keccak256With F`). Here each function that hashes is rewritten with Keccak-256 a separate function `H` (`…H`), the
code text the Statement's, only the hash changed (UniComplete's `sampleH`, UniKeccakComplete's `pcsOpenKH`,
`pcsOpenKOH` for `RecStatement.pcsOpenKO`; WithHash's `commitWithH`). **At `H = keccak256With F`** each is the Statement's (`…_eqH`). And
`runWithH_post`: `Pi2Run.runWith_post` at any `H` (the run's success and public data do not depend on the hashes).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2H

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniStatement (Chan ChanM)

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- `RecStatement.ivWith` with Keccak-256 `H`. -/
def ivWithH (pi1Iv setupRoot : List UInt8) (setupOod : E) (digest : List UInt8) (logN : ℕ) : m (List UInt8) := do
  let d ← H (ivTag ++ pi1Iv ++ setupRoot ++ UniKeccak.elementBytes24 setupOod ++ digest ++ [logN.toUInt8])
  return digestBytes d

/-- `RecStatement.reduceWith` with Keccak-256 `H`. -/
def reduceWithH (s : Spec) (statement : List E) (frameAt : ℕ → List UInt8) : ChanM m Reduced := do
  let mut pubs := statement
  for rd in s.reads do
    match rd with
    | .integer b => pubs := pubs ++ [UniStatement.eK (UInt64.ofNat (← UniStatement.nextInteger (m := m) b))]
    | .root =>
      let (lo, hi) ← UniStatement.nextRoot (m := m)
      pubs := pubs ++ [lo, hi]
    | .scalar => pubs := pubs ++ [← UniStatement.nextScalar (m := m)]
    | .narrow => pubs := pubs ++ [← nextNarrow (m := m)]
    | .frame p => pubs := pubs ++ UniStatement.publicWordsOf (frameAt p)
  let wRoot ← UniStatement.nextRoot (m := m)
  let wOod ← UniStatement.nextScalar (m := m)
  let α ← UniKeccakComplete.sampleH H
  let β ← UniKeccakComplete.sampleH H
  let γ ← UniKeccakComplete.sampleH H
  let qRoot ← UniStatement.nextRoot (m := m)
  let qOod ← UniStatement.nextScalar (m := m)
  let t ← UniKeccakComplete.sampleH H
  let a ← UniStatement.nextScalars (m := m) (2 ^ s.logRow)
  let ξ ← UniStatement.nextScalar (m := m)
  let sv ← UniStatement.nextScalar (m := m)
  let ρ ← UniKeccakComplete.sampleH H
  let inp : Inputs E := ⟨pubs, α, β, γ, t, a, ξ, sv, ρ⟩
  return ⟨pubs, pubs.map pairPoint, (wRoot, qRoot), (wOod, qOod), inp, s.core.run inp⟩

/-- `RecStatement.runWith` with Keccak-256 `H`. -/
def runWithH (s : Spec) (iv publicInput : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8) :
    m Outcome := do
  let seed ← H (name ++ iv ++ publicInput ++ (frameReads s.reads).flatMap frameAt)
  let walk : ChanM m Reduced := do
    let r ← reduceWithH H s (UniStatement.publicWordsOf publicInput) frameAt
    UniStatement.finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- `Pi2Circuit.digestWith` with Keccak-256 `H`. -/
def digestWithH (c : Pi2Circuit) : m (List UInt8) := do
  let sigma ← H ((List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4)
  let kappa ← H ((List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat)
  let d ← H (c.circuit.encoding ++ digestBytes sigma ++ digestBytes kappa)
  return digestBytes d

/-- `RecDeployment.ivWith` with Keccak-256 `H`. -/
def ivOfH (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let c := D.circuitAt roots.pi1
  let digest ← digestWithH H c
  ivWithH H (D.pi1IvAt roots.pi1) (digestBytes roots.pi2) roots.pi2Ood digest c.circuit.logN

/-- `RecStatement.pcsOpenKO` with Keccak-256 `H`: the out-of-domain point read off `H`
(`WhirBridge.Pcs.pcsVerifyWithHashO`). -/
def pcsOpenKOH (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) : m Bool :=
  if h : pt.length = n then WhirBridge.Pcs.pcsVerifyWithHashO H F ⟨root, ood, pt, v, h⟩ p else pure false

/-- `pcsOpenWords` with Keccak-256 `H`: `W`'s and `Q`'s sizes (`oodRead`) by `pcsOpenKOH`, the others by
`pcsOpenKH`. -/
def pcsOpenWordsH (words : List (List UInt8)) (proof : Compile.Proof) : m Bool :=
  match claimOfWords words with
  | none => pure false
  | some (root, ood, point, value) =>
    if oodRead point.length then pcsOpenKOH H F point.length root ood point value proof
    else UniKeccakComplete.pcsOpenKH H F point.length root ood point value proof

/-- `RecDeployment.contractWith` with Keccak-256 `H`. -/
def contractWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let iv ← ivOfH H D roots
  let o ← runWithH H (Spec.of c.circuit) iv input.toList (frameOf proof.pi1Claims) proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let enc := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood
      proof.stream r
    if !encodedDeclared c.circuit (enc.take D.pi1Calls.length) proof.pi1Claims then return (false, []) else
    let calls := proof.pi1Claims ++ enc.drop D.pi1Calls.length
    if calls.length ≠ 7 then return (false, calls) else
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenWordsH H F words p)
    return (ok, calls)

/-- `RecDeployment.verifierWith` with Keccak-256 `H`. -/
def verifierWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) : m Bool := do
  return (← contractWithH H F D roots input proof).1

/-- `Pi2Circuit.setupTreeWith` with Keccak-256 `H`. -/
def setupTreeWithH (c : Pi2Circuit) : m LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH H (stackVars c.circuit.logN).2.2 c.setupStack

/-- `UniKeccak.setupTreeKWith` with Keccak-256 `H`: the commitment of the Keccak setup stack. -/
def setupTreeKWithH (D : UniKeccak.KDeployment) : m LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH H (UniStatement.setupLayout D.shape).vars (UniKeccak.setupStackK D.prog D.shape)

/-- `RecDeployment.setupTreesWith` with Keccak-256 `H` (`F` unused: the setup only hashes). -/
def setupTreesWithH (_F : KeccakState → m KeccakState) (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← setupTreeKWithH H D.pi1
  let r1 := D.pi1.setupRoots t1
  let t2 ← setupTreeWithH H (D.circuitAt r1)
  return ⟨t1, t2, r1.fOod, (D.circuitAt r1).setupOod t2.root⟩

/-- `pi1GraphVerifierWith` with Keccak-256 `H`. -/
def pi1GraphVerifierWithH (D : RecDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) : m Bool := do
  match RecGraph.evalGraphDeployed (pi1GraphAt roots) (D.pi1IvAt roots) input.toList proof.stream with
  | none => return false
  | some out =>
    if !(out.zeros.all (· == 0) && out.nonzeros.all (· != 0)) then return false
    match out.calls.mapM decodePi1Call with
    | none => return false
    | some ops =>
      if ops.length ≠ 3 then return false
      let mut ok := true
      for ((o, c), p) in (ops.zip UniStatement.commitments).zip [proof.c1, proof.c2, proof.setup] do
        ok := ok && (← UniKeccakComplete.pcsOpenKH H F (UniKeccak.stackVarsK D.pi1.shape c) o.1 o.2.1 o.2.2.1
          o.2.2.2 p)
      return ok

/-- `Couplings.openAt` with Keccak-256 `H`. -/
def openAtH (o : Pi1Opening) (p : Compile.Proof) : m Bool :=
  if oodRead o.2.2.1.length then pcsOpenKOH H F o.2.2.1.length o.1 o.2.1 o.2.2.1 o.2.2.2 p
  else UniKeccakComplete.pcsOpenKH H F o.2.2.1.length o.1 o.2.1 o.2.2.1 o.2.2.2 p

/-- `Couplings.openSeq` with Keccak-256 `H`. -/
def openSeqH (ops : List Pi1Opening) (proof : RecProof) : m Bool := do
  let b1 ← openAtH H F (ops.getD 0 default) proof.c1
  let b2 ← openAtH H F (ops.getD 1 default) proof.c2
  let b3 ← openAtH H F (ops.getD 2 default) proof.f
  return b1 && b2 && b3

end With

/-! ## At `H = keccak256With F`: the Statement's -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem ivWith_eqH (pi1Iv setupRoot : List UInt8) (setupOod : E) (digest : List UInt8) (logN : ℕ) :
    RecStatement.ivWith F pi1Iv setupRoot setupOod digest logN =
      ivWithH (keccak256With F) pi1Iv setupRoot setupOod digest logN := rfl

theorem reduceWith_eqH (s : Spec) (statement : List E) (frameAt : ℕ → List UInt8) :
    reduceWith F s statement frameAt = reduceWithH (keccak256With F) s statement frameAt := rfl

theorem runWith_eqH (s : Spec) (iv publicInput : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8) :
    runWith F s iv publicInput frameAt stream = runWithH (keccak256With F) s iv publicInput frameAt stream := rfl

theorem digestWith_eqH (c : Pi2Circuit) : c.digestWith F = digestWithH (keccak256With F) c := rfl

theorem ivWith_deploy_eqH (D : RecDeployment) (roots : RecSetupRoots) :
    D.ivWith F roots = ivOfH (keccak256With F) D roots := rfl

theorem pcsOpenKO_eqH (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    pcsOpenKO F n root ood pt v p = pcsOpenKOH (keccak256With F) F n root ood pt v p := rfl

theorem pcsOpenWords_eqH (words : List (List UInt8)) (proof : Compile.Proof) :
    pcsOpenWords F words proof = pcsOpenWordsH (keccak256With F) F words proof := rfl

theorem contractWith_eqH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.contractWith F roots input proof = contractWithH (keccak256With F) F D roots input proof := rfl

theorem verifierWith_eqH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.verifierWith F roots input proof = verifierWithH (keccak256With F) F D roots input proof := by
  unfold RecDeployment.verifierWith verifierWithH
  rw [contractWith_eqH]

theorem setupTreeWith_eqH (c : Pi2Circuit) : c.setupTreeWith F = setupTreeWithH (keccak256With F) c := by
  unfold Pi2Circuit.setupTreeWith setupTreeWithH
  exact E2ECompleteness.commitWith_eqH F _ _

theorem setupTreeKWith_eqH (D : UniKeccak.KDeployment) :
    UniKeccak.setupTreeKWith F D = setupTreeKWithH (keccak256With F) D := by
  unfold UniKeccak.setupTreeKWith setupTreeKWithH
  exact E2ECompleteness.commitWith_eqH F _ _

theorem setupTreesWith_eqH (D : RecDeployment) :
    D.setupTreesWith F = setupTreesWithH (keccak256With F) F D := by
  unfold RecDeployment.setupTreesWith setupTreesWithH
  simp only [setupTreeKWith_eqH, setupTreeWith_eqH]

theorem pi1GraphVerifierWith_eqH (D : RecDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) :
    pi1GraphVerifierWith F D roots input proof = pi1GraphVerifierWithH (keccak256With F) F D roots input proof := rfl

theorem openAt_eqH (o : Pi1Opening) (p : Compile.Proof) : openAt F o p = openAtH (keccak256With F) F o p := rfl

theorem openSeq_eqH (ops : List Pi1Opening) (proof : RecProof) :
    openSeq F ops proof = openSeqH (keccak256With F) F ops proof := rfl

end Eq

/-- `Couplings.pcsOpenWords` at decoded words, with Keccak-256 `H`: the claim's opening. -/
theorem pcsOpenWordsH_eq {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)
    (w : List (List UInt8)) (p : Compile.Proof) (x : Digest × E × List E × E) (h : claimOfWords w = some x) :
    pcsOpenWordsH H F w p = openAtH H F x p := by
  unfold pcsOpenWordsH openAtH
  rw [h]

/-- **An opening not at `W`'s or `Q`'s sizes** is the fixed-point check `pcsOpenKH`. -/
theorem openAtH_of_not {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)
    (o : Pi1Opening) (p : Compile.Proof) (h : oodRead o.2.2.1.length = false) :
    openAtH H F o p = UniKeccakComplete.pcsOpenKH H F o.2.2.1.length o.1 o.2.1 o.2.2.1 o.2.2.2 p := by
  unfold openAtH
  rw [h]
  rfl

/-- **An opening at `W`'s or `Q`'s sizes** is the oracle-point check `pcsOpenKOH`. -/
theorem openAtH_of {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)
    (o : Pi1Opening) (p : Compile.Proof) (h : oodRead o.2.2.1.length = true) :
    openAtH H F o p = pcsOpenKOH H F o.2.2.1.length o.1 o.2.1 o.2.2.1 o.2.2.2 p := by
  unfold openAtH
  rw [h]
  rfl

/-- **The oracle-point check at a pure Keccak-256 `Hk`** is the check at the point `oodPointWith Hk n`. -/
theorem pcsOpenKOH_id (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (n : ℕ) (root : Digest)
    (ood : E) (pt : List E) (v : E) (p : Compile.Proof) (hpt : pt.length = n) :
    pcsOpenKOH (m := Id) (Pure.pure ∘ Hk) F n root ood pt v p =
      WhirBridge.Pcs.pcsVerifyWithHash (m := Id) (Pure.pure ∘ Hk) F (WhirBridge.Pcs.oodPointWith Hk n)
        ⟨root, ood, pt, v, hpt⟩ p := by
  unfold pcsOpenKOH
  simp only [hpt, ↓reduceDIte]
  exact WhirBridge.Pcs.UnionO.pcsVerifyWithHashO_pure (m := Id) Hk F _ p

/-! ## The run's public data, at any `H` -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem sampleH_run (H : List UInt8 → m Digest) (c : Chan) :
    ((UniKeccakComplete.sampleH H).run).run c =
      (fun st ↦ (.ok (PcsQuotient.Transcript.challengeOf st), sampled c st)) <$>
        H (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold UniKeccakComplete.sampleH sampled
  simp [Except.map]

theorem reads_sampleH (H : List UInt8 → m Digest) : Reads (UniKeccakComplete.sampleH H) 0 fun _ _ _ ↦ True := by
  intro c
  rw [sampleH_run]
  exact holds_map (holds_true _) fun st _ ↦ ⟨rfl, fun a _ ↦ ⟨rfl, trivial⟩, fun _ ↦ ⟨_, rfl⟩⟩

theorem reads_reduceWithH (H : List UInt8 → m Digest) (s : RecStatement.Spec) (stmt : List E)
    (frameAt : ℕ → List UInt8) :
    Reads (reduceWithH H s stmt frameAt) (pi2Bytes s) fun d cur r ↦
      r.scalars = foldReads RecStatement.Read.bytes (pubsStep frameAt) d cur s.reads stmt ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint := by
  unfold reduceWithH
  refine reads_mono (reads_bind (reads_forIn RecStatement.Read.bytes (pubsStep frameAt) _ (fun rd b ↦ ?_) s.reads stmt)
    fun pubs _ ↦
      reads_bind reads_nextRoot fun wRoot _ ↦
      reads_bind reads_nextScalar fun wOod _ ↦
      reads_bind (reads_sampleH H) fun α _ ↦
      reads_bind (reads_sampleH H) fun β _ ↦
      reads_bind (reads_sampleH H) fun γ _ ↦
      reads_bind reads_nextRoot fun qRoot _ ↦
      reads_bind reads_nextScalar fun qOod _ ↦
      reads_bind (reads_sampleH H) fun t _ ↦
      reads_bind (reads_nextScalars _) fun a _ ↦
      reads_bind reads_nextScalar fun ξ _ ↦
      reads_bind reads_nextScalar fun sv _ ↦
      reads_bind (reads_sampleH H) fun ρ _ ↦ reads_pure _) (by unfold pi2Bytes; omega) ?_
  · cases rd with
    | integer bytes =>
      refine reads_mono (reads_bind (reads_nextInteger bytes) fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | root =>
      refine reads_mono (reads_bind reads_nextRoot fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | scalar =>
      refine reads_mono (reads_bind reads_nextScalar fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | narrow =>
      refine reads_mono (reads_bind reads_nextNarrow fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | frame p =>
      refine reads_mono (reads_pure _) rfl ?_
      rintro d cur st hst
      subst hst
      rfl
  · rintro d cur r ⟨pubs, hpubs, w, -, wo, -, α, -, β, -, γ, -, q, -, qo, -, t, -, a, -, ξ, -, sv, -, ρ, -, hr⟩
    subst hr
    exact ⟨hpubs, rfl⟩

/-- **`runWith_post` at any `H`.** -/
theorem runWithH_post (H : List UInt8 → m Digest) (s : RecStatement.Spec) (iv input : List UInt8)
    (frameAt : ℕ → List UInt8) (stream : Array UInt8) :
    Holds (runWithH H s iv input frameAt stream) fun o ↦
      (∀ r, o.result = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input frameAt stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, o.result = .ok r) := by
  unfold runWithH
  refine holds_bind (holds_true _) fun seed _ ↦ holds_bind (Q := fun p ↦
    (∀ r, p.1 = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input frameAt stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, p.1 = .ok r)) ?_ fun p hp ↦ ?_
  · rw [ExceptT.run_bind, StateT.run_bind]
    refine holds_bind (reads_reduceWithH H s (UniStatement.publicWordsOf input) frameAt (Chan.start seed stream)) ?_
    rintro ⟨e, c'⟩ ⟨hd, hok, hfit⟩
    simp only [Chan.start] at hd hok hfit
    cases e with
    | error err =>
      simp only [StateT.run_pure]
      refine holds_pure ⟨fun r hr ↦ absurd hr (by simp), fun hsz ↦ ?_⟩
      obtain ⟨a, ha⟩ := hfit (by omega)
      exact absurd ha (by simp)
    | ok r =>
      simp only
      obtain ⟨hcur, hsc, hpp⟩ := hok r rfl
      rw [ExceptT.run_bind, StateT.run_bind, finish_run]
      simp only [pure_bind]
      split_ifs with hf
      · simp only
        refine holds_pure ⟨fun r' hr' ↦ ?_, fun _ ↦ ⟨r, rfl⟩⟩
        simp only [Except.ok.injEq] at hr'
        subst hr'
        refine ⟨by rw [← hd, ← hf, hcur]; omega, hsc, hpp⟩
      · simp only [StateT.run_pure]
        refine holds_pure ⟨fun r' hr' ↦ absurd hr' (by simp), fun hsz ↦ absurd ?_ hf⟩
        rw [hcur, hd, hsz]; omega
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

end Generic

end RecCompose.Pi2H

/-- info: 'RecCompose.Pi2H.contractWith_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2H.contractWith_eqH

/-- info: 'RecCompose.Pi2H.runWithH_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2H.runWithH_post
