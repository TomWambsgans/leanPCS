-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statements composed are
-- `formal/RecStatement/RecStatement/Security.lean`'s (branch `lean-rec-statement` @ f0a9e21, with the composition's
-- two fixes, `lean-rec-compose`).
import RecStatement

/-!
# The composition's vocabulary

π2's outcome (`RecStatement.RecOutcome2`), its fields named; `W`'s candidates and a candidate's witness values, as π2's
extractor (`recExtractFrom2`) lists and reads them; `pi1GraphAcceptsB` decides `Pi1GraphAccepts`; the extractor finds
a stream as soon as one candidate's is accepted (`recExtractFrom2_of_mem`).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## π2's outcome -/

section Outcome

variable (z : RecOutcome2)

/-- The public input. -/
abbrev inp : Vector UInt8 32 := z.1.1.1
/-- The proof. -/
abbrev prf : RecProof := z.1.1.2
/-- The contract's verdict. -/
abbrev acc : Bool := z.1.2
/-- The setup's Keccak-256 evaluations. -/
abbrev evs : List (List UInt8 × Digest) := z.2.1
/-- The adversary's transcript. -/
abbrev lg : OracleQueryLog := z.2.2.1
/-- The setup's roots. -/
abbrev rts : RecSetupRoots := z.2.2.2.1
/-- The contract's calls. -/
abbrev cls : List (List (List UInt8)) := z.2.2.2.2

end Outcome

/-- **The setup commitment the Keccak π1-rec3's graph was recorded at** (`RecGraphKeccak.verifierOutputsWithK …
keccak128 referenceRootsK`: the graph's setup claim holds its `F` root and out-of-domain answer as constants, which the
contract replaces by the setup's). The one name every RecCompose file uses for it, so that a change of the reference
commitment is a change here. -/
abbrev keccakRefRoots : UniKeccak.SetupRootsK := RecGraphKeccak.Pi1.referenceRootsK

/-! ## `W`'s candidates -/

/-- `W`'s stack variables at π1's setup commitment (`(stackVars m).1`). -/
abbrev wVars (D : RecDeployment) (roots : RecSetupRoots) : ℕ :=
  (stackVars (D.circuitAt roots.pi1).circuit.logN).1

/-- **`W`'s candidates** on given preimages, as `recExtractFrom2` lists them: the word committed under the root the
stream names after π1's public data, decoded (fast path, unique decoder, list decoder). -/
def wCandidates (D : RecDeployment) (roots : RecSetupRoots) (pre : Digest → ℕ → Option (List UInt8))
    (proof : RecProof) : List (Vector K (2 ^ wVars D roots)) :=
  let c := (D.circuitAt roots.pi1).circuit
  candidates (wVars D roots) (committedWord pre (wVars D roots)
    (streamRoot proof.stream ((rootsAt c.reads).getD (rootReads c.reads) 0)))

/-- **A candidate's witness values** `w(ω_i)` (the stack's leading `N` words read back, `basisValue` in the `B` basis),
as `recExtractFrom2` reads them. -/
def witnessOf (D : RecDeployment) (roots : RecSetupRoots) (w : Vector K (2 ^ wVars D roots)) : ℕ → K :=
  let c := (D.circuitAt roots.pi1).circuit
  let table := Array.ofFn (n := 2 ^ c.logN) fun i ↦ w.toArray.getD i.val 0
  fun i ↦ UniStatement.basisValue table c.logN i

/-- `W`'s candidates of an outcome (on the preimages of its setup's evaluations and transcript). -/
abbrev outcomeCandidates (D : RecDeployment) (z : RecOutcome2) : List (Vector K (2 ^ wVars D (rts z))) :=
  wCandidates D (rts z) (preimagesOf (evs z) (lg z)) (prf z)

theorem recExtractFrom2_eq (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : RecProof) :
    recExtractFrom2 D roots input pre proof =
      match pi1OpsOf D roots input proof.stream with
      | none => none
      | some ops => (wCandidates D roots pre proof).findSome? fun w ↦
          if pi1GraphAcceptsB (D.pi1IvAt roots.pi1) input (D.pi1Stream (witnessOf D roots w)) ops then
            some (D.pi1Stream (witnessOf D roots w)) else none := rfl

/-! ## `Pi1GraphAccepts`, decided -/

theorem pi1GraphAcceptsB_iff (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8)
    (ops : List Pi1Opening) : pi1GraphAcceptsB iv1 input s ops = true ↔ Pi1GraphAccepts iv1 input s ops := by
  unfold pi1GraphAcceptsB Pi1GraphAccepts
  constructor
  · intro h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i out hout
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨hz, hnz⟩, hc⟩ := h
      split at hc
      · exact absurd hc Bool.false_ne_true
      · rename_i gops hg
        simp only [decide_eq_true_eq] at hc
        exact ⟨out, gops, hout, hz, hnz, hg, hc.1, hc.2⟩
  · rintro ⟨out, gops, hout, hz, hnz, hg, h1, h2⟩
    rw [hout]
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    refine ⟨⟨hz, hnz⟩, ?_⟩
    rw [hg]
    simp only [decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- **The extractor finds a stream as soon as one candidate's is accepted**: with the contract's π1 openings `ops`
read off the calldata, a candidate whose π1 stream π1-rec3's graph accepts with them makes the extractor output an
accepted stream (the first such). -/
theorem recExtractFrom2_of_mem (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : RecProof) (ops : List Pi1Opening)
    (hops : pi1OpsOf D roots input proof.stream = some ops) (w : Vector K (2 ^ wVars D roots))
    (hw : w ∈ wCandidates D roots pre proof)
    (hacc : Pi1GraphAccepts (D.pi1IvAt roots.pi1) input (D.pi1Stream (witnessOf D roots w)) ops) :
    ∃ s, recExtractFrom2 D roots input pre proof = some s ∧ Pi1GraphAccepts (D.pi1IvAt roots.pi1) input s ops := by
  rw [recExtractFrom2_eq, hops]
  simp only
  set f : Vector K (2 ^ wVars D roots) → Option (Array UInt8) := fun w ↦
    if pi1GraphAcceptsB (D.pi1IvAt roots.pi1) input (D.pi1Stream (witnessOf D roots w)) ops then
      some (D.pi1Stream (witnessOf D roots w)) else none with hf
  cases h : (wCandidates D roots pre proof).findSome? f with
  | none =>
    have := List.findSome?_eq_none_iff.mp h w hw
    rw [hf] at this
    simp only [(pi1GraphAcceptsB_iff _ _ _ _).mpr hacc, ite_true] at this
    exact absurd this (Option.some_ne_none _)
  | some s =>
    refine ⟨s, rfl, ?_⟩
    obtain ⟨w', -, hw'⟩ := List.exists_of_findSome?_eq_some h
    rw [hf] at hw'
    simp only at hw'
    split at hw'
    · rename_i hb
      cases Option.some.inj hw'
      exact (pi1GraphAcceptsB_iff _ _ _ _).mp hb
    · exact absurd hw' (by simp)

end RecCompose
