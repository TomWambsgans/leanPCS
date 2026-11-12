-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The contract is `formal/RecStatement`'s
-- (`RecStatement/Security.lean`: `contractWith`, `pcsOpenWords`, `contractPi1Openings`, `pi1OpsOf`, the experiment
-- `recSoundnessExperiment2`; `RecStatement/Calls.lean`: `pcsCalls`, `callWord`).
import RecCompose.Pi2Run
import RecCompose.Part1
import RecCompose.Part2

/-!
# The contract's π1 openings are the declared claims: `DeclaredGood`, `DeclaredClaims`

**`declaredGood`**: on every outcome of π2's knowledge-soundness experiment whose contract accepts, the declared π1
claims (`RecProof.pi1Claims`) decode (`claimOfWords`), to the contract's π1 openings (its first three claims);
**`declaredClaims`**: they are three, π1-rec4's graph's claims' count.

* the contract's claims are the declared π1 claims followed by π2's four (`pcsCalls`, its encoded π1 claims dropped:
  `pcsCalls_length`), seven of them, so the declared ones are three;
* the contract accepts only if each of its claims decoded (`pcsOpenWords` answers `false` to a claim that does not:
  `holds_pcsOpenWords`, `holds_forIn_and`), so the first three do;
* the experiment's every outcome is one of these (`contractWith_post`, through the experiment's binds, `simulateQ` and
  the run: `Holds`, `holds_support`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open OracleComp OracleSpec Common

/-! ## The contract's claims -/

theorem pcsCalls_length (c : Circuit) (pi1 : List (List CallWord)) (sr : List UInt8) (so : E)
    (stream : Array UInt8) (r : Reduced) : (pcsCalls c pi1 sr so stream r).length = pi1.length + 4 := by
  simp [pcsCalls]

/-- **`mapM` in `Option` succeeds when each step does.** -/
theorem mapM_option_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    obtain ⟨ys, hys⟩ := mapM_option_some f l fun z hz ↦ h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- The contract's π1 openings exist when its first three calls decode. -/
theorem contractPi1Openings_some (calls : List (List (List UInt8)))
    (h : ∀ words ∈ calls.take 3, (claimOfWords words).isSome) : ∃ ops, contractPi1Openings calls = some ops := by
  unfold contractPi1Openings
  exact mapM_option_some _ _ fun words hw ↦ by simpa using h words hw

/-! ## The contract's loop of openings -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The opening check answers `false` to a claim that does not decode.** -/
theorem holds_pcsOpenWords (F : KeccakState → m KeccakState) (words : List (List UInt8))
    (p : LeanVM.Protocol.Compile.Proof) :
    Holds (pcsOpenWords F words p) fun b ↦ b = true → (claimOfWords words).isSome := by
  unfold pcsOpenWords
  split
  · exact holds_pure fun h ↦ absurd h (by simp)
  · rename_i h
    exact holds_mono (holds_true _) fun _ _ _ ↦ by rw [h]; rfl

/-- **A loop that ands its body's answers** answers `true` only if its start does and every body's answer was `true`
for an element with `G`. -/
theorem holds_forIn_and {γ : Type} (G : γ → Prop) (f : γ → Bool → m (ForInStep Bool))
    (hf : ∀ x b, Holds (f x b) fun st ↦ ∃ c, st = .yield (b && c) ∧ (c = true → G x)) :
    ∀ (l : List γ) (b : Bool), Holds (forIn l b f) fun r ↦ r = true → b = true ∧ ∀ x ∈ l, G x
  | [], b => by
    simp only [List.forIn_nil]
    exact holds_pure fun h ↦ ⟨h, by simp⟩
  | x :: l, b => by
    rw [List.forIn_cons]
    refine holds_bind (hf x b) fun st ⟨c, hst, hc⟩ ↦ ?_
    subst hst
    simp only
    refine holds_mono (holds_forIn_and G f hf l (b && c)) fun r hr h ↦ ?_
    obtain ⟨hbc, hl⟩ := hr h
    simp only [Bool.and_eq_true] at hbc
    refine ⟨hbc.1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hc hbc.2
    · exact hl y hy

/-- **The contract accepts only with three declared π1 claims, its first three claims, which decode, and a stream of
the length π2's run reads** (`pi2Bytes`, `runWith_post`). -/
theorem contractWith_post (F : KeccakState → m KeccakState) (D : RecDeployment) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (proof : RecProof) :
    Holds (D.contractWith F roots input proof) fun x ↦ x.1 = true →
      (proof.pi1Claims.length = 3 ∧ ∃ ops, proof.pi1Claims.mapM claimOfWords = some ops ∧
        contractPi1Openings x.2 = some ops) ∧
      proof.stream.size = pi2Bytes (Spec.of (D.circuitAt roots.pi1).circuit) := by
  unfold RecDeployment.contractWith
  refine holds_bind (holds_true _) fun iv _ ↦ holds_bind (runWith_post F _ _ _ _ _) fun o ho ↦ ?_
  split
  · exact holds_pure fun h ↦ absurd h (by simp)
  · rename_i r hr
    have hsz := (ho.1 r hr).1
    split_ifs with hacc
    · exact holds_pure fun h ↦ absurd h (by simp)
    dsimp only
    split_ifs with hdec hlen
    · exact holds_pure fun h ↦ absurd h (by simp)
    · exact holds_pure fun h ↦ absurd h (by simp)
    · refine holds_bind (holds_forIn_and (fun x ↦ (claimOfWords x.1).isSome) _ (fun x b ↦ ?_) _ true)
        fun ok hok ↦ holds_pure fun h ↦ ?_
      · obtain ⟨words, p⟩ := x
        simp only
        exact holds_bind (holds_pcsOpenWords F words p) fun c hc ↦ holds_pure ⟨c, rfl, hc⟩
      · simp only at h
        obtain ⟨-, hdec'⟩ := hok h
        set enc := pcsCalls (D.circuitAt roots.pi1).circuit (pi1CallsWith D.pi1Calls roots.pi1)
          (digestBytes roots.pi2) roots.pi2Ood proof.stream r with henc
        have hlenE : enc.length = D.pi1Calls.length + 4 := by
          rw [henc, pcsCalls_length]
          simp [pi1CallsWith]
        have hlen' : (proof.pi1Claims ++ enc.drop D.pi1Calls.length).length = 7 := by simpa using hlen
        have h3 : proof.pi1Claims.length = 3 := by
          rw [List.length_append, List.length_drop, hlenE] at hlen'
          omega
        have hopen : proof.openings.length = 7 := rfl
        obtain ⟨ops, hops⟩ := contractPi1Openings_some (proof.pi1Claims ++ enc.drop D.pi1Calls.length)
          fun words hw ↦ by
            have hwc : words ∈ proof.pi1Claims ++ enc.drop D.pi1Calls.length := List.mem_of_mem_take hw
            have hfst : ((proof.pi1Claims ++ enc.drop D.pi1Calls.length).zip proof.openings).map Prod.fst =
                proof.pi1Claims ++ enc.drop D.pi1Calls.length :=
              List.map_fst_zip (by rw [hlen', hopen])
            rw [← hfst] at hwc
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hwc
            exact hdec' x hx
        refine ⟨⟨h3, ops, ?_, hops⟩, hsz⟩
        rw [← hops]
        unfold contractPi1Openings
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

end Generic

/-! ## On the experiment's outcomes -/

/-- The outcomes' fact. -/
theorem outcomes_post (D : RecDeployment) (A : RecAdversary) :
    ∀ z ∈ support (recSoundnessExperiment2 D A), acc z = true →
      ((prf z).pi1Claims.length = 3 ∧ ∃ ops, (prf z).pi1Claims.mapM claimOfWords = some ops ∧
        contractPi1Openings (cls z) = some ops) ∧
      (prf z).stream.size = pi2Bytes (Spec.of (D.circuitAt (rts z).pi1).circuit) := by
  refine holds_support ?_
  unfold recSoundnessExperiment2 runWithRandomPermutation
  refine holds_run' (holds_simulateQ _ ?_) []
  refine holds_bind (holds_true _) fun trees _ ↦ holds_bind (holds_true _) fun zt _ ↦ ?_
  obtain ⟨z, transcript⟩ := zt
  refine holds_bind (contractWith_post queryPermutation D trees.roots z.1 z.2) fun ac hac ↦ ?_
  obtain ⟨accepted, calls⟩ := ac
  exact holds_pure hac

/-- **`DeclaredGood`**: on every accepted outcome, the declared π1 claims decode to the contract's π1 openings. -/
theorem declaredGood (D : RecDeployment) : DeclaredGood D :=
  fun A z hz ha ↦ (outcomes_post D A z hz ha).1.2

/-- **`DeclaredClaims`**: on every accepted outcome, the proof declares three π1 claims, π1-rec4's graph's count. -/
theorem declaredClaims (D : RecDeployment) : DeclaredClaims D := by
  intro A z hz ha
  exact ⟨(outcomes_post D A z hz ha).1.1, (outcomes_post D A z hz ha).2⟩

end RecCompose

/-- info: 'RecCompose.declaredGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.declaredGood

/-- info: 'RecCompose.declaredClaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.declaredClaims
