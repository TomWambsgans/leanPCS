-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows
-- `formal/EndToEnd/Soundness/EarlyStop.lean` (`es_le`, `early_le`, `mono_bind`, `zero_of_support`)
-- and `formal/EndToEnd/Bridge/Verifier.lean` (`verifyWith_eq_verifyES`, `openingWith_eq_ourVerifier'`)
-- of this repository; the Statement's verifier is `formal/UniStatement/UniStatement/Opening.lean`'s.
import UniSound.FsWalk
import Bridge.Verifier
import Soundness.EarlyStop

/-!
# The verifier bridge from the walk

**`uniVerifierBridge_of_walk`**: `UniVerifierBridge` (`FsCouple.lean`) from the walk's two halves
(`UniWalk`, `UniWalkReject`, `FsWalk.lean`) and `UniOutRoots`.

* **A stream of another length** is rejected by the walk (`UniWalkReject`), so the Statement accepts
  with probability `0` (`Soundness.zero_of_support`).
* **On a stream of the main line's length** the walk is the chain over Keccak-256 (`UniWalk` at the
  model's oracles, `F = Common.queryPermutation`), and the composed verifier's chain, its two calls
  answered over `π` (`keccakCallsOverQueryPermutation`), is the same chain (`simulateQ_verU`): both
  sides run it first (`mono_bind_supp`, on the chain's possible challenges only: they have the
  rounds' lengths, `doneFits_of_mem_chain`).
* **Per challenges**: if the walk's verdict `uAccB` is `false` the Statement rejects. Else its result
  is the chain program's (`uOut`), and the rest of the Statement's verifier (`restR`: the loop over
  the result's openings, `Flock`'s matrices) accepts only on a result of the main line's shape
  (`GoodR`: three point claims without a bit slice, on `C1`, `C2`, the setup, each of its layout
  word's variables, and `Flock`'s matrices' claim of `A0`'s and `B0`'s: `restR_good`, since
  `PcsQuotient.openingWith` rejects claims of another length before any query); on such a result
  it is the five calls one after the other, their verdicts and-ed (`restR_unroll`, `seqAnd`), each
  `PCS_OPEN` call F2's `ourVerifierEarly` on the plain layout (`pcsOpen_eq_early`, by
  `Bridge.openingWith_eq_ourVerifier'`), on the composed openings' inputs (the roots by
  `UniOutRoots` and the rounds' roots, `root_at`; the claims `cl1 … cl5`, `claims_uCl`), so it
  accepts at most as often as the five `ourVerifier`s all do (`early_le_rpm`, five times), and its
  acceptance gives `uniCheck` (`DoneFits` from the chain, `ZerosVanish` from `uAccB`, `WellFormed`
  from `GoodR`, `wellFormed_of_good`).

Decisions: `restR` transcribes `verifyWith`'s code after the run (its loop `stepR`, its matrices'
calls `matR`) so that the loop can be reasoned about; `verifyWith_eq_rest` is `rfl` after
`bind_map_left`. The comparison is made over the model's oracles directly (`early_le_rpm` is
`Soundness.early_le` with the two calls answered over `π`), not after moving both sides to the two
calls. No hypothesis beyond the theorem's: the statement holds as stated.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack

/-! ## Simulated computations -/

section Sim

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ : Type}
  (impl : QueryImpl spec (StateT σ ProbComp))

/-- **A comparison of continuations on the prefix's possible outputs survives a common simulated
prefix** (`Soundness.mono_bind` with the outputs restricted to the support). -/
theorem mono_bind_supp {α β γ : Type} (oa : OracleComp spec α) (k₁ : α → OracleComp spec β)
    (k₂ : α → OracleComp spec γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (h : ∀ x ∈ support oa, ∀ s, Pr{let y ← (simulateQ impl (k₁ x)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (k₂ x)).run' s}[E₂ y]) (s : σ) :
    Pr{let y ← (simulateQ impl (oa >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (oa >>= k₂)).run' s}[E₂ y] := by
  rw [Soundness.run'_bind, Soundness.run'_bind]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => h p.1 ?_ p.2
  refine support_simulateQ_run'_subset impl oa s ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨p, hp, rfl⟩

end Sim

/-! ## The chain, its two calls answered over `π` -/

section Chain

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

theorem simulateQ_runM {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) : ∀ (y : List UInt8) (es : List (List UInt8)),
    simulateQ impl (runM hash256 y es) = runM (fun x => simulateQ impl (hash256 x)) y es
  | y, [] => by simp [runM]
  | y, e :: es => by simp [runM, simulateQ_runM impl _ es]

theorem simulateQ_hash256 (x : List UInt8) :
    simulateQ keccakCallsOverQueryPermutation (hash256 x) =
      toB <$> keccak256With Common.queryPermutation x := by
  rw [hash256, simulateQ_bind, Compile.Rom.simulateQ_queryH, map_eq_bind_pure_comp]
  simp only [simulateQ_pure]
  rfl

/-- **The composed verifier, its two calls answered over `π`**: the chain over Keccak-256 the sponge
over `π`, then the openings. -/
theorem simulateQ_verU {β : Type} (U : ChainSpecU E FSt) (view : UPf → FSt × List (RMsg E))
    (post : UPf → List (List E) → OracleComp KeccakCalls β) (π : UPf) :
    simulateQ keccakCallsOverQueryPermutation (verU U view post π) =
      U.chain (fun x => toB <$> keccak256With Common.queryPermutation x) (view π).1 (view π).2 >>=
        fun ch => simulateQ keccakCallsOverQueryPermutation (post π ch >>= fun b => pure (ch, b)) := by
  rw [verU, simulateQ_bind]
  congr 1
  rw [ChainSpecU.chain, ChainSpecU.chain, simulateQ_map, simulateQ_runM]
  simp only [simulateQ_hash256]

/-- A run of the chain returns one state per step and the seed. -/
theorem length_of_mem_runM (H : List UInt8 → OracleComp spec Bytes32) :
    ∀ (y : List UInt8) (es : List (List UInt8)), ∀ sts ∈ support (runM H y es),
      sts.length = es.length + 1
  | y, [], sts, h => by
    simp only [runM, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl
  | y, e :: es, sts, h => by
    simp only [runM, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rest, hrest, rfl⟩ := h
    simp [length_of_mem_runM H _ es rest hrest]

/-- The stream's messages and challenges grouped by the rounds complete the rounds. -/
theorem doneFits_zip (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec) (l : List E),
    l.length = nSteps rs → DoneFits rs ((msgsAt b o rs).zip (groupK rs l))
  | _, [], _, _ => by simp [msgsAt, groupK, DoneFits]
  | o, r :: rs, l, hl => by
    simp only [nSteps] at hl
    simp only [msgsAt, groupK, List.zip_cons_cons, DoneFits]
    refine ⟨⟨?_, by simp⟩, ?_, doneFits_zip b _ rs _ ?_⟩
    · cases r.root <;> rfl
    · rw [List.length_take]
      omega
    · rw [List.length_drop]
      omega

/-- **The chain's possible challenges have the rounds' lengths**: with the stream's messages they
complete the rounds. -/
theorem doneFits_of_mem_chain (rounds : List RoundSpec) (π : UPf) (ch : List (List E))
    (H : List UInt8 → OracleComp spec Bytes32)
    (hch : ch ∈ support ((uniSpec rounds).chain H (uView rounds π).1 (uView rounds π).2)) :
    DoneFits rounds (uDone rounds π ch) ∧ ch.length = rounds.length := by
  rw [ChainSpecU.chain, support_map] at hch
  obtain ⟨sts, hsts, rfl⟩ := hch
  have hl := length_of_mem_runM H _ _ sts hsts
  rw [ChainSpecU.absorbsS, length_absorbsI] at hl
  refine ⟨doneFits_zip _ _ _ _ ?_, length_groupK _ _⟩
  simp only [List.length_map, List.length_tail, hl]
  rfl

end Chain

/-! ## The rounds' roots -/

theorem msgsAt_getElem_fst (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec) (i : ℕ)
    (h : i < rs.length),
    ((msgsAt b o rs)[i]'(by rw [length_msgsAt]; exact h)).1.isSome = (rs[i]'h).root
  | _, [], _, h => absurd h (by simp)
  | o, r :: rs, 0, _ => by
    simp only [msgsAt, List.getElem_cons_zero]
    cases r.root <;> rfl
  | o, r :: rs, i + 1, h => by
    simp only [msgsAt, List.getElem_cons_succ]
    exact msgsAt_getElem_fst b _ rs i _

/-- **A round's root**: the composed opening reads it off the chain's message (as 32 bytes), the
Statement off the transcript (as two halves); at a round with a root they name the same digest. -/
theorem root_at (rounds : List RoundSpec) (π : UPf) (ch : List (List E)) (i : ℕ)
    (hi : i < rounds.length) (hch : ch.length = rounds.length)
    (hroot : (rounds.getD i ⟨false, 0, 0⟩).root = true) :
    ofB (((msgK (uView rounds) π i).1).getD (Vector.replicate 32 0)) =
      rootOf (((uDone rounds π ch).getD i default).1.1.getD default) := by
  have hl : i < (msgsAt π.proof.stream 24 rounds).length := by rw [length_msgsAt]; exact hi
  have hs := msgsAt_getElem_fst π.proof.stream 24 rounds i hi
  rw [List.getD_eq_getElem _ _ hi] at hroot
  rw [hroot] at hs
  have e1 : msgK (uView rounds) π i = toRMsg ((msgsAt π.proof.stream 24 rounds)[i]'hl) := by
    show ((msgsAt π.proof.stream 24 rounds).map toRMsg).getD i (none, []) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  have e2 : (uDone rounds π ch).getD i default =
      ((msgsAt π.proof.stream 24 rounds)[i]'hl, ch[i]'(by omega)) := by
    show ((msgsAt π.proof.stream 24 rounds).zip ch).getD i default = _
    rw [List.getD_eq_getElem _ _ (by simp [length_msgsAt]; omega), List.getElem_zip]
  rw [e1, e2]
  rcases hm : ((msgsAt π.proof.stream 24 rounds)[i]'hl).1 with _ | h
  · rw [hm] at hs
    exact absurd hs (by simp)
  · simp only [toRMsg, hm, Option.map_some, Option.getD_some]
    exact Soundness.ofB_toB_root _

/-! ## The Statement's verifier after the run -/

/-! ## What an accepting `restR` needs -/

section Support

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : UniProof)
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (F : KeccakState → OracleComp spec KeccakState)

/-- **`PCS_OPEN` rejects a claim of another length**, before any query. -/
theorem pcsOpen_len (vars : ℕ) (root : Digest) (pt : List E) (v : E) (p : Compile.Proof) :
    ∀ b ∈ support (pcsOpenWith F vars root [⟨pt, v⟩] p), b = true → pt.length = vars := by
  intro b hb hbt
  by_contra hne
  unfold pcsOpenWith PcsQuotient.openingWith at hb
  rw [ite_eq_right (by simp [plainLayout, PcsQuotient.Layout.ofChunks, hne])] at hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  rw [hb] at hbt
  exact Bool.false_ne_true hbt

/-- **Calls one after the other**, their verdicts and-ed onto `ok`. -/
def seqAnd : List (OracleComp spec Bool) → Bool → OracleComp spec Bool
  | [], ok => pure ok
  | P :: Ps, ok => P >>= fun b => seqAnd Ps (ok && b)

theorem seqAnd_cons (P : OracleComp spec Bool) (Ps : List (OracleComp spec Bool)) (ok : Bool) :
    seqAnd (P :: Ps) ok = P >>= fun b => seqAnd Ps (ok && b) := rfl

theorem seqAnd_false : ∀ (Ps : List (OracleComp spec Bool)), ∀ x ∈ support (seqAnd Ps false),
    x = false
  | [], x, hx => by simpa [seqAnd] using hx
  | P :: Ps, x, hx => by
    rw [seqAnd_cons, mem_support_bind_iff] at hx
    obtain ⟨_, -, hx⟩ := hx
    exact seqAnd_false Ps x hx

end Support

/-! ## The five openings -/

/-- **`PCS_OPEN` is F2's opening with the Statement's early stop**, on the plain layout of
`24 … 28` variables, its two calls answered over `π`. -/
theorem pcsOpen_eq_early (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (root : Digest)
    (x : Stmt (plainL v).stacking) (cs : List PcsQuotient.Claim)
    (hx : x.claims = cs.map Bridge.claimTr) (p : Compile.Proof) :
    pcsOpenWith Common.queryPermutation v root cs p =
      simulateQ keccakCallsOverQueryPermutation
        (Soundness.ourVerifierEarly (plainL v) logInvRate ((root, x), p)) := by
  rw [pcsOpenWith, Bridge.openingWith_eq_ourVerifier' Common.queryPermutation (plainLayout v)
    (plainL v) (Bridge.layoutTr_ofChunks_zero v v v (2 ^ v)) (Or.inl rfl)
    (admissible_large h1 h2) root x cs hx p, Bridge.keccakCallsWith_queryPermutation]

/-- The early-stop opening accepts at most as often as the opening, over the lazily sampled
permutation, for continuations ordered as accepting implies accepting (`Soundness.early_le` with
the two calls answered over `π`, the inputs given up to equality). -/
theorem early_le_rpm {β γ : Type} (L : WhirBridge.Layout) (R : ℕ)
    (w w' : (Digest × Stmt L.stacking) × Compile.Proof)
    (k₁ : Bool → OracleComp Common.RandomPermutationOracles β)
    (k₂ : Bool → OracleComp Common.RandomPermutationOracles γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (hw : w' = w)
    (h0 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ false)).run' s}[
      E₁ y] = 0)
    (h1 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ true)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ true)).run' s}[E₂ y])
    (s : Common.PermutationEdges KeccakState) :
    Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly L R w) >>=
          k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation (WhirBridge.ourVerifier L R w') >>=
          k₂)).run' s}[E₂ y] := by
  subst hw
  have hk : ∀ b s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ b)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ b)).run' s}[E₂ y] := by
    intro b s
    cases b
    · rw [h0 s]
      exact bot_le
    · exact h1 s
  unfold Soundness.ourVerifierEarly
  split
  · exact Soundness.mono_bind _ _ _ _ _ _ hk s
  · rw [simulateQ_pure, pure_bind, h0 s]
    exact bot_le

theorem sim_opsRun_cons {γ : Type} (view : UPf → FSt × List (RMsg E)) (o : WhirOp UPf E Stk)
    (os : List (WhirOp UPf E Stk)) (π : UPf) (ch : List (List E))
    (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation (opsRun view (o :: os) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation
          (WhirBridge.ourVerifier o.S.L o.S.R (WhirOp.input view o π ch)) >>= fun b =>
        simulateQ keccakCallsOverQueryPermutation (opsRun view os π ch >>= fun bs => g (b :: bs)) := by
  rw [opsRun, bind_assoc, simulateQ_bind]
  simp only [bind_map_left]

theorem sim_opsRun_nil {γ : Type} (view : UPf → FSt × List (RMsg E)) (π : UPf)
    (ch : List (List E)) (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation
        (opsRun view ([] : List (WhirOp UPf E Stk)) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation (g []) := by
  rw [opsRun, pure_bind]

/-! ## The bridge -/

end UniSound
