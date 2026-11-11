-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/UniKeccakComplete/UniKeccakComplete/K/
-- PcsProver.lean` (`pcsProveH` and its lemmas) with the out-of-domain point a parameter, as `crates/pcs_claim`'s
-- `prove_claim` takes it from `commit_words` (`ood_point(n, root)` over Keccak-256); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `runProof_prove`,
-- `prove_ne_none`, `findNonce_eq_none_iff`, `runI_openingProgram`, `runFrom_corr`, `runFrom_eq_proveFromM`,
-- `proveM_id`, `implH`, `simulateQ_queryH`.
import UniKeccakComplete.K.PcsProver
import WhirBridge.PcsUnionOracle

/-!
# The honest opening of a PCS claim at a given out-of-domain point

UniKeccakComplete's `pcsProveH` opens a PCS claim at the deployed out-of-domain point `oodPoint n root` (a function of
the root). π2's prover opens `W`'s and `Q`'s claims at the point the contract reads off Keccak-256
(`RecStatement.pcsOpenKO`: `WhirBridge.Pcs.oodPointM H n root`), which its own run asks of `H`. Here the prover with
the point `z` a parameter:

* **`pcsProveZH fuel n z tree stack pt v`**: `pcsProveH` with `z` in place of `pcsZ n tree.root` and the answer
  `stackEval stack z`; at `z = pcsZ n tree.root` it is `pcsProveH` (`pcsProveH_eq_Z`, `rfl`);
* **`pcsVerify_pcsProveZH`**: at a pure `H`, `F`, every proof it makes at `z = (zOf root).toList` is accepted by
  `pcsVerifyWithHash H F zOf` on the claim of the root, the answer `stackEval stack z`, the point and its value
  (`23 ≤ n ≤ 28`); **`pcsProveZH_fails_only_at_pow`**;
* over the two calls: **`simulateQ_pcsProveZH`**, **`disc_pcsProveZH`**, **`cost_pcsProveZH`**,
  **`pcsProveZH_eq_some_none`**; and the point itself: **`simulateQ_oodPointM`**, **`oodPointM_id`** (at a pure
  Keccak-256 `Hk`, the point is `oodPointWith Hk n root`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF simulateQ_absorb)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.PcsZ

open UniComplete UniKeccakComplete
open UniStatement (plainLayout)

/-! ## The prover -/

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **The honest opening of a PCS claim at the out-of-domain point `z`** (`prove_claim`) on the stack committed by
`tree`, at `n` variables: the point claim `(pt, v)` with the out-of-domain answer `stackEval stack z`; `none` if the
point has not `n` coordinates or a proof of work finds no nonce below `fuel`. -/
def pcsProveZH (fuel n : ℕ) (z : List E) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    m (Option Compile.Proof) :=
  if h : pt.length = n then do
    let (r0, r1) := digestScalars tree.root
    let sp ← pcsSpongeH H F
      (WhirBridge.Pcs.claimBytes (pcsClaimOf n tree.root (stackEval stack z) pt v h))
    let sp ← absorb F sp r0 dsObserve
    let sp ← absorb F sp r1 dsObserve
    let r ← runFromWithHash H F fuel
      (verifyStackedOpening n PcsQuotient.logInvRate (pcsSC z (stackEval stack z) pt v))
      (some (PcsQuotient.openingScript (plainLayout n) stack [⟨z, stackEval stack z⟩, ⟨pt, v⟩])) sp [tree]
    return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩
  else pure none

/-- **At the deployed point it is UniKeccakComplete's prover.** -/
theorem pcsProveH_eq_Z (fuel n : ℕ) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    pcsProveH H F fuel n tree stack pt v = pcsProveZH H F fuel n (pcsZ n tree.root) tree stack pt v := rfl

end With

/-! ## The prover is mumbai's compiled honest prover -/

/-- **The PCS prover at `z` is mumbai's compiled honest prover** of `openingProgram n 1 (pcsSC z …)`, at a pure hash
and permutation, on the stack's commitment. -/
theorem pcsProveZH_eq_prove (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel n : ℕ) (h1 : 6 ≤ n)
    (h2 : n ≤ 64) (hw : Whir.Admissible n PcsQuotient.logInvRate) (stack : Array K) (z : List E) (hz : z.length = n)
    (pt : List E) (hpt : pt.length = n) (v : E) :
    pcsProveZH (m := Id) H F fuel n z (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt v =
      Compile.prove H F
        (Whir.Complete.openingProgram n PcsQuotient.logInvRate (pcsSC z (stackEval stack z) pt v))
        (Whir.Complete.openingProver n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
          (pcsSC z (stackEval stack z) pt v))
        (pcsSpongeH (m := Id) H F (WhirBridge.Pcs.claimBytes
          (pcsClaimOf n (E2ECompleteness.commitWithH (m := Id) H n stack).root (stackEval stack z) pt v
            hpt))).state fuel := by
  have hword : (Whir.Complete.openingProver n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
      (pcsSC z (stackEval stack z) pt v)).word [] = stackWordFast n 1 stack := by
    show Whir.Complete.stackWord _ _ = _
    rw [E2ECompleteness.stackWordFast_colOf h1, Enc.stackWordFast_eq h2]
  have hrun : ∀ (sp : Sponge) (cs : List LeanVM.Prover.Tree) (ht w : ℕ) (W : Word),
      proveFromM (m := Id) H F (Whir.Complete.openingProver n PcsQuotient.logInvRate
          (E2ECompleteness.colOf n stack) (pcsSC z (stackEval stack z) pt v)) fuel
        ((verifyStackedOpening n PcsQuotient.logInvRate (pcsSC z (stackEval stack z) pt v)).bind
          fun _ ↦ Prog.ret true) sp [Ev.commit ht w W] cs =
      runFromWithHash (m := Id) H F fuel
        (verifyStackedOpening n PcsQuotient.logInvRate (pcsSC z (stackEval stack z) pt v))
        (some (PcsQuotient.openingScript (plainLayout n) stack [⟨z, stackEval stack z⟩, ⟨pt, v⟩]))
        sp cs := by
    intro sp cs ht w W
    have hwalk : Script.walk (Whir.Complete.honestCommitOpening n PcsQuotient.logInvRate
        (E2ECompleteness.colOf n stack) (pcsSC z (stackEval stack z) pt v) >>= fun _ ↦ Script.ret ())
          [Ev.commit ht w W] =
        some ((Whir.Complete.honestOpening n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
          (pcsSC z (stackEval stack z) pt v)).bind fun _ ↦ Script.ret ()) := rfl
    rw [Whir.Complete.openingProver, ← runFrom_eq_proveFromM (m := Id) H F fuel _ _ _ sp _ cs hwalk,
      E2ECompleteness.runFromWithHash_bind_ret]
    exact (runFrom_corr (m := Id) H F fuel _ (corr_pcs h1 h2 stack hz hpt _ v) sp cs).symm
  rw [← proveM_id, E2ECompleteness.openingProgram_eq hw]
  simp only [pcsProveZH, hpt, ↓reduceDIte]
  simp only [E2ECompleteness.commitWithH]
  simp only [proveM, proveFromM, hword, List.nil_append, hrun, bind_assoc, pure_bind, Option.map_map,
    pcsSpongeH_eta]
  rfl

/-! ## The opening check accepts -/

/-- **The honest PCS opening at the point `zOf root` is accepted** (`23 ≤ n ≤ 28`), at a pure Keccak-256 `H` and
permutation `F`: every proof `pcsProveZH` makes at `(zOf root).toList` of the point claim `⟨pt, stackEval stack pt⟩` on
the stack's commitment is accepted by `pcsVerifyWithHash H F zOf` on the PCS claim of the commitment's root, its
out-of-domain answer `stackEval stack (zOf root)`, the point and the value. -/
theorem pcsVerify_pcsProveZH (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (zOf : Digest → Vector E n) (stack : Array K) (hs : stack.size = 2 ^ n)
    (pt : List E) (hpt : pt.length = n) {π : Compile.Proof}
    (hπ : pcsProveZH (m := Id) H F fuel n (zOf (E2ECompleteness.commitWithH (m := Id) H n stack).root).toList
      (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt (stackEval stack pt) = some π) :
    WhirBridge.Pcs.pcsVerifyWithHash (m := Id) H F zOf
      (pcsClaimOf n (E2ECompleteness.commitWithH (m := Id) H n stack).root
        (stackEval stack (zOf (E2ECompleteness.commitWithH (m := Id) H n stack).root).toList) pt
        (stackEval stack pt) hpt)
      π = true := by
  have hw : Whir.Admissible n PcsQuotient.logInvRate := UniKeccakSound.admissible_k h1 h2
  have hπ' := (pcsProveZH_eq_prove H F fuel n (by omega) (by omega) hw stack _ (by simp) pt hpt _).symm.trans hπ
  -- the proof's first two scalars are the root's
  have hroot : WhirBridge.rootOf π = some (E2ECompleteness.commitWithH (m := Id) H n stack).root := by
    simp only [pcsProveZH, hpt, ↓reduceDIte] at hπ
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hπ
    exact digestOfScalars_digestScalars _
  generalize hR : (E2ECompleteness.commitWithH (m := Id) H n stack).root = R at hπ' hroot ⊢
  have hz : (zOf R).toList.length = n := by simp
  have hacc := runProof_prove H F _ _ _ fuel
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (E2ECompleteness.colOf n stack) _
      (pcsSC_holds stack hs hz hpt) (pcsSC_multilinear n _ _ _ _) chal).1)
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (E2ECompleteness.colOf n stack) _
      (pcsSC_holds stack hs hz hpt) (pcsSC_multilinear n _ _ _ _) chal).2) hπ'
  have hmv : WhirBridge.Pcs.minVars ≤ n ∧ n ≤ WhirBridge.Pcs.maxVars :=
    ⟨by unfold WhirBridge.Pcs.minVars; omega, by unfold WhirBridge.Pcs.maxVars; omega⟩
  unfold WhirBridge.Pcs.pcsVerifyWithHash
  simp only [hmv, and_self, ↓reduceIte, pcsClaimOf] at hacc ⊢
  show (if WhirBridge.rootOf π = some R then _ else _) = true
  simp only [hroot, ↓reduceIte]
  rw [prog_eq_openingProgram _ (by simp) _]
  exact hacc

/-- **The PCS prover at `z` fails only at its proof of work.** -/
theorem pcsProveZH_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (z : List E) (hz : z.length = n) (pt : List E)
    (hpt : pt.length = n) (v : E)
    (h : pcsProveZH (m := Id) H F fuel n z (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt v = none) :
    ∃ (sc : List StackClaim) (hist : List Ev) (k : Prog Bool) (sp : Sponge),
      (Whir.Complete.openingProgram n PcsQuotient.logInvRate sc).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
        ∀ i < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf i)
          (Compile.powStep F sp (Compile.nonceOf i)).1 = false := by
  rw [pcsProveZH_eq_prove H F fuel n (by omega) (by omega) (UniKeccakSound.admissible_k h1 h2) stack z hz pt hpt
    v] at h
  by_contra hne
  refine prove_ne_none H F _ _ _ fuel (fun hist bits k sp hg hn ↦ hne ?_) h
  obtain rfl := ((E2ECompleteness.movesOK_openingProgram _ _ _).after hg).1
  exact ⟨_, hist, k, sp, hg, ((findNonce_eq_none_iff F _ sp fuel).1 hn).2⟩

/-! ## Over the two calls -/

section Commute

variable {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl KeccakCalls m)

theorem simulateQ_pcsProveZH (fuel n : ℕ) (z : List E) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    simulateQ impl (pcsProveZH callKeccak256 callKeccakF1600 fuel n z tree stack pt v) =
      pcsProveZH (implH impl) (implF impl) fuel n z tree stack pt v := by
  unfold pcsProveZH
  split
  · simp only [simulateQ_bind, simulateQ_pcsSpongeH, simulateQ_absorb,
      E2ECompleteness.simulateQ_runFromWithHash, simulateQ_pure]
  · simp

/-- **The out-of-domain point, simulated**: its `n` Keccak-256 calls answered by `impl`. -/
theorem simulateQ_oodPointM (n : ℕ) (r : Digest) :
    simulateQ impl (WhirBridge.Pcs.oodPointM callKeccak256 n r) = WhirBridge.Pcs.oodPointM (implH impl) n r := by
  unfold WhirBridge.Pcs.oodPointM
  generalize List.range n = l
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, ih, simulateQ_queryH]

end Commute

/-- **At a pure Keccak-256 the point is `oodPointWith`.** -/
theorem oodPointM_id (Hk : Bytes → Digest) (n : ℕ) (r : Digest) :
    WhirBridge.Pcs.oodPointM (m := Id) (Pure.pure ∘ Hk) n r = pure (WhirBridge.Pcs.oodPointWith Hk n r).toList :=
  WhirBridge.Pcs.UnionO.oodPointM_pure (m := Id) Hk n r

section Disc

open E2ECompleteness

/-- **The PCS prover at `z` is disciplined.** -/
theorem disc_pcsProveZH (fuel n : ℕ) (z : List E) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    Disc (pcsProveZH callKeccak256 callKeccakF1600 fuel n z tree stack pt v) := by
  intro h
  unfold pcsProveZH
  split
  · refine (duplexP_pcsSpongeH _ h).bind fun sp h₁ hs ↦ ?_
    refine (LeanVM.Rpm.duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
    refine (LeanVM.Rpm.duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
    exact (duplexP_runFromWithHash _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial
  · trivial

end Disc

section Failure

variable {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}

/-- **A PCS opening at `z` fails only at a `17`-bit proof of work**, in `Option`. -/
theorem pcsProveZH_eq_some_none {fuel n : ℕ} {z : List E} {tree : Tree} {stack : Array K} {pt : List E} {v : E}
    (h : pcsProveZH H F fuel n z tree stack pt v = some none) (hpt : pt.length = n) :
    ∃ sp', LeanVM.Protocol.Compile.Rom.ProverSp sp' ∧
      findNonceM F Whir.queryGrindingBits sp' fuel = some none := by
  simp only [pcsProveZH, hpt, ↓reduceDIte] at h
  obtain ⟨sp₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  rcases r with _ | _
  · exact E2ECompleteness.runFromWithHash_eq_some_none _ fuel _ _ _ _
      (EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _)
      (LeanVM.Protocol.Compile.Rom.proverSp_absorb (LeanVM.Protocol.Compile.Rom.proverSp_absorb
        (proverSp_pcsSpongeH h₀) h₁) h₂) hr
  · cases h

end Failure

section Cost

open E2ECompleteness.Cost

/-- **The PCS prover's cost at `z`**: as `cost_pcsProveH`. -/
theorem cost_pcsProveZH (fuel n : ℕ) (z : List E) (tree : Tree) (stack : Array K) (pt : List E) (v : E) {w : ℕ}
    (hw : pt.length ≤ w) :
    QC (pcsProveZH callKeccak256 callKeccakF1600 fuel n z tree stack pt v)
      ((82 + 24 * w) / 136 + 1 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel) := by
  unfold pcsProveZH
  split
  · rename_i hpt
    refine (qc_pcsSpongeH _ ((82 + 24 * w) / 136 + 1) (by rw [WhirBridge.Pcs.claimBytes_length]; omega)).bind_le
      (fun sp ↦ (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le (fun sp ↦
        (cost_runFromWithHash fuel costHeight _ _ sp [tree] _ _ (costs_vso _ _ _)
          (wordsLE_openingScript _ stack _)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) (by omega)
  · exact qc_pure _ _

end Cost

end RecCompose.PcsZ

/-- info: 'RecCompose.PcsZ.pcsVerify_pcsProveZH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.PcsZ.pcsVerify_pcsProveZH

/-- info: 'RecCompose.PcsZ.pcsProveZH_fails_only_at_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.PcsZ.pcsProveZH_fails_only_at_pow

/-- info: 'RecCompose.PcsZ.simulateQ_pcsProveZH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.PcsZ.simulateQ_pcsProveZH

/-- info: 'RecCompose.PcsZ.cost_pcsProveZH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.PcsZ.cost_pcsProveZH
