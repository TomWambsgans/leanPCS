-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `crates/pcs_claim` (`prove_claim`: the
-- out-of-domain answer, the claim's seed, the root's two scalars, the stacked opening of the two claims) and
-- `crates/leanvm/univariate/src/prover/opening.rs`. Adapts this repository's `E2ECompleteness.ProverOpening`
-- (`proveOpeningWithH_eq_prove`, `openingWithH_proveOpeningWithH`, `exists_failed_pow_opening`),
-- `E2ECompleteness.WithHash`, `Duplex`, `Cost`, `Grinding` (the opening's simulation, discipline, cost and failure) to
-- the PCS claim's seed; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `runProof_prove`, `prove_ne_none`, `findNonce_eq_none_iff` (`Protocol/Compile/Prover.lean`),
-- `runI_openingProgram`, `honestOpening`, `basisTable` (`Protocol/Whir/Complete/Opening.lean`), `runFrom_corr`,
-- `runFrom_eq_proveFromM` (`Prover/Corr.lean`, `Prover/Refine.lean`), `proveM_id` (`Protocol/Compile/Rom/Prover.lean`).
import UniComplete.Whir
import WhirBridge.Pcs
import UniKeccakSound.Fs.Whir23
import E2ECompleteness.Grinding
import E2ECompleteness.Cost

/-!
# The honest opening of a PCS claim

The Keccak verifier opens each of its three commitments by the EIP draft's PCS claim
(`UniKeccak.pcsOpenK`, `WhirBridge.Pcs.pcsVerifyWithHash`): the claim `root ‖ ood ‖ point ‖ value` of a stack of `n`
variables, its opening WHIR's stacked opening of the two claims `f(z) = ood`, `f(point) = value`, `z` the root's
out-of-domain point (`WhirBridge.Pcs.oodPoint n root`), from the seed `F(seedInput(H(claim), 0))`, the proof's first
two scalars the root. Here the honest prover of it and its acceptance:

* **`pcsOod`**: the out-of-domain answer, the stack's multilinear extension (`stackEval`) at `z`;
* **`pcsProveH`** (`prove_claim`): the root's two scalars, then the Statement's opening script at the plain layout
  (`PcsQuotient.openingScript (plainLayout n)`, its weight table the two claims' `eq` on the cube) run against the
  claim's program (`verifyStackedOpening n 1 (pcsSC z ood point value)`) from the claim's sponge (`pcsSpongeH`);
* **`pcsProveH_eq_prove`**: at a pure hash and permutation it is mumbai's compiled honest prover of
  `openingProgram n 1 (pcsSC …)`; the script makes the moves of mumbai's `honestOpening` of the claims' `eq` weights,
  since at the plain layout a claim's weight on the cube is `eq` (`UniComplete.stackWeight_plain`, `basisTable_pcs`);
* **`pcsVerify_pcsProveH`**: every proof it makes of `⟨point, stackEval stack point⟩` on the stack's commitment is
  accepted by `pcsVerifyWithHash`, at `23 ≤ n ≤ 28` (admissible, `UniKeccakSound.admissible_k`);
  **`pcsProveH_fails_only_at_pow`**: it fails only at a `17`-bit proof of work;
* over the two calls: **`simulateQ_pcsProveH`**, **`simulateQ_pcsVerify`**, **`disc_pcsProveH`**, **`disc_pcsVerify`**,
  **`cost_pcsProveH`**, **`cost_pcsVerify`**, and **`pcsProveH_eq_some_none`** (a failure in `Option` is a failed
  search at a sponge the prover keeps).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF simulateQ_absorb)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete

open UniComplete
open UniStatement (plainLayout)

/-! ## The prover -/

/-- **The two stack claims of a PCS claim** at the out-of-domain point `z` (`WhirBridge.Pcs.stacking`'s): `eq(z, ·)`
of value `ood`, `eq(point, ·)` of value `value`. -/
def pcsSC (z : List E) (ood : E) (pt : List E) (v : E) : List StackClaim :=
  [(WhirBridge.eqZ z, ood), (WhirBridge.eqZ pt, v)]

/-- The out-of-domain point of a root, on `n` variables (the deployed Keccak-256: a function of the root). -/
def pcsZ (n : ℕ) (root : Digest) : List E := (WhirBridge.Pcs.oodPoint n root).toList

/-- **The out-of-domain answer**: the stack's multilinear extension at the root's out-of-domain point. -/
def pcsOod (n : ℕ) (stack : Array K) (root : Digest) : E := stackEval stack (pcsZ n root)

/-- A PCS claim on `n` variables. -/
def pcsClaimOf (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (h : pt.length = n) :
    WhirBridge.Pcs.Claim1 n :=
  ⟨root, ood, pt, v, h⟩

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **The claim's sponge** (`pcs_claim`'s transcript): the permutation of the IV `H(claim)` and the zero public
digest, nothing pending. -/
def pcsSpongeH (bytes : Bytes) : m Sponge := do
  let iv ← H bytes
  return ⟨← F (seedInput iv WhirBridge.publicDigest), []⟩

/-- **The honest opening of a PCS claim** (`prove_claim`) on the stack committed by `tree`, at `n` variables: the
point claim `(pt, v)` with the out-of-domain answer `pcsOod`; `none` if the point has not `n` coordinates or a proof
of work finds no nonce below `fuel`. -/
def pcsProveH (fuel n : ℕ) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    m (Option Compile.Proof) :=
  if h : pt.length = n then do
    let (r0, r1) := digestScalars tree.root
    let sp ← pcsSpongeH H F
      (WhirBridge.Pcs.claimBytes (pcsClaimOf n tree.root (pcsOod n stack tree.root) pt v h))
    let sp ← absorb F sp r0 dsObserve
    let sp ← absorb F sp r1 dsObserve
    let r ← runFromWithHash H F fuel
      (verifyStackedOpening n PcsQuotient.logInvRate (pcsSC (pcsZ n tree.root) (pcsOod n stack tree.root) pt v))
      (some (PcsQuotient.openingScript (plainLayout n) stack
        [⟨pcsZ n tree.root, pcsOod n stack tree.root⟩, ⟨pt, v⟩])) sp [tree]
    return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩
  else pure none

end With

/-! ## The weights on the cube -/

/-- **At the plain layout the opening script's weights are the claims' `eq`** on the cube: the basis table of the
layout's stack claims is that of the two `eq` claims. -/
theorem basisTable_pcs {n : ℕ} (h1 : 6 ≤ n) (h2 : n ≤ 64) {z pt : List E} (hz : z.length = n)
    (hpt : pt.length = n) (ood v : E) (scales : List E) :
    Whir.Complete.basisTable n scales (PcsQuotient.stackClaims (plainLayout n) [⟨z, ood⟩, ⟨pt, v⟩]) =
      Whir.Complete.basisTable n scales (pcsSC z ood pt v) := by
  unfold Whir.Complete.basisTable Whir.Complete.tableOf
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' : i < 2 ^ (6 + (n - 6)) := by
    rw [show 6 + (n - 6) = n by omega]
    exact List.mem_range.1 hi
  have hrot := Whir.Complete.boolPoint_rotIndex 6 (n - 6) i hi'
  have hj := Whir.Complete.rotIndex_lt hi'
  rw [show n - 6 + 6 = n by omega] at hrot hj
  rw [show 6 + (n - 6) = n by omega] at hrot
  beta_reduce
  rw [show EndToEnd.laneBits = 6 from rfl, ← hrot]
  have hp : (plainLayout n).logPiece = none := rfl
  simp only [Whir.Complete.batchedBasis, PcsQuotient.stackClaims, hp, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, List.append_nil, List.map_cons, List.map_nil, pcsSC]
  rw [stackWeight_plain h1 h2 ⟨z, ood⟩ hz hj, stackWeight_plain h1 h2 ⟨pt, v⟩ hpt hj,
    WhirBridge.eqZ_eq_eqEval, WhirBridge.eqZ_eq_eqEval, Whir.Complete.eqEval_comm z,
    Whir.Complete.eqEval_comm pt]

/-- mumbai's honest opening reads its claims through their number, their values and their basis table. -/
theorem honestOpening_congr {n R : ℕ} (q : Column n) {c₁ c₂ : List StackClaim}
    (hl : c₁.length = c₂.length) (hv : c₁.map (·.2) = c₂.map (·.2))
    (hb : ∀ scales, Whir.Complete.basisTable n scales c₁ = Whir.Complete.basisTable n scales c₂) :
    Whir.Complete.honestOpening n R q c₁ = Whir.Complete.honestOpening n R q c₂ := by
  unfold Whir.Complete.honestOpening
  simp only [hl, hv, hb]

/-- **The opening script at the plain layout makes the moves of mumbai's honest opening of the two `eq`
claims.** -/
theorem corr_pcs {n : ℕ} (h1 : 6 ≤ n) (h2 : n ≤ 64) (stack : Array K) {z pt : List E} (hz : z.length = n)
    (hpt : pt.length = n) (ood v : E) :
    Corr (fun _ _ ↦ True) (PcsQuotient.openingScript (plainLayout n) stack [⟨z, ood⟩, ⟨pt, v⟩])
      ((Whir.Complete.honestOpening n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
        (pcsSC z ood pt v)).bind fun _ ↦ Script.ret ()) := by
  have h := E2ECompleteness.corr_openingScript_ret (plainLayout n) (weightShape_plain h1 h2) stack
    [⟨z, ood⟩, ⟨pt, v⟩] (fun c hc ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hz
      · exact hpt)
  have hp : (plainLayout n).logPiece = none := rfl
  rwa [show (plainLayout n).logN = n from rfl,
    honestOpening_congr _ (by simp [PcsQuotient.stackClaims, hp, pcsSC])
      (by simp [PcsQuotient.stackClaims, hp, pcsSC]) (basisTable_pcs h1 h2 hz hpt ood v)] at h

/-! ## The prover is mumbai's compiled honest prover -/

theorem pcsSpongeH_eta (H : Bytes → Digest) (F : KeccakState → KeccakState) (bytes : Bytes) :
    (⟨(pcsSpongeH (m := Id) H F bytes).state, []⟩ : Sponge) = pcsSpongeH (m := Id) H F bytes := rfl

/-- **The PCS prover is mumbai's compiled honest prover** of `openingProgram n 1 (pcsSC …)` with the honest strategy
of the stack's column, from the claim's sponge, at a pure hash and permutation, on the stack's commitment. -/
theorem pcsProveH_eq_prove (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel n : ℕ) (h1 : 6 ≤ n)
    (h2 : n ≤ 64) (hw : Whir.Admissible n PcsQuotient.logInvRate) (stack : Array K) (pt : List E)
    (hpt : pt.length = n) (v : E) :
    pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt v =
      Compile.prove H F
        (Whir.Complete.openingProgram n PcsQuotient.logInvRate
          (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v))
        (Whir.Complete.openingProver n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
          (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v))
        (pcsSpongeH (m := Id) H F (WhirBridge.Pcs.claimBytes
          (pcsClaimOf n (E2ECompleteness.commitWithH (m := Id) H n stack).root
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v hpt))).state fuel := by
  have hz : (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root).length = n := by simp [pcsZ]
  have hword : (Whir.Complete.openingProver n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
      (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
        (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v)).word [] =
      stackWordFast n 1 stack := by
    show Whir.Complete.stackWord _ _ = _
    rw [E2ECompleteness.stackWordFast_colOf h1, Enc.stackWordFast_eq h2]
  have hrun : ∀ (sp : Sponge) (cs : List LeanVM.Prover.Tree) (ht w : ℕ) (W : Word),
      proveFromM (m := Id) H F (Whir.Complete.openingProver n PcsQuotient.logInvRate
          (E2ECompleteness.colOf n stack) (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v)) fuel
        ((verifyStackedOpening n PcsQuotient.logInvRate
          (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v)).bind
          fun _ ↦ Prog.ret true) sp [Ev.commit ht w W] cs =
      runFromWithHash (m := Id) H F fuel
        (verifyStackedOpening n PcsQuotient.logInvRate
          (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v))
        (some (PcsQuotient.openingScript (plainLayout n) stack
          [⟨pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root,
            pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root⟩, ⟨pt, v⟩]))
        sp cs := by
    intro sp cs ht w W
    have hwalk : Script.walk (Whir.Complete.honestCommitOpening n PcsQuotient.logInvRate
        (E2ECompleteness.colOf n stack) (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
          (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v) >>= fun _ ↦ Script.ret ())
          [Ev.commit ht w W] =
        some ((Whir.Complete.honestOpening n PcsQuotient.logInvRate (E2ECompleteness.colOf n stack)
          (pcsSC (pcsZ n (E2ECompleteness.commitWithH (m := Id) H n stack).root)
            (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt v)).bind
              fun _ ↦ Script.ret ()) := rfl
    rw [Whir.Complete.openingProver, ← runFrom_eq_proveFromM (m := Id) H F fuel _ _ _ sp _ cs hwalk,
      E2ECompleteness.runFromWithHash_bind_ret]
    exact (runFrom_corr (m := Id) H F fuel _ (corr_pcs h1 h2 stack hz hpt _ v) sp cs).symm
  rw [← proveM_id, E2ECompleteness.openingProgram_eq hw]
  simp only [pcsProveH, hpt, ↓reduceDIte]
  simp only [E2ECompleteness.commitWithH] at hword hrun ⊢
  simp only [proveM, proveFromM, hword, List.nil_append, hrun, bind_assoc, pure_bind, Option.map_map,
    pcsSpongeH_eta]
  rfl

/-! ## The opening check accepts -/

/-- **The claim's program** (`WhirBridge.Pcs.prog`: the root, the check, accept) is mumbai's `openingProgram` of the
two `eq` claims, at a point `z` of `n` coordinates. -/
theorem prog_eq_openingProgram {n R : ℕ} (z : List E) (hz : z.length = n) (x : WhirBridge.Pcs.Claim1 n) :
    WhirBridge.Pcs.prog n R z x = Whir.Complete.openingProgram n R (pcsSC z x.ood x.point x.value) := by
  unfold WhirBridge.Pcs.prog Whir.Complete.openingProgram
  have hc : ∀ c ∈ [(⟨z, x.ood⟩ : WhirBridge.Claim), ⟨x.point, x.value⟩],
      c.point.length = (WhirBridge.Pcs.stacking n).vars := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hz
    · exact x.wide
  rw [WhirBridge.Pcs.check_eq z hz x, WhirBridge.Stacking.check_eq_ite, ite_eq_left_of_eq_true _ _ (eq_true hc)]
  rfl

/-- The stack's column's polynomial is the stack's multilinear extension. -/
theorem colEval_colOf {n : ℕ} (stack : Array K) (hs : stack.size = 2 ^ n) (p : List E) (hp : p.length = n) :
    WhirBridge.Pcs.colEval (E2ECompleteness.colOf n stack) p = stackEval stack p := by
  rw [stackEval_eq stack p (by rw [hs, hp]), WhirBridge.Pcs.colEval, hp, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Whir.Complete.eqEval_comm, mul_comm]
  congr 2
  simp [E2ECompleteness.colOf, Vector.getD, Array.getD_eq_getD_getElem?, x.isLt]

/-- **The two claims hold** of the stack's column: its multilinear extension at `z` and at the point. -/
theorem pcsSC_holds {n : ℕ} (stack : Array K) (hs : stack.size = 2 ^ n) {z pt : List E} (hz : z.length = n)
    (hpt : pt.length = n) :
    ∀ sc ∈ pcsSC z (stackEval stack z) pt (stackEval stack pt),
      EndToEnd.StackClaim.Holds n sc (E2ECompleteness.colOf n stack) := by
  intro sc hsc
  simp only [pcsSC, List.mem_cons, List.not_mem_nil, or_false] at hsc
  rcases hsc with rfl | rfl
  · exact (WhirBridge.Pcs.holds_iff (E2ECompleteness.colOf n stack) ⟨z, stackEval stack z⟩).2
      (colEval_colOf stack hs z hz)
  · exact (WhirBridge.Pcs.holds_iff (E2ECompleteness.colOf n stack) ⟨pt, stackEval stack pt⟩).2
      (colEval_colOf stack hs pt hpt)

/-- The two claims' weights are multilinear. -/
theorem pcsSC_multilinear (n : ℕ) (z : List E) (ood : E) (pt : List E) (v : E) :
    ∀ sc ∈ pcsSC z ood pt v, EndToEnd.IsMultilinearFn n sc.1 := by
  intro sc hsc
  simp only [pcsSC, List.mem_cons, List.not_mem_nil, or_false] at hsc
  rcases hsc with rfl | rfl <;>
    exact Completeness.isMultilinearFn_of_isMultiaffine (WhirBridge.isMultiaffine_eqZ _ n)

/-- **The honest PCS opening is accepted** (`23 ≤ n ≤ 28`), at a pure Keccak-256 `H` and permutation `F`: every
proof `pcsProveH` makes of the point claim `⟨pt, stackEval stack pt⟩` on the stack's commitment is accepted by
`pcsVerifyWithHash` on the PCS claim of the commitment's root, its out-of-domain answer `pcsOod`, the point and the
value. -/
theorem pcsVerify_pcsProveH (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ n) (pt : List E) (hpt : pt.length = n)
    {π : Compile.Proof}
    (hπ : pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt
      (stackEval stack pt) = some π) :
    WhirBridge.Pcs.pcsVerifyWithHash (m := Id) H F (WhirBridge.Pcs.oodPoint n)
      (pcsClaimOf n (E2ECompleteness.commitWithH (m := Id) H n stack).root
        (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt (stackEval stack pt) hpt)
      π = true := by
  have hw : Whir.Admissible n PcsQuotient.logInvRate := UniKeccakSound.admissible_k h1 h2
  have hπ' := (pcsProveH_eq_prove H F fuel n (by omega) (by omega) hw stack pt hpt _).symm.trans hπ
  generalize hR : (E2ECompleteness.commitWithH (m := Id) H n stack).root = R at hπ' ⊢
  have hz : (pcsZ n R).length = n := by simp [pcsZ]
  have hacc := runProof_prove H F _ _ _ fuel
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (E2ECompleteness.colOf n stack) _
      (pcsSC_holds stack hs hz hpt) (pcsSC_multilinear n _ _ _ _) chal).1)
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (E2ECompleteness.colOf n stack) _
      (pcsSC_holds stack hs hz hpt) (pcsSC_multilinear n _ _ _ _) chal).2) hπ'
  -- the proof's first two scalars are the root's
  have hroot : WhirBridge.rootOf π = some R := by
    simp only [pcsProveH, hpt, ↓reduceDIte] at hπ
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hπ
    rw [← hR]
    exact digestOfScalars_digestScalars _
  have hmv : WhirBridge.Pcs.minVars ≤ n ∧ n ≤ WhirBridge.Pcs.maxVars :=
    ⟨by unfold WhirBridge.Pcs.minVars; omega, by unfold WhirBridge.Pcs.maxVars; omega⟩
  unfold WhirBridge.Pcs.pcsVerifyWithHash
  simp only [hmv, and_self, ↓reduceIte, pcsClaimOf] at hacc ⊢
  show (if WhirBridge.rootOf π = some R then _ else _) = true
  simp only [hroot, ↓reduceIte]
  rw [prog_eq_openingProgram _ (by simp) _]
  exact hacc

/-- **The PCS prover fails only at its proof of work**: if it returns no proof on a point of `n` coordinates, the
opening program reached WHIR's `17`-bit proof of work at a sponge where every nonce below `fuel` fails. -/
theorem pcsProveH_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (pt : List E) (hpt : pt.length = n) (v : E)
    (h : pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt v = none) :
    ∃ (sc : List StackClaim) (hist : List Ev) (k : Prog Bool) (sp : Sponge),
      (Whir.Complete.openingProgram n PcsQuotient.logInvRate sc).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
        ∀ i < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf i)
          (Compile.powStep F sp (Compile.nonceOf i)).1 = false := by
  rw [pcsProveH_eq_prove H F fuel n (by omega) (by omega) (UniKeccakSound.admissible_k h1 h2) stack pt hpt v] at h
  by_contra hne
  refine prove_ne_none H F _ _ _ fuel (fun hist bits k sp hg hn ↦ hne ?_) h
  obtain rfl := ((E2ECompleteness.movesOK_openingProgram _ _ _).after hg).1
  exact ⟨_, hist, k, sp, hg, ((findNonce_eq_none_iff F _ sp fuel).1 hn).2⟩

/-! ## Over the two calls -/

section Commute

variable {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl KeccakCalls m)

theorem simulateQ_pcsSpongeH (bytes : Bytes) :
    simulateQ impl (pcsSpongeH callKeccak256 callKeccakF1600 bytes) =
      pcsSpongeH (implH impl) (implF impl) bytes := by
  simp only [pcsSpongeH, simulateQ_bind, simulateQ_queryH, simulateQ_queryF, simulateQ_pure]

theorem simulateQ_pcsProveH (fuel n : ℕ) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    simulateQ impl (pcsProveH callKeccak256 callKeccakF1600 fuel n tree stack pt v) =
      pcsProveH (implH impl) (implF impl) fuel n tree stack pt v := by
  unfold pcsProveH
  split
  · simp only [simulateQ_bind, simulateQ_pcsSpongeH, simulateQ_absorb,
      E2ECompleteness.simulateQ_runFromWithHash, simulateQ_pure]
  · simp

theorem simulateQ_pcsVerify {n : ℕ} (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
    (π : Compile.Proof) :
    simulateQ impl (WhirBridge.Pcs.pcsVerifyWithHash callKeccak256 callKeccakF1600 zOf x π) =
      WhirBridge.Pcs.pcsVerifyWithHash (implH impl) (implF impl) zOf x π := by
  unfold WhirBridge.Pcs.pcsVerifyWithHash runProofWithHash
  split
  · simp only [simulateQ_bind, simulateQ_queryH, simulateQ_queryF]
    congr 1; funext iv; congr 1; funext seed
    split
    · simp only [simulateQ_bind, E2ECompleteness.simulateQ_runWithHash]
      congr 1; funext o
      split <;> simp
    · simp
  · simp

end Commute

section Disc

open E2ECompleteness

theorem duplexP_pcsSpongeH (bytes : Bytes) (h : List KeccakState) :
    LeanVM.Rpm.DuplexP (pcsSpongeH callKeccak256 callKeccakF1600 bytes) h fun sp h' ↦ sp.state ∈ h' := by
  unfold pcsSpongeH
  refine (((LeanVM.Rpm.hOnly_queryH _).duplexP h)).bind fun iv h' hh ↦ ?_
  subst hh
  exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
    ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The PCS prover is disciplined.** -/
theorem disc_pcsProveH (fuel n : ℕ) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    Disc (pcsProveH callKeccak256 callKeccakF1600 fuel n tree stack pt v) := by
  intro h
  unfold pcsProveH
  split
  · refine (duplexP_pcsSpongeH _ h).bind fun sp h₁ hs ↦ ?_
    refine (LeanVM.Rpm.duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
    refine (LeanVM.Rpm.duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
    exact (duplexP_runFromWithHash _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial
  · trivial

/-- **The PCS opening check is disciplined.** -/
theorem disc_pcsVerify {n : ℕ} (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n) (π : Compile.Proof) :
    Disc (WhirBridge.Pcs.pcsVerifyWithHash callKeccak256 callKeccakF1600 zOf x π) := by
  intro h
  unfold WhirBridge.Pcs.pcsVerifyWithHash runProofWithHash
  split
  · refine (((LeanVM.Rpm.hOnly_queryH _).duplexP h)).bind fun iv h' hh ↦ ?_
    subst hh
    refine (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed ↦ ?_⟩
    split
    · exact (LeanVM.Rpm.duplexP_run _ ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ _
        List.mem_cons_self).bind fun z _ _ ↦ by split <;> trivial
    · trivial
  · trivial

end Disc

section Failure

variable {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}

theorem proverSp_pcsSpongeH {bytes : Bytes} {sp : Sponge} (h : pcsSpongeH H F bytes = some sp) :
    LeanVM.Protocol.Compile.Rom.ProverSp sp := by
  simp only [pcsSpongeH] at h
  obtain ⟨iv, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨by simp, by simp⟩

/-- **A PCS opening fails only at a `17`-bit proof of work**, in `Option`. -/
theorem pcsProveH_eq_some_none {fuel n : ℕ} {tree : Tree} {stack : Array K} {pt : List E} {v : E}
    (h : pcsProveH H F fuel n tree stack pt v = some none) (hpt : pt.length = n) :
    ∃ sp', LeanVM.Protocol.Compile.Rom.ProverSp sp' ∧
      findNonceM F Whir.queryGrindingBits sp' fuel = some none := by
  simp only [pcsProveH, hpt, ↓reduceDIte] at h
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

theorem qc_pcsSpongeH (bytes : Bytes) (B : ℕ) (hB : bytes.length < 136 * B) :
    QC (pcsSpongeH callKeccak256 callKeccakF1600 bytes) (B + 1) := by
  unfold pcsSpongeH
  exact (qc_H_le (k := B) hB).bind_le (fun iv ↦ (qc_F _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl

/-- **The PCS prover's cost**: its IV (`6` blocks: a claim of at most `28` coordinates), the seed's permutation, the
root's two absorptions and the runner. -/
theorem cost_pcsProveH (fuel n : ℕ) (hn : n ≤ 28) (tree : Tree) (stack : Array K) (pt : List E) (v : E) :
    QC (pcsProveH callKeccak256 callKeccakF1600 fuel n tree stack pt v)
      (6 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel) := by
  unfold pcsProveH
  split
  · refine (qc_pcsSpongeH _ 6 (by rw [WhirBridge.Pcs.claimBytes_length]; omega)).bind_le (fun sp ↦
      (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le (fun sp ↦
        (cost_runFromWithHash fuel costHeight _ _ sp [tree] _ _ (costs_vso _ _ _)
          (wordsLE_openingScript _ stack _)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) (by omega)
  · exact qc_pure _ _

/-- **The PCS opening check's cost**: its IV (`6` blocks), the seed's permutation, then the compiled run of the
claim's program (the root's commitment, the stacked opening). -/
theorem cost_pcsVerify {n : ℕ} (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n) (π : Compile.Proof) :
    QC (WhirBridge.Pcs.pcsVerifyWithHash callKeccak256 callKeccakF1600 zOf x π)
      (6 + 1 + 3 * (2 + ((4 + (2 + whirBound)) + 0))) := by
  unfold WhirBridge.Pcs.pcsVerifyWithHash runProofWithHash
  split
  · rename_i hn
    have hw : Whir.Admissible n WhirBridge.logInvRate := WhirBridge.Pcs.admissible_v1 n hn.1 hn.2
    have hn28 : n ≤ 28 := hn.2
    refine (qc_H_le (k := 6) ?_).bind_le (b := 1 + 3 * (2 + ((4 + (2 + whirBound)) + 0)))
      (fun iv ↦ (qc_F _).bind_le (b := 3 * (2 + ((4 + (2 + whirBound)) + 0))) (fun seed ↦ ?_) le_rfl) (by omega)
    · rw [WhirBridge.Pcs.claimBytes_length]; omega
    · split
      · rw [prog_eq_openingProgram _ (by simp) x, E2ECompleteness.openingProgram_eq hw]
        refine (cost_runWithHash costHeight _ _ (2 + ((4 + (2 + whirBound)) + 0)) (fun _ ↦ True) ?_ ?_ ?_).bind_le
          (b := 0) (fun z ↦ by split <;> exact qc_pure _ 0) (by omega)
        · refine ⟨by unfold costHeight WhirBridge.logInvRate; omega, by omega, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact Prog.Costs.bind (costs_vso _ _ _) fun _ _ ↦ Prog.Costs.ret' trivial
        · exact ⟨by unfold LeanVM.Rpm.maxWidth; omega,
            LeanVM.Rpm.WidthsLE.bind (widthsLE_vso _ _ _) fun _ ↦ trivial⟩
        · intro r hr
          simp at hr
      · exact qc_pure _ _
  · exact qc_pure _ _

end Cost

end UniKeccakComplete
