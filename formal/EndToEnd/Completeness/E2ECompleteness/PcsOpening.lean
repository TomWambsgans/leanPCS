-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapts leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `corr_openingFast` (`lean_vm/LeanVM/Prover/Whir.lean`) for
-- `corr_pcsOpeningScript`, `toList_basisTableA` (`WhirBasis.lean`) for `pcsWeightTable_eq`,
-- `stackWordFast_eq` (`Ntt.lean`), `proveFromM_eq_some_none` (`Protocol/Compile/Rom/Complete.lean`)
-- for `runFromWithHash_eq_some_none`, and uses `runFrom_eq_proveFromM`, `runFrom_corr` (`Refine.lean`,
-- `Corr.lean`), `proveM_id` (`Protocol/Compile/Rom/Prover.lean`), `runI_openingProgram`
-- (`Protocol/Whir/Complete/Opening.lean`), `runProof_prove` (`Protocol/Compile/Prover.lean`),
-- `isMultilinearFn_eqEval`, `multilinearEval_eq_sum` (`Protocol/Whir/Complete/Tables.lean`), `mleK_eq`
-- (`Prover/Mle.lean`), `proverSp_absorb` (`Protocol/Compile/Rom/Complete.lean`), `squeeze_option`
-- (`Protocol/Compile/Rom/Final.lean`), `movesOK_verifyStackedOpening`
-- (`Protocol/EndToEnd/Sound/Moves.lean`). The generic lemmas (`colOf`, `getD_colOf`,
-- `stackTableA_colOf`, `toList_stackTableA_colOf`, `openingProgram_eq`, `runFromWithHash_bind_ret`,
-- `stackWordFast_colOf`, `runWithHash_bind`, `runFromWithHash_eq_some_none`) are copied from this
-- repository's previous `E2ECompleteness/{ProverDefs,ProverOpening,Grinding}.lean`, and
-- `lt_two_pow_add` from `formal/WhirBridge/WhirBridge/Hidden.lean`.
import E2ECompleteness.PcsWithHash
import LeanVM.Prover.Whir
import LeanVM.Prover.Refine
import LeanVM.Prover.WhirTables
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Protocol.Compile.Rom.Prover
import LeanVM.Protocol.Compile.Rom.Complete
import LeanVM.Protocol.Compile.Rom.Final
import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# The PCS claim's WHIR opening is complete

`proveClaimWithH` (`PcsWithHash.lean`, the Statement's `proveClaimWith` with Keccak-256 explicit)
runs `pcsOpeningScript` (mumbai's `openingFast` with the PCS weight table `pcsWeightTable`) against
the verifier's program `verifyStackedOpening n 1 (pcsStackClaims z c claim)`. Here, at a pure hash
`H` and permutation `F`:

* **`pcsWeightTable_eq`**: the weight table `eq(z, ·) + λ·eq(point, ·)` at the rotated position is
  mumbai's `basisTable` of the two stack claims with the scales `[1, λ]`.
* **`corr_pcsOpeningScript`**: `pcsOpeningScript` makes the moves of mumbai's `honestOpening` of the
  two stack claims on the table as a column (`colOf`).
* **`proveClaimWithH_eq_prove`**: the opening prover, from the table's commitment, is mumbai's
  compiled honest prover `prove` of `openingProgram` with `openingProver`, from the opening's sponge.
* **`pcsOpeningWithH_eq_runProof`**: the opening check, on a proof whose first two scalars encode
  the commitment's root, is the compiled verifier `runProofWithHash` of `openingProgram`.
* **`pcsStackClaims_holds`**, **`pcsStackClaims_multilinear`**: the two stack claims hold of the
  table's column when `c.ood` and `claim.value` are the table's polynomial at `z` and at the point,
  and their weights are multilinear.
* **`admissible_of_vars`**: `15 ≤ n ≤ 28` is WHIR-admissible at rate `1/2`.
* **`pcsOpeningWithH_proveClaimWithH`** (completeness): every proof the opening prover produces for
  a true claim on an honest commitment is accepted; `pcsOpeningWithH_commitmentWithH`: the same at
  `commitmentWithH`'s tree and commitment.
* **`proveClaimWithH_eq_some_none`**: with the calls answered in `Option`, the opening prover fails
  only at a `17`-bit proof of work at a sponge the honest prover keeps.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Compile.Rom (ProverSp proverSp_absorb squeeze_option)

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Generic facts -/

/-- **A table as WHIR's column** of `2^μ` words: word `x` is the array's, zero past it (the
commitment reads the table with `getD`, `stackWordFast`). -/
def colOf (μ : ℕ) (a : Array K) : Column μ := ⟨Vector.ofFn fun x ↦ a.getD x.val 0⟩

theorem getD_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_colOf (μ : ℕ) (a : Array K) {i : ℕ} (hi : i < 2 ^ μ) :
    (colOf μ a).values.toArray.getD i 0 = a.getD i 0 := by
  simp [colOf, Array.getD_eq_getD_getElem?, hi]

/-- `15 ≤ n ≤ 28` (`minVars`, `maxVars`) is WHIR-admissible at rate `1/2`. -/
theorem admissible_of_vars {n : ℕ} (h : minVars ≤ n ∧ n ≤ maxVars) :
    Whir.Admissible n PcsQuotient.logInvRate := by
  simp only [minVars, maxVars] at h
  simp only [Whir.Admissible, Whir.minLogStack, Whir.maxLogStack, Whir.minLogInvRate,
    Whir.maxLogInvRate, PcsQuotient.logInvRate]
  omega

/-- The out-of-domain point has `n` coordinates. -/
theorem length_oodPointWithH (H : Bytes → Digest) (n : ℕ) (root : Digest) :
    (oodPointWithH (m := Id) H n root).length = n := by
  show (Id.run (List.mapM _ (List.range n))).length = n
  rw [List.idRun_mapM, List.length_map, List.length_range]

/-! ## The weight table -/

/-- Entry `y` of the equality kernel of `p`: `eq(p, bits of y)`. -/
theorem eqKernelA_getD_point (p : List E) {y : ℕ} (hy : y < 2 ^ p.length) :
    (eqKernelA p).getD y 0 = eqEval p (boolPoint p.length y) := by
  rw [Enc.eqKernelA_getD, Whir.Complete.getD_eqKernel _ _ hy, Whir.Complete.eqEval_comm]

theorem dot_powers_two (lam a b : E) : dot (powers lam 2) [a, b] = a + lam * b := by
  simp [powers, powersFrom, dot]

/-- The rotated position `⌊i/64⌋ + 2^(n−6)·(i mod 64)` is on the cube. -/
theorem rot_lt {n i : ℕ} (h6 : 6 ≤ n) (hi : i < 2 ^ n) :
    i / 2 ^ 6 + 2 ^ (n - 6) * (i % 2 ^ 6) < 2 ^ n := by
  have h := Whir.Complete.rotIndex_lt (k := 6) (n := n - 6) (i := i)
    (by rw [show 6 + (n - 6) = n by omega]; exact hi)
  rwa [show n - 6 + 6 = n by omega] at h

/-- **The PCS weight table is the batched weight of the two stack claims on the cube**, in WHIR's
variable order (mumbai's `basisTable`, scales `[1, λ]`). -/
theorem pcsWeightTable_eq {n : ℕ} (h6 : 6 ≤ n) (z : List E) (c : Commitment) (claim : Claim)
    (hz : z.length = n) (hp : claim.point.length = n) (lam : E) :
    (pcsWeightTable n z claim.point lam).toList =
      Whir.Complete.basisTable n (powers lam 2) (pcsStackClaims z c claim) := by
  have hsz : (pcsWeightTable n z claim.point lam).size = 2 ^ n := by simp [pcsWeightTable]
  refine Enc.list_ext_getD (by simp [hsz, Whir.Complete.basisTable]) fun i hi ↦ ?_
  have hi' : i < 2 ^ n := by simpa [hsz] using hi
  have hrot : (boolPoint n i).drop EndToEnd.laneBits ++ (boolPoint n i).take EndToEnd.laneBits =
      boolPoint n (i / 2 ^ 6 + 2 ^ (n - 6) * (i % 2 ^ 6)) := by
    have h := Whir.Complete.boolPoint_rotIndex 6 (n - 6) i
      (by rw [show 6 + (n - 6) = n by omega]; exact hi')
    rw [show 6 + (n - 6) = n by omega, show n - 6 + 6 = n by omega] at h
    exact h.symm
  have hpos := rot_lt h6 hi'
  rw [Enc.toList_getD_E, Whir.Complete.basisTable, Whir.Complete.getD_tableOf _ _ _ hi', hrot]
  simp only [pcsWeightTable, PcsQuotient.laneFold]
  rw [getD_ofFn' _ hi']
  simp only [Whir.Complete.batchedBasis, pcsStackClaims, List.map_cons, List.map_nil,
    dot_powers_two]
  rw [eqKernelA_getD_point z (by rw [hz]; exact hpos),
    eqKernelA_getD_point claim.point (by rw [hp]; exact hpos), hz, hp]

/-! ## The stack claims hold and are multilinear -/

/-- **A table's polynomial at `p` is a true stack claim** of its column, the weight `eq(p, ·)`. -/
theorem holds_eqEval {n : ℕ} (table : Array K) (hsz : table.size = 2 ^ n) (p : List E)
    (hp : p.length = n) :
    EndToEnd.StackClaim.Holds n (fun x ↦ eqEval p x, tableEval table p) (colOf n table) := by
  unfold EndToEnd.StackClaim.Holds tableEval
  rw [mleK_eq, Whir.Complete.multilinearEval_eq_sum n _ _ (by simp [hsz]) hp]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqEval p (boolPoint n x) *
    ofK ((colOf n table).values.getD x 0)) (2 ^ n)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ n := Finset.mem_range.1 hi
  have h1 : (colOf n table).values.getD i 0 = table.getD i 0 := by
    simp [colOf, Vector.getD, Array.getD_eq_getD_getElem?, hi']
  have h2 : (table.toList.map ofK).getD i 0 = ofK (table.getD i 0) := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi', hsz]
  rw [h1, h2, Whir.Complete.eqEval_comm, mul_comm]

/-- **The two stack claims hold** of the table's column, for the table's values at `z` and at the
point. -/
theorem pcsStackClaims_holds {n : ℕ} (table : Array K) (hsz : table.size = 2 ^ n) (z : List E)
    (hz : z.length = n) (c : Commitment) (hood : tableEval table z = c.ood) (claim : Claim)
    (hp : claim.point.length = n) (hval : tableEval table claim.point = claim.value) :
    ∀ sc ∈ pcsStackClaims z c claim, EndToEnd.StackClaim.Holds n sc (colOf n table) := by
  intro sc hsc
  simp only [pcsStackClaims, List.mem_cons, List.mem_nil_iff, or_false] at hsc
  rcases hsc with rfl | rfl
  · have h := holds_eqEval table hsz z hz
    rwa [hood] at h
  · have h := holds_eqEval table hsz claim.point hp
    rwa [hval] at h

/-- **The two stack claims' weights are multilinear.** -/
theorem pcsStackClaims_multilinear {n : ℕ} (z : List E) (hz : z.length = n) (c : Commitment)
    (claim : Claim) (hp : claim.point.length = n) :
    ∀ sc ∈ pcsStackClaims z c claim, EndToEnd.IsMultilinearFn n sc.1 := by
  intro sc hsc
  simp only [pcsStackClaims, List.mem_cons, List.mem_nil_iff, or_false] at hsc
  rcases hsc with rfl | rfl
  · subst hz; exact Whir.Complete.isMultilinearFn_eqEval z
  · subst hp; exact Whir.Complete.isMultilinearFn_eqEval claim.point

/-! ## The script makes the specification's moves -/

/-- The stack table of an array is its column's. -/
theorem stackTableA_colOf {μ : ℕ} (h6 : 6 ≤ μ) (stack : Array K) :
    stackTableA μ stack = stackTableA μ (colOf μ stack).values.toArray := by
  unfold stackTableA
  congr 1
  funext i
  have hi : i.val < 2 ^ (6 + (μ - 6)) := by rw [show 6 + (μ - 6) = μ by omega]; exact i.isLt
  have h := Whir.Complete.rotIndex_lt hi
  rw [show μ - 6 + 6 = μ by omega] at h
  rw [getD_colOf μ stack (show i.val / 2 ^ 6 + 2 ^ (μ - 6) * (i.val % 2 ^ 6) < 2 ^ μ from h)]

theorem toList_stackTableA_colOf {μ : ℕ} (h6 : 6 ≤ μ) (stack : Array K) :
    (stackTableA μ stack).toList = Whir.Complete.stackTable μ (colOf μ stack) := by
  rw [stackTableA_colOf h6, Enc.toList_stackTableA]

/-- **The PCS opening script makes the moves of mumbai's honest opening** of the two stack claims
on the table's column: the same scalars sent and words committed, for every challenge and
opening. -/
theorem corr_pcsOpeningScript {n : ℕ} (h6 : 6 ≤ n) (hμ : n ≤ 64) (table : Array K) (z : List E)
    (c : Commitment) (claim : Claim) (hz : z.length = n) (hp : claim.point.length = n) :
    Corr (fun _ _ ↦ True) (pcsOpeningScript n table z c claim)
      (Whir.Complete.honestOpening n PcsQuotient.logInvRate (colOf n table)
        (pcsStackClaims z c claim)) := by
  simp only [pcsOpeningScript, Whir.Complete.honestOpening]
  refine corrW_sampleE fun lam ↦ ?_
  cases Whir.ladder n PcsQuotient.logInvRate with
  | none => trivial
  | some config =>
    dsimp only
    simp only [Whir.Complete.hWhirRun]
    refine Corr.bind' (corr_roundA' (pcsWeightTable_eq h6 z c claim hz hp lam)
      (toList_stackTableA_colOf h6 table)) fun quad _ hq ↦ ?_
    subst hq
    have := corr_levelsA hμ (Whir.Complete.stackTable n (colOf n table)) config 0
      ⟨dot (powers lam 2) [c.ood, claim.value],
        Whir.Complete.roundQuad (dot (powers lam 2) [c.ood, claim.value])
          (Whir.Complete.basisTable n (powers lam 2) (pcsStackClaims z c claim))
          (Whir.Complete.stackTable n (colOf n table)), [], []⟩
      (pcsWeightTable n z claim.point lam) (stackTableA n table)
      (by rw [toList_stackTableA_colOf h6]; rfl)
    rwa [pcsWeightTable_eq h6 z c claim hz hp] at this

/-- The same, then nothing. -/
theorem corr_pcsOpeningScript_ret {n : ℕ} (h6 : 6 ≤ n) (hμ : n ≤ 64) (table : Array K)
    (z : List E) (c : Commitment) (claim : Claim) (hz : z.length = n)
    (hp : claim.point.length = n) :
    Corr (fun _ _ ↦ True) (pcsOpeningScript n table z c claim)
      ((Whir.Complete.honestOpening n PcsQuotient.logInvRate (colOf n table)
        (pcsStackClaims z c claim)).bind fun _ ↦ Script.ret ()) := by
  rw [← Script.bind_ret (pcsOpeningScript n table z c claim)]
  exact Corr.bind (fun _ _ _ ↦ trivial) _ _ (corr_pcsOpeningScript h6 hμ table z c claim hz hp)

/-! ## The prover is mumbai's compiled honest prover -/

/-- The opening program at an admissible shape: the stack's commitment, then the opening, then
accept. -/
theorem openingProgram_eq {μ R : ℕ} (hw : Whir.Admissible μ R) (sc : List StackClaim) :
    Whir.Complete.openingProgram μ R sc =
      Prog.commit (μ - 6 + R) (2 ^ 6)
        ((verifyStackedOpening μ R sc).bind fun _ ↦ Prog.ret true) := by
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
  simp only [Whir.Complete.openingProgram, commitStack, hc, Verifier.liftOption, Prog.bind_eq,
    Prog.pure_eq, Prog.ret_bind, levelShape, Prog.readCommitment]
  rfl

/-- **A trailing `return` changes no proof**: the runner sees only the moves. -/
theorem runFromWithHash_bind_ret {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (fuel : ℕ) {α β : Type} (b : Bool) :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List LeanVM.Prover.Tree),
      runFromWithHash H F fuel (P.bind fun _ ↦ Prog.ret b) S sp cs =
        runFromWithHash H F fuel P S sp cs := by
  intro P
  induction P with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | sample k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | grind bits k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | commit ht w k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | query i ps k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]

theorem lt_two_pow_add {a b o z : ℕ} (ho : o < 2 ^ a) (hz : z < 2 ^ b) :
    o + 2 ^ a * z < 2 ^ (a + b) := by
  rw [pow_add]
  calc o + 2 ^ a * z < 2 ^ a + 2 ^ a * z := by omega
    _ = 2 ^ a * (z + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left _ hz

/-- The executable stack word reads the array as its column. -/
theorem stackWordFast_colOf {μ : ℕ} (h6 : 6 ≤ μ) (R : ℕ) (a : Array K) :
    stackWordFast μ R a = stackWordFast μ R (colOf μ a).values.toArray := by
  have hb : ∀ {v u : ℕ}, v < 2 ^ (μ - 6) → u < 64 → v + 2 ^ (μ - 6) * u < 2 ^ μ := by
    intro v u hv hu
    have h := lt_two_pow_add (b := 6) hv (show u < 2 ^ 6 from hu)
    rwa [show μ - 6 + 6 = μ by omega] at h
  have hcodes : stackCodes μ R a = stackCodes μ R (colOf μ a).values.toArray := by
    simp only [stackCodes]
    congr 1
    funext u
    congr 2
    funext v
    rw [getD_colOf μ a (hb v.isLt u.isLt)]
  funext p
  simp only [stackWordFast, stackWordFast.stackWordOf]
  rw [hcodes]
  split_ifs with hp
  · rfl
  · apply congrArg List.reverse
    refine List.map_congr_left fun u hu ↦ ?_
    have hfun : (fun x ↦ a.getD (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u) 0) =
        fun x ↦ (colOf μ a).values.toArray.getD
          (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u) 0 :=
      funext fun x ↦
        (getD_colOf μ a (hb (LeanVM.Protocol.Whir.bitsToNat_lt x) (List.mem_range.1 hu))).symm
    rw [hfun]

/-- The opening's sponge starts with nothing pending (the only fact about the seed the proofs
use). -/
theorem pcsSpongeWithH_eta (H : Bytes → Digest) (F : KeccakState → KeccakState) (c : Commitment)
    (claim : Claim) :
    (⟨(pcsSpongeWithH (m := Id) H F c claim).state, []⟩ : Sponge) =
      pcsSpongeWithH (m := Id) H F c claim := rfl

theorem id_bind_eq' {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_pure_eq' {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- **The PCS opening prover is mumbai's compiled honest prover**, at a pure hash `H` and
permutation `F`: from the table's commitment (`commitWithH`), running `pcsOpeningScript` against the
verifier's program from the opening's sponge is `prove` of `openingProgram` (commit the table's
word, open the two stack claims at the root's out-of-domain point, accept) with the honest strategy
`openingProver` of the table's column, seeded with the opening's sponge state. -/
theorem proveClaimWithH_eq_prove (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) {n : ℕ} (hr : minVars ≤ n ∧ n ≤ maxVars) (table : Array K) (c : Commitment)
    (claim : Claim) (hp : claim.point.length = n) :
    proveClaimWithH (m := Id) H F fuel (commitWithH (m := Id) H n table) table c claim =
      Compile.prove H F
        (Whir.Complete.openingProgram n PcsQuotient.logInvRate
          (pcsStackClaims (oodPointWithH (m := Id) H n c.root) c claim))
        (Whir.Complete.openingProver n PcsQuotient.logInvRate (colOf n table)
          (pcsStackClaims (oodPointWithH (m := Id) H n c.root) c claim))
        (pcsSpongeWithH (m := Id) H F c claim).state fuel := by
  have hw := admissible_of_vars hr
  have h6 : 6 ≤ n := by simp only [minVars] at hr; omega
  have hμ : n ≤ 64 := by simp only [maxVars] at hr; omega
  have hz := length_oodPointWithH H n c.root
  have hword : ∀ z : List E, (Whir.Complete.openingProver n PcsQuotient.logInvRate (colOf n table)
      (pcsStackClaims z c claim)).word [] = stackWordFast n PcsQuotient.logInvRate table := by
    intro z
    show Whir.Complete.stackWord _ _ = _
    rw [stackWordFast_colOf h6, Enc.stackWordFast_eq hμ]
  have hrun : ∀ z : List E, z.length = n → ∀ (sp : Sponge) (cs : List LeanVM.Prover.Tree)
      (ht w : ℕ) (W : Word),
      proveFromM (m := Id) H F (Whir.Complete.openingProver n PcsQuotient.logInvRate
          (colOf n table) (pcsStackClaims z c claim)) fuel
        ((verifyStackedOpening n PcsQuotient.logInvRate (pcsStackClaims z c claim)).bind
          fun _ ↦ Prog.ret true) sp [Ev.commit ht w W] cs =
      runFromWithHash (m := Id) H F fuel
        (verifyStackedOpening n PcsQuotient.logInvRate (pcsStackClaims z c claim))
        (some (pcsOpeningScript n table z c claim)) sp cs := by
    intro z hz sp cs ht w W
    have hwalk : Script.walk (Whir.Complete.honestCommitOpening n PcsQuotient.logInvRate
        (colOf n table) (pcsStackClaims z c claim) >>= fun _ ↦ Script.ret ()) [Ev.commit ht w W] =
        some ((Whir.Complete.honestOpening n PcsQuotient.logInvRate (colOf n table)
          (pcsStackClaims z c claim)).bind fun _ ↦ Script.ret ()) := rfl
    rw [Whir.Complete.openingProver, ← runFrom_eq_proveFromM (m := Id) H F fuel _ _ _ sp _ cs hwalk,
      runFromWithHash_bind_ret]
    exact (runFrom_corr (m := Id) H F fuel _
      (corr_pcsOpeningScript_ret h6 hμ table z c claim hz hp) sp cs).symm
  rw [← proveM_id, openingProgram_eq hw]
  simp only [proveM, proveFromM, proveClaimWithH, commitWithH, hword, List.nil_append, hp,
    hrun _ hz, bind_assoc, pure_bind, Option.map_map, pcsSpongeWithH_eta]
  rfl

/-! ## The opening check is the compiled verifier -/

/-- Running a sequence is running its first part, then the rest from the state it leaves (copied
from Bridge-Defs). -/
theorem runWithHash_bind {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) {α β : Type} (P : Prog α) (f : α → Prog β) :
    ∀ s : ProgState, runWithHash H F (P.bind f) s = runWithHash H F P s >>= fun o => match o with
      | some (a, s') => runWithHash H F (f a) s'
      | none => pure none := by
  induction P with
  | ret a => intro s; simp [Prog.bind, runWithHash]
  | fail => intro s; simp [Prog.bind, runWithHash]
  | read k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split <;> simp [ih]
  | sample k ih =>
    intro s
    simp [Prog.bind, runWithHash, ih]
  | grind b k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext sp; congr 1; funext cs
      split <;> simp [ih]
  | commit h w k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp only [bind_assoc]
      congr 1; funext sp0; congr 1; funext sp1
      split <;> simp [ih]
    · simp
  | query i ps k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext o
      split <;> simp [ih]

/-- **The PCS opening check is the compiled verifier of `openingProgram`** from the opening's
sponge, on a proof whose first two scalars encode the commitment's root, for a claim of `n`
variables, `15 ≤ n ≤ 28`. -/
theorem pcsOpeningWithH_eq_runProof (H : Bytes → Digest) (F : KeccakState → KeccakState)
    {n : ℕ} (hr : minVars ≤ n ∧ n ≤ maxVars) (c : Commitment) (claim : Claim)
    (hp : claim.point.length = n) (x0 x1 : E) (rest : List E) (os : List Opening)
    (hd : digestOfScalars (x0, x1) = some c.root) :
    pcsOpeningWithH (m := Id) H F c claim ⟨x0 :: x1 :: rest, os⟩ =
      runProofWithHash (m := Id) H F
        (Whir.Complete.openingProgram n PcsQuotient.logInvRate
          (pcsStackClaims (oodPointWithH (m := Id) H n c.root) c claim))
        (pcsSpongeWithH (m := Id) H F c claim).state ⟨x0 :: x1 :: rest, os⟩ := by
  subst hp
  rw [openingProgram_eq (admissible_of_vars hr)]
  simp only [pcsOpeningWithH, runProofWithHash, runWithHash, hd, hr, and_self, ↓reduceIte,
    runWithHash_bind, List.nil_append, id_bind_eq', id_pure_eq', pcsSpongeWithH_eta,
    show PcsQuotient.laneFold = 6 from rfl, show (2 : ℕ) ^ 6 = 64 from rfl]
  split <;> rename_i h <;> simp [h]

/-! ## Completeness -/

/-- **The PCS opening check accepts every proof the PCS opening prover produces** for a true claim
on an honest commitment, at a pure hash `H` and permutation `F`: a table of `2^n` words,
`15 ≤ n ≤ 28`, committed by `commitWithH`; a commitment `c` with the tree's root and the table's
polynomial at the root's out-of-domain point; a claim of `n` coordinates that the table's
polynomial satisfies. -/
theorem pcsOpeningWithH_proveClaimWithH (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) {n : ℕ} (hr : minVars ≤ n ∧ n ≤ maxVars) (table : Array K)
    (hsz : table.size = 2 ^ n) (c : Commitment)
    (hroot : c.root = (commitWithH (m := Id) H n table).root)
    (hood : tableEval table (oodPointWithH (m := Id) H n c.root) = c.ood) (claim : Claim)
    (hp : claim.point.length = n) (hval : tableEval table claim.point = claim.value)
    {π : Compile.Proof}
    (hπ : proveClaimWithH (m := Id) H F fuel (commitWithH (m := Id) H n table) table c claim =
      some π) :
    pcsOpeningWithH (m := Id) H F c claim π = true := by
  have hw := admissible_of_vars hr
  have hz := length_oodPointWithH H n c.root
  have hholds := pcsStackClaims_holds table hsz _ hz c hood claim hp hval
  have hml := pcsStackClaims_multilinear _ hz c claim hp
  have hacc := runProof_prove H F _ _ _ fuel
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (colOf n table) _ hholds hml chal).1)
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (colOf n table) _ hholds hml chal).2)
    ((proveClaimWithH_eq_prove H F fuel hr table c claim hp).symm.trans hπ)
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hπ
  rw [pcsOpeningWithH_eq_runProof H F hr c claim hp _ _ t.1 t.2
    (by rw [hroot]; exact digestOfScalars_digestScalars _)]
  exact hacc

/-- **Completeness at the commitment `commitmentWithH`**: the proof of a true claim on the honest
commitment (`commitmentWithH`, the Statement's `commit_words`) is accepted. -/
theorem pcsOpeningWithH_commitmentWithH (H : Bytes → Digest)
    (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ} (hr : minVars ≤ n ∧ n ≤ maxVars)
    (table : Array K) (hsz : table.size = 2 ^ n) (claim : Claim) (hp : claim.point.length = n)
    (hval : tableEval table claim.point = claim.value) {π : Compile.Proof}
    (hπ : proveClaimWithH (m := Id) H F fuel (commitmentWithH (m := Id) H n table).1 table
      (commitmentWithH (m := Id) H n table).2 claim = some π) :
    pcsOpeningWithH (m := Id) H F (commitmentWithH (m := Id) H n table).2 claim π = true :=
  pcsOpeningWithH_proveClaimWithH H F fuel hr table hsz _ rfl rfl claim hp hval hπ

/-! ## The prover fails only at a proof of work -/

section Failure

variable {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}

/-- **The script runner fails only at a proof of work** (mumbai's `proveFromM_eq_some_none`, for
`runFromWithHash`): if it fails, with the queries answered in `Option`, along a program whose proofs
of work all have `b` bits, then a `b`-bit search fails at a sponge the honest prover keeps. -/
theorem runFromWithHash_eq_some_none (b fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      EndToEnd.Sound.MovesOK (· = b) True P → ProverSp sp →
      LeanVM.Prover.runFromWithHash H F fuel P S sp cs = some none →
      ∃ sp', ProverSp sp' ∧ findNonceM F b sp' fuel = some none := by
  induction P with
  | ret a => intro S sp cs _ _ hp; cases hp
  | fail => intro S sp cs _ _ hp; cases hp
  | read k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ _ (hm _) (proverSp_absorb hsp hsp') hr
    · cases hp
  | sample k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hr
    exact ih _ _ _ _ (hm _) ⟨by simp, by simp⟩ hp
  | grind bits k ih =>
    intro S sp cs hm hsp hp
    have hb : bits = b := hm.1
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨o, ho, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases o with _ | n
    · subst hb
      exact ⟨sp, hsp, ho⟩
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hsp' : ProverSp r.2 := by
        simp only [powStepM, bind, Option.bind_eq_some_iff] at hr
        obtain ⟨sp', -, hs⟩ := hr
        obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hs
        exact ⟨by simp, by simp⟩
      rcases t with _ | _
      · exact ih _ _ _ hm.2 hsp' ht
      · cases hp
  | commit ht w k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨tree, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp0, h0, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp1, h1, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ hm.2 (proverSp_absorb (proverSp_absorb hsp h0) h1) hr
    · cases hp
  | query i ps k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    split at hp
    · cases hp
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact ih _ _ _ _ (hm _) hsp hr
      · cases hp

/-- The opening's sponge waits for nothing. -/
theorem proverSp_pcsSpongeWithH {c : Commitment} {claim : Claim} {sp : Sponge}
    (h : pcsSpongeWithH H F c claim = some sp) : ProverSp sp := by
  simp only [pcsSpongeWithH] at h
  obtain ⟨iv, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨by simp, by simp⟩

/-- **A PCS opening fails only at a `17`-bit proof of work**, at a sponge the honest prover
keeps, every nonce below `fuel` failing. -/
theorem proveClaimWithH_eq_some_none {fuel : ℕ} {tree : Tree} {table : Array K} {c : Commitment}
    {claim : Claim} (h : proveClaimWithH H F fuel tree table c claim = some none) :
    ∃ sp', ProverSp sp' ∧ findNonceM F Whir.queryGrindingBits sp' fuel = some none := by
  simp only [proveClaimWithH] at h
  obtain ⟨sp₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  rcases r with _ | _
  · exact runFromWithHash_eq_some_none _ fuel _ _ _ _
      (EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _)
      (proverSp_absorb (proverSp_absorb (proverSp_pcsSpongeWithH h₀) h₁) h₂) hr
  · cases h

end Failure

/-! ## Axioms -/

/--
info: 'E2ECompleteness.Pcs.pcsWeightTable_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pcsWeightTable_eq

/--
info: 'E2ECompleteness.Pcs.corr_pcsOpeningScript' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms corr_pcsOpeningScript

/--
info: 'E2ECompleteness.Pcs.proveClaimWithH_eq_prove' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms proveClaimWithH_eq_prove

/--
info: 'E2ECompleteness.Pcs.pcsOpeningWithH_eq_runProof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pcsOpeningWithH_eq_runProof

/--
info: 'E2ECompleteness.Pcs.pcsOpeningWithH_proveClaimWithH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pcsOpeningWithH_proveClaimWithH

/--
info: 'E2ECompleteness.Pcs.pcsOpeningWithH_commitmentWithH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pcsOpeningWithH_commitmentWithH

/--
info: 'E2ECompleteness.Pcs.proveClaimWithH_eq_some_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms proveClaimWithH_eq_some_none

end E2ECompleteness.Pcs
