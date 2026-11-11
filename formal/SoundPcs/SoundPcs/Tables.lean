-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Claims,Decoder}.lean` of this repository (`tabEval_eq_mle`, `tableCode`,
-- `mem_tableCode_dec`) to the EIP's PCS claims, whose committed stack is the table itself (version 1's
-- `stacking n`); uses leanerVM `mumbai`'s cube-point lemmas (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a0, MIT OR Apache-2.0): `bitsEquiv`, `bitsEquiv_val`, `boolPoint_bitsToNat`, `eqEval_bitsL`,
-- `eqEval_comm`.
import SoundPcs.Stages

/-!
# The committed tables, as F1 reads them

Version 1's PCS commits a table of `n` variables as itself (`WhirBridge.Pcs.stacking`): a candidate of a root is a
column `q : Column n`, and a claim holds of it when its polynomial `colEval q` has the value at the point.

* **`colFn`**, **`colEval_eq_mle`**: a column read as F1 reads tables (`c b` the entry whose index has bits `b`);
  its polynomial at a point of `n` coordinates is F1's `mle` of it;
* **`colCode n hw read`**: the `TableCode` of a committed table of `n` variables at rate `1/2` (Merkle height
  `rootHeight`, leaves of `8 · 64` bytes, the certified list bound, the computable decoder `decodeColumns` of the
  Merkle word, each column read by `read`); **`mem_colCode_dec`**: through injective answers, the reads of exactly
  the candidates of mumbai's `extract` of the root;
* `listHi_choose_24`, `listHi_28`: the certified lists at `24` and `28` variables.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

namespace SoundPcs

open Compose QuotientSecurity LeanVM LeanVM.Protocol LeanVM.Parameters LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd WhirBridge WhirBridge.Pcs Finset

/-! ## A column as F1 reads it -/

/-- A column's entries as F1's tables read them: the entry whose index has bits `b`, in `E`. -/
def colFn {n : ℕ} (q : Column n) : (Fin n → Bool) → E :=
  tabFn (v := n) q.values

theorem getD_values {n : ℕ} (q : Column n) (i : Fin (2 ^ n)) :
    q.values.getD i 0 = (q.values : Vector K (2 ^ n))[i] := by
  simp [Vector.getD, i.isLt]

/-- **A column's polynomial is F1's `mle`**: at a point of `n` coordinates, `colEval q` is `mle` of its entries at
the point's coordinates. -/
theorem colEval_eq_mle {n : ℕ} (q : Column n) (p : List E) (hp : p.length = n) :
    colEval q p = mle (colFn q) (fun k => p.getD k 0) := by
  unfold colEval mle colFn tabFn
  rw [← Equiv.sum_comp (Whir.bitsEquiv n)]
  refine sum_congr rfl fun b _ => ?_
  rw [getD_values, mul_comm]
  refine congrArg (ofK (q.values : Vector K (2 ^ n))[Whir.bitsEquiv n b] * ·) ?_
  rw [Whir.bitsEquiv_val, Whir.Sound.boolPoint_bitsToNat, Whir.Sound.eqEval_bitsL p hp]
  refine prod_congr rfl fun k _ => ?_
  cases b k <;> simp [CharTwo.sub_eq_add]

/-! ## The table code of a committed table -/

/-- **The table code of a committed table of `n` variables** at rate `1/2`: the Merkle tree of level 0, the
certified list bound, and the decoder: the candidates of the Merkle word (`decodeColumns`), each read by
`read`. -/
def colCode (n : ℕ) (hw : Whir.Admissible n logInvRate) {M : Type} (read : Column n → M) : TableCode M where
  height := rootHeight n logInvRate
  leafLen := leafBytes
  bound := (Whir.Params.certOf n logInvRate 0).listHi
  dec w := (decodeColumns n logInvRate (wordOfMerkle (rootHeight n logInvRate) (2 ^ laneFold) w)).map read
  length_dec w := by
    rw [List.length_map]
    exact length_decodeColumns_le hw _

theorem colCode_dec (n : ℕ) (hw : Whir.Admissible n logInvRate) {M : Type} (read : Column n → M)
    (w : Fin (2 ^ rootHeight n logInvRate) → Option (List UInt8)) :
    (colCode n hw read).dec w =
      (decodeColumns n logInvRate (wordOfMerkle (rootHeight n logInvRate) (2 ^ laneFold) w)).map read := by
  simp only [colCode]

/-- **What the table code decodes, under a root**: with the answers injective on the history, the reads of the
candidates of mumbai's `extract` of the root. -/
theorem mem_colCode_dec {n : ℕ} (hw : Whir.Admissible n logInvRate) {M : Type} (read : Column n → M)
    {H : QuotientRpm.Hist} {T : QuotientRpm.Table} (hinj : Set.InjOn T ↑H) (D : Digest) (g : M) :
    g ∈ (colCode n hw read).dec (merkleWord H T (rootHeight n logInvRate) leafBytes (toB D)) ↔
      ∃ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
          (Rom.extract (ansOf H T) D (rootHeight n logInvRate) (2 ^ laneFold)), read q = g := by
  rw [colCode_dec, List.mem_map]
  simp only [mem_decodeColumns hw, candidates_wordOfMerkle hinj]

/-- **What a committed table's list commitment holds**, through injective answers: the reads of the candidates of
mumbai's `extract` of the root. -/
theorem mem_cands_colCode {n : ℕ} (hw : Whir.Admissible n logInvRate) {M : Type} (read : Column n → M)
    {H : QuotientRpm.Hist} {T : QuotientRpm.Table} (hinj : Set.InjOn T ↑H) (r : QuotientRpm.Bytes32) (g : M) :
    g ∈ (colCode n hw read).commit.cands H T r ↔
      ∃ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
          (Rom.extract (ansOf H T) (ofB r) (rootHeight n logInvRate) (2 ^ laneFold)), read q = g := by
  have key : ∀ D : Digest, toB D = r → (g ∈ (colCode n hw read).commit.cands H T r ↔
      ∃ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
        (Rom.extract (ansOf H T) D (rootHeight n logInvRate) (2 ^ laneFold)), read q = g) := by
    intro D hD
    subst hD
    exact mem_colCode_dec hw read hinj D g
  exact key (ofB r) (LeanVM.Rpm.digestToRpm_ofRpm r)

theorem colCode_bound (n : ℕ) (hw : Whir.Admissible n logInvRate) {M : Type} (read : Column n → M) :
    (colCode n hw read).commit.bound = (Whir.Params.certOf n logInvRate 0).listHi := rfl

/-- **The certified lists of the two commitments' sizes** at `2^22` rows: `W` and the wiring (`24` variables), `T`
(`28`). -/
theorem listHi_choose_24 :
    (Whir.Params.certOf 24 logInvRate 0).listHi * ((Whir.Params.certOf 24 logInvRate 0).listHi - 1) / 2 ≤
      2 ^ 27 := by
  decide +kernel

theorem listHi_28 : (Whir.Params.certOf 28 logInvRate 0).listHi = 3564 := by
  decide +kernel

/-! ## Points -/

theorem getD_fun_succ {m : ℕ} (l : List E) :
    (fun k : Fin (m + 1) => l.getD k 0) = Fin.snoc (fun k : Fin m => l.getD k 0) (l.getD m 0) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k <;> simp

theorem getD_take_fun {m : ℕ} (P : List E) :
    (fun k : Fin m => (P.take m).getD k 0) = fun k : Fin m => P.getD k 0 := by
  funext k
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt k.isLt]

end SoundPcs
