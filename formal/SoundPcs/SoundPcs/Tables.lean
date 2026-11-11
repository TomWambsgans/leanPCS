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
* **`assemble_claims`**: the claims on the quotient table's three parts (`PcsBridge.newClaims`: `H` at its point
  and at the sum point, `Q`, `G`) give `reduce`'s two claims on the assembled table (`PcsBridge.assemble`,
  `mle_assemble`), when no denominator vanishes.
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

/-- **The certified lists of the four commitments** at `2^22` rows: `W` and `G` (`25` variables) `7908`, `H`
(`27`) `4473`, `Q` (`28`) `3564`. -/
theorem listHi_parts :
    (Whir.Params.certOf 25 logInvRate 0).listHi = 7908 ∧
      (Whir.Params.certOf 27 logInvRate 0).listHi = 4473 ∧
      (Whir.Params.certOf 28 logInvRate 0).listHi = 3564 := by
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

theorem getD_replicate_fun {m : ℕ} (a : E) :
    (fun k : Fin m => (List.replicate m a).getD k 0) = fun _ : Fin m => a := by
  funext k
  simp [List.getD_eq_getElem?_getD, k.isLt]

open Reduce in
/-- The quotient point's coordinates below `m + 2`: `w_k(t)` times the `k`-th inverse. -/
theorem quotient_point_getD_lt (c : Consts) (m : ℕ) (S : Fin 4 → E) (α β γ t ρ : E) (A : Fin 4 → E)
    (next : E) {k : ℕ} (hk : k < m + 2) :
    (claimsOf c m S α β γ t A next ρ).quotient.point.getD k 0 =
      wChain t k * inverses c m α β t A next k := by
  rw [quotient_point_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_map, List.getElem?_range hk]

open Reduce in
theorem quotient_point_getD_at (c : Consts) (m : ℕ) (S : Fin 4 → E) (α β γ t ρ : E) (A : Fin 4 → E)
    (next : E) (i : ℕ) :
    (claimsOf c m S α β γ t A next ρ).quotient.point.getD (m + 2 + i) 0 =
      [wChain t m * inverses c m α β t A next (m + 2), ρ, extension.1.1, extension.1.2].getD i 0 := by
  rw [quotient_point_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
    List.getD_eq_getElem?_getD]
  simp

/-! ## The quotient table from its parts -/

open Reduce PcsBridge in
/-- **The parts' claims give `reduce`'s claims on the assembled table.** If no denominator vanishes, and the
parts' tables satisfy the claims `PcsBridge.newClaims` makes of `reduce`'s (`H`'s at its point and at the sum
point, `Q`'s and `G`'s at theirs), then the table assembled from them (`PcsBridge.assemble`) satisfies `reduce`'s
quotient claim and its sum claim. -/
theorem assemble_claims (S : Fin 4 → E) (α β γ t ρ : E) (A : Fin 4 → E) (next qv gv : E)
    (hnz : (denominators statementConsts 24 α β t A next).prod ≠ 0)
    (hp : product statementConsts α β t A next ≠ 0) (hρ : 1 + ρ ≠ 0)
    (cH : (Fin (24 + 1 + 1 + 1) → Bool) → E) (cQ : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E)
    (cG : (Fin (24 + 1) → Bool) → E)
    (hH : mle cH (fun k => (newClaims (claimsOf statementConsts 24 S α β γ t A next ρ)
      (hInvOf α β t ρ A next) qv gv).h.point.getD k 0) =
      (newClaims (claimsOf statementConsts 24 S α β γ t A next ρ) (hInvOf α β t ρ A next) qv gv).h.value)
    (hQ : mle cQ (fun k => (newClaims (claimsOf statementConsts 24 S α β γ t A next ρ)
      (hInvOf α β t ρ A next) qv gv).q.point.getD k 0) = qv)
    (hG : mle cG (fun k => (newClaims (claimsOf statementConsts 24 S α β γ t A next ρ)
      (hInvOf α β t ρ A next) qv gv).g.point.getD k 0) = gv)
    (hS : mle cH (fun k => (newClaims (claimsOf statementConsts 24 S α β γ t A next ρ)
      (hInvOf α β t ρ A next) qv gv).sum.point.getD k 0) =
      (claimsOf statementConsts 24 S α β γ t A next ρ).sum.value) :
    mle (assemble cH cQ cG) (fun k => (claimsOf statementConsts 24 S α β γ t A next ρ).quotient.point.getD k 0) =
        (claimsOf statementConsts 24 S α β γ t A next ρ).quotient.value ∧
      mle (assemble cH cQ cG) (fun k => (claimsOf statementConsts 24 S α β γ t A next ρ).sum.point.getD k 0) =
        (claimsOf statementConsts 24 S α β γ t A next ρ).sum.value := by
  set r := claimsOf statementConsts 24 S α β γ t A next ρ with hr
  set P := r.quotient.point with hP
  have hlen : P.length = 30 := by simp [hP, hr, quotient_point_eq]
  have two : ∀ x : E, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  -- The quotient claim.
  have hTpt : (fun k : Fin (24 + 1 + 1 + 1 + 1 + 1 + 1) => P.getD k 0) =
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (fun k : Fin 24 => P.getD k 0)
        (P.getD 24 0)) (P.getD 25 0)) (P.getD 26 0)) (P.getD 27 0)) (P.getD 28 0)) (P.getD 29 0) := by
    rw [getD_fun_succ, getD_fun_succ, getD_fun_succ, getD_fun_succ, getD_fun_succ, getD_fun_succ]
  have hpts : (newClaims r (hInvOf α β t ρ A next) qv gv).h.point =
        P.take 24 ++ [P.getD 24 0, P.getD 28 0, P.getD 29 0] ∧
      (newClaims r (hInvOf α β t ρ A next) qv gv).q.point =
        P.take 24 ++ [P.getD 24 0, P.getD 25 0, P.getD 28 0, P.getD 29 0] ∧
      (newClaims r (hInvOf α β t ρ A next) qv gv).g.point = P.take 24 ++ [P.getD 24 0] := by
    exact ⟨rfl, rfl, rfl⟩
  have hl24 : (P.take 24).length = 24 := by simp [hlen]
  have hHpt : (fun k : Fin (24 + 1 + 1 + 1) =>
      (P.take 24 ++ [P.getD 24 0, P.getD 28 0, P.getD 29 0]).getD k 0) =
      Fin.snoc (Fin.snoc (Fin.snoc (fun k : Fin 24 => P.getD k 0) (P.getD 24 0)) (P.getD 28 0))
        (P.getD 29 0) := by
    rw [show P.take 24 ++ [P.getD 24 0, P.getD 28 0, P.getD 29 0] =
        ((P.take 24 ++ [P.getD 24 0]) ++ [P.getD 28 0]) ++ [P.getD 29 0] by simp,
      getD_snoc_fun (n := 24 + 1 + 1) _ (by simp [hl24]),
      getD_snoc_fun (n := 24 + 1) _ (by simp [hl24]), getD_snoc_fun (n := 24) _ hl24, getD_take_fun]
  have hQpt : (fun k : Fin (24 + 1 + 1 + 1 + 1) =>
      (P.take 24 ++ [P.getD 24 0, P.getD 25 0, P.getD 28 0, P.getD 29 0]).getD k 0) =
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (fun k : Fin 24 => P.getD k 0) (P.getD 24 0))
        (P.getD 25 0)) (P.getD 28 0)) (P.getD 29 0) := by
    rw [show P.take 24 ++ [P.getD 24 0, P.getD 25 0, P.getD 28 0, P.getD 29 0] =
        (((P.take 24 ++ [P.getD 24 0]) ++ [P.getD 25 0]) ++ [P.getD 28 0]) ++ [P.getD 29 0] by simp,
      getD_snoc_fun (n := 24 + 1 + 1 + 1) _ (by simp [hl24]),
      getD_snoc_fun (n := 24 + 1 + 1) _ (by simp [hl24]),
      getD_snoc_fun (n := 24 + 1) _ (by simp [hl24]), getD_snoc_fun (n := 24) _ hl24, getD_take_fun]
  have hGpt : (fun k : Fin (24 + 1) => (P.take 24 ++ [P.getD 24 0]).getD k 0) =
      Fin.snoc (fun k : Fin 24 => P.getD k 0) (P.getD 24 0) := by
    rw [getD_snoc_fun (n := 24) _ hl24, getD_take_fun]
  rw [hpts.1, hHpt] at hH
  rw [hpts.2.1, hQpt] at hQ
  rw [hpts.2.2, hGpt] at hG
  -- The `H` weight times `hInv` is one.
  have hd := prod_denominators_ne_zero hnz
  have h25 : 1 + sq^[25] t ≠ 0 := hd.1 25 (by norm_num)
  have hc := hd.2.1
  have hP25 : P.getD 25 0 = sq^[25] t * (1 + sq^[25] t)⁻¹ := by
    rw [hP, hr, quotient_point_getD_lt _ _ _ _ _ _ _ _ _ _ (by norm_num : 25 < 24 + 2), inverses,
      getD_denominators_lt _ _ _ _ _ _ _ (by norm_num : 25 < 24 + 2), wChain_eq]
  have hP26 : P.getD 26 0 = sq^[24] t * (product statementConsts α β t A next + sq^[24] t)⁻¹ := by
    rw [hP, hr, show (26 : ℕ) = 24 + 2 + 0 from rfl, quotient_point_getD_at]
    simp only [List.getD_cons_zero, inverses, getD_denominators_copy, wChain_eq]
  have hP27 : P.getD 27 0 = ρ := by
    rw [hP, hr, show (27 : ℕ) = 24 + 2 + 1 from rfl, quotient_point_getD_at]
    simp
  have hinv : hInvOf α β t ρ A next = (1 + sq^[25] t) *
      (product statementConsts α β t A next + sq^[24] t) *
      (product statementConsts α β t A next)⁻¹ * (1 + ρ)⁻¹ := by
    simp only [hInvOf, wChain_eq]
  have hwH : (1 + P.getD 25 0) * (1 + P.getD 26 0) * (1 + P.getD 27 0) * hInvOf α β t ρ A next = 1 := by
    rw [hP25, hP26, hP27, hinv]
    have e1 : 1 + sq^[25] t * (1 + sq^[25] t)⁻¹ = (1 + sq^[25] t)⁻¹ := by
      field_simp
      linear_combination two (sq^[25] t)
    have e2 : 1 + sq^[24] t * (product statementConsts α β t A next + sq^[24] t)⁻¹ =
        product statementConsts α β t A next * (product statementConsts α β t A next + sq^[24] t)⁻¹ := by
      field_simp
      linear_combination two (sq^[24] t)
    rw [e1, e2]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hTpt, mle_assemble, hH, hQ, hG]
    simp only [newClaims, PcsQuotient.quotientParts, hP, Nat.add_zero, Nat.reduceAdd]
    linear_combination (r.quotient.value + P.getD 26 0 * (1 + P.getD 27 0) * qv +
      (1 + P.getD 25 0) * (1 + P.getD 26 0) * P.getD 27 0 * (1 + P.getD 28 0) * (1 + P.getD 29 0) * gv) *
      hwH + two (P.getD 26 0 * (1 + P.getD 27 0) * qv) +
      two ((1 + P.getD 25 0) * (1 + P.getD 26 0) * P.getD 27 0 * (1 + P.getD 28 0) * (1 + P.getD 29 0) * gv)
  · -- The sum claim: at the sum point, only `H` remains.
    have hSpt : (fun k : Fin (24 + 1 + 1 + 1 + 1 + 1 + 1) => r.sum.point.getD k 0) =
        Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (fun _ : Fin 24 => (1 : E)) 0) 0) 0) 0)
          extension.1.1) extension.1.2 := by
      rw [hr, sum_point_eq, show Reduce.sumPoint 24 = (((((List.replicate 24 (1 : E) ++ [0]) ++ [0]) ++ [0]) ++
          [0]) ++ [extension.1.1]) ++ [extension.1.2] by simp [Reduce.sumPoint],
        getD_snoc_fun (n := 24 + 1 + 1 + 1 + 1 + 1) _ (by simp),
        getD_snoc_fun (n := 24 + 1 + 1 + 1 + 1) _ (by simp),
        getD_snoc_fun (n := 24 + 1 + 1 + 1) _ (by simp), getD_snoc_fun (n := 24 + 1 + 1) _ (by simp),
        getD_snoc_fun (n := 24 + 1) _ (by simp), getD_snoc_fun (n := 24) _ (by simp), getD_replicate_fun]
    have hHs : (fun k : Fin (24 + 1 + 1 + 1) =>
        (newClaims r (hInvOf α β t ρ A next) qv gv).sum.point.getD k 0) =
        Fin.snoc (Fin.snoc (Fin.snoc (fun _ : Fin 24 => (1 : E)) 0) extension.1.1) extension.1.2 := by
      rw [show (newClaims r (hInvOf α β t ρ A next) qv gv).sum.point = PcsQuotient.sumPoint 22 from rfl,
        ClaimsAux.sumPoint_eq, show List.replicate 24 (1 : E) ++ [0, extension.1.1, extension.1.2] =
          ((List.replicate 24 (1 : E) ++ [0]) ++ [extension.1.1]) ++ [extension.1.2] by simp,
        getD_snoc_fun (n := 24 + 1 + 1) _ (by simp), getD_snoc_fun (n := 24 + 1) _ (by simp),
        getD_snoc_fun (n := 24) _ (by simp), getD_replicate_fun]
    rw [hHs] at hS
    rw [hSpt, mle_assemble, hS]
    ring

end SoundPcs
