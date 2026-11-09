-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows
-- `formal/EndToEnd/Soundness/Cost.lean` of this repository (its `allQ_ourVerifier`, and leanerVM
-- `mumbai`'s cost lemmas, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
-- Apache-2.0: `Short`, `hashBlocks_le_of_short`, `isWeightBound_of_isTotalQueryBound`).
import UniSound.FsProof
import Soundness.Cost

/-!
# The composed verifier's calls of `π`

`UniNumbers.verifier` from the rounds' sizes: the composed verifier (the chain over the univariate
encoding, then the five openings) makes at most `nQ + Σ QO` queries, each **short** (at most
`2^39 + 9` bytes, so at most `2^32` calls of `π`): the seed's input is `80` bytes, a step's at most
`32 + 24 + 32 + 24 nv` with `nv ≤ 2^30` scalars a round; an opening's one claim of at most `28`
coordinates (`Soundness.allQ_ourVerifier`). So at most `(2^10 + 5 · 10122) · 2^32 ≤ 2^80`
(**`uniNumbers_of`**).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile WhirBridge UniStatement
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

theorem allQ_hash256 {x : List UInt8} (hx : x.length ≤ 2 ^ 39 + 9) :
    AllQueriesSatisfy (hash256 x) Short :=
  allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH hx) fun _ => LeanVM.Rpm.allQ_pure _

theorem allQ_runM : ∀ (y : List UInt8) (es : List (List UInt8)), y.length ≤ 2 ^ 39 + 9 →
    (∀ e ∈ es, 32 + e.length ≤ 2 ^ 39 + 9) → AllQueriesSatisfy (runM hash256 y es) Short
  | y, [], hy, _ => allQueriesSatisfy_bind (allQ_hash256 hy) fun _ => LeanVM.Rpm.allQ_pure _
  | y, e :: es, hy, he => allQueriesSatisfy_bind (allQ_hash256 hy) fun st =>
      allQueriesSatisfy_bind (allQ_runM (stepIn st e) es (by
        rw [length_stepIn]
        exact he e List.mem_cons_self) fun e' he' => he e' (List.mem_cons_of_mem _ he'))
        fun _ => LeanVM.Rpm.allQ_pure _

theorem isTotalQueryBound_opsRun {Pf F M St : Type} (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (opsRun view ops π ch) (ops.map fun o => o.S.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [opsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.S.queries _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun view os π ch)

theorem allQ_opsRun {Pf F M St : Type} (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      (∀ o ∈ ops, (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30) →
        AllQueriesSatisfy (opsRun view ops π ch) Short
  | [], _, _, _ => trivial
  | o :: os, π, ch, h => by
    simp only [opsRun]
    refine allQueriesSatisfy_bind (Soundness.allQ_ourVerifier _ _ _ (h o List.mem_cons_self).1
      (h o List.mem_cons_self).2) fun _ => ?_
    rw [map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (allQ_opsRun view os π ch fun o' ho' =>
      h o' (List.mem_cons_of_mem _ ho')) fun _ => LeanVM.Rpm.allQ_pure _

theorem mkStmt_length_le (L : WhirBridge.Layout) (hL : L.extra = []) (cs : List WhirBridge.Claim) :
    (mkStmt L hL cs).claims.length ≤ 1 := by
  unfold mkStmt
  split_ifs with h
  · exact h.1
  · simp

theorem length_uniEnc (m : RMsg E) : (uniEnc m).length ≤ 32 + 24 * m.2.length := by
  unfold uniEnc
  split <;> simp

/-- The bytes a step absorbs: at most `24 + 32 + 24 B` for messages of at most `B` scalars. -/
theorem length_mem_absorbsI (s : FSt) (B : ℕ) : ∀ (i : ℕ) (rs : List RoundSpec)
    (ms : List (RMsg E)), (∀ m ∈ ms, m.2.length ≤ B) →
      ∀ e ∈ absorbsI ((uniSpec rs).encAt s) i rs ms, e.length ≤ 24 + 32 + 24 * B
  | _, [], _, _, e, he => by simp [absorbsI] at he
  | i, r :: rs, ms, hm, e, he => by
    simp only [absorbsI, List.mem_cons, List.mem_append, List.mem_replicate] at he
    rcases he with rfl | ⟨-, rfl⟩ | he
    · have hB : (ms.headD (none, [])).2.length ≤ B := by
        rcases ms with _ | ⟨m, ms⟩
        · simp
        · exact hm m List.mem_cons_self
      have h1 := length_uniEnc (ms.headD (none, []))
      have h2 : 24 * (ms.headD (none, [])).2.length ≤ 24 * B := Nat.mul_le_mul_left 24 hB
      unfold ChainSpecU.encAt
      have he : ((uniSpec (r :: rs)).enc (ms.headD (none, []))).length =
          (uniEnc (ms.headD (none, []))).length := rfl
      split_ifs
      · rw [List.length_append]
        have hp : ((uniSpec (r :: rs)).pre s).length = 24 := by
          show s.2.2.toList.length = 24
          simp
        omega
      · omega
    · simp
    · exact length_mem_absorbsI s B (i + 1) rs ms.tail
        (fun m hm' => hm m (List.mem_of_mem_tail hm')) e he

end UniSound

