-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniKeccak`'s `batchK`
-- (`Verifier.lean`); the proof is `formal/UniSound/UniSound/CodeBatch.lean`'s `batch_eq`, without the pending
-- matrices.
import UniKeccakSound.Code.Shape

/-!
# The Keccak verifier's batching sumcheck as reads, draws and a result

**`batchK_eq`**: at the main line's Fiat–Shamir shape, `batchK` is `λ`, the sumcheck's `varsOf layouts` rounds of two
scalars and a challenge (`readRounds`), the stacks' values (`combined.length` scalars), the terminal zero
`sum + last`, and the result: each a function of what was read and drawn (`batchPureK`). No pending matrices, no
bit-slice claim, each claim's weight `weightAtK`.
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-- The batch's terminal fold over the stacks on the Keccak VM: `Σ_k λ^k W_k(r) ext_k(r) v_k` (`weightAtK`), `λ^n`,
the point claims. -/
def batchFoldK (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (r : List E) (values : List E) :
    E × E × Array (Commitment × Opening) :=
  (combined.zip values).foldl
    (fun acc x =>
      (acc.1 + acc.2.1 * weightAtK x.1.2 (layoutOf layouts x.1.1) r ringMap *
          (List.range' (layoutOf layouts x.1.1).vars (varsOf layouts - (layoutOf layouts x.1.1).vars)).foldl
            (fun e j => e * (1 + r.getD j 0)) 1 * x.2,
        acc.2.1 * lambda,
        acc.2.2.push (x.1.1, .point (r.take (layoutOf layouts x.1.1).vars) x.2 none)))
    (0, 1, #[])

/-- **What the Keccak batch computes** from `λ`, its rounds `brs` and the stacks' values `tl`: the zero it collects
(the terminal `sum + last`) and its point claims. -/
def batchPureK (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (brs : Done) (tl : List E) :
    List E × List (Commitment × Opening) :=
  let sc := decodeSC (batchTarget combined lambda).1 (List.replicate (varsOf layouts) none) brs
  let fo := batchFoldK combined layouts ringMap lambda sc.1 tl
  ([fo.1 + sc.2], fo.2.2.toList)

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The Keccak batch at the main line's shape**: `λ`, the rounds, the values, the terminal zero, the result. -/
theorem batchK_eq (P : KeccakState → m KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    batchK P .main combined layouts ringMap = (do
      let lambda ← sample P
      let brs ← readRounds P (List.replicate (varsOf layouts) ⟨false, 2, 0⟩)
      let tl ← nextScalars (m := m) combined.length
      ChainProg.requireZeros (batchPureK combined layouts ringMap lambda brs tl).1
      pure (batchPureK combined layouts ringMap lambda brs tl).2) := by
  unfold batchK
  simp only [FsShape.narrow, sumcheckDrawn_false, sumcheck_eq, sumcheckR_eq, List.length_replicate]
  congr 1
  funext lambda
  rw [bind_map_left]
  congr 1
  funext brs
  congr 1
  funext values
  simp [batchPureK, batchFoldK, batchTarget, layoutOf, varsOf, ChainProg.requireZeros]

end Monad

end UniKeccakSound
