-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statement is `Fs.lean`'s `UniFinal`;
-- the verifier's batch is `formal/UniStatement`'s `batch` (`CodeBatch.lean`'s `batchPure`).
import UniSound.CodeLink
import UniSound.PendingLink
import UniSound.Final

/-!
# The last link (`UniFinal`): the batch's terminal check with true claims is the last state

**`uniFinal`**: for the identity model whose batch products are the verifier's (`batchProd`: the
`λ^k`-weighted products of each commitment's claim's weight, read on the cube, and its stack
zero-extended to the batch's variables, then `λ³` times the pending matrices' term `Gext · Llift`;
`batchTargetOf` its claimed sum), the verifier's checks on a completed transcript (the terminal
`sum + λ³ value ext + last = 0` collected) with true claims (`ClaimsHold`) make the sumcheck's last
claim the partial sum at its point (`SumState`).

The algebra is `terminal_sumState` (independent of the transcript): the sumcheck's decoded rounds
are `claimAfter`/`pointAfter` (`decodeSC_none`), the full point's partial sum is
`Σ_k λ^k fold(W_k) fold(C_k) + λ³ fold(Gext) fold(Llift)` (`ProdSum.T_full`), each stack's fold is
its point claim times the zero extension (`foldAll_stackExt`), the pending term's is the terminal
(`pendingTerminalLink`).

**Hypotheses** (named, beyond the identity model's batch being the verifier's):

* `WeightMle`: each claim's weight, at the batch's point, is the fold (multilinear extension) of
  its values on the cube. **Not true in every case**: `weightAt` reads a `q_flock` slot term's row on
  `8 + |point|` coordinates, and `combine` replaces a point by a longer one it is a prefix of; when
  the slot terms' point `y(t)` is a prefix of another `C1` point (`w(t)`'s first coordinates, Flock's
  slices' point: a polynomial coincidence in `t`), the row overlaps the selector's coordinates and
  the weight is not multilinear. Outside these `t` (and the ring-switch term's `towerWeightAt`),
  unproved here.
* `LayoutVarsSmall`: the stacks have fewer than `256` variables (a layout word's byte).
* `FlockPendingShaped`: Flock's pending reduction has its shape (`Pending.Shaped`) and the slices.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics Finset FlockSound.Uni

/-! ## The sumcheck's decoded rounds -/

theorem decodeMsg_none_two (c a b : E) : decodeMsg c none [a, b] = roundCoeffs c a b := by
  simp [decodeMsg, roundCoeffs, esum]

/-- The batch's rounds as `claimAfter` reads them. -/
def roundsOf (d : Done) : List (List E × List E) := d.map fun x => (x.1.2, x.2)

/-- **The batching sumcheck's decoded rounds** are `pointAfter`, `claimAfter`. -/
theorem decodeSC_none (c : E) : ∀ (d : Done), (∀ x ∈ d, x.1.2.length = 2) →
    decodeSC c (List.replicate d.length none) d = (pointAfter (roundsOf d), claimAfter c (roundsOf d))
  | [], _ => rfl
  | r :: d, h => by
    obtain ⟨a, b, hab⟩ : ∃ a b, r.1.2 = [a, b] := by
      have h2 := h r (List.mem_cons_self ..)
      match hr : r.1.2, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    simp only [List.length_cons, List.replicate_succ, decodeSC, roundsOf, List.map_cons, pointAfter,
      claimAfter, hab, decodeMsg_none_two, List.getD_cons_zero, List.getD_cons_succ]
    have ih := decodeSC_none (polyEval (roundCoeffs c a b) (r.2.headD 0)) d
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [ih]
    rfl

/-! ## The batch's products and their terminal -/

/-- The batch's claimed sum: `Σ_k λ^k v_k + λ^n claim`. -/
def targetOf (cmb : List (Commitment × Combined)) (lam : E) (p : Flock.Pending) : E :=
  (batchTarget cmb lam).1 + (batchTarget cmb lam).2 * p.claim

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem eq_of_add_eq_zero_char2 {a b : E} (h : a + b = 0) : b = a := by
  linear_combination h - a * two_eq_zero_E

/-- A stack zero-extended folds to its point claim times the zero extension. -/
theorem foldAll_stackExt (c : Stk) (R : ℕ) (r : List E) (hR : R ≤ r.length) :
    foldAll (fun u => if u < 2 ^ R then ofK (c u) else 0) r 0 =
      mleStk c R (r.take R) * cubeEq (r.drop R) (r.length - R) 0 := by
  rw [foldAll_ext r R hR (fun u => ofK (c u))]
  congr 1
  unfold mleStk
  rw [Fin.sum_univ_eq_sum_range (fun x => cubeEq (r.take R) R x * ofK (c x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [cubeEq_take]

theorem layoutOf_vars_le (L : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutOf L c).vars ≤ varsOf L := by
  unfold layoutOf varsOf
  cases h : L.find? (fun x => x.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    simp only [Option.map_some, Option.getD_some]
    have key : ∀ (l : List (Commitment × StackLayout)) (a : ℕ), x ∈ l →
        x.2.vars ≤ (l.map fun y => y.2.vars).foldl max a := by
      intro l
      induction l with
      | nil => intro a h; simp at h
      | cons y l ih =>
        intro a h
        simp only [List.map_cons, List.foldl_cons]
        rcases List.mem_cons.mp h with rfl | h
        · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
            intro l
            induction l with
            | nil => intro b; simp
            | cons z l ih' => intro b; exact (le_max_left b z).trans (ih' _)
          exact (le_max_right a x.2.vars).trans (this _ _)
        · exact ih _ h
    exact key L 0 hx

/-! ## Completed transcripts -/

theorem doneFits_append_split : ∀ (a b : List Compose.RoundSpec) (d : Done), DoneFits (a ++ b) d →
    ∃ d1 d2, d = d1 ++ d2 ∧ DoneFits a d1 ∧ DoneFits b d2
  | [], b, d, h => ⟨[], d, rfl, trivial, h⟩
  | s :: a, b, [], h => by simp [DoneFits] at h
  | s :: a, b, x :: d, h => by
    simp only [List.cons_append, DoneFits] at h
    obtain ⟨d1, d2, rfl, h1, h2⟩ := doneFits_append_split a b d h.2.2
    exact ⟨x :: d1, d2, rfl, ⟨h.1, h.2.1, h1⟩, h2⟩

theorem doneFits_length : ∀ (a : List Compose.RoundSpec) (d : Done), DoneFits a d → d.length = a.length
  | [], [], _ => rfl
  | _ :: a, _ :: d, h => by simp only [List.length_cons, doneFits_length a d h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem doneFits_replicate_two : ∀ (n : ℕ) (d : Done), DoneFits (List.replicate n ⟨false, 2, 0⟩) d →
    ∀ x ∈ d, x.1.2.length = 2
  | 0, [], _ => by simp
  | n + 1, x :: d, h => by
    simp only [List.replicate_succ, DoneFits] at h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1.2
    · exact doneFits_replicate_two n d h.2.2 y hy
  | 0, _ :: _, h => h.elim
  | _ + 1, [], h => h.elim

theorem doneFits_noRoot_eq : ∀ (rs : List Compose.RoundSpec) (d : Done), (∀ s ∈ rs, s.root = false) →
    DoneFits rs d → d.map (fun y => (((none : Option (E × E)), y.1.2), y.2)) = d
  | [], [], _, _ => rfl
  | s :: rs, y :: d, hr, h => by
    simp only [DoneFits] at h
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    have hy : y.1.1 = none := by
      have h1 := h.1.1
      rw [hs] at h1
      exact Option.not_isSome_iff_eq_none.mp (by simp [h1])
    simp only [List.map_cons, doneFits_noRoot_eq rs d (fun s hs => hr s (List.mem_cons_of_mem _ hs)) h.2.2]
    rw [← hy]

/-! ## The layout words -/

/-- **The stacks have fewer than `256` variables** (a layout word carries them in one byte). -/
def LayoutVarsSmall (D : Deployment) : Prop := ∀ c, (layoutOf (layoutsOf D.shape) c).vars < 256

theorem layoutWordVars_layoutWord (s : Shape) (code vars placed : ℕ) (h : vars < 256) :
    layoutWordVars (layoutWord s code vars placed) = vars := by
  simp only [layoutWordVars, layoutWord, shapeBytes, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range,
    List.length_replicate, List.length_nil]
  simp [Nat.mod_eq_of_lt h]

theorem layoutWords_word (s : Shape) (c : Commitment) :
    (layoutWords s).getD (wordIndex c) [] =
      layoutWord s (layoutCode c) (layoutOf (layoutsOf s) c).vars (layoutOf (layoutsOf s) c).words := by
  cases c <;> rfl

theorem claimVars (D : Deployment) (hsmall : LayoutVarsSmall D) (c : Commitment) :
    layoutWordVars ((layoutWords D.shape).getD (wordIndex c) []) = (layoutOf (layoutsOf D.shape) c).vars := by
  rw [layoutWords_word, layoutWordVars_layoutWord _ _ _ _ (hsmall c)]

theorem matrixWordVars (s : Shape) :
    layoutWordVars ((layoutWords s).getD 3 []) = matrixVars ∧
      layoutWordVars ((layoutWords s).getD 4 []) = matrixVars :=
  ⟨layoutWordVars_layoutWord _ _ _ _ (by decide), layoutWordVars_layoutWord _ _ _ _ (by decide)⟩

theorem varsOf_ge (s : Shape) : 15 ≤ varsOf (layoutsOf s) := by
  have h := layoutOf_vars_le (layoutsOf s) .c1
  have h1 : 15 ≤ (layoutOf (layoutsOf s) .c1).vars := by
    show 15 ≤ (StackLayout.new _).vars
    exact le_max_right _ _
  omega

/-! ## The identity model's batch, and the hypotheses -/

/-! ## The last link -/

theorem map_zipIdx_fst {α β : Type} (f : α → β) : ∀ (l : List α) (k : ℕ),
    (l.zipIdx k).map (fun x => f x.1) = l.map f
  | [], _ => rfl
  | x :: l, k => by simp only [List.zipIdx_cons, List.map_cons, map_zipIdx_fst f l (k + 1)]

theorem brOf_openedOf (nF : ℕ) (c1 c2 : Stk) (pre brs : Done) (h : pre.length = nF + 3) :
    brOf nF (openedOf nF c1 c2 (pre ++ brs)) = roundsOf brs := by
  unfold brOf openedOf roundsOf
  rw [List.zipIdx_append, List.map_append, List.drop_append_of_le_length (by simp; omega),
    List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
  simp only [List.map_map, Function.comp_def]
  exact map_zipIdx_fst (fun y : UMsg × List E => (y.1.2, y.2)) brs _

/-! ## The end theorem with the code-level links in place -/

end UniSound
