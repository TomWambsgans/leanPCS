-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Chain.lean` (`label_eq`, `scalarBytes_eq`,
-- `rootScalars_eq`, `reduceWith_eq`: the old reduction's chain is F4's) and `formal/EndToEnd/Soundness/Defs.lean`
-- (`deployedWire`, `countEnc`), at commit abe22812, to the four commitments of the EIP's PCS claims
-- (`formal/ComposePcs`, `chainWith4`).
import Soundness.PcsOpenBridge
import E2ECompleteness.PcsStaging

/-!
# The Statement's reduction is the four-root chain

* **the wire** (`pcsWire I`): the statement's 64 bytes read as their halves then `1, 0, 0, 0` (`stmtWords`), a
  field element held as its three limbs, low first (`eLimbs`: the Statement's `scalarBytes` and `challengeOf`);
  its index root and encodings, which the four-root chain does not read, any;
* **the bytes**: the label (`label_eq4`: the tag, the circuit's root, its out-of-domain answer as 24 bytes, the
  statement), a root's two scalars (`halfWords_eq_scalars`: the half-words of the root two scalars name are their
  words), a scalar's word (`word_eq`), a state's challenge (`chal_eq`);
* **`reduceWithH_eq_chain4`**: on a proof whose four roots' scalars name digests, the Statement's reduction with
  Keccak-256 `H` (in any lawful monad) hashes exactly what `ComposePcs.chainWith4` hashes, in the same order, and
  returns the commitments and `claimsAt` at its challenges.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace PcsKS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientRpm QuotientSecurity Compose ComposePcs PcsQuotient PcsQuotient.Transcript

/-! ## The wire -/

/-- A countable type's injective encoding as bytes (a run of zeros as long as its index). -/
noncomputable def countEnc (α : Type) [Countable α] : α → List UInt8 :=
  fun a => List.replicate ((Countable.exists_injective_nat α).choose a) 0

theorem countEnc_injective (α : Type) [Countable α] : Function.Injective (countEnc α) := by
  intro a b h
  have := congrArg List.length h
  simp only [countEnc, List.length_replicate] at this
  exact (Countable.exists_injective_nat α).choose_spec this

/-- Polynomials of degree at most `n` agree when their coefficients up to `n` do. -/
theorem poly_eq_of_coeff {p q : Polynomial E} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n + 1), p.coeff i = q.coeff i) : p = q := by
  refine Polynomial.ext fun k => ?_
  by_cases hk : k ≤ n
  · exact h ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- A first message within the bounds is its coefficients up to the bound: finitely many. -/
instance finite_msg₁ {P : Params E} (B : P.Bounds) : Finite B.Msg₁ := by
  refine Finite.of_injective
    (fun g : B.Msg₁ => fun (j : Fin 4) (i : Fin (B.witness + 1)) => (g.1 j).coeff i) ?_
  intro g g' hg
  exact Subtype.ext (funext fun j => poly_eq_of_coeff (g.2 j) (g'.2 j)
    fun i => congrFun (congrFun hg j) i)

/-- A second message within the bounds is its five polynomials' coefficients up to the bound. -/
instance finite_msg₂ {P : Params E} (B : P.Bounds) : Finite B.Msg₂ := by
  refine Finite.of_injective
    (fun R : B.Msg₂ => fun (i : Fin (B.quotient + 1)) =>
      (R.1.h₀.coeff i, R.1.hHigh.coeff i, R.1.q.coeff i, R.1.qGate.coeff i, R.1.junk.coeff i)) ?_
  intro R R' hR
  obtain ⟨⟨h₀, hHigh, q, qGate, junk⟩, b₁, b₂, b₃, b₄, b₅⟩ := R
  obtain ⟨⟨h₀', hHigh', q', qGate', junk'⟩, b₁', b₂', b₃', b₄', b₅'⟩ := R'
  have e := fun i => congrFun hR i
  simp only [Prod.mk.injEq] at e
  refine Subtype.ext ?_
  simp only [Params.Quotients.mk.injEq]
  exact ⟨poly_eq_of_coeff b₁ b₁' fun i => (e i).1, poly_eq_of_coeff b₂ b₂' fun i => (e i).2.1,
    poly_eq_of_coeff b₃ b₃' fun i => (e i).2.2.1, poly_eq_of_coeff b₄ b₄' fun i => (e i).2.2.2.1,
    poly_eq_of_coeff b₅ b₅' fun i => (e i).2.2.2.2⟩

/-- **The deployed wire** for F1's instance `I`: the statement's bytes read as their halves then
`1, 0, 0, 0` (`stmtWords`), the limbs `eLimbs`; the index root and the encodings, which the four-root
chain does not read, any (zero, injective). -/
noncomputable def pcsWire (I : Instance E) : Wire I.params I.bounds where
  indexRoot := default
  decode := Reduce.stmtWords
  limbs := Soundness.eLimbs
  enc₁ := countEnc I.bounds.Msg₁
  enc₁_injective := countEnc_injective I.bounds.Msg₁
  enc₂ := countEnc I.bounds.Msg₂
  enc₂_injective := countEnc_injective I.bounds.Msg₂

theorem pcsWire_decode (I : Instance E) (sb : Vector UInt8 64) :
    (pcsWire I).decode sb = Reduce.stmtWords sb := rfl

/-! ## Bytes -/

theorem tag_eq : "pcs-quotient-kc1".toUTF8.toList = QuotientRpm.tag := by decide +kernel

variable (I : Instance E)

/-- A scalar's word (`Chain::sample`): the Statement's `scalarBytes`. -/
theorem word_eq (x : E) : (pcsWire I).word x = scalarBytes x := rfl

/-- A state's challenge: the Statement's `challengeOf`. -/
theorem chal_eq (st : Digest) : (pcsWire I).chal (toB st) = challengeOf st :=
  (Bridge.challengeOf_eq st).symm

theorem drop8_word (x : E) : ((pcsWire I).word x).drop 8 = elementBytes x := rfl

/-- **The label** (`protocol::label`), transcribed twice. -/
theorem label_eq4 (index : Commitment) (stmt : Statement) :
    label index stmt = labelOf4 (pcsWire I) (toB index.root, index.ood, stmt.y ++ stmt.root) := by
  simp only [label, labelOf4, tag_eq, Bridge.toB_toList, drop8_word, Vector.toList_append,
    List.append_assoc]

/-! ## A root's two scalars -/

theorem chunk8 (b : List UInt8) (i : ℕ) (h : 8 * i + 8 ≤ b.length) :
    (List.range 8).map (fun k => b.getD (8 * i + k) 0) = (b.drop (8 * i)).take 8 := by
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

theorem digestBytes_lanes (b : List UInt8) (hb : b.length = 32) :
    digestBytes #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3] = b := by
  simp only [digestBytes, Vector.toList_mk, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    LeanVM.Rpm.wordBytes_leLane]
  rw [chunk8 b 0 (by omega), chunk8 b 1 (by omega), chunk8 b 2 (by omega), chunk8 b 3 (by omega)]
  have h32 : (b.drop (8 * 3)).take 8 = b.drop 24 := List.take_of_length_le (by simp; omega)
  rw [h32]
  conv_rhs => rw [← List.take_append_drop 8 b, ← List.take_append_drop 8 (b.drop 8),
    ← List.take_append_drop 8 ((b.drop 8).drop 8)]
  simp only [List.drop_drop]
  rfl

theorem beBytes_zero : beBytes (0 : K).lane = List.replicate 8 0 := rfl

theorem length_beBytes (w : UInt64) : (beBytes w).length = 8 := by
  simp [beBytes, LeanVM.Rpm.wordBytes_len]

theorem halfWords_of_bytes (b : List UInt8) (hb : b.length = 32) :
    halfWords (toB #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3]) =
      List.replicate 16 0 ++ b.take 16 ++ List.replicate 16 0 ++ b.drop 16 := by
  rw [halfWords, Bridge.toB_toList, digestBytes_lanes b hb]

theorem take16 (a b c d : UInt64) : (beBytes a ++ beBytes b ++ beBytes c ++ beBytes d).take 16 =
    beBytes a ++ beBytes b := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (beBytes a)]
  exact List.take_left' (by simp [length_beBytes])

theorem drop16 (a b c d : UInt64) : (beBytes a ++ beBytes b ++ beBytes c ++ beBytes d).drop 16 =
    beBytes c ++ beBytes d := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (beBytes a)]
  exact List.drop_left' (by simp [length_beBytes])

/-- **A root's two scalars** (`halves_root`): when they name a digest `r`, the half-words the four-root chain
hashes for `r` are the two scalars' words. -/
theorem halfWords_eq_scalars (s : E × E) (r : Digest) (h : rootOfHalves s = some r) :
    halfWords (toB r) = scalarBytes s.1 ++ scalarBytes s.2 := by
  have hc : s.1.limb 2 = 0 ∧ s.2.limb 2 = 0 := by
    by_contra hc
    simp only [rootOfHalves, hc, ite_false, reduceCtorEq] at h
  have hr : #v[leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++
      beBytes (s.2.limb 0).lane) 0, leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++
      beBytes (s.2.limb 1).lane ++ beBytes (s.2.limb 0).lane) 1, leLane (beBytes (s.1.limb 1).lane ++
      beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++ beBytes (s.2.limb 0).lane) 2,
      leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++
      beBytes (s.2.limb 0).lane) 3] = r := by
    simp only [rootOfHalves, hc, and_self, ite_true, Option.some.injEq] at h
    exact h
  rw [← hr, halfWords_of_bytes _ (by simp [length_beBytes]), take16, drop16]
  simp only [scalarBytes, hc.1, hc.2, beBytes_zero, List.append_assoc, List.replicate_append_replicate]

/-! ## The reduction -/

/-- **The four-root chain's proof** of a reduction proof: the statement's bytes `y ‖ root`, the four roots the
proof's scalars name (zero if they name none: the Statement rejects such a proof) with their out-of-domain answers,
the four values and `next`, and the circuit's commitment `index`. -/
def rootProofOf4 (index : Commitment) (stmt : Statement) (p : ReductionProof) : RootProof4 E :=
  ⟨stmt.y ++ stmt.root, toB ((rootOfHalves p.witness.root).getD default), p.witness.ood,
    toB ((rootOfHalves p.h.root).getD default), p.h.ood, toB ((rootOfHalves p.q.root).getD default), p.q.ood,
    toB ((rootOfHalves p.g.root).getD default), p.g.ood, (fun i => p.values.get i, p.next),
    toB index.root, index.ood⟩

/-- **The Statement's reduction is the four-root chain, then the Statement's claims**: for every lawful monad
and Keccak-256 `H`, on a proof whose four roots' scalars name digests, `reduceWithH H 22` hashes exactly what
`chainWith4` hashes over `toB ∘ H`, in the same order, and returns the four commitments and `claimsAt` at its
challenges. -/
theorem reduceWithH_eq_chain4 {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)
    (index : Commitment) (stmt : Statement) (p : ReductionProof) (rW rH rQ rG : Digest)
    (hW : rootOfHalves p.witness.root = some rW) (hH : rootOfHalves p.h.root = some rH)
    (hQ : rootOfHalves p.q.root = some rQ) (hG : rootOfHalves p.g.root = some rG) :
    E2ECompleteness.Pcs.reduceWithH H 22 index stmt p =
      (fun ch : Chals E => (claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ p.values p.next p.qValue
          p.gValue).map fun cl =>
            (⟨⟨⟨rW, p.witness.ood⟩, ⟨rH, p.h.ood⟩, ⟨rQ, p.q.ood⟩, ⟨rG, p.g.ood⟩⟩, cl⟩ : Reduced)) <$>
        chainWith4 (pcsWire I) (fun l => toB <$> H l) (rootProofOf4 index stmt p) := by
  have hS : Supported 22 := by decide
  rcases p with ⟨⟨⟨w0, w1⟩, wo⟩, ⟨⟨h0, h1⟩, ho⟩, ⟨⟨q0, q1⟩, qo⟩, ⟨⟨g0, g1⟩, go⟩, ⟨⟨vs⟩, hvs⟩, next, qv, gv⟩
  match vs, hvs with
  | [a0, a1, a2, a3], _ =>
  simp only at hW hH hQ hG
  simp only [E2ECompleteness.Pcs.reduceWithH, hS, not_true_eq_false, ↓reduceIte,
    E2ECompleteness.Pcs.startWithH, E2ECompleteness.Pcs.squeezeWithH, readCommitment, hW, hH, hQ, hG,
    Option.map_some, chainWith4, rootProofOf4, Option.getD_some, map_bind, bind_assoc, pure_bind,
    bind_map_left, map_pure, label_eq4 I]
  simp only [Chain.absorb, afterW, afterHQG, commitWords, Wire.afterValues, Wire.valueWords,
    Bridge.toB_toList, chal_eq, word_eq, halfWords_eq_scalars _ _ hW, halfWords_eq_scalars _ _ hH,
    halfWords_eq_scalars _ _ hQ, halfWords_eq_scalars _ _ hG, RootProof4.pre, RootProof4.comW,
    RootProof4.comHQG, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
    List.cons_append, List.append_assoc]
  rfl

end PcsKS
