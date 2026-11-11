-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Soundness/F1Step.lean` (`stmtWords_eq`, `provesMembership_of_sat`)
-- and `formal/EndToEnd/Bridge/Extractor.lean` (`cells_eq`, `inputBits_eq`, `readsSecret_of`) at commit abe22812,
-- to the EIP's PCS claims (the witness table committed as itself, F1's instance `rustInstance`, the circuit's random
-- rows).
import Soundness.PcsVerifier
import Bridge.Circuit.Secret
import Bridge.Ntt
import Completeness.Tables
import E2ECompleteness.PcsConstants

/-!
# A satisfying first message spells a secret

The extractor (`PcsQuotient.secretOfStack`) reads a candidate stack as the witness table: its first `2^24` entries
are the cells' polynomial in the novel basis, `Domain.values` takes them to the cells' values, and the input rows'
`V` cells are the secret's bits. Here, for F1's instance of `beta()` with the deployed wiring (`rustInstance`,
`QuotientSecurity.deployedSigma`):

* `relation_rust_iff`: F1's relation of `rustInstance` is that of the instance with the weights `coordWeight G Y`
  (`coordinate_weight`'s below `8`, the only ones the relation reads);
* **`provesMembership_of_sat`**: a first message satisfying F1's relation for the statement's words holds a
  computation of the deployed circuit proving membership of `(y, root)` (F0's `proves_of_relation_statement`,
  `Proves.bits`, `ProvesBits.membership`);
* `cells_eq`, `inputBits_eq`: the cells the extractor computes are F1's cells of the message `readW` reads off the
  stack (the additive transform, `Bridge/Ntt.lean`), so its input bits are the computation's, an input row being no
  random row;
* **`relation_of_sat`**: a stack whose read message satisfies F1's relation spells a secret of the statement
  (`Bridge.Circuit.secretMatches`).
-/

set_option linter.unusedSectionVars false

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membershipBuilder

namespace PcsKS

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash WhirBridge Primitives

/-! ## The weights -/

variable (hc : IsCantor PcsBridge.statementConsts.beta)

/-- F1's instance with `coordinate_weight`'s weights as F0c states them. -/
noncomputable abbrev instG : Instance E :=
  ⟨basisE PcsBridge.statementConsts hc, deployedSigma, coordWeight F192.G F192.Y⟩

/-- F1's instance of the deployed protocol (`SoundPcs`'s). -/
noncomputable abbrev instR : Instance E := rustInstance PcsBridge.statementConsts hc deployedSigma

include hc in
theorem rustWeights_lt (k : ℕ) (hk : k < 8) : rustWeights k = coordWeight F192.G F192.Y k := by
  have h1 := rustInstance_weights PcsBridge.statementConsts hc deployedSigma k hk
  have h2 := E2ECompleteness.Pcs.coordinateWeight_deployed k hk
  rw [h1] at h2
  exact Option.some.inj h2

theorem regionWeight_rust (J : Fin 8) (x : Fin (22 + 2) → Bool) :
    regionWeight (instR hc).c J x = regionWeight (instG hc).c J x := by
  unfold regionWeight
  split_ifs
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [show (instR hc).c k = rustWeights k from rfl,
      rustWeights_lt hc k (Finset.mem_range.mp hk)]
  · rfl

theorem relation_rust_iff (stmt : Fin 8 → E) (w : (Fin (22 + 2) → Bool) → E) :
    (instR hc).Relation stmt w ↔ (instG hc).Relation stmt w := by
  unfold Instance.Relation
  simp only [regionWeight_rust hc]
  rfl

/-! ## The statement's words -/

theorem ofBits_eq_ofU64 (n : ℕ) : K.ofBits n = F64.ofU64 (UInt64.ofNat n) := rfl

theorem ofNat_mod (n : ℕ) : UInt64.ofNat (n % 2 ^ 64) = UInt64.ofNat n :=
  UInt64.toNat_inj.mp (by simp)

theorem ofLimbs_eq_new (v : ℕ) :
    E.ofLimbs (K.ofBits (v % 2 ^ 64)) (K.ofBits (v >>> 64)) 0 =
      F192.new (UInt64.ofNat v) (UInt64.ofNat (v >>> 64)) 0 := by
  rw [ofBits_eq_ofU64, ofNat_mod, ofBits_eq_ofU64]
  rfl

/-- `reduce`'s half of the statement is F0c's (`rustHalf`). -/
theorem stmtHalf_eq_rust (b : Fin 32 → UInt8) (h : Fin 2) : stmtHalf b h = rustHalf b h := by
  unfold stmtHalf rustHalf
  exact ofLimbs_eq_new _

/-- **The wire's words are F0c's**: `stmtWords` of `y ‖ root` is `statementWords G Y y root`. -/
theorem stmtWords_eq (sb : Vector UInt8 64) :
    stmtWords sb = statementWords F192.G F192.Y (yOf sb) (Reduce.rootOf sb) := by
  rw [statementWords_G_Y]
  funext J
  fin_cases J <;> simp [stmtWords, stmtHalves, rustStatementWords, stmtHalf_eq_rust]

theorem yOf_append (y root : Vector UInt8 32) : yOf (y ++ root) = fun i => y.get i := by
  funext i
  simp only [yOf, Vector.get, Fin.cast]
  exact Vector.getElem_append_left i.2

theorem rootOf_append (y root : Vector UInt8 32) :
    Reduce.rootOf (y ++ root) = fun i => root.get i := by
  funext i
  simp only [Reduce.rootOf, Vector.get, Fin.cast]
  have h := Vector.getElem_append_right (xs := y) (ys := root) (i := 32 + (i : ℕ)) (by omega)
    (by omega)
  simpa using h

/-! ## A satisfying assignment proves membership -/

/-- **A first message satisfying F1's relation for the statement's words proves membership** of its
`(y, root)`. -/
theorem provesMembership_of_sat (stmt : PcsQuotient.Statement) (g : Params.Witness E)
    (hs : (instR hc).params.Sat (stmtWords (stmt.y ++ stmt.root)) ((instR hc).params.cells g)) :
    ProvesMembership ((instG hc).cellsOf g) (fun i => stmt.y.get i) (fun i => stmt.root.get i) := by
  have hrel := (relation_rust_iff hc _ _).mp ((instR hc).relation_of_sat _ g hs)
  rw [stmtWords_eq, yOf_append, rootOf_append] at hrel
  have hind := bitWeightsIndependent_G_Y
  exact ProvesBits.membership (((instG hc).proves_of_relation_statement deployed hind.ne_one.1
    hind.ne_one.2 rfl deployed_laid_sigma _ _ _ hrel).bits hind)

/-! ## The cells the extractor reads -/

/-- The extractor's table entries (`inputBitsOfStack`'s `wHat`): the stack's first `2^24` entries. -/
def stackHat (st : Vector K (2 ^ 25)) : Array K :=
  Array.ofFn (n := 2 ^ 24) fun i => st.toArray.getD i.val 0

theorem stackHat_size (st : Vector K (2 ^ 25)) : (stackHat st).size = 2 ^ 24 := by simp [stackHat]

theorem stackHat_getD (st : Vector K (2 ^ 25)) {i : ℕ} (hi : i < 2 ^ 24) :
    (stackHat st).getD i 0 = st[i]'(by omega) := by
  have h25 : i < 2 ^ 25 := by omega
  simp only [stackHat, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true, Option.getD_some]
  rw [Array.getElem?_eq_getElem (by simpa using h25)]
  rfl

theorem bitsToNat_snoc_false (b : Fin 24 → Bool) :
    LeanVM.Protocol.Whir.bitsToNat (Fin.snoc b false : Fin 25 → Bool) = Completeness.idx b := by
  unfold LeanVM.Protocol.Whir.bitsToNat Completeness.idx
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.toNat_false, zero_mul, add_zero,
    Fin.val_castSucc]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases b k <;> simp

include hc in
theorem cantorUpTo : Bridge.Ntt.CantorUpTo 24 := ⟨hc.1, fun k hk => hc.2 k hk⟩

/-- **The cells the extractor reads are F1's cells of the table**: entry `p < 2^24` of
`Domain.values 24 0 (stackHat st)` is, in `E`, F1's cell `p` of the first message `readW` reads off the stack. -/
theorem cells_eq (st : Vector K (2 ^ 25)) {p : ℕ} (hp : p < 2 ^ 24) :
    ofK ((PcsQuotient.Domain.values 24 0 (stackHat st)).getD p 0) =
      (instG hc).cellsOf (witnessOfTable (k := 22 + 1) (SoundPcs.colFn (⟨st⟩ : Column 25)))
        (QuotientSecurity.cellOf p) := by
  have hB := cantorUpTo hc
  rw [Bridge.Ntt.values_getD_tablePoly hB (by decide) 0 (stackHat st) (stackHat_size st) hp, zero_add,
    Bridge.Ntt.point_eq_cantor hB (by decide) hp]
  rw [Completeness.cellsOf_witnessTable]
  have hpt : (Bridge.Ntt.cantorOf hB).point (Completeness.bitsOf 24 p) =
      (basisK PcsBridge.statementConsts hc).point (QuotientSecurity.cellOf p) := by
    simp only [QuotientSecurity.CantorBasis.point, Bridge.Ntt.cantorOf, basisK]
    rfl
  have hent : (fun b : Fin 24 → Bool => SoundPcs.colFn (⟨st⟩ : Column 25) (Fin.snoc b false)) =
      fun b => ofK ((stackHat st).getD (Completeness.idx b) 0) := by
    funext b
    rw [stackHat_getD st (Completeness.idx_lt b)]
    have hi : ((LeanVM.Protocol.Whir.bitsEquiv 25 (Fin.snoc b false : Fin 25 → Bool)) : ℕ) =
        Completeness.idx b := by
      rw [LeanVM.Protocol.Whir.bitsEquiv_val]
      exact bitsToNat_snoc_false b
    simp only [SoundPcs.colFn, tabFn, Fin.getElem_fin, hi]
  have e1 : ∀ (X : K) (P : Polynomial K),
      ofK (Polynomial.eval X P) = Polynomial.eval (ofK X) (P.map (algebraMap K E)) := by
    intro X P
    rw [Polynomial.eval_map]
    show algebraMap K E (Polynomial.eval X P) = Polynomial.eval₂ (algebraMap K E) (algebraMap K E X) P
    rw [Polynomial.eval₂_hom]
  rw [e1, map_tablePoly, hpt, ← point_basisE]
  exact congrArg (fun f => Polynomial.eval ((basisE PcsBridge.statementConsts hc).point
    (QuotientSecurity.cellOf p)) (QuotientSecurity.tablePoly f)) hent.symm

theorem ofK_eq_bitF {x : K} {b : Bool} (h : ofK x = QuotientSecurity.bitF b) : decide (x = 1) = b := by
  have hinj : Function.Injective (algebraMap K E) := (algebraMap K E).injective
  cases b
  · have h0 : algebraMap K E x = algebraMap K E 0 := by
      rw [map_zero]; exact h
    have := hinj h0
    simp [this]
  · have h1 : algebraMap K E x = algebraMap K E 1 := by
      rw [map_one]; exact h
    simp [hinj h1]

/-- An input row is no random row (it reads itself in `Y`, a random row the one). -/
theorem not_random_of_input (C : ChiCircuit (Fin (2 ^ 22))) (r : Fin (2 ^ 22)) (h : C.isInput r) :
    ¬ C.isRandom r := fun hr => by
  have h1 := (C.hInput r h).2.1
  rw [(C.hRandom r hr).2.1] at h1
  cases h1

/-- **The input bits the extractor reads off a stack are the computation's**: if F1's cells of the message
`readW` reads off the stack hold a computation `v` of the deployed circuit, the extractor's `inputBitsOfStack` are
`v`'s bits at the input rows. -/
theorem inputBits_eq (st : Vector K (2 ^ 25)) (v : Fin (2 ^ 22) → Bool)
    (hcomp : deployed.Computes ((instG hc).cellsOf
      (witnessOfTable (k := 22 + 1) (SoundPcs.colFn (⟨st⟩ : Column 25)))) v) :
    PcsQuotient.inputBitsOfStack (PcsQuotient.membership 22) st =
      (PcsQuotient.membership 22).inputs.toList.map (QuotientSecurity.natVal v) := by
  have hlog := Bridge.Circuit.membership_logRows 22
  unfold PcsQuotient.inputBitsOfStack
  simp only [hlog]
  refine List.map_congr_left fun r hr => ?_
  have hr' : r < 2 ^ 22 := Bridge.Circuit.membership_inputs_lt r (Array.mem_def.mpr hr)
  have hin : deployed.isInput ⟨r, hr'⟩ := by
    show r ∈ PcsCircuit.membership.inputs
    rw [← Bridge.Circuit.membership_inputs]
    exact Array.mem_def.mpr hr
  have h4 : 4 * r + 3 < 2 ^ 24 := by omega
  have hc' := cells_eq hc st h4
  have hrow := (hcomp.2 ⟨r, hr'⟩ (not_random_of_input deployed _ hin)).2.2.2
  rw [QuotientSecurity.rowCell_eq_cellOf] at hrow
  have e3 : (4 * (⟨r, hr'⟩ : Fin (2 ^ 22)).val + ((3 : Fin 4) : ℕ)) = 4 * r + 3 := rfl
  rw [e3, ← hc'] at hrow
  rw [QuotientSecurity.natVal, dite_eq_left hr']
  exact ofK_eq_bitF hrow

/-- **A stack whose read message satisfies F1's relation for the statement's words spells a secret of the
statement.** -/
theorem relation_of_sat (stmt : PcsQuotient.Statement) (st : Vector K (2 ^ 25))
    (hs : (instR hc).params.Sat (stmtWords (stmt.y ++ stmt.root))
      ((instR hc).params.cells (SoundPcs.readW hc deployedSigma ⟨st⟩).1)) :
    PcsQuotient.Relation stmt (PcsQuotient.secretOfStack (PcsQuotient.membership PcsQuotient.logRows) st) := by
  obtain ⟨v, hcomp, hy, hroot⟩ := provesMembership_of_sat hc stmt _ hs
  rw [show PcsQuotient.logRows = 22 from rfl]
  unfold PcsQuotient.secretOfStack
  rw [inputBits_eq hc st v hcomp]
  exact Bridge.Circuit.secretMatches stmt v hy hroot

end PcsKS
