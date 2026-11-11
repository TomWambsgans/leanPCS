-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Leaves

/-!
# The contract's claims are the Statement's (F5)

`run_calldata`: on the calldata of a statement and a proof (`calldata`), with the deployed Keccak-256
and the circuit's commitment `index` in storage (`deployed`), the contract reaches its checks of declared
claims exactly when the Statement's reduction (`PcsQuotient.reduce`, over Keccak-f[1600]) accepts, and
the three PCS claims it checks declared are then, byte for byte, the EIP encodings
(`PcsQuotient.pcsClaimBytes`) of the reduction's three claims on their commitments, in the order of
`Claims::on` (`checkPairs`). `accepts_calldata`: so the contract accepts exactly when every one of
those claims is attested.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient PcsQuotient.Transcript
  Program Emitted

local notation "W" => word limbsEquiv
local notation "EL" => elem limbsEquiv

/-- **The three PCS claims of a reduced proof** with their commitments, in the order of `Claims::on`
(`Reduced.checks` without the openings). -/
def checkPairs (index : Commitment) (r : Reduced) : List (Commitment × Claim) :=
  [(r.commitments.witness, r.claims.witness), (index, r.claims.wiring), (r.commitments.table, r.claims.copy)]

/-! ## Claims from words -/

/-- A claim's bytes from its words (`claimBytes`, with the words resolved). -/
def wordsBytes (f : Word → ℕ) (r : Word × Word × List Word × Word) : List UInt8 :=
  [1, r.2.2.1.length.toUInt8] ++ beBytes 32 (f r.1) ++
    (r.2.1 :: (r.2.2.1 ++ [r.2.2.2])).flatMap fun w => beBytes 24 (f w)

theorem getD_outputs_map (f : Word → ℕ) (hf : f (.const 0) = 0) (i : ℕ) :
    (outputs.map f).getD i 0 = f (outAt i) := by
  rw [outAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases outputs[i]? <;> simp [hf]

theorem claimBytes_map (f : Word → ℕ) (hf : f (.const 0) = 0) (c : ℕ × ℕ × List ℕ × ℕ) :
    claimBytes (outputs.map f) c = wordsBytes f (resolve c) := by
  simp only [claimBytes, wordsBytes, resolve, List.length_map, getD_outputs_map f hf, List.flatMap_cons,
    List.flatMap_append, List.flatMap_map, List.flatMap_nil]

theorem wordsBytes_eq {f : Word → ℕ} {wr wo wv : Word} {pw : List Word} {c : Commitment} {cl : Claim}
    (hr : beBytes 32 (f wr) = digestBytes c.root) (ho : beBytes 24 (f wo) = elementBytes c.ood)
    (hl : pw.length = cl.point.length)
    (hp : pw.flatMap (fun w => beBytes 24 (f w)) = cl.point.flatMap elementBytes)
    (hv : beBytes 24 (f wv) = elementBytes cl.value) :
    wordsBytes f (wr, wo, pw, wv) = pcsClaimBytes c cl := by
  simp only [wordsBytes, pcsClaimBytes, List.flatMap_cons, List.flatMap_append, hr, ho, hl, hp, hv,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-! ## The leaves -/

section Calldata

variable (index : Commitment) (stmt : Statement) (p : ReductionProof) (frame : UInt8) (rw rt : Digest)

local notation "CD" => cdOf stmt p frame rw rt
local notation "E0" => deployed index CD

variable {p rw rt} in
theorem leafOK_calldata (hw : rootOfHalves p.witness.root = some rw) (ht : rootOfHalves p.table.root = some rt) :
    LeafOK E0 (chainVals index stmt p) := by
  obtain ⟨-, -, -, -, -, -, x, c, vy, nx, cα, cβ, cμ, ct, cρ⟩ := vals_leaves index stmt frame hw ht
  refine ⟨fun k hk => ?_, elem_of_word cα, elem_of_word cβ, elem_of_word cμ, elem_of_word ct, elem_of_word x,
    elem_of_word c, elem_of_word vy, elem_of_word nx, elem_of_word cρ⟩
  have hs : leaves₀.s.getD k 0 = k + 2 := by
    simp only [leaves₀]
    interval_cases k <;> rfl
  rw [hs]
  exact elem_of_word (vals_stmt index stmt p frame rw rt k hk)

variable {p rw rt} in
theorem oods_calldata (hw : rootOfHalves p.witness.root = some rw) (ht : rootOfHalves p.table.root = some rt) :
    val limbsEquiv E0 12 = p.witness.ood ∧ val limbsEquiv E0 21 = p.table.ood := by
  obtain ⟨-, -, o0, -, -, o1, -⟩ := vals_leaves index stmt frame hw ht
  exact ⟨elem_of_word o0, elem_of_word o1⟩

theorem root_word (j : ℕ) (hj : j < 2) :
    beBytes 32 (wordOf E0 (values E0) (.calldata (64 + 32 * j))) =
      digestBytes ([rw, rt][j]'(by simpa using hj)) := by
  have hl := length_CD stmt p frame rw rt
  show beBytes 32 (cdWord (CD) (64 + 32 * j)) = _
  rw [cdWord_slice _ _ (by omega), roots_slice stmt p frame rw rt j hj, beBytes32_digest]

end Calldata

theorem node_word (e : Env) (k : ℕ) :
    beBytes 24 (wordOf e (values e) (.node k)) = elementBytes (val limbsEquiv e k) :=
  beBytes24_elem _

theorem nodes_words (e : Env) (pt : List ℕ) :
    (pt.map Word.node).flatMap (fun w => beBytes 24 (wordOf e (values e) w)) =
      (pt.map (val limbsEquiv e)).flatMap elementBytes := by
  simp only [List.flatMap_map]
  exact List.flatMap_congr fun k _ => node_word e k

/-! ## The contract on calldata -/

theorem checkId_some : checkId = some 247 := by decide +kernel

theorem nonzero_eq : nonzero = [247] := rfl

theorem node_247 : ∃ a b, nodes[247]? = some (.mul a b) := ⟨209, 246, by decide +kernel⟩

theorem values_247_lt (e : Env) : (values e).getD 247 0 < B192 := by
  obtain ⟨a, b, h⟩ := node_247
  rw [values_mul e h]
  exact mulE_lt _ _

theorem word_zero : W (0 : E) = 0 := rfl

theorem values_247_ne (e : Env) : (values e).getD 247 0 ≠ 0 ↔ val limbsEquiv e 247 ≠ 0 := by
  constructor
  · intro h hv
    apply h
    have := congrArg W hv
    rw [val, word_elem', Nat.mod_eq_of_lt (values_247_lt e), word_zero] at this
    exact this
  · intro h hv
    apply h
    rw [val, hv, elem_zero isF192_primitives]

theorem any_zero_iff (l : List E) : l.any (· = 0) = true ↔ l.prod = 0 := by
  rw [List.any_eq_true, List.prod_eq_zero_iff]
  simp

/-- **The contract's claims on calldata** (F5): on the calldata of a statement and a proof, with the
deployed Keccak-256 and the circuit's commitment `index` in storage, the contract reaches its checks
exactly when the Statement's reduction accepts, and then checks declared, in order, the EIP encodings of
the reduction's three claims on their commitments. -/
theorem run_calldata (index : Commitment) (stmt : Statement) (p : ReductionProof) (frame : UInt8)
    (cd : List UInt8) (h : calldata stmt p frame = some cd) :
    (run (deployed index cd)).map calls =
      (reduce 22 index stmt p).map fun r => (checkPairs index r).map fun c => pcsClaimBytes c.1 c.2 := by
  obtain ⟨rw, rt, hw, ht, rfl⟩ := calldata_some h
  change (run (deployed index (cdOf stmt p frame rw rt))).map calls = _
  set e := deployed index (cdOf stmt p frame rw rt) with he
  set I := chainVals index stmt p with hIdef
  have hI : LeafOK e I := leafOK_calldata index stmt frame hw ht
  rw [reduce_eq index stmt p hw ht,
    show claimsAt 22 stmt I.α I.β I.μ I.t I.ρ p.values p.next =
      claimsAt PcsQuotient.logRows I.stmt I.α I.β I.μ I.t I.ρ I.v I.next from rfl,
    Formula.claimsAt_eq]
  have h247 : val limbsEquiv e 247 = (Formula.denominators I).prod :=
    checkId_spec (e := e) I hI 247 checkId_some
  have hrun : run e = if (values e).getD 247 0 != 0 then some (outputs.map (wordOf e (values e)))
      else none := by
    have hwf : WellFormed e.cd := wellFormed_CD stmt p frame rw rt
    rw [run, if_pos hwf, nonzero_eq]
    simp
  rw [hrun]
  by_cases hz : (Formula.denominators I).any (· = 0) = true
  · have hv : (values e).getD 247 0 = 0 := by
      by_contra hne
      exact ((values_247_ne e).mp hne) (h247.trans ((any_zero_iff _).mp hz))
    rw [if_pos hz, hv]
    rfl
  · have hnz : (Formula.denominators I).prod ≠ 0 := fun h0 => hz ((any_zero_iff _).mpr h0)
    have hv : (values e).getD 247 0 ≠ 0 := (values_247_ne e).mpr (h247 ▸ hnz)
    rw [if_neg hz, if_pos (by simpa using hv)]
    simp only [Option.map_some]
    congr 1
    -- the claims' words
    have hre := reduceIds_eq
    rw [chain_eq] at hre
    rcases ho : reduceIds with _ | o
    · rw [ho] at hre; cases hre
    rw [ho] at hre
    have hcw : claimWords leaves₀ o = claims.map resolve := by
      simpa using hre
    obtain ⟨hwP, hwV, hfP, hfV, hcP, hcV⟩ := reduceIds_spec (e := e) I hI hnz o ho
    obtain ⟨o0, o1⟩ := oods_calldata index stmt frame hw ht
    have hf0 : wordOf e (values e) (.const 0) = 0 := rfl
    rw [calls, List.map_congr_left (fun c _ => claimBytes_map _ hf0 c),
      show (fun c => wordsBytes (wordOf e (values e)) (resolve c)) = wordsBytes (wordOf e (values e)) ∘ resolve
        from rfl, ← List.map_map, ← hcw]
    have hlen : ∀ (l : List ℕ) (P : List E), l.map (val limbsEquiv e) = P → (l.map Word.node).length = P.length :=
      fun l P h => by rw [← h]; simp
    have hpt : ∀ (l : List ℕ) (P : List E), l.map (val limbsEquiv e) = P →
        (l.map Word.node).flatMap (fun w => beBytes 24 (wordOf e (values e) w)) = P.flatMap elementBytes :=
      fun l P h => by rw [nodes_words, h]
    have hval : ∀ (k : ℕ) (x : E), val limbsEquiv e k = x → beBytes 24 (wordOf e (values e) (.node k)) =
        elementBytes x := fun k x h => by rw [node_word, h]
    simp only [claimWords, checkPairs, List.map_cons, List.map_nil]
    refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))
    · exact wordsBytes_eq (root_word index stmt p frame rw rt 0 (by norm_num)) (hval _ _ o0)
        (hlen _ _ hwP) (hpt _ _ hwP) (hval _ _ hwV)
    · exact wordsBytes_eq (beBytes32_digest index.root) (elementBytes_eq index.ood).symm
        (hlen _ _ hfP) (hpt _ _ hfP) (hval _ _ hfV)
    · exact wordsBytes_eq (root_word index stmt p frame rw rt 1 (by norm_num)) (hval _ _ o1)
        (hlen _ _ hcP) (hpt _ _ hcP) (hval _ _ hcV)

/-- **The contract's verdict on calldata**: it accepts exactly when the Statement's reduction accepts and
claim `k` of `checkPairs` (its EIP encoding) is attested, for every `k`. -/
theorem accepts_calldata (attest : ℕ → List UInt8 → Bool) (index : Commitment) (stmt : Statement)
    (p : ReductionProof) (frame : UInt8) (cd : List UInt8) (h : calldata stmt p frame = some cd) :
    accepts attest (deployed index cd) =
      match reduce 22 index stmt p with
      | none => false
      | some r => allAttested attest 0 ((checkPairs index r).map fun c => pcsClaimBytes c.1 c.2) := by
  have hr := run_calldata index stmt p frame cd h
  unfold accepts
  rcases hrun : run (deployed index cd) with _ | ws <;>
    rcases hred : reduce 22 index stmt p with _ | r <;> rw [hrun, hred] at hr <;> simp at hr ⊢
  rw [hr]

end Implementation
