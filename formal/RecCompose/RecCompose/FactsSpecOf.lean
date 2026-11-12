-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.FactsSpec

/-!
# `SpecOf (Spec.of Data.circuit).core` of a compiled circuit whose view is `Data.circuit`

**`specOf_data`**: the compiler accepted (`compile r = .ok c`), the view is `Data.circuit`, the circuit valid; then the
verifier's constants are the compiled circuit's, its pairs `pairOfC` (the slots), `Φ`'s terms the four ports of
nonzero value in order (`92 + J`: the three claims' Keccak-256s and the statement), its public limbs `pubOfC`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives Finset

/-! ## `Spec.of Data.circuit`'s fields -/

theorem spec_phi : (Spec.of Data.circuit).phi = phiOf Data.circuit := by
  unfold Spec.of
  dsimp only

theorem spec_maxGamma : (Spec.of Data.circuit).maxGamma = 1 := by
  unfold Spec.of
  dsimp only
  exact data_maxGamma

theorem spec_pairs : (Spec.of Data.circuit).pairs = Data.pairs.map fun p ↦
    (⟨p.logRows, (pairConstants p 4 (cosetConstants 4 20)).1 * ((pairConstants p 4 (cosetConstants 4 20)).2)⁻¹⟩ :
      SpecPair) := by
  unfold Spec.of
  dsimp only
  exact List.map_congr_left fun p _ ↦ rfl

theorem spec_groups : (Spec.of Data.circuit).groups = groupsOf Data.circuit := by
  unfold Spec.of
  dsimp only

theorem spec_c : (Spec.of Data.circuit).c = normalisedConstants (cosetConstants 4 20) := by
  unfold Spec.of
  dsimp only
  rw [show Data.circuit.logRow = 4 from rfl, show Data.circuit.logN = 24 from rfl]

theorem core_groups : (Spec.of Data.circuit).core.groups =
    (groupsOf Data.circuit).map fun g ↦ (⟨g.role, g.formula.toF, g.pulls, g.pairs⟩ : GroupF E) := by
  simp only [Spec.core, spec_groups]

theorem core_maxGamma : (Spec.of Data.circuit).core.maxGamma = 1 := by
  simp only [Spec.core, spec_maxGamma]

theorem core_c_data : (Spec.of Data.circuit).core.c =
    normalisedConstantsF (cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) 4) 20) := by
  simp only [Spec.core, spec_c]
  exact core_c 4 20

theorem core_pairs : (Spec.of Data.circuit).core.pairs = Data.pairs.map fun p ↦
    (p.logRows, kE ((pairConstants p 4 (cosetConstants 4 20)).1 * ((pairConstants p 4 (cosetConstants 4 20)).2)⁻¹)) := by
  simp only [Spec.core, spec_pairs, List.map_map]
  rfl

theorem core_phi : (Spec.of Data.circuit).core.phi = [(15, (List.range 4).map fun J ↦
    (Data.holes.getD (92 + J) 0 / 16, (Data.publicTerms.getD (92 + J) default).value.toF))] := by
  simp only [Spec.core, spec_phi, data_phi, List.map_cons, List.map_nil, List.map_map]
  rfl

theorem core_phiTerms : phiTerms (Spec.of Data.circuit).core = (List.range 4).map fun J ↦
    (15, Data.holes.getD (92 + J) 0 / 16, (Data.publicTerms.getD (92 + J) default).value.toF) := by
  rw [phiTerms, core_phi, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
  rfl

theorem core_phiTerms_length : (phiTerms (Spec.of Data.circuit).core).length = 4 := by
  rw [core_phiTerms, List.length_map, List.length_range]

theorem core_phiTerms_getD {J : ℕ} (hJ : J < 4) : (phiTerms (Spec.of Data.circuit).core).getD J noPhi =
    (15, Data.holes.getD (92 + J) 0 / 16, (Data.publicTerms.getD (92 + J) default).value.toF) := by
  rw [core_phiTerms, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hJ),
    List.getElem_map, List.getElem_range]

/-! ## The assembly -/

/-- **The verifier's constants are the compiled circuit's.** -/
theorem specOf_data {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    (hview : viewOf c.circuit = Data.circuit) (hV : c.circuit.toPiop.Valid) (hhash : c.circuit.hashed = Data.hashed) :
    SpecOf (Spec.of Data.circuit).core c.circuit.toPiop UniComplete.Domain.basisE (pairOfC c.circuit) (fun J ↦ 92 + J)
      (pubOfC c.circuit) := by
  have hlogN := viewOf_logN hview
  have hlogW := viewOf_logW hview
  have hports := viewOf_ports hview
  have hroots := viewOf_roots hview
  have hpairs := viewOf_pairs hview
  have hformulas := viewOf_formulas hview
  have hterms := viewOf_terms hview
  have hslen : (Spec.of Data.circuit).core.pairs.length = (slots c.circuit).length := by
    rw [core_pairs, List.length_map, ← hpairs, pairsOf_length]
  have htl := core_phiTerms_length
  have hholes := viewOf_holes hview
  have hhl : c.circuit.hashed.length = 3 := by rw [hhash]; rfl
  have hnP : c.circuit.toPiop.nP = 99 := by
    show (c.circuit.ports.toList.map (·.position)).length = 99
    rw [List.length_map, Array.length_toList, hports]
  have hN : c.circuit.toPiop.N = 2 ^ 24 := by
    show 2 ^ c.circuit.logN = _
    rw [hlogN]
  have hW : c.circuit.toPiop.W = 16 := by
    show 2 ^ c.circuit.logWidth = _
    rw [hlogW]
    rfl
  have hpd : ∀ i < (slots c.circuit).length, Data.pairs.getD i default = (pairsOf c.circuit).getD i default :=
    fun i _ ↦ by rw [hpairs]
  -- the source of a port, from `Data`'s public terms
  have hsrc : ∀ j < 99, Data.publicTerms.getD j default =
      ⟨2 ^ 24 + j, ⟨termOf 3 0 (c.circuit.ports.getD j default).source, none⟩⟩ := by
    intro j hj
    rw [← hterms, publicTermsOf_getD _ (by rw [hports]; exact hj), hlogN, hroots, hhl]
  have hport : ∀ j < 99, c.circuit.toPiop.port j = Data.holes.getD j 0 := by
    intro j hj
    have hsz : j < c.circuit.ports.size := by rw [hports]; exact hj
    rw [← hholes, holesOf_getD _ hsz]
    simp only [RecPiop.Circuit.port, RecCircuit.Circuit.toPiop, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?, List.getElem?_map, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem hsz]
    rfl
  have hgam := powersList_two
  exact {
    logN := hlogN.symm
    logRow := hlogW.symm
    hn := by show c.circuit.logN ≤ 32; rw [hlogN]; norm_num
    omega := funext fun i ↦ (UniComplete.Domain.omega_basisE i).symm
    c := by
      rw [core_c_data, show c.circuit.toPiop.logW = c.circuit.logWidth from rfl,
        show c.circuit.toPiop.logN = c.circuit.logN from rfl, hlogN, hlogW]
      exact normConsts_of_spec _ 20
    pair_mem := fun i hi ↦ pairOfC_mem hV (hslen ▸ hi)
    pair_inj := fun i hi j hj h ↦ pairOfC_inj hV (hslen ▸ hi) (hslen ▸ hj) h
    pair_surj := fun p hp ↦ by
      obtain ⟨i, hi, he⟩ := pairOfC_surj hV hp
      exact ⟨i, hslen ▸ hi, he⟩
    pair_s := fun i hi ↦ by
      have hi' := hslen ▸ hi
      rw [core_pairs, List.getD_eq_getElem _ _ (by rw [List.length_map]; rw [← hpairs, pairsOf_length]; exact hi'),
        List.getElem_map, ← List.getD_eq_getElem _ default, hpd i hi', pairsOf_getD _ hi']
      rfl
    pair_z := fun i hi ↦ by
      have hi' := hslen ▸ hi
      rw [core_pairs, List.getD_eq_getElem _ _ (by rw [List.length_map]; rw [← hpairs, pairsOf_length]; exact hi'),
        List.getElem_map, ← List.getD_eq_getElem _ default, hpd i hi']
      rw [core_c_data, pair_z_eq _ (by
        rw [pairsOf_getD _ hi']
        have := pairOfC_logRows_le hV hi'
        rw [hlogN, hlogW] at this
        exact this)]
      rw [pairsOf_getD _ hi']
      show zHat _ _ (Heap.omega _ (_ * 2 ^ 4 + _)) = zHat _ _ (Heap.omega _ (_ * c.circuit.toPiop.W + _))
      rw [hW]
      rfl
    groups_perm := by
      rw [core_groups, List.flatMap_map, core_pairs, List.length_map]
      exact groupsOf_perm Data.circuit
    group_role := fun g hg i hi ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, hrole, -, -⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show (pairOfC c.circuit i).2 = g0.role
      rw [hrole, show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      rfl
    group_pulls := fun g hg i hi ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, -, hpulls, -⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show g0.pulls = _
      rw [hpulls, show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      obtain ⟨-, -, hf⟩ := mem_slots.mp (slot_mem hV hi')
      show _ = !(c.circuit.toPiop.regionRole (RecCircuit.toBlock ((slots c.circuit).getD i default).1)
        ((slots c.circuit).getD i default).2.1).isPort
      rw [toPiop_regionRole]
      exact roleFormula_pulls hf
    group_formula := fun g hg i hi γ v ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, hrole, -, hform⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show g0.formula.toF.eval (powersList γ ((Spec.of Data.circuit).core.maxGamma + 1)) (fun c ↦ v (c ^^^ g0.role)) = _
      rw [core_maxGamma, hform, show Data.circuit.formulas = Data.formulas from rfl,
        show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', ← hformulas, formulasOf_getD_pair _ hi', hrole,
        show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      obtain ⟨-, -, hf⟩ := mem_slots.mp (slot_mem hV hi')
      show _ = (c.circuit.toPiop.regionRole (RecCircuit.toBlock ((slots c.circuit).getD i default).1)
        ((slots c.circuit).getD i default).2.1).value γ (v 0) fun x ↦ v (((slots c.circuit).getD i default).2.1 ^^^ x)
      rw [toPiop_regionRole, roleFormula_eval hf _ γ (hgam γ).1 (hgam γ).2 (v 0)]
      congr 1
      funext x
      rw [Nat.xor_comm]
    phi_nodup := by rw [core_phi]; simp
    phi_port_lt := fun J hJ ↦ by rw [htl] at hJ; rw [hnP]; omega
    phi_port_inj := fun J _ J' _ h ↦ by omega
    phi_role := fun J hJ ↦ by
      rw [htl] at hJ
      rw [core_phiTerms_getD hJ, hport _ (by omega), hW, data_holes_role J hJ]
    phi_row := fun J hJ ↦ by
      rw [htl] at hJ
      rw [core_phiTerms_getD hJ, hport _ (by omega), hW]
    zero_ports := fun j hj hnot pubs γ ↦ by
      rw [hnP] at hj
      have hj16 : j < 92 ∨ 96 ≤ j := by
        by_contra h
        exact hnot (j - 92) (by rw [htl]; omega) (by omega)
      have h := hsrc j hj
      have ht := data_zero_terms j hj hj16
      rw [h] at ht
      unfold RecPiop.Circuit.pubFp pubOfC
      rw [hroots, hhl]
      rcases termOf_eq_nil ht with hz | hz <;> rw [hz] <;> exact fpList_zero _ γ
    phi_value := fun J hJ pubs γ ↦ by
      rw [htl] at hJ
      rw [core_phiTerms_getD hJ, hsrc _ (by omega), core_maxGamma]
      have hJ' : 92 + J < c.circuit.toPiop.nP := by rw [hnP]; omega
      unfold RecPiop.Circuit.pubFp pubOfC
      rw [limbs_toPiop hc hJ', hroots, hhl]
      exact term_value_source 3 0 _ pubs γ }

end RecCompose
