-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`), the verifier's arithmetic `formal/RecStatement`'s
-- (`checks_claims_iff_post2`).
import RecCompose.Pi2HonestQ

/-!
# π2's honest prover: its claims hold and the verifier's check passes, off the bad challenges

**`pi2_honest`**: at a setup of the real deployment's circuit (the compiled circuit `C.G roots`, its facts `Fa`, the setup
columns `hcol`), for a witness `w` satisfying the circuit at the public limbs of the scalars, the honest prover's stacks
(`honestW`: `W`'s placed table; `honestQ`: the sixteen slots of `h`, `q`, `P`, `q_P` placed) and the honest inputs of
the verifier's arithmetic (`honestInputs`: the true fold values at `t`, `ξ = κ(t) + β σ(t)` from the setup's halves,
`s = P(t)`, any `ρ`): **the verifier's one check passes and π2's five claims hold on the stacks** (`Pi2ClaimsHold`),
unless

* **`BadCopy`** (`α, β`): a non-hole's `d_pull(i) = α + w_i + β ω_i` or `d_push(i) = α + P_v(i) + κ_i + β ω_{σ_i}` is
  zero;
* **`BadT`** (`t`): `t ∈ V_{m+1}` (`w_{m+1}(t) = 0`), `c_h = d_pull(t) d_push(t) = 0`, `c_h + c_q = 0`, or
  `α + P_v(t) + κ(t) + β σ(t) = 0`.

The proof: the model's polynomials of the honest stacks are the prover's (by the stacks' placement and interpolation
on `V_m` and on the coset), `q` and `q_P` the honest ones (`novP_qNovel`, `novP_qpNovel`), so the identity and `P`'s
definition are zero; `Σ_V h = 0` (`sum_hValues`); `ξ` is the setup's claim; the fold values are `W`'s true ones;
`s = P(t)`; so `RecPiop.Post2` holds, and `checks_claims_iff_post2` with the model's claims gives the claims.

**Counting** (`card_badCopy_le`, `card_badT_le`): at most `2N |E|²` triples `(α, β, γ)` are bad (each denominator is
zero on `|E|²` of them, `α` being determined by `β, γ`), and for a good triple at most `9N` points `t`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

/-! ## The honest objects -/

/-- **The honest `W` stack**: the witness's basis-`B` coefficients placed under `W`'s layout (the prover's `wStack`). -/
def honestW (G : RecPiop.Circuit E) (w : ℕ → K) : Stk :=
  fun j ↦ (placePublic (layoutsOf G.logN).1 fun i ↦ (wTableB G w).getD i 0).getD j 0

/-- **The honest `Q` stack**: the sixteen slots placed under `Q`'s layout (the prover's `qStack`), `Φ` the
verifier's at the public scalars `pubs`. -/
def honestQ (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E) : Stk :=
  fun j ↦ (placePublic (layoutsOf G.logN).2.1 (qEntry G.logN (hNovel G w α β) (qNovel G w α β γ (phiOn S pubs γ))
    (pNovel G w) (qpNovel G w γ))).getD j 0

/-- **The honest inputs** of the verifier's arithmetic: the scalars, the challenges, the true fold values at `t`,
`ξ` from the setup's halves and `s = P(t)` (the prover's `inputs`). -/
def honestInputs (G : RecPiop.Circuit E) (setupStack : Array K) (w : ℕ → K) (scalars : List E)
    (α β γ t ρ : E) : Inputs E :=
  ⟨scalars, α, β, γ, t, foldValues G.logN G.logW (wTableB G w) t, xiOf G.logN setupStack β t,
    sOf G.logN (pNovel G w) t, ρ⟩

/-- **The witness's polynomial** (degree below `N`): its novel coefficients'. -/
noncomputable def witnessPoly (G : RecPiop.Circuit E) (w : ℕ → K) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0

/-- `σ`'s and `κ`'s polynomials (degree below `N`). -/
noncomputable def sigmaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0

noncomputable def kappaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0

/-- **`P`'s polynomial** (degree below `N`): `P`'s novel coefficients'. -/
noncomputable def pushPolyH (G : RecPiop.Circuit E) (w : ℕ → K) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ ((pNovel G w).map ofK).getD j 0

/-- **The copy argument's bad challenges**: a non-hole's `d_pull` or `d_push` on `V_m` zero (π2v3: neither the
public limbs `pub` nor `γ` enter, the ports being out of the copy argument). -/
def BadCopy (G : RecPiop.Circuit E) (w : ℕ → K) (_pub : ℕ → List E) (α β _γ : E) : Prop :=
  (∃ i < G.N, ¬ G.IsHole i ∧ RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i = 0) ∨
    (∃ i < G.N, ¬ G.IsHole i ∧ G.dPushV pi2Omega (RecCircuit.emb w) α β i = 0)

/-- **The honest push denominator** `α + P + κ + β σ`. -/
noncomputable def dPushH (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) : E[X] :=
  C α + pushPolyH G w + kappaPoly G + C β * sigmaPoly G

/-- **The bad points `t`**: `t ∈ V_{m+1}`, `c_h = d_pull(t) d_push(t)` zero, `c_h + c_q` zero, or
`α + P_v(t) + κ(t) + β σ(t)` zero. -/
def BadT (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ t : E) : Prop :=
  QuotientSecurity.sq^[G.logN + 1] t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β).eval t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β + G.zV pi2Omega).eval t = 0 ∨
    (C α + G.pushPolyV pi2Omega (witnessPoly G w) γ + kappaPoly G + C β * sigmaPoly G).eval t = 0

/-! ## Facts of the honest objects -/

theorem size_wValues (G : RecPiop.Circuit E) (w : ℕ → K) : (wValues G w).size = 2 ^ G.logN := by
  simp [wValues, RecPiop.Circuit.N]

theorem witnessPoly_omega (G : RecPiop.Circuit E) (w : ℕ → K) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (witnessPoly G w).eval (pi2Omega i) = RecCircuit.emb w i := by
  unfold witnessPoly
  rw [novP_valuesK_omega hm _ (size_wValues G w) hi]
  unfold wValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rfl

theorem sigmaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (sigmaPoly G).eval (pi2Omega i) = pi2Omega (G.sigma i) := by
  unfold sigmaPoly
  rw [novP_values_omega hm _ (by simp [sigmaValues, RecPiop.Circuit.N]) hi]
  unfold sigmaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rw [pi2Omega_eq]

theorem kappaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (kappaPoly G).eval (pi2Omega i) = G.kappa i := by
  unfold kappaPoly
  rw [novP_values_omega hm _ (by simp [kappaValues, RecPiop.Circuit.N]) hi]
  unfold kappaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]

theorem hNovel_omega (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0).eval (pi2Omega i) =
      (hValues G w α β).getD i 0 :=
  novP_values_omega hm _ (size_hValues w α β) hi

/-- **`P`'s polynomial takes `P_v + κ`** on `V_m`, for a witness at a circuit over `K`. -/
theorem pushPolyH_omega (G : RecPiop.Circuit E) (hK : KCircuit G) (w : ℕ → K) {pub : ℕ → List E}
    (hw : G.Satisfies pub (RecCircuit.emb w)) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (pushPolyH G w).eval (pi2Omega i) = pvValue G w i := by
  unfold pushPolyH
  have e : ((pNovel G w).map ofK) = UniComplete.novelOfValuesK G.logN (pColumn G w) := rfl
  rw [e, novP_valuesK_omega hm _ (size_pColumn w) hi]
  unfold pColumn
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  exact limb_zero_of_mem (pvValue_mem hK w hw hi)

/-- The honest polynomials are `HonestPolys`. -/
theorem honestPolys (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (S : RecPiop.SetupPolys G pi2Omega)
    (hσ : S.σP = sigmaPoly G) (hκ : S.κP = kappaPoly G) :
    HonestPolys G w α β S (witnessPoly G w)
      (UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0) (pushPolyH G w) :=
  ⟨rfl, hσ, hκ, rfl, rfl⟩

/-! ## The stacks read back -/

theorem layoutW_eq {m : ℕ} (hm : 20 ≤ m) :
    (layoutsOf m).1 = PcsQuotient.Layout.ofChunks m m (max m minCertifiedStack) [(0, 2 ^ m)] := by
  simp only [layoutsOf, stackVars, minCertifiedStack, hm, ite_true]

theorem layoutQ_eq {m : ℕ} (hm : 20 ≤ m) :
    (layoutsOf m).2.1 = PcsQuotient.Layout.ofChunks (m + 4) m (max (m + 4) minCertifiedStack) (quotientChunks m) := by
  simp only [layoutsOf, stackVars, minCertifiedStack, hm, ite_true]

/-- **`W`'s layout reads back the honest table.** -/
theorem readW_honest (G : RecPiop.Circuit E) (w : ℕ → K) (hm : 20 ≤ G.logN) {i : ℕ} (hi : i < 2 ^ G.logN) :
    (layoutsOf G.logN).1.readEntry (honestW G w) i = (wTableB G w).getD i 0 := by
  unfold honestW
  rw [layoutW_eq hm]
  refine readEntry_placePublic _ (placePublic_logPiece _ _ _ _) _ i (block_mem_ofChunks
    (by simp only [minCertifiedStack, PcsQuotient.laneFold]; omega) (List.mem_singleton_self _)
    (Nat.div_eq_of_lt hi))

theorem mem_quotientChunks {m c : ℕ} (hc : c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 10 ∨ c = 11 ∨
    c = 13 ∨ c = 14 ∨ c = 15) : (c, 2 ^ m) ∈ quotientChunks m := by
  unfold quotientChunks
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **`Q`'s layout reads back the honest table** at a listed chunk. -/
theorem readQ_honest (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    (hm : 20 ≤ G.logN) {c i : ℕ} (hc : (c, 2 ^ G.logN) ∈ quotientChunks G.logN) (hi : i / 2 ^ G.logN = c) :
    (layoutsOf G.logN).2.1.readEntry (honestQ G S pubs w α β γ) i =
      qEntry G.logN (hNovel G w α β) (qNovel G w α β γ (phiOn S pubs γ)) (pNovel G w) (qpNovel G w γ) i := by
  unfold honestQ
  rw [layoutQ_eq hm]
  exact readEntry_placePublic _ (placePublic_logPiece _ _ _ _) _ i (block_mem_ofChunks
    (by simp only [minCertifiedStack, PcsQuotient.laneFold]; omega) hc hi)

theorem qEntry_at (m : ℕ) (hN qN : Array E) (pN qpN : Array K) {pd kind l : ℕ} (hpd : pd < 2 ^ (m + 1))
    (hk : kind < 2) :
    qEntry m hN qN pN qpN (pd + 2 ^ (m + 1) * (kind + 2 * l)) =
      if l < 3 then (if kind = 0 then (if pd < 2 ^ m then limbN (hN.getD pd 0) l else 0)
        else limbN (qN.getD pd 0) l)
      else if l = 3 then (if kind = 0 then (if pd < 2 ^ m then 0 else pN.getD (pd - 2 ^ m) 0) else qpN.getD pd 0)
      else 0 := by
  unfold qEntry
  have h1 : (pd + 2 ^ (m + 1) * (kind + 2 * l)) % 2 ^ (m + 1) = pd := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpd]
  have h2 : (pd + 2 ^ (m + 1) * (kind + 2 * l)) / 2 ^ (m + 1) = kind + 2 * l := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hpd, zero_add]
  have h3 : (kind + 2 * l) / 2 = l := by omega
  have h4 : (kind + 2 * l) % 2 = kind := by omega
  simp only [h1, h2, h3, h4]

theorem yE_eq : yE = Primitives.F192.Y := rfl

theorem limbN_zero (x : E) : limbN x 0 = x.limb 0 := rfl
theorem limbN_one (x : E) : limbN x 1 = x.limb 1 := rfl
theorem limbN_two (x : E) : limbN x 2 = x.limb 2 := rfl

/-- **An element of `E` from its limbs**: `Σ_l Y^l c_l`. -/
theorem limbs_sum_eq (x : E) : ∑ l ∈ range 3, yE ^ l * ofK (limbN x l) = x := by
  have hk : ∀ a : K, ofK a = Primitives.F192.ofF64 a := fun _ ↦ rfl
  have hl : ∀ i, x.limb i = Primitives.F192.limb x i := fun _ ↦ rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, limbN_zero, limbN_one, limbN_two, hk, hl]
  conv_rhs => rw [← Primitives.F192.ofLimbs_limb x, Primitives.F192.ofLimbs_eq]
  rw [yE_eq]
  ring

theorem chunk_div {m pd j : ℕ} (_hpd : pd < 2 ^ (m + 1)) :
    (pd + 2 ^ (m + 1) * j) / 2 ^ m = pd / 2 ^ m + 2 * j := by
  rw [pow_succ, show 2 ^ m * 2 * j = 2 ^ m * (2 * j) by ring, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

theorem pd_div_lt {m pd : ℕ} (hpd : pd < 2 ^ (m + 1)) : pd / 2 ^ m < 2 := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  rw [pow_succ] at hpd
  omega

/-- **`h`'s coefficient read back from the honest `Q`** (`pd < N`). -/
theorem qCoef_honest_h (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    (hm : 20 ≤ G.logN) {pd : ℕ} (hpd : pd < 2 ^ G.logN) :
    qCoef (qTable G.logN (honestQ G S pubs w α β γ)) G.logN 0 pd = (hNovel G w α β).getD pd 0 := by
  have hpd' : pd < 2 ^ (G.logN + 1) := lt_of_lt_of_le hpd (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold qCoef qTable
  conv_rhs => rw [← limbs_sum_eq ((hNovel G w α β).getD pd 0)]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := mem_range.mp hl
  rw [readQ_honest G S pubs w α β γ hm (c := 4 * l) (mem_quotientChunks (by omega))
      (by rw [chunk_div hpd', Nat.div_eq_of_lt hpd]; ring),
    qEntry_at _ _ _ _ _ hpd' (by norm_num)]
  simp [hpd, hl']

/-- **`q`'s coefficient read back from the honest `Q`** (`pd < 2N`). -/
theorem qCoef_honest_q (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    (hm : 20 ≤ G.logN) {pd : ℕ} (hpd : pd < 2 ^ (G.logN + 1)) :
    qCoef (qTable G.logN (honestQ G S pubs w α β γ)) G.logN 1 pd =
      (qNovel G w α β γ (phiOn S pubs γ)).getD pd 0 := by
  have hd := pd_div_lt hpd
  unfold qCoef qTable
  conv_rhs => rw [← limbs_sum_eq ((qNovel G w α β γ (phiOn S pubs γ)).getD pd 0)]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := mem_range.mp hl
  rw [readQ_honest G S pubs w α β γ hm (c := pd / 2 ^ G.logN + 2 * (1 + 2 * l))
      (mem_quotientChunks (by generalize pd / 2 ^ G.logN = d at hd; omega))
      (chunk_div hpd),
    qEntry_at _ _ _ _ _ hpd (by norm_num)]
  simp [hl']

/-- **`P`'s coefficient read back from the honest `Q`** (`k < N`). -/
theorem pCoef_honest (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    (hm : 20 ≤ G.logN) {k : ℕ} (hk : k < 2 ^ G.logN) :
    pCoef (qTable G.logN (honestQ G S pubs w α β γ)) G.logN k = ((pNovel G w).map ofK).getD k 0 := by
  have hpd : k + 2 ^ G.logN < 2 ^ (G.logN + 1) := by rw [pow_succ]; omega
  unfold pCoef qTable
  rw [readQ_honest G S pubs w α β γ hm (c := 13) (mem_quotientChunks (by omega))
      (by rw [chunk_div hpd, Nat.add_div_right _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hk]),
    qEntry_at _ _ _ _ _ hpd (by norm_num), UniKeccakComplete.AlgC.getD_map_ofK]
  simp

/-- **`q_P`'s coefficient read back from the honest `Q`** (`pd < 2N`). -/
theorem qpCoef_honest (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    (hm : 20 ≤ G.logN) {pd : ℕ} (hpd : pd < 2 ^ (G.logN + 1)) :
    qpCoef (qTable G.logN (honestQ G S pubs w α β γ)) G.logN pd = ofK ((qpNovel G w γ).getD pd 0) := by
  have hd := pd_div_lt hpd
  unfold qpCoef qTable
  rw [readQ_honest G S pubs w α β γ hm (c := pd / 2 ^ G.logN + 2 * (1 + 2 * 3))
      (mem_quotientChunks (by generalize pd / 2 ^ G.logN = d at hd; omega))
      (chunk_div hpd),
    qEntry_at _ _ _ _ _ hpd (by norm_num)]
  simp

end RecCompose

/-- info: 'RecCompose.qCoef_honest_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.qCoef_honest_q

/-- info: 'RecCompose.readW_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.readW_honest
