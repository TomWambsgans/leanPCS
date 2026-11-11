-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsGame128.lean`
-- (`fsLayer128_of_gameV`) and `Fs128.lean` (`le_uniBound128`) to π2's verifier on the EIP's PCS claims, through
-- `Compose.knowledgeSoundness_listChainU_closed128SG` (openings of any verifier, the setup's stacks and the protocol
-- read off the setup), `FsBind.lean`'s `prEvent_doomFG_p2Ops_le` (the seven openings once, `Q`'s binding) and
-- `Compose.prEvent_pairTr_expLG_le` (the seed's pair).
import RecCompose.FsOps
import RecCompose.FsSetup
import RecCompose.FsExtract
import RecCompose.FsWalk
import RecCompose.FsBind
import Compose.FirstDoom
import Compose.SeedPair

/-!
# π2's Fiat–Shamir layer, from its bridges

**`pi2FsLayer_of`**: `Pi2FsLayer D` at the real deployment from the coupling (`Pi2GameLeV`'s inequality, `hG`), the
composed verifier's facts (its duplex shape and cost, the IV moved into the adversary, the extractor's word unchanged
by the IV's log, the seed's first 32 bytes, the event read through the transcript's answers) and `Q`'s binding
(`qOodBinding`, proved: `FsBind.lean`), as `UniSound.fsLayer128_of_gameV`:

* `rpm_le_kcS`: the random-permutation game to the two-oracle game (the permutation's term);
* the IV moved into the adversary (`hexpU`), the event to the framework's `BreaksOK` at the protocol of the setup's
  commitments (`liftPiop2 (R s)`, `hpre`; the extractor's word read before the IV's log, `hext`);
* `knowledgeSoundness_listChainU_closed128SG` on π2's chain, the openings (`hok_p2`: `W`'s (with π1's three declared
  claims) and `Q`'s decoders, the setup's stack read off the proof), setup (`p2Setup_noLabel`), the last link from
  `Pi2FsLayer`'s (`hlink_p2`), `maxErrK ≤ e` (`maxErrK_p2`);
* the openings' doom (`prEvent_doomFG_p2Ops_le`: π2's four PCS claims once, after π1's three declared claims, through
  `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`,
  and `Q`'s binding) and the seed's pair (`prEvent_pairTr_expLG_le`);
* the numbers (`le_pi2BoundE`): the openings' `(N + 10122)(εExact + 5 (N + 10122)/2^256)` and the binding's
  `N δc 28 ≤ N 2^-160 ≤ N 2^-156` in `pi2Bound`'s openings term (`pi2OpenErr ≥ εExact + 2^-156`, `Pi2OpenErrOK`), its
  `N (N + 1)/2^256` in the chain's term (`8 N` there against the chain's `7 N`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

-- `Layers.lean`'s instance of `SampleableType E` (the one `Pi2FsLayer`'s protocols are at), not `Completeness`'s.
attribute [local instance high] LeanVM.Protocol.instSampleableTypeE

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

/-! ## The numbers -/

/-- **The openings' error in `pi2Bound`** (`Numbers.pi2OpenErr`) covers the PCS claims' per-group bound and `Q`'s
binding per query: `εExact + 2^-156 ≤ pi2OpenErr`. -/
def Pi2OpenErrOK : Prop := εExact + (2 : ℝ≥0∞)⁻¹ ^ 156 ≤ pi2OpenErr

theorem pi2OpenErrOK : Pi2OpenErrOK := le_of_eq rfl

section Bits

theorem le256' {a b : ℕ} (h : a ≤ b) : (a : ℝ≥0∞) / 2 ^ 256 ≤ (b : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

/-- **The composed bound is at most `pi2BoundE`**: the openings' term and `Q`'s binding at `N`, the seed's pair and the
chain's at `N`, the permutation's at `QS 2^32 + Q + 2^49` calls, `N` the two-oracle game's queries (the setup's two
trees, the adversary and the IV, the chain, the openings). -/
theorem le_pi2BoundE (hOE : Pi2OpenErrOK) (e : ℝ≥0∞) (Q QS nQ nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24 + 2 ^ 21)
    (hnQ : nQ ≤ 2 ^ 10) (hr : nRf ≤ 5) (d p m : ℝ≥0∞)
    (hd : d ≤ bndU (QS + (QS + Q + 4) + nQ + 71050) + δBind (QS + (QS + Q + 4) + nQ + 71050))
    (hp : p ≤ ((2 * (QS + (QS + Q + 4) + nQ + 71050) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)
    (hm : m ≤ e) :
    d + p + ((QS + (QS + Q + 4) + nQ + 71050 : ℕ) : ℝ≥0∞) *
        (m + (((nRf + 2) * (QS + (QS + Q + 4) + nQ + 71050) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + 2 ^ 49 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ pi2BoundE e Q := by
  have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have h21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
  have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  set N := QS + (QS + Q + 4) + nQ + 71050 with hNdef
  set M := pi2N Q with hMdef
  have hNM : N + 10122 ≤ M := by rw [hNdef, hMdef]; unfold pi2N; omega
  have hN1 : N + 1 ≤ M := le_trans (Nat.add_le_add_left (by norm_num) N) hNM
  have hNle : N ≤ M := le_trans (Nat.le_succ N) hN1
  -- the openings, once
  have b1 : bndU N ≤ (M : ℝ≥0∞) * (εExact + ((5 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
    mul_le_mul' (Nat.cast_le.mpr hNM) (add_le_add le_rfl (le256' (Nat.mul_le_mul_left 5 hNM)))
  -- `Q`'s binding: `N δc 28` in the openings' term
  have b2 : (N : ℝ≥0∞) * Pcs.δc 28 ≤ (M : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 156 :=
    mul_le_mul' (Nat.cast_le.mpr hNle) (δc_28_le.trans
      (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)))
  have b12 : bndU N + (N : ℝ≥0∞) * Pcs.δc 28 ≤
      (M : ℝ≥0∞) * (pi2OpenErr + ((5 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine (add_le_add b1 b2).trans ?_
    rw [← mul_add]
    refine mul_le_mul' le_rfl ?_
    calc εExact + ((5 * M : ℕ) : ℝ≥0∞) / 2 ^ 256 + (2 : ℝ≥0∞)⁻¹ ^ 156 =
          (εExact + (2 : ℝ≥0∞)⁻¹ ^ 156) + ((5 * M : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring
      _ ≤ _ := add_le_add hOE le_rfl
  -- the pair
  have b3 : p ≤ ((2 * M ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    hp.trans (le256' (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hNle 2)))
  -- the chain, with the binding's `N (N + 1)/2^256`
  have b4 : ((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + (N : ℝ≥0∞) * (m + (((nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      (M : ℝ≥0∞) * (e + ((8 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    rw [mul_add (N : ℝ≥0∞) m, d256]
    calc ((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((N : ℝ≥0∞) * m + ((N * ((nRf + 2) * N) : ℕ) : ℝ≥0∞) / 2 ^ 256)
        = (N : ℝ≥0∞) * m + ((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
            ((N * ((nRf + 2) * N) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring
      _ = (N : ℝ≥0∞) * m + ((N * (N + 1) + N * ((nRf + 2) * N) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [add_assoc, a256]
      _ ≤ (M : ℝ≥0∞) * e + ((M * (8 * M) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          refine add_le_add (mul_le_mul' (Nat.cast_le.mpr hNle) hm) (le256' ?_)
          calc N * (N + 1) + N * ((nRf + 2) * N) ≤ M * M + M * (7 * M) :=
                Nat.add_le_add (Nat.mul_le_mul hNle hN1) (Nat.mul_le_mul hNle
                  (Nat.mul_le_mul (Nat.add_le_add_right hr 2) hNle))
            _ = M * (8 * M) := by ring
      _ = (M : ℝ≥0∞) * (e + ((8 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) := by rw [mul_add, d256]
  -- the permutation
  have b5 : ((QS * 2 ^ 32 + Q + 2 ^ 49 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
    refine ENNReal.div_le_div_right (pow_le_pow_left₀ bot_le (Nat.cast_le.mpr ?_) 2) _
    have h32 : QS * 2 ^ 32 ≤ (3 * 2 ^ 24 + 2 ^ 21) * 2 ^ 32 := Nat.mul_le_mul_right _ hQS
    have h81 : (3 * 2 ^ 24 + 2 ^ 21) * 2 ^ 32 + 2 ^ 49 ≤ (2 : ℕ) ^ 81 := by norm_num
    calc QS * 2 ^ 32 + Q + 2 ^ 49 = (QS * 2 ^ 32 + 2 ^ 49) + Q := by ring
      _ ≤ 2 ^ 81 + Q := Nat.add_le_add_right ((Nat.add_le_add_right h32 _).trans h81) Q
  have hd' : d ≤ bndU N + (N : ℝ≥0∞) * Pcs.δc 28 + ((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    refine hd.trans (le_of_eq ?_)
    unfold δBind
    ring
  unfold pi2BoundE
  calc _ ≤ (bndU N + (N : ℝ≥0∞) * Pcs.δc 28) + ((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + p +
        (N : ℝ≥0∞) * (m + (((nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((QS * 2 ^ 32 + Q + 2 ^ 49 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 :=
      add_le_add (add_le_add (add_le_add hd' le_rfl) le_rfl) le_rfl
    _ = (bndU N + (N : ℝ≥0∞) * Pcs.δc 28) + p +
        (((N * (N + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + (N : ℝ≥0∞) * (m + (((nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256)) +
        ((QS * 2 ^ 32 + Q + 2 ^ 49 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by ring
    _ ≤ (M : ℝ≥0∞) * (pi2OpenErr + ((5 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((2 * M ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (M : ℝ≥0∞) * (e + ((8 * M : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 :=
      add_le_add (add_le_add (add_le_add b12 b3) b4) b5
    _ = _ := by ring

end Bits

/-! ## The links -/

section Links

variable (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniKeccakSound.UniShapesK D.pi1)

include hD in
theorem circuitAt_real (roots : UniKeccak.SetupRootsK) : (D.circuitAt roots).circuit = cc := hD.1 _

/-- **The openings' `OKP`.** -/
theorem hok_p2 : ∀ o ∈ p2Ops, GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) o := by
  intro o ho
  simp only [p2Ops, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact okp_W D hs
  · exact okp_setupOp D hs
  · exact okp_Q D hs

/-- A list of length three. -/
theorem list_three_eq {α : Type} (l : List α) (h : l.length = 3) (d : α) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [a, b, c], _ => rfl

/-- A list of length `n + 1` is its first `n` entries and its last. -/
theorem take_getD_eq {α : Type} : ∀ (l : List α) (n : ℕ), l.length = n + 1 → ∀ d : α, l.take n ++ [l.getD n d] = l
  | [a], 0, _, _ => rfl
  | a :: l, n + 1, h, d => by
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [take_getD_eq l n (by simpa using h) d]
  | [], _, h, _ => by simp at h
  | _ :: _ :: _, 0, h, _ => by simp at h

/-- A list of length one. -/
theorem list_one_eq {α : Type} (l : List α) (h : l.length = 1) (d : α) : l = [l.getD 0 d] := by
  match l, h with
  | [a], _ => rfl

include hD in
/-- **The composition's last link from `Pi2FsLayer`'s**: candidates good at `W`'s and `Q`'s rounds and `none` at
`ρ`'s, the setup's table good, and the check, make the opened transcript `pi2Opened` then `ρ`'s round, the claims
true (`Pi2ClaimsHold`), so the protocol's last state holds. -/
theorem hlink_p2 (R : RecSetupRoots → Compose.Piop pi2K Stk)
    (hpost : ∀ roots (s : Pi2St) (cW cQ : Stk) (ow oq : List E) (inp : Inputs E), inp.scalars = s.2 →
      inp.a.length = 2 ^ (Spec.of (D.circuitAt roots.pi1).circuit).core.logRow →
      ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0 →
      Pi2ClaimsHold D roots inp cW cQ →
      (R roots).post s (pi2Opened cW cQ ow oq inp) (none, inp.a ++ [inp.ξ, inp.s]) [inp.ρ])
    (π : P2Pf) (ch : List (List E)) (cs : List (Option Stk)) (hc : p2Check π ch)
    (hl : cs.length = pi2Spec.K.rounds.length)
    (hg : ∀ i (h : i < cs.length), (pi2Spec.K.spec i).root → p2Good i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), (pi2Spec.K.spec i).root = false → cs[i] = none)
    (hgS : p2GoodS D π ch) :
    ∃ p m c, opened cs (p2View π).2 ch = p ++ [(m, c)] ∧
      (liftPiop2 (R π.roots)).post (p2View π).1 p m c := by
  obtain ⟨hsz, hch, hc0, hc1, hc2, hall⟩ := hc
  have hl3 : cs.length = 3 := hl
  have g0 := hg 0 (by omega) rfl
  have g1 := hg 1 (by omega) rfl
  have n2 := hn 2 (by omega) rfl
  unfold p2Good at g0 g1
  rw [ite_eq_left rfl] at g0
  rw [ite_eq_right (by decide), ite_eq_left rfl] at g1
  obtain ⟨cW, hcW, hW⟩ := g0
  obtain ⟨cQ, hcQ, hQ1, hQ2⟩ := g1
  have hcs : cs = [some cW, some cQ, none] := by
    rw [list_three_eq cs hl3 none]
    simp only [List.getD_eq_getElem _ _ (show 0 < cs.length by omega),
      List.getD_eq_getElem _ _ (show 1 < cs.length by omega), List.getD_eq_getElem _ _ (show 2 < cs.length by omega)]
    rw [hcW, hcQ, n2]
  have hvals : ((p2Msgs π).getD 2 default).2 = (p2Inputs π ch).a ++ [(p2Inputs π ch).ξ, (p2Inputs π ch).s] := by
    show ((p2Msgs π).getD 2 default).2 = ((p2Msgs π).getD 2 default).2.take 16 ++
      [((p2Msgs π).getD 2 default).2.getD 16 0, ((p2Msgs π).getD 2 default).2.getD 17 0]
    rw [p2Msgs_eq]
    rfl
  have hcirc := circuitAt_real D hD π.roots.pi1
  have hpost' := hpost π.roots (stOf (p2View π).1) cW cQ
    [UniSound.scalarAt π.proof.stream 32] [UniSound.scalarAt π.proof.stream 88] (p2Inputs π ch) rfl (by
      rw [hcirc, spec_core_logRow]
      show (((p2Msgs π).getD 2 default).2.take 16).length = 2 ^ 4
      rw [p2Msgs_eq]
      simp) (by rw [hcirc]; exact hall) (by
      unfold Pi2ClaimsHold
      simp only
      rw [hcirc]
      unfold p2GoodS at hgS
      exact ⟨hW, hQ1, hQ2, hgS⟩)
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ch = [a, b, c] := ⟨_, _, _, list_three_eq ch hch []⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2
  obtain ⟨a0, a1, a2, rfl⟩ : ∃ x y z, a = [x, y, z] := ⟨_, _, _, list_three_eq a hc0 0⟩
  obtain ⟨b0, rfl⟩ : ∃ x, b = [x] := ⟨_, list_one_eq b hc1 0⟩
  obtain ⟨c0, rfl⟩ : ∃ x, c = [x] := ⟨_, list_one_eq c hc2 0⟩
  refine ⟨_, _, _, ?_, hpost'⟩
  rw [hcs]
  unfold p2View
  rw [p2Msgs_eq]
  rw [p2Msgs_eq] at hvals
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hvals
  simp only [List.map_cons, List.map_nil, opened, List.headD_cons, List.tail_cons, UniSound.toRMsg,
    Option.map_some, Option.map_none, hvals]
  rfl

end Links

/-! ## The Fiat–Shamir layer -/

/-- **π2's Fiat–Shamir layer from its bridges** at the real deployment: the coupling (`hG`), the composed verifier's
duplex shape and cost (`hdup`, `hcost`), the IV in the adversary (`hIvAdv`, `hexpU`), the extractor's word before the
IV's log (`hext`), the seed's first 32 bytes (`hlab`), the event read through the transcript's answers (`hcongr`),
the chain's queries (`hnQ`); `Q`'s binding is proved (`qOodBinding`, `FsBind.lean`). -/
theorem pi2FsLayer_of (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniKeccakSound.UniShapesK D.pi1)
    (hG : ∀ (P : RecSetupRoots → Pi2St → Stk → Prop) (A : RecAdversary),
      Pr{let z ← recSoundnessExperiment2 D A}[acc z = true ∧
          ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w)] ≤
        Pr{let z ← Common.runWithRandomPermutation (rpmGameS (p2Setup D hs) p2Fix (p2Adv A) (p2Ver D))}[
          P2BreaksRel P (ivOut2 z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))])
    (hdup : ∀ π, LeanVM.Rpm.DuplexVm (p2Ver D π) [])
    (hcost : ∀ π, Common.QueryCostAtMost (p2Ver D π) LeanVM.Rpm.hashBlocks (2 ^ 49))
    (hIvAdv : ∀ (A₀ : SOut → OracleComp KeccakCalls P2Pf) (n : ℕ), (∀ s, IsTotalQueryBound (A₀ s) n) →
      ∀ s, IsTotalQueryBound (p2IvAdv D A₀ s) (n + 4))
    (hexpU : ∀ A₀ : SOut → OracleComp KeccakCalls P2Pf,
      expU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) (gopsRun p2View p2Ops) =
        (fun w => (ivOut2 w.1, w.2 ++ ivLog D w.1.1 w.1.2.1)) <$> kcGameS (p2Setup D hs) p2Fix A₀ (p2Ver D))
    (hext : ∀ (z : P2Pf × (List (List E) × List Bool)) (tr : Transcript) (π : P2Pf)
      (x : Bytes32 × Bytes32 × Bytes32 × Bytes32),
      extractorK (fun i => (p2Tc i).commit) p2View (z, tr ++ ivLog D π x) =
        extractorK (fun i => (p2Tc i).commit) p2View (z, tr))
    (hlab : ∀ (A₀ : SOut → OracleComp KeccakCalls P2Pf) (T : KTable), ∃ w,
      Sum.inl w ∈ (tableQueryLog (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) T).map Sigma.fst ∧
      (pi2Spec.label (p2View (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)))).1).take 32 =
        RecStatement.name ++ (viewT T w).toList.take (32 - RecStatement.name.length))
    (hcongr : ∀ (P : RecSetupRoots → Pi2St → Stk → Prop) (z : P2Pf × (List (List E) × List Bool))
      (tr tr' : Transcript), (∀ x, lookTr tr x = lookTr tr' x) → P2BreaksRel P (z, tr) →
        P2BreaksRel P (z, tr'))
    (hnQ : pi2Spec.K.nQ ≤ 2 ^ 10) :
    Pi2FsLayer D := by
  intro R e herr P hpre hpost A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (p2Setup D hs) (hOnly_p2Setup D hs) (p2QS D) (p2QS D * 2 ^ 32)
    (isTotalQueryBound_p2Setup D hs) (cost_p2Setup D hs) p2Fix (p2Adv A) Q
    (fun s => Common.isWeightBound_map _ (hQ _)) (p2Ver D) hdup (2 ^ 49) hcost
    (fun z tr => P2BreaksRel P (ivOut2 z, tr)) (fun z tr tr' h hz => hcongr P _ tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128SG pi2Spec p2View
    (fun s => liftPiop2 (R s)) (fun π => π.roots) p2Ops p2Tc p2Check p2Good (p2GoodS D)
    (p2Setup D hs) p2Fix (p2Stk D) (p2IvAdv D A₀) (p2QS D) (p2QS D + Q + 4) (isTotalQueryBound_p2Setup D hs)
    (hIvAdv A₀ _ hA₀) (fun _ _ => rfl) (hok_p2 D hs) hcov_p2 (hS_p2 D) (fun π _ _ => hfit_p2 π)
    (fun π ch cs hc hl hg hn hgS => hlink_p2 D hD R hpost π ch cs hc hl hg hn hgS) (p2Setup_noLabel D hs)
    RecStatement.name (hlab A₀) e (fun s => maxErrK_p2 _ e fun j hj => herr _ j hj)
  have hkc : Pr{let z ← (simulateQ randomOracle (kcGameS (p2Setup D hs) p2Fix A₀ (p2Ver D))).run' ∅}[
        P2BreaksRel P (ivOut2 z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀))
          (gopsRun p2View p2Ops))).run' ∅}[
        BreaksOK pi2Spec.K (fun i => (p2Tc i).commit) (liftPiop2 (R z.1.1.roots)) p2View p2Check
          (fun bs => ∀ k < p2Ops.length, bs.getD k false = true) z] := by
    rw [hexpU A₀, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨h1, h2, fun c hc hpre' => ?_⟩
    rw [hext] at hc
    have hc' := hc
    simp only [extractorK, optC, msgK_p2View_zero, List.mem_map] at hc'
    obtain ⟨q, -, rfl⟩ := hc'
    exact h3 _ hc q rfl (hpre _ _ _ _ hpre')
  -- The run before the openings, and its queries.
  set X := preU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) with hXdef
  have hX : IsTotalQueryBound X (p2QS D + (p2QS D + Q + 4) + pi2Spec.K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _ (isTotalQueryBound_p2Setup D hs)
      (hIvAdv A₀ _ hA₀))
  -- The openings once, and `Q`'s binding.
  have hdoom := prEvent_doomFG_p2Ops_le X _ hX
  -- The seed's pair.
  have hpair := prEvent_pairTr_expLG_le p2View X p2Ops _ hX RecStatement.name name_length
  have hsum : (p2Ops.map fun o => o.QO).sum = 71050 := by simp [p2Ops, PcsOp.gop, qOp, wOpM]
  refine (hG P A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  rw [hsum] at hpair ⊢
  exact le_pi2BoundE pi2OpenErrOK e Q (p2QS D) pi2Spec.K.nQ pi2Spec.nRf (p2QS_le D hs) hnQ (show 5 ≤ 5 by decide)
    _ _ _ hdoom hpair le_rfl

end RecCompose

/-- info: 'RecCompose.le_pi2BoundE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.le_pi2BoundE

/-- info: 'RecCompose.hlink_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hlink_p2

/-- info: 'RecCompose.pi2FsLayer_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_of
