-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's Flock prover (`Rec4Prover.lean`'s
-- `flockProve4`) against its verifier (`Rec4VerifierH.lean`'s `verifyWalkedKH4`): `FlockProverSync.lean`'s
-- `syncs_zerocheck`, `syncs_front`, `flockSyncs`, `FlockProverShape.lean`'s `zerocheckW_eq`, `frontW_eq`,
-- `FlockProverSum.lean`'s `zc_values`, `terminalHolds` and `FlockProverMain.lean`'s `flockRingSum` with the zerocheck's
-- first coordinate given (`zerocheckW4`) and no ring map drawn.
import UniKeccakComplete.K.FlockProverMain
import UniKeccakComplete.K.Rec4Prover

/-!
# π1-rec4's Flock: in step with its verifier, its terminal zero, its ring identity at every map

At a pure Keccak-256 `H` (`Id`), every writer (any challenges), every first coordinate `c`, on `q_flock`'s words `q`:

* **`flockSyncs4`**: `verifyWalkedKH4 (pure ∘ H) log_n v c`, on a channel synchronised with the prover's writer, reads
  `flockProve4`'s messages, draws the same challenges, collects one value `flockZero4` (the lincheck's terminal check
  on the honest front) and returns the prover's output (Flock's point, the slices);
* **`flockZero4_eq_zero`** (`log_n = 17 + κ`, `k ≤ 6`, `FlockHolds κ q`): that value is zero (`terminalHolds4`, the
  main line's argument on `zerocheckW4`'s run: `zc_values4`, the univariate skip's completeness `Skip.skipComplete`);
* **`flockRingSum4`**: at **every** map of six challenges (π1-rec4 draws it after `C2`), the target of the slices
  sent is `Σ_u Φ(eq(point, u)) q_flock[u]` (`ringHolds_pure`);
* `flock4_point_length_trace`: on a trace, the point has `h_SHA3 + 11` coordinates.

The proofs are the π1-rec3 ones (`FlockProverSync`, `FlockProverShape`, `FlockProverSum`, `FlockProverMain`) with the
zerocheck's run `zerocheckW4_eq` (its sampled coordinates `squares c …`, of the same length) in place of
`zerocheckW_eq`; the programs are unfolded one bind at a time into existentials, as there.
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol.KeccakHash Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The runs -/

section Runs

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-- **π1-rec4's zerocheck** is the skip's start and the rounds' output, its sampled coordinates `squares c …`. -/
theorem zerocheckW4_eq (logN k : ℕ) (c : E) (wit : Wit) (w : Wr) :
    ∃ (sampled : List E) (st : ZcStart) (zc : ZcOut), sampled.length = logN - k - nFixed ∧
      (∃ w1, st = ((skipW H k (fixedChallenges ++ sampled) wit).run w1).1) ∧
      (∃ w2, zc = ((zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c).run w2).1) ∧
      ((Rec4.zerocheckW4 H logN k c wit).run w).1 =
        (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb) := by
  refine ⟨squares c (logN - k - nFixed), _, _, squares_length _ _, ⟨w, rfl⟩,
    ⟨((skipW H k (fixedChallenges ++ squares c (logN - k - nFixed)) wit).run w).2, rfl⟩, ?_⟩
  simp only [Rec4.zerocheckW4, run_bind_id, run_pure_id]

/-- **π1-rec4's front** is `frontOf` of the zerocheck's output, `α` and the lincheck's output. -/
theorem frontW4_eq (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    ∃ (zc : Option E × List E × E × E × E) (alpha : E) (lc : LcOut),
      zc = ((Rec4.zerocheckW4 H logN v.skip c (witOf logN q)).run w).1 ∧
      (∃ w2, lc = ((lcRounds H UniKeccak.lincheckRoundsK (lcClaim zc alpha) (lcWeightsOf v.skip zc alpha)
        (lcWitnessOf v.skip q zc)).run w2).1) ∧
      ((Rec4.frontW4 H logN v c q).run w).1 = frontOf v zc alpha lc := by
  refine ⟨_, ((sampleW H).run ((Rec4.zerocheckW4 H logN v.skip c (witOf logN q)).run w).2).1, _, rfl,
    ⟨((sampleW H).run ((Rec4.zerocheckW4 H logN v.skip c (witOf logN q)).run w).2).2, rfl⟩, ?_⟩
  simp only [Rec4.frontW4, run_bind_id, run_pure_id]

/-- **π1-rec4's front holds the slices it sent.** -/
theorem frontW4_slices (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    ((Rec4.frontW4 H logN v c q).run w).1.1.slices = some ((Rec4.frontW4 H logN v c q).run w).1.2 := by
  obtain ⟨zc, alpha, lc, _, _, hfr⟩ := frontW4_eq H logN v c q w
  rw [hfr]
  rfl

/-- **π1-rec4's Flock prover's output**: the front's point and slices. -/
theorem flockProve4_run (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    ((Rec4.flockProve4 H logN v c q).run w).1 =
      (((Rec4.frontW4 H logN v c q).run w).1.1.point, ((Rec4.frontW4 H logN v c q).run w).1.2) := by
  simp only [Rec4.flockProve4, run_bind_id, run_pure_id]

/-- **The front's point has `log_n − 6` coordinates** (`log_n ≥ 17`, `k ≤ 6`). -/
theorem frontW4_point_length (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr)
    (hk : v.skip ≤ 6) (hN : 17 ≤ logN) :
    ((Rec4.frontW4 H logN v c q).run w).1.1.point.length = logN - 6 := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW4_eq H logN v c q w
  obtain ⟨sampled, st, zo, hlen, -, ⟨w3, hzo⟩, heq⟩ := zerocheckW4_eq H logN v.skip c (witOf logN q) w
  have hchi : zc.2.1.length = logN - v.skip := by
    rw [hzc, heq]
    show zo.chi.length = _
    rw [hzo, zcRounds_chi_length, List.length_append, fixedChallenges_length, hlen]
    unfold nFixed
    omega
  have hlen' : lc.challenges.length = 11 := by rw [hlc, lcRounds_length]; rfl
  have hsz : lc.z.size = 64 := by
    rw [hlc, lcRounds_z]
    refine foldl_foldHigh_size _ 6 _ ?_
    rw [lcRounds_length, lcWitnessOf_size]
    rfl
  rw [hfr]
  exact (frontOf_shape v zc alpha lc logN hk hN hchi hlen' hsz).2.2.2.2.2.2

end Runs

/-! ## In step with the verifier -/

section Sync

variable (H : List UInt8 → LeanVM.Protocol.Digest)

/-- **π1-rec4's zerocheck**: no draw (the first coordinate given), the coset values and `z` (with a skip), the rounds,
`v_a`, `v_b`. -/
theorem syncs_zerocheck4 (logN k : ℕ) (c : E) (wit : Wit) (w : Wr) :
    Syncs (Rec4.Flock.zerocheckFirstH (m := Id) (Pure.pure ∘ H) logN k c)
      (Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit) w
      (((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit).run w).1.1,
        ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit).run w).1.2.1,
        ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit).run w).1.2.2.1,
        ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit).run w).1.2.2.2.1,
        ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN k c wit).run w).1.2.2.2.2) [] := by
  by_cases hk : 0 < k
  · have hk' : (k > 0) = True := eq_true hk
    unfold Rec4.Flock.zerocheckFirstH Rec4.zerocheckW4 skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, sumcheckH_eq, startAt]
    refine Syncs.bind' (syncs_scalars' (cosetValues k (fixedChallenges ++ squares c (logN - k - nFixed)) wit)
      (2 ^ k) (cosetValues_length _ _ _) _) ?_
    refine Syncs.bind' (syncs_sample H _) ?_
    refine Syncs.bind' (syncs_zcRounds H (fixedChallenges ++ squares c (logN - k - nFixed)) _ _ _ _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
    simp only [run_bind_id, run_pure_id, sampleW_run]
  · have hk' : (k > 0) = False := eq_false hk
    unfold Rec4.Flock.zerocheckFirstH Rec4.zerocheckW4 skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, sumcheckH_eq, startNone]
    refine Syncs.bind' (syncs_zcRounds H (fixedChallenges ++ squares c (logN - k - nFixed)) 0 wit.a wit.b wit.c w) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
    simp only [run_bind_id, run_pure_id, sampleW_run]

/-- **π1-rec4's front**: the zerocheck from `c`, `α`, the lincheck's 11 rounds, the slices; the verifier's `Front` is
the prover's. -/
theorem syncs_front4 (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    Syncs (Rec4.frontKH4 (m := Id) (Pure.pure ∘ H) logN v c) (Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q) w
      ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1 [] := by
  unfold Rec4.frontKH4 Rec4.frontW4
  simp only [bind_assoc, pure_bind, sumcheckH_eq, map_eq_bind_pure_comp]
  refine Syncs.bind' (syncs_zerocheck4 H logN v.skip c (witOf logN q) w) ?_
  refine Syncs.bind' (syncs_sample H _) ?_
  simp only [sampleW_run, lcClaim]
  refine Syncs.bind' (syncs_lcRounds H UniKeccak.lincheckRoundsK _
    (lcWeightsOf v.skip ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN v.skip c (witOf logN q)).run w).1
      (Wr.sampled H ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN v.skip c (witOf logN q)).run w).2).1)
    (lcWitnessOf v.skip q ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN v.skip c (witOf logN q)).run w).1)
    (Wr.sampled H ((Rec4.zerocheckW4 (m := Id) (Pure.pure ∘ H) logN v.skip c (witOf logN q)).run w).2).2) ?_
  refine Syncs.bind' (syncs_scalars' _ kBits (lcRounds_z_length H _ _ _ _ _ _) _) ?_
  refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
  simp only [run_bind_id, run_pure_id, sampleW_run, frontOf]

/-- **The value π1-rec4's verifier collects on the honest front** from the writer `w`: the lincheck's terminal check
(`verifyWalkedK4`'s `require_zero`). -/
def flockZero4 (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) : E :=
  let fr := ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1
  UniKeccak.structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime (fr.slices.getD []) fr.alpha + fr.rLc

theorem flockZero4_eq' (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    flockZero4 H logN v c q w =
      UniKeccak.structuredTerminal ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.zSkip
          ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.rowLow
          ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.chiIn
          ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.chiInPrime
          (((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.slices.getD [])
          ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.alpha +
        ((Rec4.frontW4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1.1.rLc :=
  rfl

/-- **π1-rec4's Flock prover in step with `verifyWalkedKH4`**: from every writer, the verifier returns the prover's
output (the point, the slices) and collects `flockZero4`. -/
theorem flockSyncs4 (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E) (q : Array K) (w : Wr) :
    Syncs (Rec4.verifyWalkedKH4 (m := Id) (Pure.pure ∘ H) logN v c)
      (Rec4.flockProve4 (m := Id) (Pure.pure ∘ H) logN v c q) w
      ((Rec4.flockProve4 (m := Id) (Pure.pure ∘ H) logN v c q).run w).1 [flockZero4 H logN v c q w] := by
  have hsl := frontW4_slices (Pure.pure ∘ H) logN v c q w
  rw [flockZero4_eq' H logN v c q w]
  unfold Rec4.verifyWalkedKH4 Rec4.flockProve4
  refine syncs_bind_nil (syncs_front4 H logN v c q w) ?_
  refine syncs_requireZero_then ?_
  rw [hsl, Option.getD_some]
  refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
  simp only [run_bind_id, run_pure_id]

end Sync

/-! ## The terminal vanishes -/

/-- **π1-rec4's zerocheck's values** (`v_a`, `v_b`, `v_c`) are `A z`, `B z`, `z` at its point (`zc_values` on
`zerocheckW4`'s run). -/
theorem zc_values4 (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ k : ℕ) (c : E) (hk : k ≤ 6) (q : Array K)
    (hF : FlockHolds κ q) (hskipC : 0 < k → SkipComplete k) (w : Wr) :
    ∃ (zSkip : Option E) (low chiIn chiRest : List E) (va vb vc : E),
      ((Rec4.zerocheckW4 H (17 + κ) k c (witOf (17 + κ) q)).run w).1 = (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) ∧
      low.length = 6 - k ∧ chiIn.length = 11 ∧ chiRest.length = κ ∧
      (rowLowWeights zSkip low).1.length = 2 ^ k ∧
      va = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * aZ q t row ∧
      vb = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * bZ q t row ∧
      vc = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * zAt q t row := by
  obtain ⟨sampled, st, zo, hlen, ⟨w1, hst⟩, ⟨w2, hzo⟩, heq⟩ :=
    zerocheckW4_eq H (17 + κ) k c (witOf (17 + κ) q) w
  generalize hr : fixedChallenges ++ sampled = r at hst hzo
  have hrlen : r.length = 17 + κ - k := by
    rw [← hr, List.length_append, fixedChallenges_length, hlen]; unfold nFixed; omega
  have hkr : k + r.length = 17 + κ := by omega
  have hchilen : zo.chi.length = 17 + κ - k := by rw [hzo, zcRounds_chi_length, hrlen]
  have hlow : (zo.chi.take (packing - k)).length = 6 - k := by
    rw [List.length_take, hchilen]; unfold packing; omega
  have hin : ((zo.chi.drop (packing - k)).take UniKeccak.lincheckRoundsK).length = 11 := by
    rw [List.length_take, List.length_drop, hchilen, lincheckRoundsK_eq]; unfold packing; omega
  have hcr : ((zo.chi.drop (packing - k)).drop UniKeccak.lincheckRoundsK).length = κ := by
    rw [List.length_drop, List.length_drop, hchilen, lincheckRoundsK_eq]; unfold packing; omega
  have hchi : zo.chi.take (packing - k) ++ (zo.chi.drop (packing - k)).take UniKeccak.lincheckRoundsK ++
      (zo.chi.drop (packing - k)).drop UniKeccak.lincheckRoundsK = zo.chi := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  generalize hlowdef : zo.chi.take (packing - k) = low at hlow hchi
  generalize hindef : (zo.chi.drop (packing - k)).take UniKeccak.lincheckRoundsK = chiIn at hin hchi
  generalize hcrdef : (zo.chi.drop (packing - k)).drop UniKeccak.lincheckRoundsK = chiRest at hcr hchi
  have hstart := skip_start H κ k hk q hF hskipC r hkr low hlow w1 st hst
  have hsk := hstart.1
  have hsa := hstart.2.1
  have hsb := hstart.2.2.1
  have hsc := hstart.2.2.2.1
  have hea := hstart.2.2.2.2.1
  have heb := hstart.2.2.2.2.2.1
  have hec := hstart.2.2.2.2.2.2.1
  have hclaim := hstart.2.2.2.2.2.2.2
  have hzc3 := zcRounds_complete H r st.claim st.a st.b st.c w2 hsa hsb hsc hclaim
  rw [← hzo] at hzc3
  have hptlen : (low ++ chiIn ++ chiRest).length = r.length := by rw [hchi, hchilen, hrlen]
  have hTz : ∀ (Tz : Array E), Tz.size = 2 ^ r.length → Tz.size = 2 ^ (low ++ chiIn ++ chiRest).length :=
    fun Tz h ↦ by rw [hptlen]; exact h
  have hE : ∀ (Tz T : Array E), (∀ b < 2 ^ r.length, Tz.getD b 0 = ∑ x ∈ range (2 ^ k),
      (rowLowWeights st.zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0) →
      ∀ b < 2 ^ (low ++ chiIn ++ chiRest).length, Tz.getD b 0 = ∑ x ∈ range (2 ^ k),
        (rowLowWeights st.zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0 :=
    fun Tz T h b hb ↦ h b (by rw [← hptlen]; exact hb)
  have va := zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.a (hTz _ hsa)
    (hE _ _ hea) (aZ q) (fun row hrow t ht ↦ (witOf_getD κ q hrow ht).1)
  have vb := zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.b (hTz _ hsb)
    (hE _ _ heb) (bZ q) (fun row hrow t ht ↦ (witOf_getD κ q hrow ht).2.1)
  have vc := zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.c (hTz _ hsc)
    (hE _ _ hec) (zAt q) (fun row hrow t ht ↦ (witOf_getD κ q hrow ht).2.2)
  rw [hchi] at va vb vc
  refine ⟨st.zSkip, low, chiIn, chiRest, zo.va, zo.vb, zo.running + zo.va * zo.vb, ?_, hlow, hin, hcr, hsk,
    ?_, ?_, ?_⟩
  · rw [heq, hchi]
  · rw [hzc3.1, va]
  · rw [hzc3.2.1, vb]
  · rw [hzc3.2.2, ← vc, add_comm, ← add_assoc, add_self_E, zero_add]

/-- **π1-rec4's lincheck's terminal check vanishes on the honest front** (`terminalHolds` on `frontW4`'s run). -/
theorem terminalHolds4 (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant) (c : E)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hF : FlockHolds κ q) :
    UniKeccak.structuredTerminal ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.zSkip
        ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.rowLow ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.chiIn
        ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.chiInPrime
        (((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.slices.getD [])
        ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.alpha +
      ((Rec4.frontW4 H (17 + κ) v c q).run w).1.1.rLc = 0 := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW4_eq H (17 + κ) v c q w
  obtain ⟨zSkip, low, chiIn, chiRest, va, vb, vc, hzeq, hlow, hin, hcr, hsk, hva, hvb, hvc⟩ :=
    zc_values4 H κ v.skip c hk q hF (fun _ ↦ Skip.skipComplete _ hk) w
  rw [← hzc] at hzeq
  subst hzeq
  rw [hfr]
  have hχ : lc.challenges.length = 11 := by rw [hlc, lcRounds_length]; rfl
  have hpk : packing - v.skip = low.length := by rw [hlow]; unfold packing; rfl
  have h1 : (low ++ chiIn ++ chiRest).take (packing - v.skip) = low := by
    rw [hpk, List.append_assoc, List.take_left' rfl]
  have h2 : ((low ++ chiIn ++ chiRest).drop (packing - v.skip)).take UniKeccak.lincheckRoundsK = chiIn := by
    rw [hpk, List.append_assoc, List.drop_left' rfl, List.take_left' (by rw [hin]; rfl)]
  have h3 : ((low ++ chiIn ++ chiRest).drop (packing - v.skip)).drop UniKeccak.lincheckRoundsK = chiRest := by
    rw [hpk, List.append_assoc, List.drop_left' rfl, List.drop_left' (by rw [hin]; rfl)]
  have hW : lcWeightsOf v.skip (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) alpha =
      lincheckWeights (rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha := by
    unfold lcWeightsOf; rw [h1, h2]
  have hZ : lcWitnessOf v.skip q (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) = lincheckWitness q chiRest := by
    unfold lcWitnessOf; rw [h3]
  rw [hW, hZ] at hlc
  have hWs : (lincheckWeights (rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha).size =
      2 ^ (UniKeccak.lincheckRoundsK + 6) := by
    rw [show UniKeccak.lincheckRoundsK + 6 = 17 from rfl]
    simp [lincheckWeights, keccakR1csLogSize]
  have hZs : (lincheckWitness q chiRest).size = 2 ^ (UniKeccak.lincheckRoundsK + 6) := by
    rw [show UniKeccak.lincheckRoundsK + 6 = 17 from rfl]
    simp [lincheckWitness, keccakR1csLogSize]
  have hinit : lcClaim (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) alpha =
      ∑ i ∈ range (2 ^ (UniKeccak.lincheckRoundsK + 6)),
        (lincheckWeights (rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha).getD i 0 *
          (lincheckWitness q chiRest).getD i 0 := by
    rw [show (2 : ℕ) ^ (UniKeccak.lincheckRoundsK + 6) = 2 ^ 17 from rfl, lincheck_init,
      lincheckWitness_pin κ q hF chiRest hcr, mul_one, ← hva, ← hvb, ← hvc]
    rfl
  have hcomp := lcRounds_complete H UniKeccak.lincheckRoundsK 6 _ _ _ w2 hWs hZs hinit
  rw [← hlc] at hcomp
  have hz : lc.z = lc.challenges.foldl foldHigh (lincheckWitness q chiRest) := by rw [hlc, lcRounds_z]
  have hs : lc.z.toList.length = 64 := by
    rw [Array.length_toList, hz]
    exact foldl_foldHigh_size _ 6 _ (by rw [hχ]; simp [lincheckWitness, keccakR1csLogSize])
  simp only [frontOf, h1, h2, Option.getD_some]
  refine terminal_pure v.skip hk zSkip low chiIn lc.challenges alpha lc.claim lc.z.toList hsk hlow hin hχ hs ?_
  rw [hcomp, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [toList_getD, hz]

/-- **The value π1-rec4's verifier collects on the honest front is zero**, at `log_n = 17 + κ`, `k ≤ 6`, every first
coordinate and writer, given Flock's relation on `q_flock`. -/
theorem flockZero4_eq_zero (H : List UInt8 → LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant) (c : E)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hF : FlockHolds κ q) : flockZero4 H (17 + κ) v c q w = 0 :=
  terminalHolds4 (Pure.pure ∘ H) κ v c q w hk hF

/-! ## The ring identity at every map, the point's length -/

/-- **π1-rec4's Flock ring identity** (tower order): at every map of six challenges, the target of the slices sent
is `Σ_u Φ(eq(point, u)) q_flock[u]`. -/
theorem flockRingSum4 (H : List UInt8 → Id LeanVM.Protocol.Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : E)
    (q : Array K) (w : Wr) (map : List E) (hmap : map.length = 6) :
    ∑ u ∈ range (2 ^ ((Rec4.flockProve4 H logN v c q).run w).1.1.length),
      towerRingMap ((eqKernel ((Rec4.flockProve4 H logN v c q).run w).1.1).getD u 0) map * ofK (q.getD u 0) =
        towerTarget ((Rec4.flockProve4 H logN v c q).run w).1.2 map := by
  rw [flockProve4_run]
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW4_eq H logN v c q w
  have hlen : lc.challenges.length = 11 := by rw [hlc, lcRounds_length]; rfl
  have hz : lc.z = lc.challenges.foldl foldHigh (lcWitnessOf v.skip q zc) := by rw [hlc, lcRounds_z]
  generalize ((Rec4.frontW4 H logN v c q).run w).1 = frs at hfr ⊢
  subst hfr
  show ∑ u ∈ range (2 ^ (lc.challenges.reverse ++
        (zc.2.1.drop (packing - v.skip)).drop UniKeccak.lincheckRoundsK).length),
      towerRingMap ((eqKernel (lc.challenges.reverse ++
        (zc.2.1.drop (packing - v.skip)).drop UniKeccak.lincheckRoundsK)).getD u 0) map * ofK (q.getD u 0) =
    towerTarget lc.z.toList map
  rw [hz]
  exact ringHolds_pure q _ lc.challenges map hlen hmap

/-- **On a trace, π1-rec4's Flock point has `h_SHA3 + 11` coordinates.** -/
theorem flock4_point_length_trace (H : List UInt8 → LeanVM.Protocol.Digest) (tr : Trace)
    (v : UniKeccak.KeccakVariant) (hk : v.skip ≤ 6) (c : E) (w : Wr) :
    ((Rec4.flockProve4 (m := Id) (Pure.pure ∘ H) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) v c
      tr.qflock).run w).1.1.length = tr.shape.heights.getD opSha3 0 + 11 := by
  rw [flockProve4_run]
  dsimp only
  rw [frontW4_point_length (Pure.pure ∘ H) _ v c _ w hk (by unfold keccakR1csLogSize; omega)]
  unfold keccakR1csLogSize
  omega

end UniKeccakComplete.FlockP

/-- info: 'UniKeccakComplete.FlockP.flockSyncs4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.FlockP.flockSyncs4

/-- info: 'UniKeccakComplete.FlockP.flockZero4_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.FlockP.flockZero4_eq_zero

/-- info: 'UniKeccakComplete.FlockP.flockRingSum4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.FlockP.flockRingSum4

/-- info: 'UniKeccakComplete.FlockP.flock4_point_length_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.FlockP.flock4_point_length_trace
