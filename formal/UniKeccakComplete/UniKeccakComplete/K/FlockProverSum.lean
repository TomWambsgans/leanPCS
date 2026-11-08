-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockProverSum.lean`.
import UniKeccakComplete.K.FlockProverSumZc

/-!
# The lincheck's terminal check vanishes on the honest front: `terminalHolds`

**`terminalHolds`**: for the honest prover at `log_n = 17 + κ`, any skip `k ≤ 6`, either Fiat–Shamir shape, every
writer (any challenges), if `q_flock` satisfies Flock's relation (`FlockHolds κ q`, `TraceHonest.flock`), the
verifier's check `structuredTerminal zSkip row_low chi_in chi_in' s α + r_lc` on the prover's front is zero, **given,
for `k > 0`, the univariate skip's completeness** (`SkipComplete k`: the verifier's interpolation of `2^k` zeros and
the prover's coset values at `z` is the skip polynomial's value `Σ_b eq(r, b) (Â B̂ + Ẑ)(z, b)` whenever
`Az ∘ Bz + z` vanishes on every position; a fact about `lagrangeWeights` and the PHI nodes alone, proved for every
`k ≤ 6` in `FlockProverSkip.lean`, `Skip.skipComplete`). At `k = 0` there is no skip.

The chain: the zerocheck's claim is its summand's sum (the R1CS, or `SkipComplete`), its rounds keep it
(`zcRounds_complete`), so `v_a`, `v_b`, `v_c` are `A z`, `B z`, `z` at the zerocheck's point (`zc_fold_eq`); the
lincheck's first claim is then its weights against its witness (`lincheck_init`, the pin `lincheckWitness_pin`),
its rounds keep it (`lcRounds_complete`), and its last claim makes the terminal check vanish (`terminal_pure`).
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- **The univariate skip's completeness** at `k` skip variables (the one fact the terminal's identity assumes,
for `k > 0`): for tables `A z`, `B z`, `z` of `2^(k + |r|)` entries with `Az ∘ Bz + z = 0` everywhere, the verifier's
start of the zerocheck (`lagrange_interpolate(2^(k+1), 0^(2^k) ++ coset, z)`, the prover's coset values) is the sum
`Σ_b eq(r, b) (A_z B_z + Z_z)(b)` of the tables at the skip's point (`skipFold` by `lagrangeWeights (2^k) z`). -/
def SkipComplete (k : ℕ) : Prop :=
  ∀ (r : List E) (wit : Wit) (z : E), wit.a.size = 2 ^ (k + r.length) → wit.b.size = 2 ^ (k + r.length) →
    wit.c.size = 2 ^ (k + r.length) →
    (∀ i < 2 ^ (k + r.length), wit.a.getD i 0 * wit.b.getD i 0 + wit.c.getD i 0 = 0) →
    lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ cosetValues k r wit) z =
      ∑ b ∈ range (2 ^ r.length), eqB r b *
        ((skipFold k (lagrangeWeights (2 ^ k) z) wit.a).getD b 0 *
          (skipFold k (lagrangeWeights (2 ^ k) z) wit.b).getD b 0 +
          (skipFold k (lagrangeWeights (2 ^ k) z) wit.c).getD b 0)

/-! ## The witness's tables -/

theorem witOf_size (logN : ℕ) (q : Array K) :
    (witOf logN q).a.size = 2 ^ logN ∧ (witOf logN q).b.size = 2 ^ logN ∧ (witOf logN q).c.size = 2 ^ logN := by
  simp [witOf]

theorem witOf_getD (κ : ℕ) (q : Array K) {row t : ℕ} (hrow : row < 2 ^ 17) (ht : t < 2 ^ κ) :
    (witOf (17 + κ) q).a.getD (row + 2 ^ 17 * t) 0 = aZ q t row ∧
      (witOf (17 + κ) q).b.getD (row + 2 ^ 17 * t) 0 = bZ q t row ∧
      (witOf (17 + κ) q).c.getD (row + 2 ^ 17 * t) 0 = zAt q t row := by
  have hi : row + 2 ^ 17 * t < 2 ^ (17 + κ) := by
    rw [pow_add]
    calc row + 2 ^ 17 * t < 2 ^ 17 + 2 ^ 17 * t := by omega
      _ = 2 ^ 17 * (t + 1) := by ring
      _ ≤ 2 ^ 17 * 2 ^ κ := Nat.mul_le_mul_left _ ht
  have hdiv : (row + 2 ^ 17 * t) / 2 ^ 17 = t := by
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hrow, zero_add]
  have hmod : (row + 2 ^ 17 * t) % 2 ^ 17 = row := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have ht' : t < 2 ^ (17 + κ - keccakR1csLogSize) := by
    unfold keccakR1csLogSize; rw [show 17 + κ - 17 = κ by omega]; exact ht
  refine ⟨?_, ?_, ?_⟩
  · rw [witOf]
    simp only
    rw [E2ECompleteness.getD_ofFn' _ hi]
    simp only [hdiv, hmod]
    rw [E2ECompleteness.getD_ofFn' _ ht']
    simp only [aZ]
  · rw [witOf]
    simp only
    rw [E2ECompleteness.getD_ofFn' _ hi]
    simp only [hdiv, hmod]
    rw [E2ECompleteness.getD_ofFn' _ ht']
    simp only [bZ]
  · rw [witOf]
    simp only
    rw [E2ECompleteness.getD_ofFn' _ hi]
    simp only [hdiv, hmod]

/-- **The R1CS on the witness's tables**: `Az ∘ Bz + z = 0` at every position. -/
theorem witOf_holds (κ : ℕ) (q : Array K) (hF : FlockHolds κ q) :
    ∀ i < 2 ^ (17 + κ), (witOf (17 + κ) q).a.getD i 0 * (witOf (17 + κ) q).b.getD i 0 +
      (witOf (17 + κ) q).c.getD i 0 = 0 := by
  intro i hi
  have hdecomp : i = i % 2 ^ 17 + 2 ^ 17 * (i / 2 ^ 17) := (Nat.mod_add_div i _).symm
  have hrow : i % 2 ^ 17 < 2 ^ 17 := Nat.mod_lt _ (by norm_num)
  have ht : i / 2 ^ 17 < 2 ^ κ := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_add, add_comm]; exact hi
  obtain ⟨ha, hb, hc⟩ := witOf_getD κ q hrow ht
  rw [hdecomp, ha, hb, hc, (blocks_hold κ q hF ht).1 _ hrow]
  exact add_self_E _

/-! ## The zerocheck's values -/

theorem skipFold_size (k : ℕ) (w : List E) (T : Array E) : (skipFold k w T).size = T.size / 2 ^ k := by
  simp [skipFold]

theorem skipFold_getD (k : ℕ) (w : List E) (T : Array E) {b : ℕ} (hb : b < T.size / 2 ^ k) :
    (skipFold k w T).getD b 0 = ∑ x ∈ range (2 ^ k), w.getD x 0 * T.getD (x + 2 ^ k * b) 0 := by
  rw [skipFold, E2ECompleteness.getD_ofFn' _ hb, sumTo_eq]

/-- A table's value at the zerocheck's point, its entries `f t row` at `row + 2^17 t`. -/
theorem zc_table_value (zSkip : Option E) (low chiIn chiRest : List E) (k κ : ℕ) (hk : k ≤ 6)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) (hin : chiIn.length = 11)
    (hcr : chiRest.length = κ) (T Tz : Array E) (hTz : Tz.size = 2 ^ (low ++ chiIn ++ chiRest).length)
    (hTzE : ∀ b < 2 ^ (low ++ chiIn ++ chiRest).length,
      Tz.getD b 0 = ∑ x ∈ range (2 ^ k), (rowLowWeights zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0)
    (f : ℕ → ℕ → E) (hf : ∀ row < 2 ^ 17, ∀ t < 2 ^ κ, T.getD (row + 2 ^ 17 * t) 0 = f t row) :
    ((low ++ chiIn ++ chiRest).foldl foldE Tz).getD 0 0 =
      ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * f t row := by
  rw [zc_fold_eq zSkip low chiIn chiRest k hk hskip hlow hin T Tz hTz hTzE]
  refine sum_congr rfl fun t ht ↦ congrArg (eqB chiRest t * ·) (sum_congr rfl fun row hr ↦ ?_)
  rw [hf row (mem_range.mp hr) t (by rw [← hcr]; exact mem_range.mp ht)]

theorem lagrangeWeights_length (count : ℕ) (pt : E) : (lagrangeWeights count pt).length = count := by
  unfold lagrangeWeights
  simp only [List.length_map, List.length_range]

/-- **The skip's start**: the tables at the skip's point and the claim the summand's sum. -/
theorem skip_start (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ k : ℕ) (hk : k ≤ 6) (q : Array K)
    (hF : FlockHolds κ q)
    (hskipC : 0 < k → SkipComplete k) (r : List E) (hkr : k + r.length = 17 + κ) (low : List E)
    (hlow : low.length = 6 - k) (w1 : Wr) (st : ZcStart)
    (hst : st = ((skipW H k r (witOf (17 + κ) q)).run w1).1) :
    (rowLowWeights st.zSkip low).1.length = 2 ^ k ∧
      st.a.size = 2 ^ r.length ∧ st.b.size = 2 ^ r.length ∧ st.c.size = 2 ^ r.length ∧
      (∀ b < 2 ^ r.length, st.a.getD b 0 = ∑ x ∈ range (2 ^ k),
        (rowLowWeights st.zSkip low).1.getD x 0 * (witOf (17 + κ) q).a.getD (x + 2 ^ k * b) 0) ∧
      (∀ b < 2 ^ r.length, st.b.getD b 0 = ∑ x ∈ range (2 ^ k),
        (rowLowWeights st.zSkip low).1.getD x 0 * (witOf (17 + κ) q).b.getD (x + 2 ^ k * b) 0) ∧
      (∀ b < 2 ^ r.length, st.c.getD b 0 = ∑ x ∈ range (2 ^ k),
        (rowLowWeights st.zSkip low).1.getD x 0 * (witOf (17 + κ) q).c.getD (x + 2 ^ k * b) 0) ∧
      st.claim = ∑ b ∈ range (2 ^ r.length), eqB r b * (st.a.getD b 0 * st.b.getD b 0 + st.c.getD b 0) := by
  obtain ⟨hwa, hwb, hwc⟩ := witOf_size (17 + κ) q
  have hdiv : 2 ^ (17 + κ) / 2 ^ k = 2 ^ r.length := by
    rw [← hkr, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
  have hholds := witOf_holds κ q hF
  by_cases h0 : 0 < k
  · obtain ⟨z, hz⟩ := (skipW_eq H k r (witOf (17 + κ) q) w1).1 h0
    rw [← hst] at hz
    subst hz
    have hskipw : (rowLowWeights (some z) low).1 = lagrangeWeights (2 ^ k) z := by
      show lagrangeWeights (2 ^ (packing - low.length)) z = _
      rw [hlow, show packing - (6 - k) = k by unfold packing; omega]
    have hz1 : (startAt k (cosetValues k r (witOf (17 + κ) q)) z (witOf (17 + κ) q)).zSkip = some z := rfl
    have hza : (startAt k (cosetValues k r (witOf (17 + κ) q)) z (witOf (17 + κ) q)).a =
      skipFold k (lagrangeWeights (2 ^ k) z) (witOf (17 + κ) q).a := rfl
    have hzb : (startAt k (cosetValues k r (witOf (17 + κ) q)) z (witOf (17 + κ) q)).b =
      skipFold k (lagrangeWeights (2 ^ k) z) (witOf (17 + κ) q).b := rfl
    have hzc : (startAt k (cosetValues k r (witOf (17 + κ) q)) z (witOf (17 + κ) q)).c =
      skipFold k (lagrangeWeights (2 ^ k) z) (witOf (17 + κ) q).c := rfl
    have hzl : (startAt k (cosetValues k r (witOf (17 + κ) q)) z (witOf (17 + κ) q)).claim =
      lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ cosetValues k r (witOf (17 + κ) q)) z := rfl
    rw [hz1, hza, hzb, hzc, hzl, hskipw]
    refine ⟨lagrangeWeights_length _ _, ?_, ?_, ?_, fun b hb ↦ ?_, fun b hb ↦ ?_, fun b hb ↦ ?_, ?_⟩
    · rw [skipFold_size, hwa, hdiv]
    · rw [skipFold_size, hwb, hdiv]
    · rw [skipFold_size, hwc, hdiv]
    · exact skipFold_getD k _ _ (by rw [hwa, hdiv]; exact hb)
    · exact skipFold_getD k _ _ (by rw [hwb, hdiv]; exact hb)
    · exact skipFold_getD k _ _ (by rw [hwc, hdiv]; exact hb)
    · exact hskipC h0 r (witOf (17 + κ) q) z (by rw [hwa, hkr]) (by rw [hwb, hkr]) (by rw [hwc, hkr])
        (fun i hi ↦ hholds i (by rw [← hkr]; exact hi))
  · have hk0 : k = 0 := by omega
    have hz := (skipW_eq H k r (witOf (17 + κ) q) w1).2 hk0
    rw [← hst] at hz
    subst hz
    subst hk0
    refine ⟨rfl, ?_, ?_, ?_, fun b _ ↦ ?_, fun b _ ↦ ?_, fun b _ ↦ ?_, ?_⟩
    · show (witOf (17 + κ) q).a.size = _; rw [hwa, ← hkr, zero_add]
    · show (witOf (17 + κ) q).b.size = _; rw [hwb, ← hkr, zero_add]
    · show (witOf (17 + κ) q).c.size = _; rw [hwc, ← hkr, zero_add]
    · show (witOf (17 + κ) q).a.getD b 0 = ∑ x ∈ range (2 ^ 0), [(1 : E)].getD x 0 * _
      simp only [pow_zero, range_one, sum_singleton, List.getD_cons_zero, one_mul, zero_add]
    · show (witOf (17 + κ) q).b.getD b 0 = ∑ x ∈ range (2 ^ 0), [(1 : E)].getD x 0 * _
      simp only [pow_zero, range_one, sum_singleton, List.getD_cons_zero, one_mul, zero_add]
    · show (witOf (17 + κ) q).c.getD b 0 = ∑ x ∈ range (2 ^ 0), [(1 : E)].getD x 0 * _
      simp only [pow_zero, range_one, sum_singleton, List.getD_cons_zero, one_mul, zero_add]
    · show (0 : E) = ∑ b ∈ range (2 ^ r.length), eqB r b * ((witOf (17 + κ) q).a.getD b 0 *
        (witOf (17 + κ) q).b.getD b 0 + (witOf (17 + κ) q).c.getD b 0)
      refine (sum_eq_zero fun b hb ↦ ?_).symm
      rw [hholds b (by rw [← hkr, zero_add]; exact mem_range.mp hb), mul_zero]

/-- **The zerocheck's values** (`v_a`, `v_b`, `v_c`) are `A z`, `B z`, `z` at its point, through the rows'
weights: given Flock's relation and, with a skip, `SkipComplete`. Stated for the zerocheck's point split as `front`
splits it. -/
theorem zc_values (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ k : ℕ) (fs : FsShape) (hk : k ≤ 6) (q : Array K)
    (hF : FlockHolds κ q) (hskipC : 0 < k → SkipComplete k) (w : Wr) :
    ∃ (zSkip : Option E) (low chiIn chiRest : List E) (va vb vc : E),
      ((zerocheckW H (17 + κ) k fs (witOf (17 + κ) q)).run w).1 = (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) ∧
      low.length = 6 - k ∧ chiIn.length = 11 ∧ chiRest.length = κ ∧
      (rowLowWeights zSkip low).1.length = 2 ^ k ∧
      va = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * aZ q t row ∧
      vb = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * bZ q t row ∧
      vc = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn row * zAt q t row := by
  obtain ⟨sampled, st, zo, hlen, ⟨w1, hst⟩, ⟨w2, hzo⟩, heq⟩ := zerocheckW_eq H (17 + κ) k fs (witOf (17 + κ) q) w
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


/-! ## The terminal -/

/-- **The lincheck's terminal check vanishes on the honest front**: at a pure Keccak-256, `log_n = 17 + κ`, any skip
`k ≤ 6`, either Fiat–Shamir shape, every writer (any challenges), given Flock's relation on `q_flock` and, for
`k > 0`, the univariate skip's completeness (`SkipComplete k`). -/
theorem terminalHolds (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ : ℕ) (v : UniKeccak.KeccakVariant)
    (q : Array K) (w : Wr) (hk : v.skip ≤ 6) (hF : FlockHolds κ q)
    (hskipC : 0 < v.skip → SkipComplete v.skip) :
    UniKeccak.structuredTerminal ((frontW H (17 + κ) v q).run w).1.1.zSkip
        ((frontW H (17 + κ) v q).run w).1.1.rowLow ((frontW H (17 + κ) v q).run w).1.1.chiIn
        ((frontW H (17 + κ) v q).run w).1.1.chiInPrime (((frontW H (17 + κ) v q).run w).1.1.slices.getD [])
        ((frontW H (17 + κ) v q).run w).1.1.alpha +
      ((frontW H (17 + κ) v q).run w).1.1.rLc = 0 := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW_eq H (17 + κ) v q w
  obtain ⟨zSkip, low, chiIn, chiRest, va, vb, vc, hzeq, hlow, hin, hcr, hsk, hva, hvb, hvc⟩ :=
    zc_values H κ v.skip v.fs hk q hF hskipC w
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

end UniKeccakComplete.FlockP
