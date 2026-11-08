-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The sumcheck's loop as a recursion follows
-- `formal/FlockSound/FlockSoundUni/Loops.lean` (branch `lean-flock-sound`, `sumcheckR`, `forIn_sumcheck`,
-- `sumcheck_eq`), here for `sumcheckH` (Keccak-256 an explicit call) at `Id`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockProverSync.lean` and `Rec3FlockSync.lean`.
import UniKeccakComplete.K.FlockProverShape
import UniKeccakComplete.K.SyncBasic

/-!
# Flock's prover and `verifyWalkedKH` in step: `FlockSyncs`

**`flockSyncs`**: at a pure Keccak-256 `H`, for every variant (either Fiat–Shamir shape) and every writer, the
verifier's `verifyWalkedKH (pure ∘ H) log_n v`, on a channel synchronised with the prover's writer, reads back the
prover's messages, draws the same challenges, collects **one** value, the lincheck's terminal check
`flockZero H log_n v q w` (`structuredTerminal … + r_lc` on the prover's front, a verifier-only step), and returns
`(out.point, out.end_)`, the channel synchronised after (`SyncBasic`'s `FlockSyncs`). Piece by piece:

* `sumcheckH_eq`: the verifier's sumcheck loop is a recursion (`sumcheckRH`);
* `syncs_zcRounds`, `syncs_lcRounds`: the zerocheck's eq-factored rounds and the lincheck's;
* `syncs_drawW`: the zerocheck's draw, `drawRunH fs` against `drawW fs` (one by one, or the squares of one
  challenge);
* `syncs_zerocheck`, `syncs_front`, `syncs_ringEnd` (tower order: `v.flock.slices = .tower`), then `flockSyncs`.

The verifier's programs are unfolded by `simp only` with their join points inlined, never evaluated; the structured
terminal is never unfolded: the value collected is matched with `flockZero` by its definition (`rfl`).
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol.KeccakHash

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The sumcheck's loop as a recursion -/

section Loop

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-- **`sumcheckH` as a recursion**: a round's message, its challenge, then the rounds after it. -/
def sumcheckRH (count : ℕ) : E → List (Option E) → ChanM Id (List E × E)
  | c, [] => pure ([], c)
  | c, e :: es => do
    let msg ← roundPoly (m := Id) count c e
    let ch ← sampleH H
    let r ← sumcheckRH count (polyEval msg ch) es
    pure (ch :: r.1, r.2)

theorem forIn_sumcheckH (count : ℕ) :
    ∀ (es : List (Option E)) (pt : Array E) (c : E),
      ((forIn es (pt, c) fun e (s : Array E × E) ↦ do
          let message ← roundPoly (m := Id) count s.2 e
          let challenge ← sampleH H
          pure (ForInStep.yield (s.1.push challenge, polyEval message challenge))) >>=
        fun s ↦ pure (s.1.toList, s.2)) =
      (fun r ↦ (pt.toList ++ r.1, r.2)) <$> sumcheckRH H count c es
  | [], pt, c => by simp [sumcheckRH]
  | e :: es, pt, c => by
    simp only [List.forIn_cons, bind_assoc, pure_bind, sumcheckRH, map_bind]
    congr 1
    funext msg
    congr 1
    funext ch
    rw [forIn_sumcheckH count es (pt.push ch) (polyEval msg ch)]
    simp [Array.toList_push]

/-- **`sumcheckH` is `sumcheckRH`.** -/
theorem sumcheckH_eq (c : E) (count : ℕ) (es : List (Option E)) :
    sumcheckH H c count es = sumcheckRH H count c es := by
  have h := forIn_sumcheckH H count es #[] c
  simp only [Array.toList_empty, List.nil_append, id_map'] at h
  rw [← h, sumcheckH]

end Loop

/-! ## `Syncs` helpers -/

section Helpers

variable {α β γ δ : Type}

theorem Syncs.bind' {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {w : Wr} {a : α}
    {c : γ} (h1 : Syncs v p w a []) (h2 : Syncs (f a) (g (p.run w).1) (p.run w).2 c []) :
    Syncs (v >>= f) (p >>= g) w c [] :=
  Syncs.bind h1 h2

theorem Syncs.pure' (a : α) (b : β) (w : Wr) : Syncs (Pure.pure a : ChanM Id α) (Pure.pure b : WrM Id β) w a [] :=
  (Steps.pure a b w.stream.size w).syncs

theorem Syncs.congr_a {v : ChanM Id α} {p : WrM Id β} {w : Wr} {a a' : α} {zs : List E} (h : Syncs v p w a zs)
    (e : a = a') : Syncs v p w a' zs := e ▸ h

theorem Syncs.congr_v {v v' : ChanM Id α} {p : WrM Id β} {w : Wr} {a : α} {zs : List E} (h : Syncs v p w a zs)
    (e : v = v') : Syncs v' p w a zs := e ▸ h

theorem Syncs.congr_p {v : ChanM Id α} {p p' : WrM Id β} {w : Wr} {a : α} {zs : List E} (h : Syncs v p w a zs)
    (e : p = p') : Syncs v p' w a zs := e ▸ h

/-- The collected values, rewritten. -/
theorem syncs_congr_zs {v : ChanM Id α} {p : WrM Id β} {w : Wr} {a : α} {zs zs' : List E} (h : Syncs v p w a zs)
    (e : zs = zs') : Syncs v p w a zs' := e ▸ h

/-- **A first step that collects nothing**: the bind lemma with the first step's values empty. -/
theorem syncs_bind_nil {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {w : Wr} {a : α}
    {c : γ} {zs : List E} (h1 : Syncs v p w a []) (h2 : Syncs (f a) (g (p.run w).1) (p.run w).2 c zs) :
    Syncs (v >>= f) (p >>= g) w c zs :=
  syncs_congr_zs (Syncs.bind h1 h2) (List.nil_append zs)

/-- **The terminal's `require_zero`**, the verifier's alone: it collects `x`, then the rest synchronises. -/
theorem syncs_requireZero_then {x : E} {f : ChanM Id γ} {g : WrM Id δ} {w : Wr} {c : γ} (h : Syncs f g w c []) :
    Syncs (requireZero (m := Id) x >>= fun _ ↦ f) g w c [x] := by
  have h2 := Syncs.bind (f := fun _ ↦ f) (g := fun _ ↦ g) (syncs_requireZero x w) h
  exact Syncs.congr_p (syncs_congr_zs h2 (List.append_nil [x])) (pure_bind () fun _ ↦ g)

/-- `next_scalars(n)` reads the `n` scalars sent. -/
theorem syncs_scalars' (xs : List E) (n : ℕ) (hn : xs.length = n) (w : Wr) :
    Syncs (nextScalars (m := Id) n) (sendScalars (m := Id) xs) w xs [] := hn ▸ syncs_scalars xs w

end Helpers

/-! ## The rounds -/

/-- **An eq-factored round** (`roundPoly 3 claim (some r)`) reads the two scalars sent. -/
theorem syncs_round_eq (claim r c1 c2 : E) (w : Wr) :
    Syncs (roundPoly (m := Id) 3 claim (some r)) (sendScalar (m := Id) c1 >>= fun _ ↦ sendScalar (m := Id) c2) w
      ([claim + r * esum [c1, c2]] ++ [c1, c2]) [] := by
  have hr : Reads (roundPoly (m := Id) 3 claim (some r)) ([c1, c2].flatMap scalarWire)
      ([claim + r * esum [c1, c2]] ++ [c1, c2]) [] :=
    (nextScalars_reads [c1, c2]).bind_pure (f := fun tail ↦ [claim + r * esum tail] ++ tail)
  have hw : Writes (sendScalar (m := Id) c1 >>= fun _ ↦ sendScalar (m := Id) c2) w () ([c1, c2].flatMap scalarWire) :=
    Writes.congr ((sendScalar_writes c1 w).bind (sendScalar_writes c2 _)) rfl (by simp)
  exact (Steps.readWrite hr hw).syncs

/-- **A round without an eq factor** (`roundPoly 3 claim none`) reads the two scalars sent. -/
theorem syncs_round_plain (claim c0 c2 : E) (w : Wr) :
    Syncs (roundPoly (m := Id) 3 claim none) (sendScalar (m := Id) c0 >>= fun _ ↦ sendScalar (m := Id) c2) w
      ([c0, claim + esum [c2]] ++ [c2]) [] := by
  have hr : Reads (roundPoly (m := Id) 3 claim none) (scalarWire c0 ++ [c2].flatMap scalarWire)
      ([c0, claim + esum [c2]] ++ [c2]) [] :=
    (nextScalar_reads c0).bind ((nextScalars_reads [c2]).bind_pure (f := fun tail ↦ [c0, claim + esum tail] ++ tail))
      |>.congr rfl rfl (by simp)
  have hw : Writes (sendScalar (m := Id) c0 >>= fun _ ↦ sendScalar (m := Id) c2) w ()
      (scalarWire c0 ++ [c2].flatMap scalarWire) :=
    Writes.congr ((sendScalar_writes c0 w).bind (sendScalar_writes c2 _)) rfl (by simp)
  exact (Steps.readWrite hr hw).syncs

variable (H : List UInt8 → LeanVM.Protocol.Digest)

/-- **The zerocheck's rounds**: the verifier's sumcheck with the eq coordinates `r` reads the prover's rounds and
returns its point and its last claim. -/
theorem syncs_zcRounds : ∀ (r : List E) (claim : E) (a b c : Array E) (w : Wr),
    Syncs (sumcheckRH (Pure.pure ∘ H) 3 claim (r.map some)) (zcRounds (m := Id) (Pure.pure ∘ H) r claim a b c) w
      (((zcRounds (m := Id) (Pure.pure ∘ H) r claim a b c).run w).1.chi,
        ((zcRounds (m := Id) (Pure.pure ∘ H) r claim a b c).run w).1.running) []
  | [], claim, a, b, c, w => Syncs.pure' ([], claim) _ w
  | r :: rest, claim, a, b, c, w => by
    have ev : sumcheckRH (Pure.pure ∘ H) 3 claim ((r :: rest).map some) =
        (roundPoly (m := Id) 3 claim (some r) >>= fun msg ↦ sampleH (m := Id) (Pure.pure ∘ H) >>= fun ch ↦
          sumcheckRH (Pure.pure ∘ H) 3 (polyEval msg ch) (rest.map some) >>= fun r' ↦ Pure.pure (ch :: r'.1, r'.2)) :=
      rfl
    have ep : zcRounds (m := Id) (Pure.pure ∘ H) (r :: rest) claim a b c =
        ((sendScalar (m := Id) (zcRound (eqKernel rest) a b c).1 >>= fun _ ↦
            sendScalar (m := Id) (zcRound (eqKernel rest) a b c).2) >>= fun _ ↦
          sampleW (m := Id) (Pure.pure ∘ H) >>= fun x ↦
            zcRounds (m := Id) (Pure.pure ∘ H) rest
              (polyEval ([claim + r * esum [(zcRound (eqKernel rest) a b c).1, (zcRound (eqKernel rest) a b c).2]] ++
                [(zcRound (eqKernel rest) a b c).1, (zcRound (eqKernel rest) a b c).2]) x)
              (foldE a x) (foldE b x) (foldE c x) >>= fun out ↦
            Pure.pure (⟨x :: out.chi, out.running, out.va, out.vb⟩ : ZcOut)) := by
      simp only [zcRounds, bind_assoc]
    rw [ev, ep]
    refine Syncs.bind' (syncs_round_eq claim r _ _ w) ?_
    refine Syncs.bind' (syncs_sample H _) ?_
    refine Syncs.bind' (syncs_zcRounds rest _ _ _ _ _) ?_
    exact Syncs.pure' _ _ _

/-- **The lincheck's rounds**: the verifier's sumcheck of `n` rounds without eq factors reads the prover's rounds
and returns its challenges and its last claim. -/
theorem syncs_lcRounds : ∀ (n : ℕ) (claim : E) (wt z : Array E) (w : Wr),
    Syncs (sumcheckRH (Pure.pure ∘ H) 3 claim (List.replicate n none)) (lcRounds (m := Id) (Pure.pure ∘ H) n claim wt z) w
      (((lcRounds (m := Id) (Pure.pure ∘ H) n claim wt z).run w).1.challenges,
        ((lcRounds (m := Id) (Pure.pure ∘ H) n claim wt z).run w).1.claim) []
  | 0, claim, wt, z, w => Syncs.pure' ([], claim) _ w
  | n + 1, claim, wt, z, w => by
    have ev : sumcheckRH (Pure.pure ∘ H) 3 claim (List.replicate (n + 1) none) =
        (roundPoly (m := Id) 3 claim none >>= fun msg ↦ sampleH (m := Id) (Pure.pure ∘ H) >>= fun ch ↦
          sumcheckRH (Pure.pure ∘ H) 3 (polyEval msg ch) (List.replicate n none) >>= fun r' ↦
            Pure.pure (ch :: r'.1, r'.2)) :=
      rfl
    have ep : lcRounds (m := Id) (Pure.pure ∘ H) (n + 1) claim wt z =
        ((sendScalar (m := Id) (lcRound wt z).1 >>= fun _ ↦ sendScalar (m := Id) (lcRound wt z).2) >>= fun _ ↦
          sampleW (m := Id) (Pure.pure ∘ H) >>= fun x ↦
            lcRounds (m := Id) (Pure.pure ∘ H) n
              (polyEval ([(lcRound wt z).1, claim + esum [(lcRound wt z).2]] ++ [(lcRound wt z).2]) x)
              (foldHigh wt x) (foldHigh z x) >>= fun out ↦
            Pure.pure (⟨x :: out.challenges, out.claim, out.z⟩ : LcOut)) := by
      simp only [lcRounds, bind_assoc]
    rw [ev, ep]
    refine Syncs.bind' (syncs_round_plain claim _ _ w) ?_
    refine Syncs.bind' (syncs_sample H _) ?_
    refine Syncs.bind' (syncs_lcRounds n _ _ _ _) ?_
    exact Syncs.pure' _ _ _

/-! ## The zerocheck's draw -/

/-- **The zerocheck's draw**, either Fiat–Shamir shape: `drawRunH fs` reads nothing and draws the prover's
challenges (`samplesH` against `samplesW`; or one challenge, none for an empty run, and its squares). -/
theorem syncs_drawW (fs : FsShape) (n : ℕ) (w : Wr) :
    Syncs (drawRunH (m := Id) (Pure.pure ∘ H) fs n) (drawW (m := Id) (Pure.pure ∘ H) fs n) w
      ((drawW (m := Id) (Pure.pure ∘ H) fs n).run w).1 [] := by
  cases fs with
  | main => exact syncs_samples H n w
  | rec1 | rec2 | rec3 =>
    unfold drawRunH drawW
    by_cases hn : n = 0
    · simp only [if_pos hn]
      exact Syncs.pure' [] [] w
    · simp only [if_neg hn]
      refine Syncs.bind' (syncs_sample H w) ?_
      refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
      simp only [run_bind_id, run_pure_id, sampleW_run]

/-! ## The zerocheck -/

theorem cosetValues_length (k : ℕ) (r : List E) (wit : Wit) : (cosetValues k r wit).length = 2 ^ k := by
  simp [cosetValues]

/-- **The zerocheck**: the sampled coordinates (drawn as `fs` has them), the coset values and `z` (with a skip), the
rounds, `v_a`, `v_b`. -/
theorem syncs_zerocheck (logN k : ℕ) (fs : FsShape) (wit : Wit) (w : Wr) :
    Syncs (Flock.zerocheckFsH (m := Id) (Pure.pure ∘ H) logN k fs)
      (zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit) w
      (((zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit).run w).1.1,
        ((zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit).run w).1.2.1,
        ((zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit).run w).1.2.2.1,
        ((zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit).run w).1.2.2.2.1,
        ((zerocheckW (m := Id) (Pure.pure ∘ H) logN k fs wit).run w).1.2.2.2.2) [] := by
  by_cases hk : 0 < k
  · have hk' : (k > 0) = True := eq_true hk
    unfold Flock.zerocheckFsH zerocheckW skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, sumcheckH_eq, startAt]
    refine Syncs.bind' (syncs_drawW H fs (logN - k - nFixed) w) ?_
    refine Syncs.bind' (syncs_scalars' (cosetValues k (fixedChallenges ++
      ((drawW (m := Id) (Pure.pure ∘ H) fs (logN - k - nFixed)).run w).1) wit) (2 ^ k)
      (cosetValues_length _ _ _) _) ?_
    refine Syncs.bind' (syncs_sample H _) ?_
    refine Syncs.bind' (syncs_zcRounds H (fixedChallenges ++
      ((drawW (m := Id) (Pure.pure ∘ H) fs (logN - k - nFixed)).run w).1) _ _ _ _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
    simp only [run_bind_id, run_pure_id, sampleW_run]
  · have hk' : (k > 0) = False := eq_false hk
    unfold Flock.zerocheckFsH zerocheckW skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, sumcheckH_eq, startNone]
    refine Syncs.bind' (syncs_drawW H fs (logN - k - nFixed) w) ?_
    refine Syncs.bind' (syncs_zcRounds H (fixedChallenges ++
      ((drawW (m := Id) (Pure.pure ∘ H) fs (logN - k - nFixed)).run w).1) 0 wit.a wit.b wit.c
      ((drawW (m := Id) (Pure.pure ∘ H) fs (logN - k - nFixed)).run w).2) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.bind' (syncs_scalar _ _) ?_
    refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
    simp only [run_bind_id, run_pure_id, sampleW_run]

/-! ## The ring switch's end, the front -/

/-- The ring switch's end at the Keccak variant: tower order. -/
theorem ringEndH_flock (v : UniKeccak.KeccakVariant) (s : List E) :
    Flock.ringEndH (m := Id) (Pure.pure ∘ H) v.flock s =
      (samplesH (m := Id) (Pure.pure ∘ H) ringMapShifts.length >>= fun map ↦
        Pure.pure (Flock.End.ring map (towerTarget s map))) := rfl

/-- **The ring switch's end**: the map's 6 challenges, the target (tower order), returned as it is. -/
theorem syncs_ringEnd (v : UniKeccak.KeccakVariant) (s : List E) (w : Wr) :
    Syncs (Flock.ringEndH (m := Id) (Pure.pure ∘ H) v.flock s) (ringEndW (m := Id) (Pure.pure ∘ H) s) w
      ((ringEndW (m := Id) (Pure.pure ∘ H) s).run w).1 [] := by
  rw [ringEndH_flock]
  unfold ringEndW
  refine Syncs.bind' (syncs_samples H ringMapShifts.length w) ?_
  refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
  simp only [run_bind_id, run_pure_id]

/-- The lincheck's folded witness has `64` entries (the slices). -/
theorem lcRounds_z_length (claim : E) (wt : Array E) (k : ℕ) (q : Array K) (zc : Option E × List E × E × E × E)
    (w : Wr) :
    ((lcRounds (m := Id) (Pure.pure ∘ H) UniKeccak.lincheckRoundsK claim wt (lcWitnessOf k q zc)).run w).1.z.toList.length =
      kBits := by
  rw [Array.length_toList, lcRounds_z]
  refine foldl_foldHigh_size _ 6 _ ?_
  rw [lcRounds_length, lcWitnessOf_size]
  rfl

/-- **The front**: the zerocheck, `α`, the lincheck's 11 rounds, the slices; the verifier's `Front` is the
prover's. -/
theorem syncs_front (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) :
    Syncs (frontKH (m := Id) (Pure.pure ∘ H) logN v) (frontW (m := Id) (Pure.pure ∘ H) logN v q) w
      ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1 [] := by
  unfold frontKH frontW
  simp only [bind_assoc, pure_bind, sumcheckH_eq, map_eq_bind_pure_comp]
  refine Syncs.bind' (syncs_zerocheck H logN v.skip v.fs (witOf logN q) w) ?_
  refine Syncs.bind' (syncs_sample H _) ?_
  simp only [sampleW_run, lcClaim]
  refine Syncs.bind' (syncs_lcRounds H UniKeccak.lincheckRoundsK _
    (lcWeightsOf v.skip ((zerocheckW (m := Id) (Pure.pure ∘ H) logN v.skip v.fs (witOf logN q)).run w).1
      (Wr.sampled H ((zerocheckW (m := Id) (Pure.pure ∘ H) logN v.skip v.fs (witOf logN q)).run w).2).1)
    (lcWitnessOf v.skip q ((zerocheckW (m := Id) (Pure.pure ∘ H) logN v.skip v.fs (witOf logN q)).run w).1)
    (Wr.sampled H ((zerocheckW (m := Id) (Pure.pure ∘ H) logN v.skip v.fs (witOf logN q)).run w).2).2) ?_
  refine Syncs.bind' (syncs_scalars' _ kBits (lcRounds_z_length H _ _ _ _ _ _) _) ?_
  refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
  simp only [run_bind_id, run_pure_id, sampleW_run, frontOf]

/-! ## `FlockSyncs` -/

/-- **The value the verifier collects on the honest front** from the writer `w`: the lincheck's terminal check
`structuredTerminal … + r_lc` (`verifyWalkedK`'s `require_zero`). -/
def flockZero (H : List UInt8 → LeanVM.Protocol.Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K)
    (w : Wr) : E :=
  let fr := ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1
  UniKeccak.structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime (fr.slices.getD []) fr.alpha + fr.rLc

/-- `flockZero`, unfolded (the terminal itself left folded). -/
theorem flockZero_eq' (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) (w : Wr) :
    flockZero H logN v q w =
      UniKeccak.structuredTerminal ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.zSkip
          ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.rowLow
          ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.chiIn
          ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.chiInPrime
          (((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.slices.getD [])
          ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.alpha +
        ((frontW (m := Id) (Pure.pure ∘ H) logN v q).run w).1.1.rLc :=
  rfl

/-- **`FlockSyncs` of the honest Flock prover** (`SyncBasic`'s statement): at a pure Keccak-256, every `log_n`, every
variant (either Fiat–Shamir shape), every writer; the value collected is `flockZero`. -/
theorem flockSyncs (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) :
    FlockSyncs H (flockProve (m := Id) (Pure.pure ∘ H)) logN v q (flockZero H logN v q) := by
  intro w
  have hsl := frontW_slices (Pure.pure ∘ H) logN v q w
  rw [flockZero_eq' H logN v q w]
  unfold verifyWalkedKH flockProve
  refine syncs_bind_nil (syncs_front H logN v q w) ?_
  refine syncs_requireZero_then ?_
  -- `rw`, not `simp`, for `getD`: `simp` uses the `rfl` lemma as a definitional step, and the kernel's check of
  -- `(some s).getD [] ≡ s` then reduces the projections of the prover's run (deep recursion).
  rw [hsl, Option.getD_some]
  refine Syncs.bind' (syncs_ringEnd H v _ _) ?_
  refine Syncs.congr_a (Syncs.pure' _ _ _) ?_
  simp only [run_bind_id, run_pure_id]

end UniKeccakComplete.FlockP
