-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The links' form is `UniSound/Fs.lean`'s and
-- `UniSound/Fs128.lean`'s, for the Keccak verifier (`formal/UniKeccak`: `reduceWithK`, `verifyWithK`, three openings).
import UniSound.Fs128
import UniKeccakSound.PiopK

/-!
# The Keccak verifier's code-level link, last link and Fiat–Shamir layer (main line)

Three hypotheses of the end theorem, each about `formal/UniKeccak`'s verifier, as `UniSound`'s:

* **`UniCodeK`** (the code-level link): after the row counts, `reduceWithK` on the main line (`keccakMain`, point
  claims) is a chain program on `uniRounds`, its Flock rounds Flock's on the Keccak-f block, its tail the three
  stacks' values at the batch's point (no `a`, `b`: no matrices' claims).
* **`UniFinalK`** (the last link): the verifier's checks with the three point claims true make Flock's zeros vanish
  (the structured terminal) and the batching sumcheck's last claim the identity model's
  `Σ_{k<3} λ^k W_k(r) C_k(r)` at its point, unless `t` is a root of the merge polynomial.
* **`FsLayer128K`** (the Fiat–Shamir layer at `≥ 128` bits): every round-by-round sound protocol on the main line's
  rounds whose first state is the Keccak VM's relation and whose last follows from the checks with true claims makes
  the deployed Keccak verifier knowledge sound for `uniExtractorK F D` with the bound `UniSound.uniBound128 e`
  (`Fs128.lean`: the openings charged once at `269 · 2^-137`, here three of them, `C1`, `C2` and the setup; the
  chain without the tag; the seed's pair; the permutation).
-/

namespace UniKeccakSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement UniSound UniKeccak Finset
open scoped ENNReal

/-! ## Claims on candidates -/

/-- **The stack a commitment's claim is on**: `C1`'s and `C2`'s candidates, the setup's honest stack
(`setupStackK`). -/
def stackForK (D : KDeployment) (c1 c2 : Stk) : Commitment → Stk
  | .c1 => c1
  | .c2 => c2
  | .setup => fun i => (setupStackK D.prog D.shape).getD i 0

/-- **The claims the Keccak verifier hands `PCS_OPEN` hold** of the candidates `c1`, `c2` and the setup's stack: each
commitment's point claim on its stack's multilinear extension at its Keccak layout word's variables
(`verifyWithK`'s `layoutWordVars`). -/
def ClaimsHoldK (D : KDeployment) (r : Reduced) (c1 c2 : Stk) : Prop :=
  ∀ o ∈ r.openings, ∀ pt v bs, o.2 = .point pt v bs →
    mleStk (stackForK D c1 c2 o.1) (layoutWordVars ((layoutWordsK D.shape).getD (wordIndex o.1) [])) pt = v

/-! ## The code-level link -/

/-- **The Keccak verifier's main line as a chain program** (code-level link), for the Flock phase `Fl`, with `nV`
values at `t` and `V` batch rounds: after the row counts, for each public input and counts the chain program
`prog input rows` on `uniRounds Fl.prog.rounds nV V`, with a tail of three (the three stacks' values), runs as
`reduceWithK` at the deployment's shape, `keccakMain`, point claims, up to what the verdict and the chain read
(`obsOf`). -/
structure UniCodeK {F : KeccakVm.KeccakFlockSpec} (D : KDeployment) {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) where
  prog : Vector UInt8 32 → List ℕ → ChainProg Reduced
  rounds_eq : ∀ input rows, (prog input rows).rounds = uniRounds Fl.prog.rounds nV V
  tail_eq : ∀ input rows, (prog input rows).tail = 3
  link : ∀ (input : Vector UInt8 32) {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : KeccakState → m KeccakState) (c₀ : Chan),
    obsOf <$> ((reduceWithK P D.shape (publicWordsOf input.toList) keccakMain .point).run.run c₀) =
      obsOf <$> ((readCounts D.shape.heights >>= fun rows => (prog input rows).run P).run.run c₀)

/-! ## The last link -/

/-- **The last link**: on a completed transcript and its tail, the verifier's checks (`ZerosVanish`: Flock's
structured terminal, the batch's terminal `sum + last = 0`, …) with true claims (`ClaimsHoldK`) make Flock's zeros
vanish on its transcript, and the batching sumcheck's last claim the identity model's partial sum at its point,
unless `t` is a root of the merge polynomial. -/
def UniFinalK {F : KeccakVm.KeccakFlockSpec} (D : KDeployment) {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (I : UniIdsK F D Fl) (C : UniCodeK D Fl I.nV I.V) : Prop :=
  ∀ (s : USt) done tl c1 c2, DoneFits (uniRounds Fl.prog.rounds I.nV I.V) done → tl.length = 3 →
    (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
      Fl.prog.ZerosVanish (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)) [] ∧
      ((I.zb (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done))).eval
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      SumState (I.prod s c1 (rd (openedOf Fl.prog.rounds.length c1 c2 done) 0).2
          (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).1.2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done)
            (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle
        (I.target s c1 (rd (openedOf Fl.prog.rounds.length c1 c2 done) 0).2
          (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).1.2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done)
            (Fl.prog.rounds.length + 2)).2.getD 1 0))
        (brOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)))

/-! ## The Fiat–Shamir layer -/

/-- **The Fiat–Shamir layer at `≥ 128` bits** for the Keccak verifier's main line: every round-by-round sound
protocol on the main line's rounds, its errors at most `e`, whose state before round `0` is the Keccak VM's relation
of `C1`'s candidate and whose last state follows from the verifier's checks with true claims, makes the deployed
Keccak verifier (`keccakMain`) knowledge sound for `uniExtractorK F D` with the bound `uniBound128 e`. -/
def FsLayer128K (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) : Prop :=
  ∀ (R : RbrPiop (uniRounds Fl.prog.rounds nV V) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → RelK F D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (uniRounds Fl.prog.rounds nV V) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundnessKeccak F D (uniBound128 e)

end UniKeccakSound
