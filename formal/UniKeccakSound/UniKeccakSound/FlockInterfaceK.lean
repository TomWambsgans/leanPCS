-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The interface is `UniSound.FlockSound`'s
-- (`formal/UniSound/UniSound/FlockInterface.lean`) and `FlockSound3`'s (`Rec3/FlockInterface3.lean`) for the Keccak
-- verifier's Flock phase, `formal/UniKeccak`'s `verifyWalkedK` (`crates/leanvm/statement/src/flock_min.rs`'s
-- `verify_walked_with::<S, Keccak>`).
import UniSound.Prog
import UniSound.FlockInterface
import UniKeccak.Security

/-!
# Flock's interface on the Keccak-f block

The Keccak verifier runs Flock as `verifyWalkedK P (17 + κ) v` (`UniKeccak/Verifier.lean`, `κ = h_SHA3`) between `γ`
and `C2`'s root, on `C1`'s column `q_flock` of `2^(11 + κ)` cells: the zerocheck (its coordinates as the variant's
Fiat–Shamir shape draws them), the lincheck's 11 rounds, the 64 slices, the **structured terminal** (a zero the
verifier collects: `structuredTerminal … + r_lc`), then the ring switch's map and target in tower order. It leaves
the ring switch's claim on `q_flock`, and nothing pending: no claims on `A0`, `B0`.

**`KFlockSound F κ v`** is the one hypothesis about it, the analog of `FlockSound κ` (`FlockSound3 κ`) for the
Keccak-f block `F`:

* `prog`, `link`: `verifyWalkedK` is a chain program (no root, no tail; its one zero the structured terminal's);
* `S`, `err`, `S_nil`, `step`: round-by-round soundness from `KFlockHolds F κ` (the block R1CS on every block of
  `2^17` bits, `1` at the constant position: `KeccakAux`'s first conjunct);
* `finish`: on a completed transcript whose zeros vanish (the structured terminal), the ring switch's claim on the
  column makes the state true. The structured terminal is the block's matrices' bilinear form only for the block
  the verifier was written for (`KeccakFlock.structuredTerminal_eq_bilinear`), so an instance exists for
  `F = KeccakFlock.keccakFlockSpec`.
-/

namespace UniKeccakSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **What the Flock phase establishes** of a column of `2^(11 + κ)` cells: every block of `2^17` bits, packed `64`
to a cell, satisfies the Keccak-f block's R1CS and holds `1` at its constant position (`KeccakAux`'s first conjunct
on `QFLOCK`). -/
def KFlockHolds (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) (qf : Column (KeccakVm.kWords + κ)) : Prop :=
  Lv42.Protocol.BlockR1CS.BatchHolds F.r1cs F.constPos (Lv42.Protocol.bitTable qf)

/-- **Flock's claim on `q_flock` holds**: the ring switch's `Σ_{k<64} d_k q̂(φ^k(p)) = target`, `d_k` the
tower-order coefficients of the map; with a combination end, nothing holds. -/
noncomputable def FlockEndHoldsK {κ : ℕ} (qf : Column (KeccakVm.kWords + κ)) (r : List E × Flock.End) : Prop :=
  match r.2 with
  | .ring map target =>
    ∑ k ∈ Finset.range 64, (Flock.towerCoefficients map).getD k 0 * mleE qf (twist r.1 k) = target
  | _ => False

/-- **The Flock hypothesis on the Keccak-f block** `F`, for `q_flock` of `2^(11 + κ)` cells and the variant `v`:
the Keccak verifier's Flock phase is a chain program (`link`), round-by-round sound from `KFlockHolds` to its ring
claim and its structured terminal (`S`, `err`, `S_nil`, `step`, `finish`). -/
structure KFlockSound (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) (v : KeccakVariant) where
  /-- Flock's front as a chain program: its rounds, its zero (the structured terminal), its result. -/
  prog : ChainProg (List E × Flock.End)
  /-- No round has a root; nothing is read after the last challenge. -/
  rounds_root : ∀ s ∈ prog.rounds, s.root = false
  tail_eq : prog.tail = 0
  /-- **The code-level link**: `verifyWalkedK` at `17 + κ` variables is `prog`'s canonical channel program, for every
  lawful monad and permutation. -/
  link : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (P : KeccakState → m KeccakState),
    verifyWalkedK P (keccakR1csLogSize + κ) v = prog.run P
  /-- Flock's state after its completed rounds `done`, for the column `qf`. -/
  S : Column (KeccakVm.kWords + κ) → Done → Prop
  /-- Round `j`'s error. -/
  err : ℕ → ℝ≥0∞
  /-- At the start the state holds only if the column satisfies Flock's predicate. -/
  S_nil : ∀ qf, S qf [] → KFlockHolds F κ qf
  /-- **Round by round**: round `j`'s challenges turn the state from false to true with probability at most
  `err j`, for every transcript before it and every message fitting it. -/
  step : ∀ (j : ℕ) (hj : j < prog.rounds.length) (qf : Column (KeccakVm.kWords + κ))
    (done : Done) (msg : UMsg), DoneFits (prog.rounds.take j) done →
      msg.Fits (prog.rounds[j]'hj) →
        Pr{let c ← Compose.draws E ((prog.rounds[j]'hj).ns + 1)}[
          ¬ S qf done ∧ S qf (done ++ [(msg, c)])] ≤ err j
  /-- **At the end**: on a completed transcript whose zeros vanish (the structured terminal), the ring switch's claim
  on `qf` makes the state hold. -/
  finish : ∀ (qf : Column (KeccakVm.kWords + κ)) (done : Done), DoneFits prog.rounds done →
    prog.ZerosVanish done [] → FlockEndHoldsK qf (prog.out done []) → S qf done

/-- **Flock's error per candidate**: the sum of its rounds' errors. -/
noncomputable def KFlockSound.flockError {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (h : KFlockSound F κ v) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range h.prog.rounds.length, h.err j

end UniKeccakSound
