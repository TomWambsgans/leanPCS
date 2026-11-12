-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniKeccak`'s `reduceWithK4`
-- (`UniKeccak/Verifier4.lean`), read through π1-rec3's (`Code/Link3.lean`'s `main3ProgK`).
import UniKeccakSound.Rec4.ProgW
import UniKeccakSound.Code.Link3
import UniKeccakSound.Flock.Instance
import UniKeccak.Verifier4

/-!
# π1-rec4's verifier as a wide chain program

π1-rec4's verifier (`UniKeccak.reduceWithK4`) reads π1-rec3's stream and computes π1-rec3's relations, zeros and
claims; only the challenges' derivation changes. Its rounds (**`rec4Rounds κ nV np`**):

* round `0`: the row counts, `C1`'s root and out-of-domain answer, then one wide draw: `c, β, γ` and the zerocheck's
  first coordinate `c'` (`⟨true, 1, 3⟩`);
* Flock's rounds between (**`kRoundsMid κ`**, `27 + κ` of them): π1-rec3's Flock rounds without its first (`c'`) and its
  last (the slices and the ring map);
* `C2`'s round: the `64` slices, then `C2`'s root, then its out-of-domain answer (`pv4`: `64` scalars before the root),
  Flock's structured terminal required, then one wide draw: `t` and the ring map's `f_0 … f_3` (`⟨true, 65, 4⟩`);
* the values' round: the values at `t`, then one wide draw: `ρ`, `λ`, `f_4`, `f_5` (`⟨false, nV, 3⟩`);
* the batch's `np` pair rounds and its last plain round, one challenge each (`sampleWide F 1`, `sample`'s).

**π1-rec4's transcript as π1-rec3's** (`toRec3 κ`): round `0`'s first three challenges, then Flock's first round
`((none, []), [c'])`, Flock's rounds between, Flock's last round (the slices, `f_0 … f_5`), `C2`'s round (its root,
its answer, `[t]`), the values' round (`[ρ, λ]`), the batch. **`main4ProgK`** is the wide chain program whose zeros
are π1-rec3's moved to where π1-rec4 requires them (the counts' in round `0`, Flock's structured terminal in `C2`'s),
and whose tail zeros and result are `main3ProgK`'s on `toRec3`. **`UniCodeK4`** states that `reduceWithK4` after the
row counts is such a program, up to `obsOf3`.
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics

/-! ## The rounds -/

/-- **Flock's rounds between round `0`'s draw and `C2`'s**: the skip's, the zerocheck's `14 + κ`, `v_a, v_b` and `α`,
the lincheck's `11`. -/
def kRoundsMid (κ : ℕ) : List Compose.RoundSpec :=
  [⟨false, 8, 0⟩] ++ List.replicate (14 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++ List.replicate 11 ⟨false, 2, 0⟩

theorem kRoundsPre_eq (κ : ℕ) (r0 : Compose.RoundSpec) : KF.kRoundsPre κ r0 = r0 :: kRoundsMid κ := rfl

theorem length_kRoundsMid (κ : ℕ) : (kRoundsMid κ).length = 27 + κ := by
  simp only [kRoundsMid, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

/-- **π1-rec4's rounds.** -/
def rec4Rounds (κ nV np : ℕ) : List Compose.RoundSpec :=
  [⟨true, 1, 3⟩] ++ kRoundsMid κ ++ [⟨true, 65, 4⟩, ⟨false, nV, 3⟩] ++ List.replicate np ⟨false, 8, 0⟩ ++
    [⟨false, 2, 0⟩]

theorem length_rec4Rounds (κ nV np : ℕ) : (rec4Rounds κ nV np).length = 31 + κ + np := by
  simp only [rec4Rounds, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    length_kRoundsMid]
  omega

/-- **The scalars read before each round's root**: `C2`'s (round `28 + κ`) `64` slices. -/
def pv4 (κ : ℕ) (j : ℕ) : ℕ := if j = 28 + κ then 64 else 0

/-! ## The transcript as π1-rec3's -/

/-- **Flock's front in a π1-rec4 transcript**: its first round `((none, []), [c'])` (`c'` round `0`'s fourth
challenge), then the transcript's rounds `1 … 27 + κ`. -/
def vFront4 (κ : ℕ) (d : Done) : Done :=
  ((none, []), [(d.getD 0 default).2.getD 3 0]) :: (d.drop 1).take (27 + κ)

/-- **π1-rec4's transcript as π1-rec3's**: round `0` with `c, β, γ`; Flock's front; Flock's last round (the slices,
the map `f_0 … f_5`); `C2`'s round (root, answer, `t`); the values' round (`ρ, λ`); the batch. -/
def toRec3 (κ : ℕ) (d : Done) : Done :=
  let r0 := d.getD 0 default
  let c2 := d.getD (28 + κ) default
  let v := d.getD (29 + κ) default
  [(r0.1, r0.2.take 3)] ++ vFront4 κ d ++
    [((none, c2.1.2.take 64), c2.2.drop 1 ++ v.2.drop 2), ((c2.1.1, c2.1.2.drop 64), c2.2.take 1),
      (v.1, v.2.take 2)] ++ d.drop (30 + κ)

/-! ## The program -/

/-- **π1-rec4's zeros after a round**: the counts' in round `0`, Flock's structured terminal in `C2`'s (on its
slices, the message's first `64` scalars). -/
def zeros4K (heights rows : List ℕ) (κ : ℕ) (done : Done) (msg : UMsg) : List E :=
  if done.length = 0 then [countsZeroK heights rows]
  else if done.length = 28 + κ then [KF.kTerm κ (KF.sampRec3 κ) (vFront4 κ done) (msg.2.take 64)]
  else []

/-- **The Keccak verifier at π1-rec4 as a wide chain program**, for π1-rec3's Flock phase `F3` (its program
`KF.kProg3 κ`): π1-rec4's rounds and zeros, π1-rec3's tail zeros and result on `toRec3`. -/
def main4ProgK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) : ChainProgW Reduced where
  rounds := rec4Rounds κ valsCountK np
  zeros := zeros4K D.shape.heights rows κ
  tail := 3
  tailZeros done tl := (main3ProgK D F3 np input rows).tailZeros (toRec3 κ done) tl
  out done tl := (main3ProgK D F3 np input rows).out (toRec3 κ done) tl
  pv := pv4 κ

/-! ## The code-level link -/

/-- **The Keccak verifier at π1-rec4 as a wide chain program** (code-level link), with `nV` values at `t` and `np`
pair rounds: after the row counts, the wide chain program `prog input rows` on `rec4Rounds κ nV np`, `C2`'s slices
before its root, with a tail of three, runs as `reduceWithK4` at the deployment's shape, `keccakRec4`, point claims,
up to `obsOf3`. -/
structure UniCodeK4 (D : KDeployment) (κ nV np : ℕ) where
  prog : Vector UInt8 32 → List ℕ → ChainProgW Reduced
  rounds_eq : ∀ input rows, (prog input rows).rounds = rec4Rounds κ nV np
  tail_eq : ∀ input rows, (prog input rows).tail = 3
  pv_eq : ∀ input rows, (prog input rows).pv = pv4 κ
  link : ∀ (input : Vector UInt8 32) {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : KeccakState → m KeccakState) (c₀ : Chan),
    obsOf3 <$> ((reduceWithK4 P D.shape (publicWordsOf input.toList) keccakRec4 .point).run.run c₀) =
      obsOf3 <$> ((readCounts D.shape.heights >>= fun rows => (prog input rows).runW P).run.run c₀)

end UniKeccakSound
