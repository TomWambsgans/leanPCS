-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The toolkit extends `formal/UniSound/UniSound/{CodeBase,
-- CodeZeros,CodeTables,CodeLink}.lean`'s (chain programs) to the wide chain programs of `ProgW.lean`; the wide draw is
-- `formal/UniStatement`'s `sampleWide` (`Rec.lean`).
import UniKeccakSound.Rec4.Prog4

/-!
# The code-level link's toolkit for wide chain programs

* **The wide draw** (`sampleWide_run`): one Keccak-256 of the state and the bytes read since the last challenge, the
  new state its digest; **`sampleWide_one`**: a draw of one challenge is `sample`'s; **`sampleWide_fix`**: a draw of
  `n` gives `n` challenges; **`obl_sampleWide`**: it never reads the zeros.
* **Wide chain programs' rounds** (`runRoundsW_append`, `runRoundsW_read`: rounds without root, zeros or scalars
  before a root, one challenge each, are their reads and draws; `runRoundsW_congr`: two programs alike after
  round `0` run alike there), **`obl_runW`** (a wide chain program's run never reads the zeros) and
  **`obsEq_headW`** (zeros in round `0` moved before its root and answer, observationally).
-/

namespace UniKeccakSound

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash FlockSound.Uni

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-! ## The wide draw -/

/-- The channel after a wide draw of `n` challenges from the sponge's last state `st`. -/
def sampledW (c : Chan) (st : KeccakState) (n : ℕ) : Chan :=
  { c with
    absorbed := c.cursor
    state := digestOfState st
    challenges := c.challenges ++ ((List.range n).map (challengeAt (rateBytesOf st))).toArray }

theorem sampleWide_run (F : KeccakState → m KeccakState) (n : ℕ) (c : Chan) :
    (sampleWide F n).run.run c =
      (fun st : KeccakState => ((Except.ok ((List.range n).map (challengeAt (rateBytesOf st))) :
          Except UniError (List E)), sampledW c st n)) <$>
        keccak256StateWith F (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold sampleWide
  simp only [ExceptT.run_bind, StateT.run_bind, chan_get_run, pure_bind]
  simp [StateT.run_lift, MonadLift.monadLift, ExceptT.lift, liftM, monadLift, chan_set_run,
    map_eq_bind_pure_comp, sampledW]

/-- **A wide draw of one challenge is `sample`'s** (challenge `0` of the rate is the digest's). -/
theorem sampleWide_one (F : KeccakState → m KeccakState) :
    sampleWide F 1 = (fun x => [x]) <$> sample F := by
  refine ExceptT.ext (StateT.ext fun c => ?_)
  rw [sampleWide_run, ExceptT.run_map, StateT.run_map, sample_run, keccak256With_eq]
  simp only [Functor.map_map]
  congr 1

/-- **A wide draw of `n` gives `n` challenges.** -/
theorem sampleWide_fix (F : KeccakState → m KeccakState) (n : ℕ) :
    sampleWide F n = fixLen n <$> sampleWide F n := by
  refine ExceptT.ext (StateT.ext fun c => ?_)
  rw [ExceptT.run_map, StateT.run_map, sampleWide_run]
  simp only [Functor.map_map]
  congr 1
  funext st
  simp [Except.map, fixLen_of_length]

theorem obl_sampleWide (F : KeccakState → m KeccakState) (n : ℕ) : Obl (sampleWide F n) := by
  intro c
  rw [sampleWide_run, sampleWide_run]
  simp only [Functor.map_map, nrmP]
  congr 1
  funext st
  congr 1
  simp only [sampledW, normC, zf_zf]

/-! ## Wide chain programs' rounds -/

omit [LawfulMonad m] in
/-- A round of a wide chain program, its root read by `rootRead`. -/
theorem runRoundsW_cons {α : Type} (P : ChainProgW α) (F : KeccakState → m KeccakState) (s : Compose.RoundSpec)
    (rs : List Compose.RoundSpec) (d : Done) :
    P.runRoundsW F (s :: rs) d = (do
      let pre ← nextScalars (m := m) (P.pv d.length)
      let root ← rootRead (m := m) s.root
      let post ← nextScalars (m := m) (s.nv - P.pv d.length)
      ChainProg.requireZeros (P.zeros d (root, pre ++ post))
      let chs ← sampleWide F (s.ns + 1)
      P.runRoundsW F rs (d ++ [((root, pre ++ post), chs)])) := by
  rw [ChainProgW.runRoundsW]
  rcases s with ⟨b, nv, ns⟩
  cases b <;> rfl

theorem runRoundsW_append {α : Type} (P : ChainProgW α) (F : KeccakState → m KeccakState) :
    ∀ (a b : List Compose.RoundSpec) (done : Done),
      P.runRoundsW F (a ++ b) done = (P.runRoundsW F a done >>= fun d => P.runRoundsW F b d)
  | [], b, done => by simp [ChainProgW.runRoundsW]
  | s :: a, b, done => by
    simp only [List.cons_append, runRoundsW_cons, bind_assoc, runRoundsW_append P F a b]

/-- **Rounds without root, zeros or scalars before a root, one challenge each, are their reads and draws**, after a
transcript of `n₀` rounds or more, before the round `n₁`. -/
theorem runRoundsW_read {α : Type} (P : ChainProgW α) (F : KeccakState → m KeccakState) (n₀ n₁ : ℕ)
    (hz : ∀ d msg, n₀ ≤ d.length → d.length < n₁ → P.zeros d msg = [])
    (hp : ∀ j, n₀ ≤ j → j < n₁ → P.pv j = 0) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), (∀ s ∈ rs, s.root = false ∧ s.ns = 0) → n₀ ≤ d.length →
      d.length + rs.length ≤ n₁ → P.runRoundsW F rs d = (fun e => d ++ e) <$> readRounds F rs
  | [], d, _, _, _ => by simp [ChainProgW.runRoundsW, readRounds]
  | s :: rs, d, hr, h0, h1 => by
    obtain ⟨hs, hn⟩ := hr s List.mem_cons_self
    have hl : d.length < n₁ := by simp only [List.length_cons] at h1; omega
    simp only [runRoundsW_cons, hp d.length h0 hl, hs, hn, UniSound.nextScalars_zero, rootRead,
      Bool.false_eq_true, ite_false, pure_bind, Nat.sub_zero, List.nil_append, hz d _ h0 hl, ChainProg.requireZeros,
      Nat.zero_add, sampleWide_one, readRounds, readRound, UniSound.samples_one, bind_assoc, map_bind, bind_map_left]
    refine bind_congr fun vals => bind_congr fun x => ?_
    rw [runRoundsW_read P F n₀ n₁ hz hp rs _ (fun s hs => hr s (List.mem_cons_of_mem _ hs))
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢; omega)]
    simp

omit [LawfulMonad m] in
/-- **Two wide chain programs alike after round `0`** (the same scalars before each root, the same zeros) run alike
there. -/
theorem runRoundsW_congr {α : Type} (P Q : ChainProgW α) (F : KeccakState → m KeccakState) (hp : P.pv = Q.pv)
    (hz : ∀ d : Done, d ≠ [] → P.zeros d = Q.zeros d) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), d ≠ [] → P.runRoundsW F rs d = Q.runRoundsW F rs d
  | [], d, _ => by simp only [ChainProgW.runRoundsW]
  | s :: rs, d, hd => by
    simp only [runRoundsW_cons, hp, hz d hd]
    refine bind_congr fun pre => bind_congr fun root => bind_congr fun post => bind_congr fun _ =>
      bind_congr fun chs => ?_
    exact runRoundsW_congr P Q F hp hz rs _ (by simp)

/-- **A wide chain program's rounds never read the zeros.** -/
theorem obl_runRoundsW {α : Type} (P : ChainProgW α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), Obl (P.runRoundsW F rs d)
  | [], d => by
    simp only [ChainProgW.runRoundsW]
    exact obl_pure _
  | s :: rs, d => by
    rw [runRoundsW_cons]
    exact obl_bind (obl_nextScalars _) fun _ => obl_bind (obl_rootRead s.root) fun _ =>
      obl_bind (obl_nextScalars _) fun _ => obl_bind (obl_requireZeros _) fun _ =>
        obl_bind (obl_sampleWide F _) fun _ => obl_runRoundsW P F rs _

/-- **A wide chain program's run never reads the zeros.** -/
theorem obl_runW {α : Type} (P : ChainProgW α) (F : KeccakState → m KeccakState) : Obl (P.runW F) := by
  unfold ChainProgW.runW
  exact obl_bind (obl_runRoundsW P F _ _) fun _ => obl_bind (obl_nextScalars _) fun _ =>
    obl_bind (obl_requireZeros _) fun _ => obl_pure _

/-- **The zeros of round `0` moved before its root and its one scalar** (`obsEq_withHead1` for wide chain programs):
`P` is `Q` with the zeros `zs` in round `0`, a root and one scalar, none before the root. -/
theorem obsEq_headW {α : Type} (P Q : ChainProgW α) (zs : List E) (F : KeccakState → m KeccakState) (ns : ℕ)
    (rs : List Compose.RoundSpec) (hr : P.rounds = ⟨true, 1, ns⟩ :: rs) (hrq : Q.rounds = ⟨true, 1, ns⟩ :: rs)
    (hp : P.pv = Q.pv) (hp0 : Q.pv 0 = 0) (hzP : P.zeros [] = fun _ => zs) (hzQ : Q.zeros [] = fun _ => [])
    (hz : ∀ d : Done, d ≠ [] → P.zeros d = Q.zeros d) (htl : P.tail = Q.tail) (htz : P.tailZeros = Q.tailZeros)
    (hout : P.out = Q.out) :
    ObsEq (P.runW F) (ChainProg.requireZeros zs >>= fun _ => Q.runW F) := by
  unfold ChainProgW.runW
  rw [hr, hrq]
  simp only [runRoundsW_cons, List.length_nil, hp, hp0, hzP, hzQ, UniSound.nextScalars_zero, pure_bind, rootRead,
    ite_true,
    Nat.sub_zero, nextScalars_one, bind_map_left, bind_assoc, List.nil_append, ChainProg.requireZeros, htl, htz,
    hout]
  have hrr : ∀ (r : E × E) (x : E) (chs : List E),
      P.runRoundsW F rs [((some r, [x]), chs)] = Q.runRoundsW F rs [((some r, [x]), chs)] := fun r x chs =>
    runRoundsW_congr P Q F hp hz rs _ (by simp)
  simp only [hrr]
  intro c
  exact (((obsEq_requireZeros_nextRoot zs _).trans
    (ObsEq.bind_right _ fun _ => obsEq_requireZeros_nextScalar zs _)) c).symm

end Monad

end UniKeccakSound
