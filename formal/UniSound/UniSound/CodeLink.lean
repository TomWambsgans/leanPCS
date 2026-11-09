-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniStatement`'s
-- `reduceWith` (`Verifier.lean`); Flock's phase is cited through `FlockSound.link`.
import UniSound.CodeBatch
import UniSound.CodeShape
import UniSound.CodeZeros

/-!
# The code-level link: `reduceWith` on the main line is a chain program (`UniCode`)

**`uniCode D hFlock hκ : UniCode D hFlock valsCount (varsOf (layoutsOf D.shape))`**: after the row
counts, `reduceWith` at the deployment's shape, main line (`flockMain`, point claims) is the chain
program `mainProg` on `uniRounds hFlock.prog.rounds valsCount V`, `V` the batch's variables at the
shape, with a tail of five, up to `obsOf`. Its rounds:

* `C1`'s root and `α ∈ E^4, β, γ`;
* Flock's rounds (`hFlock.link`: `Flock.verifyDeferred` is Flock's chain program; its zeros are the
  main line's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`;
* the `valsCount` values at `t` (`tableReads` of each table, then the memory's three, the
  bytecode's two, `T(t)`, `Q_W(t)`) and `ρ, λ`;
* the batch's `V` rounds (`batch_eq`);

then the stacks' three values and `a`, `b`, the batch's terminal collected (`batchPure`), and the
result (`mainOut`). Each is a function of the transcript (`mainRels`, `flockClaim`, `batchPure`), the
verifier's own computations on the values read and drawn.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The values at `t` and the relations -/

/-- **The row counts in range** (what `readCounts`' range checks accept, iteration 2's F1): six
counts, each at most `2^r` for its table's height `r`. -/
def CountsInRange (heights rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ j < 6, rows.getD j 0 ≤ 2 ^ heights.getD j 0

instance (heights rows : List ℕ) : Decidable (CountsInRange heights rows) := by
  unfold CountsInRange
  infer_instance

/-- **Flock's claim on `q_flock`** (step 7, main line: the ring switch's one term), the bit-slice
relations, the ring map. -/
def flockClaim (rels : Array Relation) (fl : List E × Option Flock.End × Flock.Pending) :
    Array Relation × List Relation × Option (List E) :=
  match fl.2.1 with
  | some (.ring map target) =>
    (rels.push ⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩, [], some map)
  | some (.combination ws value) =>
    (rels, [⟨(ws.zip (List.range ws.length)).map fun x => ⟨.qflockBits, fl.1, x.2, x.1⟩, value⟩], none)
  | none => (rels, [], none)

/-! ## The run's `C2` columns and claims -/

theorem flockClaim_mem (rels : Array Relation) (fl : List E × Option Flock.End × Flock.Pending)
    (r : Relation) (h : r ∈ rels.toList) : r ∈ (flockClaim rels fl).1.toList := by
  unfold flockClaim
  split <;> simp [h]

/-! ## Rounds of a fixed length -/

/-- A transcript cut or padded to `n` rounds. -/
def fixDone (n : ℕ) (l : Done) : Done := (List.range n).map fun i => l.getD i default

@[simp] theorem length_fixDone (n : ℕ) (l : Done) : (fixDone n l).length = n := by simp [fixDone]

theorem fixDone_succ_cons (n : ℕ) (x : UMsg × List E) (l : Done) :
    fixDone (n + 1) (x :: l) = x :: fixDone n l := by
  simp [fixDone, List.range_succ_eq_map, Function.comp_def]

theorem fixDone_of_length {n : ℕ} {l : Done} (h : l.length = n) : fixDone n l = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [fixDone, List.getD_eq_getElem?_getD, h2]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **A chain program's rounds complete one record each.** -/
theorem runRounds_fix {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List Compose.RoundSpec) (d : Done),
      P.runRounds F rs d = (fun d' => d ++ fixDone rs.length (d'.drop d.length)) <$> P.runRounds F rs d
  | [], d => by simp [ChainProg.runRounds, fixDone]
  | s :: rs, d => by
    conv_lhs => rw [runRounds_cons]
    rw [runRounds_cons]
    simp only [map_bind]
    congr 1
    funext root
    congr 1
    funext vals
    congr 1
    funext _
    congr 1
    funext chs
    rw [runRounds_fix P F rs (d ++ [((root, vals), chs)])]
    simp only [Functor.map_map]
    congr 1
    funext d'
    have hF := length_fixDone rs.length (List.drop (List.length (d ++ [((root, vals), chs)])) d')
    generalize fixDone rs.length (List.drop (List.length (d ++ [((root, vals), chs)])) d') = G at hF ⊢
    rw [List.append_assoc, List.drop_left, List.singleton_append, List.length_cons, fixDone_succ_cons,
      fixDone_of_length hF]

theorem samples_six (F : KeccakState → m KeccakState) : samples F 6 = (do
    let a ← samples F 4
    let b ← sample F
    let c ← sample F
    pure (fixLen 4 a ++ [b, c])) := by
  rw [show 6 = 4 + 2 from rfl, samples_add]
  simp [samples_eq, FlockSound.Uni.repeatM]

theorem samples_two (F : KeccakState → m KeccakState) : samples F 2 = (do
    let a ← sample F
    let b ← sample F
    pure [a, b]) := by
  simp [samples_eq, FlockSound.Uni.repeatM]

theorem ObsEq.bind_eq {α β : Type} {x y : ChanM m β} {f g : β → ChanM m α} (h : x = y)
    (hf : ∀ b, ObsEq (f b) (g b)) : ObsEq (x >>= f) (y >>= g) := by
  subst h
  exact ObsEq.bind_right x hf

theorem nextScalars_seven : nextScalars (m := m) 7 = (do
    let a1 ← nextScalar (m := m)
    let a2 ← nextScalar (m := m)
    let a3 ← nextScalar (m := m)
    let a4 ← nextScalar (m := m)
    let a5 ← nextScalar (m := m)
    let a6 ← nextScalar (m := m)
    let a7 ← nextScalar (m := m)
    pure [a1, a2, a3, a4, a5, a6, a7]) := by
  simp [nextScalars_eq, FlockSound.Uni.repeatM]

theorem runRounds_noZeros {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) (n : ℕ)
    (hz : ∀ d msg, n ≤ d.length → P.zeros d msg = []) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), (∀ s ∈ rs, s.root = false) → n ≤ d.length →
      P.runRounds F rs d = (fun e => d ++ e) <$> readRounds F rs
  | [], d, _, _ => by simp [ChainProg.runRounds, readRounds]
  | s :: rs, d, hr, hn => by
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    rw [runRounds_cons]
    simp only [rootRead, hs, Bool.false_eq_true, ite_false, pure_bind, hz d _ hn, ChainProg.requireZeros,
      readRounds, readRound, bind_assoc, map_bind]
    congr 1
    funext vals
    congr 1
    funext chs
    rw [runRounds_noZeros P F n hz rs _ (fun s hs => hr s (List.mem_cons_of_mem _ hs)) (by simp; omega)]
    simp

/-! ## Reading the transcript back -/

section Decode

variable (x0 x2 x3 : UMsg × List E) (G brs : Done)

theorem decode_r0 : ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD 0 default = x0 := by simp

theorem decode_fd (n : ℕ) (hG : G.length = n) :
    (([x0] ++ G ++ [x2] ++ [x3] ++ brs).drop 1).take n = G := by
  subst hG
  simp

theorem decode_r2 (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD (n + 1) default = x2 := by
  subst hG
  simp [List.getD_eq_getElem?_getD]

theorem decode_r3 (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD (n + 2) default = x3 := by
  subst hG
  simp [List.getD_eq_getElem?_getD]

theorem decode_brs (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).drop (n + 3) = brs := by
  subst hG
  simp [List.drop_append]

end Decode

theorem getD_fixLen_append (T i : ℕ) (v l : List E) : (fixLen T v ++ l).getD (T + i) 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_fixLen_append_zero (T : ℕ) (v l : List E) : (fixLen T v ++ l).getD T 0 = l.getD 0 0 := by
  simpa using getD_fixLen_append T 0 v l

theorem getD_five (a : List E) (b c : E) : (fixLen 4 a ++ [b, c]).getD 5 0 = c :=
  getD_fixLen_append 4 1 a [b, c]

end Monad

end UniSound
