-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The argument is `UniSound/Bus.lean`'s
-- (`BusModel.mainSound`), for the Keccak VM's instance; the bus is `formal/Heap`'s.
import UniSound.Bus
import UniKeccakSound.Ids.Model

/-!
# Round `0` on the Keccak VM: the bus and the constraints' batching

`UniSound.BusModel` for the Keccak VM (`KDeployment.inst`, `kvStack`): **`BusModelK D`** is the heap the
verifier reads off `C1` (`hd`, well formed, realizing the Keccak VM's bus where the copies hold), the constraint
vectors (`cvec`, whose vanishing gives `ConstraintsVanish`, `CountsNonzero`, `PublicLinesHold` and the copies),
and the bus bound `N`.

**`MainHoldsK B s c`**: the Keccak VM's `M3Holds` but for `aux` (trivial: `flock := none`) and the lanes' copies
on `C1` (`B.Copies`). **`BusModelK.mainSound`**: round `0` turns `¬ MainHoldsK` into `MainOK` with probability at
most `busError N + (ncv − 1)/|E|`, `UniSound.BusModel.mainSound`'s proof (`Heap.card_sat_not_balanced_le`,
`card_powComb_le`) on the Keccak VM's instance.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open scoped ENNReal

/-- **The bus and constraint model of round `0`** on the Keccak VM. -/
structure BusModelK (D : KDeployment) where
  /-- The heap the verifier reads off `C1`. -/
  hd : USt → Stk → Heap.HeapData
  wf : ∀ (s : USt) (c : Stk), (hd s c).WellFormed
  /-- The lanes' copies on `C1` (and the counts in range). -/
  Copies : USt → Stk → Prop
  /-- With the copies, the heap realizes the Keccak VM's bus of `C1`'s Keccak VM stack. -/
  realizes : ∀ (s : USt) (c : Stk), Copies s c →
    Heap.Realizes (I := D.inst s.2) (kvStack D.prog (D.sizes s.2) D.shape c) (hd s c)
  /-- A bound on both sides' tuple counts, where the copies hold. -/
  N : ℕ
  hpush : ∀ (s : USt) (c : Stk), Copies s c → Heap.busCount (D.inst s.2) .push ≤ N
  hpull : ∀ (s : USt) (c : Stk), Copies s c → Heap.busCount (D.inst s.2) .pull ≤ N
  /-- The rows the constraints are checked on, and each row's constraint vector. -/
  nrows : ℕ
  cvec : USt → Stk → ℕ → List E
  ncv : ℕ
  cvec_len : ∀ (s : USt) (c : Stk) (x : ℕ), (cvec s c x).length ≤ ncv
  cvec_ok : ∀ (s : USt) (c : Stk), (∀ x < nrows, ∀ v ∈ cvec s c x, v = 0) →
    (D.inst s.2).ConstraintsVanish (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).CountsNonzero (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList) (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    Copies s c

namespace BusModelK

variable {D : KDeployment} (B : BusModelK D)

/-- **The relation but for Flock's region**: `M3Holds` but for `aux`, and the lanes' copies on `C1`. -/
def MainHolds (s : USt) (c : Stk) : Prop :=
  (D.inst s.2).ConstraintsVanish (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).CountsNonzero (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList) (kvStack D.prog (D.sizes s.2) D.shape c) ∧
    B.Copies s c

/-- **The state after round `0`**: the heap holds at `(α, β)`, the batched constraints vanish at `γ`. -/
def MainOK (s : USt) (c : Stk) (ch : List E) : Prop :=
  (B.hd s c).Sat (fun i => ch.getD i.val 0) (ch.getD 4 0) ∧
    ∀ x < B.nrows, powComb (B.cvec s c x) (ch.getD 5 0) = 0

/-- **Round `0`'s error.** -/
noncomputable def errMain : ℝ≥0∞ :=
  Heap.busError B.N + ((B.ncv - 1 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- **Round `0` is sound** on the Keccak VM: the bus (`4N/|E|`) and the constraints' batching. -/
theorem mainSound (s : USt) (c : Stk) :
    Pr{let ch ← Compose.draws E 6}[¬ B.MainHolds s c ∧ B.MainOK s c ch] ≤ B.errMain := by
  classical
  unfold errMain
  by_cases hall : ∀ x < B.nrows, ∀ v ∈ B.cvec s c x, v = 0
  · obtain ⟨hcv, hcn, hpl, hcp⟩ := B.cvec_ok s c hall
    have hR := B.realizes s c hcp
    have hev : ∀ ch : List E, (¬ B.MainHolds s c ∧ B.MainOK s c ch) →
        ((B.hd s c).Sat (fun i => (ch.take 5).getD i.val 0) ((ch.take 5).getD 4 0) ∧
          ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c)) ∨ False := by
      intro ch ⟨hn, hok⟩
      refine Or.inl ⟨?_, fun hb => hn ⟨hcv, hb, hcn, hpl, hcp⟩⟩
      have h1 : (fun i : Fin 4 => (ch.take 5).getD i.val 0) = fun i => ch.getD i.val 0 := by
        funext i
        simp [List.getD_eq_getElem?_getD, show i.val < 5 by omega]
      have h2 : (ch.take 5).getD 4 0 = ch.getD 4 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [h1, h2]
      exact hok.1
    have hb := prEvent_draws_append_le 5 1 (fun l => (B.hd s c).Sat (fun i => l.getD i.val 0)
      (l.getD 4 0) ∧ ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c))
      (fun _ => False)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), add_zero]
    refine le_trans ?_ le_self_add
    have hc := Heap.card_sat_not_balanced_le (I := D.inst s.2) (B.wf s c) hR (B.hpush s c hcp)
      (B.hpull s c hcp)
    refine (prEvent_draws_le_of_card 4 _ (4 * B.N) ?_).trans (le_of_eq rfl)
    have h5 := BusModel.card_fin_five (fun a b => (B.hd s c).Sat a b ∧
      ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c))
    exact (le_of_eq h5).trans hc
  · obtain ⟨x₀, hx₀, v, hv, hv0⟩ : ∃ x < B.nrows, ∃ v ∈ B.cvec s c x, v ≠ 0 := by
      by_contra hne
      exact hall fun x hx v hv => by
        by_contra h0
        exact hne ⟨x, hx, v, hv, h0⟩
    have hev : ∀ ch : List E, (¬ B.MainHolds s c ∧ B.MainOK s c ch) →
        False ∨ powComb (B.cvec s c x₀) ((ch.drop 5).headD 0) = 0 := by
      intro ch ⟨_, hok⟩
      refine Or.inr ?_
      have h1 : (ch.drop 5).headD 0 = ch.getD 5 0 := by
        simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
      rw [h1]
      exact hok.2 x₀ hx₀
    have hb := prEvent_draws_append_le 5 1 (fun _ => False)
      (fun l => powComb (B.cvec s c x₀) (l.headD 0) = 0)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), zero_add]
    refine le_trans ?_ le_add_self
    refine prEvent_draws_le_of_card 0 _ _ ?_
    rw [pow_zero, mul_one]
    convert (card_powComb_le _ ⟨v, hv, hv0⟩).trans (Nat.sub_le_sub_right (B.cvec_len s c x₀) 1)
      using 1
    convert card_filter_fin_one (fun ρ => powComb (B.cvec s c x₀) ρ = 0) using 2

/-- Round `0`'s error is at most `2^32 / |E|` when `4 N + ncv ≤ 2^32`. -/
theorem errMain_le (h : 4 * B.N + B.ncv ≤ 2 ^ 32) :
    B.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold errMain Heap.busError
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

/-- **`aux` holds of every stack**: the Keccak VM's instance has no Flock region (`flock := none`; the Keccak-f
region is `KeccakAux`'s). -/
theorem aux_trivial (rows : List ℕ) (q : D.Stack rows) : (D.inst rows).aux q := by
  intro r hr
  simp [KDeployment.inst, KeccakVm.keccakIsaInstance] at hr

/-- **The relation from `MainHolds` and the Keccak-f region with the lanes' copies.** -/
theorem rel_of (F : KeccakVm.KeccakFlockSpec) (s : USt) (c : Stk) (h : B.MainHolds s c)
    (haux : KeccakVm.KeccakAux F D.prog (D.sizes s.2) (kvStack D.prog (D.sizes s.2) D.shape c)) :
    RelK F D s c :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, aux_trivial _ _⟩, haux⟩

end BusModelK

end UniKeccakSound.Ids
