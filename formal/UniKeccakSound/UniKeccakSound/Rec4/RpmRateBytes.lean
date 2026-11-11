-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Byte lemmas adapted from this repository's
-- `formal/EndToEnd/ZK/PcsRoot.lean` (`beWord_eq_bytesLane`) and `formal/EndToEnd/ZK/PcsExtract.lean` (`bsw`,
-- `bsw_bsw`, `beWord_lanesBytes`), themselves on leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0: `common/Common/Lanes.lean`).
import Compose.ListChainKRpmS
import Compose.WideSpec
import UniKeccakSound.Rec4.RateTransfer
import UniStatement.Rec

/-!
# The rate's bytes, the lanes, and the rate model's answer

The rate transfer (`Keccak256RateTransfer`) is stated on `RState`, the Keccak state's 200 bytes split as the whole rate
(136 bytes), nothing, and the capacity. Here:

* `kEquivR : Common.KState ≃ RState` (the same bytes, the rate in one piece) and `rEquiv : KeccakState ≃ RState`
  (lanes to bytes, then that);
* `rEquiv_symm_getElem`: lane `i < 17` of a byte state is read off its rate alone; `rate_rEquiv_eq`: two lane states
  agreeing on lanes `0 … 16` have the same rate;
* `rateOfState` (Keccak-256's last state read as the rate model's answer: the digest, lanes `0 … 3`, and the tail, the
  big-endian words of bytes `32 … 136`), `rbij : RateBytes ≃ Digest × TailP` (the same reading of the rate's 136
  bytes, a bijection), `rateOfState_rEquiv_symm` (the one is the other on the rate);
* `keccak256StateWith_rEquiv`: Keccak-256's last state over a permutation of the lane states is the sponge over that
  permutation read on `RState` (`keccakPaddingR`), in every monad.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace UniKeccakSound.Rec4

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Compose (TailP)
open QuotientRpm (Limbs)

/-! ## Big-endian words -/

theorem or_step {a x : ℕ} (ha : a < 2 ^ 56) (hx : x < 256) :
    a * 256 % 18446744073709551616 ||| x = a * 256 + x := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, show (256 : ℕ) = 2 ^ 8 by rfl,
    LeanVM.Rpm.or_mul_two_pow _ (by omega)]
  ring

theorem or_step0 {a x : ℕ} (hx : x < 256) : a * 256 ||| x = a * 256 + x := by
  rw [Nat.or_comm, show (256 : ℕ) = 2 ^ 8 by rfl, LeanVM.Rpm.or_mul_two_pow _ (by omega)]
  ring

theorem beWord_eq_bytesLane (b : List UInt8) (k : ℕ) :
    PcsQuotient.Transcript.beWord b k =
      LeanVM.Rpm.bytesLane (((List.range 8).map fun i ↦ b.getD (k + i) 0).reverse) := by
  apply UInt64.toNat_inj.mp
  simp only [PcsQuotient.Transcript.beWord, LeanVM.Rpm.bytesLane, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.foldr_cons, List.foldr_nil,
    UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.toNat_ofNat,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero, Nat.shiftLeft_eq]
  have hb : ∀ i, (b.getD (k + i) 0).toNat < 256 := fun i ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  generalize (b.getD (k + 0) 0).toNat = x0 at *
  generalize (b.getD (k + 1) 0).toNat = x1 at *
  generalize (b.getD (k + 2) 0).toNat = x2 at *
  generalize (b.getD (k + 3) 0).toNat = x3 at *
  generalize (b.getD (k + 4) 0).toNat = x4 at *
  generalize (b.getD (k + 5) 0).toNat = x5 at *
  generalize (b.getD (k + 6) 0).toNat = x6 at *
  generalize (b.getD (k + 7) 0).toNat = x7 at *
  norm_num
  rw [or_step0 h1, or_step (by omega) h2, or_step (by omega) h3, or_step (by omega) h4,
    or_step (by omega) h5, or_step (by omega) h6, or_step (by omega) h7]
  ring

/-- A word with its bytes reversed. -/
def bsw (w : UInt64) : UInt64 := LeanVM.Rpm.bytesLane (wordBytes w).reverse

theorem wordBytes_bytesLane_of_length {b : List UInt8} (hb : b.length = 8) :
    wordBytes (LeanVM.Rpm.bytesLane b) = b := by
  rw [LeanVM.Rpm.wordBytes_bytesLane]
  match b, hb with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem bsw_bsw (w : UInt64) : bsw (bsw w) = w := by
  unfold bsw
  rw [wordBytes_bytesLane_of_length (by simp [LeanVM.Rpm.wordBytes_len]), List.reverse_reverse]
  simpa using LeanVM.Rpm.bytesLane_wordBytes_append w []

theorem beWord_lanesBytes (l : List UInt64) (i k : ℕ) (hk : k = 8 * i) (hi : i < l.length) :
    PcsQuotient.Transcript.beWord (LeanVM.Rpm.lanesBytes l) k = bsw l[i] := by
  subst hk
  rw [beWord_eq_bytesLane, bsw]
  congr 2
  have : ∀ j ∈ List.range 8, (LeanVM.Rpm.lanesBytes l).getD (8 * i + j) 0 =
      (l[i] >>> (8 * j).toUInt64).toUInt8 := by
    intro j hj
    have hj' : j < 8 := List.mem_range.1 hj
    rw [LeanVM.Rpm.getD_lanesBytes _ _ (by omega)]
    have h1 : (8 * i + j) / 8 = i := by omega
    have h2 : (8 * i + j) % 8 = j := by omega
    simp only [h1, h2]
    rw [LeanVM.Rpm.wordBytes_getD _ _ hj']
  rw [List.map_congr_left this]
  rfl

/-! ## The rate model's answer, from lanes -/

/-- **The rate model's answer from the rate's lanes `f 0 … f 16`**: the digest (lanes `0 … 3`), the tail (lanes
`4 … 16` byte-reversed, challenge `k + 1`'s limbs lanes `3k + 6, 3k + 5, 3k + 4`). -/
def ofLanes (f : ℕ → UInt64) : Digest × TailP :=
  (#v[f 0, f 1, f 2, f 3],
    ((bsw (f 6), bsw (f 5), bsw (f 4)), (bsw (f 9), bsw (f 8), bsw (f 7)),
      (bsw (f 12), bsw (f 11), bsw (f 10)), (bsw (f 15), bsw (f 14), bsw (f 13)), bsw (f 16)))

theorem ofLanes_congr {f g : ℕ → UInt64} (h : ∀ i < 17, f i = g i) : ofLanes f = ofLanes g := by
  simp only [ofLanes, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num),
    h 9 (by norm_num), h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num), h 13 (by norm_num),
    h 14 (by norm_num), h 15 (by norm_num), h 16 (by norm_num)]

/-- The rate's seventeen lanes of an answer. -/
def toLanes (p : Digest × TailP) : List UInt64 :=
  [p.1[0], p.1[1], p.1[2], p.1[3], bsw p.2.1.2.2, bsw p.2.1.2.1, bsw p.2.1.1,
    bsw p.2.2.1.2.2, bsw p.2.2.1.2.1, bsw p.2.2.1.1, bsw p.2.2.2.1.2.2, bsw p.2.2.2.1.2.1, bsw p.2.2.2.1.1,
    bsw p.2.2.2.2.1.2.2, bsw p.2.2.2.2.1.2.1, bsw p.2.2.2.2.1.1, bsw p.2.2.2.2.2]

@[simp] theorem length_toLanes (p : Digest × TailP) : (toLanes p).length = 17 := rfl

theorem ofLanes_toLanes (p : Digest × TailP) : ofLanes (fun i ↦ (toLanes p).getD i 0) = p := by
  obtain ⟨d, ⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩, ⟨e0, e1, e2⟩, t⟩ := p
  simp only [ofLanes, toLanes, List.getD_cons_succ, List.getD_cons_zero, bsw_bsw]
  refine Prod.ext ?_ rfl
  apply Vector.ext
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem toLanes_ofLanes (f : ℕ → UInt64) : toLanes (ofLanes f) = List.ofFn fun i : Fin 17 ↦ f i := by
  simp [toLanes, ofLanes, bsw_bsw, List.ofFn_succ]

/-- The 136 bytes of the rate's seventeen lanes. -/
def bytesOfLanes (l : List UInt64) (h : l.length = 17) : RateBytes :=
  ⟨(LeanVM.Rpm.lanesBytes l).toArray, by simp [h]⟩

theorem rate_toList_eq (r : RateBytes) :
    r.toList = LeanVM.Rpm.lanesBytes (List.ofFn fun i : Fin 17 ↦ leLane r.toList i) :=
  (LeanVM.Rpm.lanesBytes_ofFn_leLane _ 17 (by simp)).symm

/-- **The rate model's answer of the rate's 136 bytes**: the digest and the tail (`ofLanes` of its lanes), a
bijection. -/
def rbij : RateBytes ≃ Digest × TailP where
  toFun r := ofLanes fun i ↦ leLane r.toList i
  invFun p := bytesOfLanes (toLanes p) (length_toLanes p)
  left_inv r := by
    apply Vector.toList_inj.mp
    show LeanVM.Rpm.lanesBytes (toLanes (ofLanes fun i ↦ leLane r.toList i)) = r.toList
    rw [toLanes_ofLanes, ← rate_toList_eq]
  right_inv p := by
    show ofLanes (fun i ↦ leLane (bytesOfLanes (toLanes p) (length_toLanes p)).toList i) = p
    conv_rhs => rw [← ofLanes_toLanes p]
    refine ofLanes_congr fun i hi ↦ ?_
    show leLane (LeanVM.Rpm.lanesBytes (toLanes p)) i = _
    rw [LeanVM.Rpm.leLane_lanesBytes _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]

theorem rbij_apply (r : RateBytes) : rbij r = ofLanes fun i ↦ leLane r.toList i := rfl

/-! ## The state's rate on bytes -/

/-- The Keccak state's bytes, the rate in one piece. -/
def kEquivR : Common.KState ≃ RState := Equiv.prodCongr kBlockEquiv (Equiv.refl _)

/-- **The lane state as `RState`**: its 200 bytes (`KState.toRpm`), the rate in one piece. -/
def rEquiv : KeccakState ≃ RState := LeanVM.Rpm.stateEquiv.trans kEquivR

theorem rEquiv_symm_apply (S : RState) : rEquiv.symm S = LeanVM.Rpm.KState.ofRpm (kEquivR.symm S) := rfl

theorem rEquiv_apply (s : KeccakState) : rEquiv s = kEquivR (LeanVM.KState.toRpm s) := rfl

/-- The rate of a byte state's two parts is the rate. -/
theorem ofRBlock_toList (R : RBlock) : (ofRBlock R).1.toList ++ (ofRBlock R).2.toList = R.1.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [ofRBlock, Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split
  · rfl
  · simp only [List.length_append] at h1
    congr 1
    omega

/-- **A lane of the rate is read off the rate's bytes.** -/
theorem rEquiv_symm_getElem (S : RState) (i : ℕ) (hi : i < 17) :
    (rEquiv.symm S)[i] = leLane S.1.1.toList i := by
  rw [rEquiv_symm_apply, LeanVM.Rpm.KState.ofRpm, Vector.getElem_ofFn]
  show leLane ((ofRBlock S.1).1.toList ++ (ofRBlock S.1).2.toList ++ S.2.toList) i = _
  rw [ofRBlock_toList, LeanVM.Rpm.leLane_append_left _ _ _ (by simp; omega)]

theorem lane_rEquiv_symm (S : RState) (i : ℕ) (hi : i < 17) :
    Keccak.lane (rEquiv.symm S) i = leLane S.1.1.toList i := by
  rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega), rEquiv_symm_getElem _ _ hi]

theorem leLane_rEquiv (s : KeccakState) (i : ℕ) (hi : i < 17) :
    leLane (rEquiv s).1.1.toList i = s[i] := by
  rw [← rEquiv_symm_getElem _ _ hi, Equiv.symm_apply_apply]

/-- **The rate of a lane state reads lanes `0 … 16` only.** -/
theorem rate_rEquiv_eq {s s' : KeccakState} (h : ∀ i (hi : i < 17), s[i] = s'[i]) :
    (rEquiv s).1.1 = (rEquiv s').1.1 := by
  apply Vector.toList_inj.mp
  rw [rate_toList_eq, rate_toList_eq (rEquiv s').1.1]
  have e : (fun i : Fin 17 ↦ leLane (rEquiv s).1.1.toList i) = fun i : Fin 17 ↦ leLane (rEquiv s').1.1.toList i := by
    funext i
    rw [leLane_rEquiv _ _ i.2, leLane_rEquiv _ _ i.2, h _ i.2]
  rw [e]

/-! ## Keccak-256's last state read as the rate model's answer -/

/-- The big-endian word of rate bytes `o … o + 8` of a sponge state. -/
def rateWord (st : KeccakState) (o : ℕ) : UInt64 :=
  PcsQuotient.Transcript.beWord (UniStatement.rateBytesOf st) o

/-- The rate past the digest as the wide draws read it (challenge `k + 1`'s limbs are the triple `k`). -/
def tailOfState (st : KeccakState) : TailP :=
  ((rateWord st 48, rateWord st 40, rateWord st 32), (rateWord st 72, rateWord st 64, rateWord st 56),
   (rateWord st 96, rateWord st 88, rateWord st 80), (rateWord st 120, rateWord st 112, rateWord st 104),
   rateWord st 128)

/-- **Keccak-256's last state as the rate model's answer**: the digest and the tail. -/
def rateOfState (st : KeccakState) : Digest × TailP := (UniStatement.digestOfState st, tailOfState st)

theorem rateBytesOf_eq_lanesBytes (st : KeccakState) :
    UniStatement.rateBytesOf st = LeanVM.Rpm.lanesBytes ((List.range 17).map (Keccak.lane st)) := by
  simp [UniStatement.rateBytesOf, LeanVM.Rpm.lanesBytes, List.flatMap_map]

theorem rateWord_eq (st : KeccakState) (i : ℕ) (hi : i < 17) : rateWord st (8 * i) = bsw (Keccak.lane st i) := by
  rw [rateWord, rateBytesOf_eq_lanesBytes, beWord_lanesBytes _ i _ rfl (by simpa using hi)]
  simp

theorem rateOfState_eq (st : KeccakState) : rateOfState st = ofLanes (Keccak.lane st) := by
  simp only [rateOfState, tailOfState, ofLanes, UniStatement.digestOfState]
  rw [show (48 : ℕ) = 8 * 6 from rfl, show (40 : ℕ) = 8 * 5 from rfl, show (32 : ℕ) = 8 * 4 from rfl,
    show (72 : ℕ) = 8 * 9 from rfl, show (64 : ℕ) = 8 * 8 from rfl, show (56 : ℕ) = 8 * 7 from rfl,
    show (96 : ℕ) = 8 * 12 from rfl, show (88 : ℕ) = 8 * 11 from rfl, show (80 : ℕ) = 8 * 10 from rfl,
    show (120 : ℕ) = 8 * 15 from rfl, show (112 : ℕ) = 8 * 14 from rfl, show (104 : ℕ) = 8 * 13 from rfl,
    show (128 : ℕ) = 8 * 16 from rfl]
  simp only [rateWord_eq _ _ (by norm_num : (4 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (5 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (6 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (7 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (8 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (9 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (10 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (11 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (12 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (13 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (14 : ℕ) < 17), rateWord_eq _ _ (by norm_num : (15 : ℕ) < 17),
    rateWord_eq _ _ (by norm_num : (16 : ℕ) < 17)]

/-- **The answer of a byte state's lanes is `rbij` of its rate.** -/
theorem rateOfState_rEquiv_symm (S : RState) : rateOfState (rEquiv.symm S) = rbij S.1.1 := by
  rw [rateOfState_eq, rbij_apply]
  exact ofLanes_congr fun i hi ↦ lane_rEquiv_symm S i hi

/-- The digest of a state is the first component of its answer. -/
theorem digestOfState_eq (st : KeccakState) : UniStatement.digestOfState st = (rateOfState st).1 := rfl

/-- The 32 digest bytes of the rate. -/
def dgOf (r : RateBytes) : Common.DigestBytes := Vector.ofFn fun i : Fin 32 ↦ r[i.val]

theorem rate_toList_split (r : RateBytes) :
    r.toList = (dgOf r).toList ++ (Vector.ofFn fun i : Fin 104 ↦ r[32 + i.val]).toList := by
  have h := ofRBlock_toList (r, Vector.replicate 0 0)
  exact h.symm

/-- **The answer's digest is the rate's first 32 bytes, as lanes.** -/
theorem rbij_fst (r : RateBytes) : (rbij r).1 = LeanVM.Digest.ofRpm (dgOf r) := by
  rw [rbij_apply]
  have e : ∀ i < 4, leLane r.toList i = leLane (dgOf r).toList i := fun i hi ↦ by
    rw [rate_toList_split, LeanVM.Rpm.leLane_append_left _ _ _ (by simp; omega)]
  simp only [ofLanes, LeanVM.Digest.ofRpm, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
    e 3 (by norm_num)]

theorem toB_rbij_fst (r : RateBytes) : Compose.toB (rbij r).1 = dgOf r := by
  rw [rbij_fst]
  exact LeanVM.Rpm.digestToRpm_ofRpm _

/-- The digest bytes of a byte state's rate are its digest bytes. -/
theorem dgOf_kEquivR (k : Common.KState) : dgOf (kEquivR k).1.1 = k.1.1 := by
  apply Vector.ext
  intro i hi
  simp [dgOf, kEquivR, kBlockEquiv, toRBlock]

end UniKeccakSound.Rec4
