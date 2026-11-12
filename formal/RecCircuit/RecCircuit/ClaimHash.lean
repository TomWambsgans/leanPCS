-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The encoding is the EIP draft's PCS claim
-- (`crates/pcs_claim`, `PcsClaim::encode`: `VERSION ‖ n ‖ root ‖ ood ‖ point ‖ value`, an element's 24 bytes
-- `element_bytes`), as `crates/leanvm/rec/src/circuit/compile.rs` hashes π1's claims in π2's circuit.
import RecCircuit.Calls

/-!
# π1's hashed claims: a satisfied circuit carries their Keccak-256

π2's circuit hashes π1's claims `hashed` (`compile::hashed_claims`, π1-rec4: all three): each claim's encoding
(`claimEncoding`, the EIP draft's PCS claim of the graph's call words: `[1, n]`, the root's 32 bytes, each later
word's element bytes `8 .. 32`) as message bits, its Keccak-256 by the sponge, the digest's four statement-order words
a `claimHash j` port. The message's bits are constants, the stream's bits (a stream root, a hashed read) or free bits
of an element, packed into limbs and checked equal to the element's own by a zero port (`packed + limbs`).

**`claimHash_port`**: on a satisfied accepted circuit whose hashed claims' zero ports carry zeros (π2's verifier
reads every zero port as zero), the `claimHash j` port carries the four big-endian words of
`keccak256 (claimEncoding S V (g.calls[hashed[j]]))`, in `RecGraph`'s semantics over Keccak-f[1600] (`rgVals`) on the
witness's stream `S` and public input.
-/

namespace RecCircuit

open Primitives PcsCircuit LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  UniStatement

/-! ## The encoding -/

/-- The bytes a claim's encoding holds of its words from position `k` on: word `0` (the root) its 32 bytes, a later
word (an element's) its bytes `8 .. 32`. -/
def claimWordBytes (stream : Array UInt8) (vals : Array RecGraph.Value) : ℕ → List RecGraph.Word → List UInt8
  | _, [] => []
  | 0, w :: ws => RecGraph.wordBytes stream vals w ++ claimWordBytes stream vals 1 ws
  | k + 1, w :: ws => (RecGraph.wordBytes stream vals w).drop 8 ++ claimWordBytes stream vals (k + 2) ws

/-- **The EIP draft's PCS-claim encoding of a claim's words** (`PcsClaim::encode`), in `RecGraph`'s semantics of the
words (`RecGraph.wordBytes`): `VERSION = 1`, `n` (the words but the root, the answer and the value), the root's 32
bytes, then each later word's element bytes `8 .. 32`. -/
def claimEncoding (stream : Array UInt8) (vals : Array RecGraph.Value) (ws : List RecGraph.Word) : List UInt8 :=
  [1, (ws.length - 3).toUInt8] ++ claimWordBytes stream vals 0 ws

theorem claimWordBytes_succ (S : Array UInt8) (V : Array RecGraph.Value) :
    ∀ (k : ℕ) (ws : List RecGraph.Word),
      claimWordBytes S V (k + 1) ws = ws.flatMap fun w => (RecGraph.wordBytes S V w).drop 8
  | _, [] => rfl
  | k, w :: ws => by
    simp only [claimWordBytes, List.flatMap_cons]
    rw [claimWordBytes_succ S V (k + 1) ws]

/-- The encoding, in the caller's terms. -/
theorem claimEncoding_eq (S : Array UInt8) (V : Array RecGraph.Value) (ws : List RecGraph.Word) :
    claimEncoding S V ws = [1, (ws.length - 3).toUInt8] ++ (ws.take 1).flatMap (RecGraph.wordBytes S V) ++
      (ws.drop 1).flatMap fun w => (RecGraph.wordBytes S V w).drop 8 := by
  cases ws with
  | nil => rfl
  | cons w ws => simp [claimEncoding, claimWordBytes, claimWordBytes_succ]

/-! ## Lists -/

theorem exists_nth_filter {α : Type} [Inhabited α] (p : α → Bool) :
    ∀ (l : List α) (m : ℕ), m < (l.filter p).length →
      ∃ J < l.length, p (l.getD J default) = true ∧ ((l.take J).filter p).length = m
  | [], m, h => by simp at h
  | a :: l, m, h => by
    by_cases ha : p a = true
    · cases m with
      | zero => exact ⟨0, by simp, by simpa using ha, by simp⟩
      | succ m =>
        rw [List.filter_cons_of_pos ha, List.length_cons] at h
        obtain ⟨J, hJ, hp, hc⟩ := exists_nth_filter p l m (by omega)
        refine ⟨J + 1, by simpa using hJ, by simpa using hp, ?_⟩
        rw [List.take_succ_cons, List.filter_cons_of_pos ha, List.length_cons, hc]
    · rw [List.filter_cons_of_neg ha] at h
      obtain ⟨J, hJ, hp, hc⟩ := exists_nth_filter p l m h
      refine ⟨J + 1, by simpa using hJ, by simpa using hp, ?_⟩
      rw [List.take_succ_cons, List.filter_cons_of_neg ha, hc]

theorem lookup_map_self (f : ℕ → ℕ) (e : ℕ) :
    ∀ L : List ℕ, (L.map fun x => (x, f x)).lookup e = if e ∈ L then some (f e) else none
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.lookup_cons]
    by_cases h : e = x
    · subst h; simp
    · have : (e == x) = false := by simpa using h
      rw [this, lookup_map_self f e L]
      simp [h]

/-! ## Bits of words -/

theorem lane_eq (x : K) : K.lane x = F64.toU64 x := rfl

/-- **The bits of a packed word**: bits whose packing `Σ B_e x^e` is `y` are `y`'s bits. -/
theorem bits_of_sum (B : ℕ → K) (hB : ∀ e < 64, B e = 0 ∨ B e = 1) (y : K)
    (h : ∑ e ∈ Finset.range 64, B e * F64.G ^ e = y) :
    ∀ e < 64, B e = ofBool ((F64.toU64 y).toNat.testBit e) := by
  let b : ℕ → ℕ := fun e => if B e = 1 then 1 else 0
  have hb : ∀ j, b j ≤ 1 := fun j => by simp only [b]; split <;> omega
  obtain ⟨hlt, htb⟩ := foldl_pow_testBit b hb 64
  set N := (List.range 64).foldl (fun acc j => acc + 2 ^ j * b j) 0
  have hBN : ∀ e < 64, B e = ofBool (N.testBit e) := by
    intro e he
    rw [htb e]
    rcases hB e he with h0 | h1
    · have hb0 : b e = 0 := by simp [b, h0]
      simp [hb0, h0, ofBool]
    · have hb1 : b e = 1 := by simp [b, h1]
      simp [hb1, h1, ofBool, he]
  have hy : y = F64.ofNat N := by rw [← h]; exact sum_bits_word B N hBN
  have hN : (F64.toU64 y).toNat = N := by
    rw [hy, ← F64.ofU64_ofNat, F64.toU64_ofU64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  intro e he
  rw [hN]; exact hBN e he

/-- Bit `t` of byte `j` of a word's eight big-endian bytes. -/
theorem be64_bit (w : UInt64) (j t : ℕ) (hj : j < 8) (ht : t < 8) :
    ((be64 w).getD j 0).toNat.testBit t = w.toNat.testBit (8 * (7 - j) + t) := by
  simp only [be64, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  have h1 : (8 * (7 - j)).toUInt64.toNat % 64 = 8 * (7 - j) := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  rw [h1, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht]

theorem be64_length (w : UInt64) : (be64 w).length = 8 := by simp [be64]

/-- An element's limb by a number below 3. -/
def limbAt (x : E) (i : ℕ) : K := if i = 0 then x.limb 0 else if i = 1 then x.limb 1 else x.limb 2

/-- **Bit `k` of an element's 24 bytes** (`element_bytes`: `c2 ‖ c1 ‖ c0` big-endian): bit `8 (7 − k/8 mod 8) + k mod 8`
of limb `2 − k/64`. -/
theorem elementWord_drop_bit (x : E) (k : ℕ) (hk : k < 192) :
    bitOf ((UniStatement.elementWord x).drop 8) k =
      (K.lane (limbAt x (2 - k / 64))).toNat.testBit (8 * (7 - k / 8 % 8) + k % 8) := by
  have e8 : (UniStatement.elementWord x).drop 8 =
      be64 (x.limb 2).lane ++ (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) := by
    simp [UniStatement.elementWord, List.append_assoc]
  rw [e8]
  unfold bitOf
  have hl := be64_length
  by_cases h0 : k / 8 < 8
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h0), be64_bit _ _ _ h0 (Nat.mod_lt _ (by norm_num))]
    have : 2 - k / 64 = 2 := by omega
    rw [this, show k / 8 % 8 = k / 8 by omega]; rfl
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl]
    by_cases h1 : k / 8 - 8 < 8
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h1), be64_bit _ _ _ h1 (Nat.mod_lt _ (by norm_num))]
      have : 2 - k / 64 = 1 := by omega
      rw [this, show k / 8 - 8 = k / 8 % 8 by omega]; rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl,
        be64_bit _ _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
      have : 2 - k / 64 = 0 := by omega
      rw [this, show k / 8 - 8 - 8 = k / 8 % 8 by omega]; rfl

/-! ## The free elements' bits -/

/-- The index of the bit at exponent `e` of a free element's limb `li` (`freeLimbBits`'s lookup). -/
def freeIdx (li e : ℕ) : ℕ := 8 * (8 * (2 - li) + (7 - e / 8)) + e % 8

/-- The exponents `freeLimbBits` takes, in its order. -/
def freeExps : List ℕ := (List.range 8).flatMap fun b => (List.range 8).map fun t => 8 * (7 - b) + t

theorem freeLimbBits_eq (bits : Array ℕ) (li : ℕ) (hli : li < 3) :
    Compiled.freeLimbBits bits li = freeExps.map fun e => (e, bits.getD (freeIdx li e) NONE) := by
  interval_cases li <;> rfl

theorem mem_freeExps : ∀ e < 64, e ∈ freeExps := by decide

namespace Compiled

variable {c : Compiled} {r : Recorded} {w : ℕ → K}

theorem freeOk_parts {X : Ctx} {packOf : Array (Option ℕ)} {fr : ℕ × Array Val × Array Val × Array Val} {id : ℕ}
    (h : c.freeOk X packOf fr id = true) :
    fr.1 = id ∧ c.live.getD id false = true ∧ isStateNode (c.nodes.getD id default) = false ∧ fr.2.1.size = 192 ∧
      (∀ k < 192, X.bitOk ((fr.2.1).getD k NONE) = true) ∧ fr.2.2.1.size = 3 ∧
      (∀ li < 3, c.packIs packOf ((fr.2.2.1).getD li NONE) (freeLimbBits fr.2.1 li) = true) ∧
      arithOk X .add fr.2.2.2 fr.2.2.1 (c.limbsOf id) = true := by
  unfold freeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, allBelow_spec h5, h6, allBelow_spec h7, h8⟩

/-- **A free element's bits are its value's**: given its zero port's limbs zero (`packed + limbs = 0`), each of its
192 free bits is the bit of the element's 24 bytes. -/
theorem free_bit_val (hc : c.Checked r) (hw : c.circuit.Satisfied w) {fr : ℕ × Array Val × Array Val × Array Val}
    {id : ℕ} (hfr : c.freeOk c.ctx c.packOf fr id = true) (hid : id < c.nodes.size)
    (hsum : ∀ l < 3, c.ctx.val w ((fr.2.2.2).getD l NONE) = 0) :
    ∀ k < 192, c.ctx.val w ((fr.2.1).getD k NONE) =
      ofBool (bitOf ((UniStatement.elementWord ((c.valsW r w).getD id default).toE).drop 8) k) := by
  have G := hc.good hw
  obtain ⟨-, hl, hns, -, hbit, hps, hpk, har⟩ := freeOk_parts hfr
  obtain ⟨hs3, hp3, hl3, hop⟩ := arith_ok G har
  -- The element's limbs.
  have hinv := node_inv hc hw id hid hl
  unfold NodeInv at hinv
  rw [hns] at hinv
  simp only [Bool.false_eq_true, ite_false] at hinv
  obtain ⟨-, hx⟩ := hinv
  set x := ((c.valsW r w).getD id default).toE
  -- `packed = limbs`.
  have hsum0 : c.limbsE w fr.2.2.2.toList = 0 := by
    rw [limbsE_toList, hsum 0 (by norm_num), hsum 1 (by norm_num), hsum 2 (by norm_num), F192.zero_eq]
  rw [hsum0, opE] at hop
  have hpe : c.limbsE w fr.2.2.1.toList = c.limbsE w (c.limbsOf id).toList := by
    have := eq_neg_of_add_eq_zero_left hop.symm
    rw [this, CharTwo.neg_eq]
  rw [limbsE_toList, limbsE_toList] at hpe
  obtain ⟨e0, e1, e2⟩ := F192.ofLimbs_injective hpe
  have hlimb : ∀ li < 3, c.ctx.val w ((fr.2.2.1).getD li NONE) = limbAt x li := by
    intro li hli
    rw [← hx]
    interval_cases li
    · rw [e0]; rfl
    · rw [e1]; rfl
    · rw [e2]; rfl
  -- Each limb's bits.
  have hbits : ∀ li < 3, ∀ e < 64, c.ctx.val w ((fr.2.1).getD (freeIdx li e) NONE) =
      ofBool ((K.lane (limbAt x li)).toNat.testBit e) := by
    intro li hli
    have hpk' := hpk li hli
    unfold packIs at hpk'
    split at hpk'
    · rename_i t ht
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpk'
      obtain ⟨⟨htl, hout⟩, hbs⟩ := hpk'
      have hok := hc.pack _ (Ctx.getD_mem default htl)
      have hv := Ctx.pack_val G hok
      rw [hout, hbs, hlimb li hli, freeLimbBits_eq _ _ hli] at hv
      have hB : ∀ e < 64, c.ctx.bitAt w (freeExps.map fun e => (e, (fr.2.1).getD (freeIdx li e) NONE)) e =
          c.ctx.val w ((fr.2.1).getD (freeIdx li e) NONE) := by
        intro e he
        rw [Ctx.bitAt, lookup_map_self, if_pos (mem_freeExps e he)]
      have := bits_of_sum _ (fun e he => by
          rw [hB e he]
          have hfi : freeIdx li e < 192 := by unfold freeIdx; omega
          exact Ctx.bit_isBit G (hbit _ hfi)) _ hv.symm
      intro e he
      rw [← hB e he, this e he, lane_eq]
    · cases hpk'
  intro k hk
  rw [elementWord_drop_bit _ k hk]
  have := hbits (2 - k / 64) (by omega) (8 * (7 - k / 8 % 8) + k % 8) (by omega)
  rw [show freeIdx (2 - k / 64) (8 * (7 - k / 8 % 8) + k % 8) = k by unfold freeIdx; omega] at this
  exact this

/-! ## The message's bits -/

theorem eval_copyFwd (r : ℕ) (f : ℕ → K) : (Ctx.copyFwdPoly r).eval f = f (r + 1) := by
  simp [Poly.eval_eq, Ctx.copyFwdPoly, Ctx.one_eq]

theorem sameBit_val (G : c.ctx.Good w) {v x : ℕ} (h : c.ctx.sameBit v x = true) : c.ctx.val w x = c.ctx.val w v := by
  unfold Ctx.sameBit at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · rw [h]
  · exact Ctx.copy_val G h
  · unfold Ctx.copyFwdOk at h
    rw [G.gate h, eval_copyFwd, add_zero, Ctx.cellVal_cons_self]

theorem constMBits_length (bytes : List UInt8) : (constMBits bytes).length = 8 * bytes.length := by
  simp [constMBits]

theorem constMBits_getD (bytes : List UInt8) (p : ℕ) (hp : p < 8 * bytes.length) (d : MBit := default) :
    (constMBits bytes).getD p d = .const (bitOf bytes p) := by
  simp [constMBits, List.getD_eq_getElem?_getD, hp, bitOf]

/-- **What a bit of a hashed claim's message means**: its bit `bit` of the encoding. A constant is it; the stream's
bit `i` is the witness's stream's; bit `k` of free element `f` (one of the first `nf`) is bit `k` of the 24 bytes of
the element at the expanded node `nodeOf f`. -/
def MBitMeans (c : Compiled) (r : Recorded) (w : ℕ → K) (nodeOf : ℕ → ℕ) (nf : ℕ) : MBit → Bool → Prop
  | .const b, bit => b = bit
  | .stream i, bit => i < 8 * (c.streamW r w).length ∧ bitOf (c.streamW r w) i = bit
  | .free f k, bit => f < nf ∧ k < 192 ∧
      bitOf ((UniStatement.elementWord ((c.valsW r w).getD (nodeOf f) default).toE).drop 8) k = bit

theorem MBitMeans.mono {nodeOf : ℕ → ℕ} {nf nf' : ℕ} (h : nf ≤ nf') {m : MBit} {bit : Bool}
    (hm : MBitMeans c r w nodeOf nf m bit) : MBitMeans c r w nodeOf nf' m bit := by
  cases m with
  | const => exact hm
  | stream => exact hm
  | free f k => exact ⟨by have := hm.1; omega, hm.2⟩

/-- **A checked message bit means its encoding's bit.** -/
theorem mbit_val (hc : c.Checked r) (hw : c.circuit.Satisfied w)
    {frees : Array (ℕ × Array Val × Array Val × Array Val)} {nodeOf : ℕ → ℕ} {nf : ℕ}
    (hfree : ∀ f < nf, ∀ k < 192, c.ctx.val w (((frees.getD f default).2.1).getD k NONE) =
      ofBool (bitOf ((UniStatement.elementWord ((c.valsW r w).getD (nodeOf f) default).toE).drop 8) k))
    {b : Bit} {m : MBit} {bit : Bool} (hok : c.mbitOk c.ctx frees b m = true) (hm : MBitMeans c r w nodeOf nf m bit) :
    Ctx.BitMeans c.ctx w b bit := by
  have G := hc.good hw
  cases m with
  | const v =>
    simp only [mbitOk, beq_iff_eq] at hok
    simp only [MBitMeans] at hm
    subst hok; subst hm
    exact bitMeans_const _ _ _
  | stream i =>
    cases b with
    | v x =>
      simp only [mbitOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
      obtain ⟨hsome, hsb⟩ := hok
      obtain ⟨hi, hbit⟩ := hm
      show c.ctx.val w x = ofBool bit
      rw [streamW_length] at hi
      have e : i = 8 * (i / 8) + i % 8 := by omega
      rw [sameBit_val G hsb, e, stream_bit hc hw (by omega) (Nat.mod_lt _ (by norm_num)) hsome, ← hbit]
      simp only [bitOf, streamW]
      all_goals try rw [show (8 * (i / 8) + i % 8) / 8 = i / 8 by omega]
      all_goals try rw [show (8 * (i / 8) + i % 8) % 8 = i % 8 by omega]
    | zero => simp [mbitOk] at hok
    | one => simp [mbitOk] at hok
  | free f k =>
    cases b with
    | v x =>
      simp only [mbitOk] at hok
      obtain ⟨hf, hk, hbit⟩ := hm
      show c.ctx.val w x = ofBool bit
      rw [sameBit_val G hok, hfree f hf k hk, hbit]
    | zero => simp [mbitOk] at hok
    | one => simp [mbitOk] at hok

/-! ## The claim's words, bit by bit -/

/-- A graph word as the checker reads a hashed claim's (`ofRGWord`, a node through the expansion's map). -/
def mapW (c : Compiled) : RecGraph.Word → Word
  | .node id => .node (c.map.getD id 0)
  | .const x => .const x
  | .stream a => .stream a

/-- Word `k`'s bytes in a claim's encoding: the root's 32, an element word's `8 .. 32`. -/
def wBytes (S : Array UInt8) (V : Array RecGraph.Value) (k : ℕ) (wd : RecGraph.Word) : List UInt8 :=
  if k = 0 then RecGraph.wordBytes S V wd else (RecGraph.wordBytes S V wd).drop 8

/-- Word `k`'s kind: the root a stream or a constant word, a later one a node or a constant. -/
def wordShape : ℕ → RecGraph.Word → Prop
  | 0, .stream _ | 0, .const _ => True
  | _ + 1, .node _ | _ + 1, .const _ => True
  | _, _ => False

theorem claimWordBytes_cons (S : Array UInt8) (V : Array RecGraph.Value) (k : ℕ) (wd : RecGraph.Word)
    (rest : List RecGraph.Word) :
    claimWordBytes S V k (wd :: rest) = wBytes S V k wd ++ claimWordBytes S V (k + 1) rest := by
  cases k <;> rfl

theorem elementWord_length (x : E) : (UniStatement.elementWord x).length = 32 := by
  simp [UniStatement.elementWord, be64]

theorem slice3 (b : List UInt8) (h : b.length = 24) : slice b 0 8 ++ (slice b 8 8 ++ slice b 16 8) = b := by
  have h16 : slice b 16 8 = b.drop 16 := by
    simp only [slice]; exact List.take_of_length_le (by simp; omega)
  rw [h16]
  simp only [slice, List.drop_zero]
  conv_rhs => rw [← List.take_append_drop 8 b, ← List.take_append_drop 8 (b.drop 8), List.drop_drop]

/-- **A hashed read's 24 bytes are its element's** (`element_bytes` of the read's value). -/
theorem input_bytes (S : List UInt8) (off : ℕ) (h : off + 24 ≤ S.length) :
    (UniStatement.elementWord (inputValue S off 24)).drop 8 = slice S off 24 := by
  have hb : (slice S off 24).length = 24 := slice_length _ _ _ h
  have h8 : ∀ a, a + 8 ≤ 24 → (slice (slice S off 24) a 8).length = 8 := fun a ha => slice_length _ _ _ (by omega)
  have e : inputValue S off 24 = F192.ofLimbs (F64.ofNat (beNat (slice (slice S off 24) 16 8)))
      (F64.ofNat (beNat (slice (slice S off 24) 8 8))) (F64.ofNat (beNat (slice (slice S off 24) 0 8))) := by
    unfold inputValue; rw [if_pos rfl]; rfl
  rw [e]
  show (List.replicate 8 0 ++ be64 (K.lane (F64.ofNat (beNat (slice (slice S off 24) 0 8)))) ++
    be64 (K.lane (F64.ofNat (beNat (slice (slice S off 24) 8 8)))) ++
    be64 (K.lane (F64.ofNat (beNat (slice (slice S off 24) 16 8))))).drop 8 = _
  rw [lane_ofNat, lane_ofNat, lane_ofNat, be64_beNat _ (h8 0 (by norm_num)), be64_beNat _ (h8 8 (by norm_num)),
    be64_beNat _ (h8 16 (by norm_num)), List.append_assoc, List.append_assoc, List.drop_left' (by simp)]
  exact slice3 _ hb

theorem stream_means (S : List UInt8) (a n p : ℕ) (h : a + n ≤ S.length) (hp : p < 8 * n) :
    bitOf S (8 * a + p) = bitOf (slice S a n) p := by
  simp only [bitOf]
  rw [slice_getD _ _ _ _ (by omega), show (8 * a + p) / 8 = a + p / 8 by omega, show (8 * a + p) % 8 = p % 8 by omega]

variable {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8} {hashed : List ℕ}

theorem mapW_node (c : Compiled) (id : ℕ) : c.mapW (.node id) = .node (c.map.getD id 0) := rfl

theorem wordSpec_succ_node (c : Compiled) (k f q : ℕ) : c.wordSpec (k + 1) (.node q) f =
    match c.nodes.getD q default with
    | .const c0 c1 c2 => (constMBits ((UniStatement.elementWord (UniStatement.eNew c0 c1 c2)).drop 8), [])
    | .input off len =>
      if c.hashedRead off len then ((List.range 192).map fun i => MBit.stream (8 * off + i), [])
      else ((List.range 192).map fun i => MBit.free f i, [q])
    | _ => ((List.range 192).map fun i => MBit.free f i, [q]) := rfl

/-- **A word's message bits mean its bytes in the encoding** (`wordSpec` against `wBytes`). -/
theorem word_means (hc : compile (ofRG g rootsAt iv hashed) = .ok c) (w : ℕ → K) (hE : ExpandSound g c)
    {k f : ℕ} {wd : RecGraph.Word} (hshape : wordShape k wd)
    (hlive : ∀ id, wd = .node id → c.live.getD (c.map.getD id 0) false = true ∧ id < g.nodes.size)
    (hS : ∀ i, MBit.stream i ∈ (c.wordSpec k (c.mapW wd) f).1 →
      i < 8 * (c.streamW (ofRG g rootsAt iv hashed) w).length)
    (nodeOf : ℕ → ℕ)
    (hnodes : ∀ i < (c.wordSpec k (c.mapW wd) f).2.length, nodeOf (f + i) = (c.wordSpec k (c.mapW wd) f).2.getD i 0) :
    (c.wordSpec k (c.mapW wd) f).1.length = 8 * (wBytes (c.streamW (ofRG g rootsAt iv hashed) w).toArray
      (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv hashed) w)) k wd).length ∧
    ∀ p < (c.wordSpec k (c.mapW wd) f).1.length, MBitMeans c (ofRG g rootsAt iv hashed) w nodeOf
      (f + (c.wordSpec k (c.mapW wd) f).2.length) ((c.wordSpec k (c.mapW wd) f).1.getD p default)
      (bitOf (wBytes (c.streamW (ofRG g rootsAt iv hashed) w).toArray
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv hashed) w)) k wd) p) := by
  have hck := checked_of_compile hc
  set r := ofRG g rootsAt iv hashed
  set S := c.streamW r w
  set V := rgVals g iv (c.pubW w) S
  -- Constant bits.
  have hconst : ∀ (bytes : List UInt8), (c.wordSpec k (c.mapW wd) f) = (constMBits bytes, []) →
      wBytes S.toArray V k wd = bytes →
      (c.wordSpec k (c.mapW wd) f).1.length = 8 * (wBytes S.toArray V k wd).length ∧
      ∀ p < (c.wordSpec k (c.mapW wd) f).1.length, MBitMeans c r w nodeOf (f + (c.wordSpec k (c.mapW wd) f).2.length)
        ((c.wordSpec k (c.mapW wd) f).1.getD p default) (bitOf (wBytes S.toArray V k wd) p) := by
    intro bytes hsp hb
    rw [hsp, hb]
    refine ⟨constMBits_length _, fun p hp => ?_⟩
    rw [constMBits_length] at hp
    rw [constMBits_getD _ _ hp]
    rfl
  -- Stream bits.
  have hstream : ∀ (a n : ℕ), (c.wordSpec k (c.mapW wd) f) = ((List.range (8 * n)).map fun i => .stream (8 * a + i), []) →
      0 < n → wBytes S.toArray V k wd = slice S a n →
      (c.wordSpec k (c.mapW wd) f).1.length = 8 * (wBytes S.toArray V k wd).length ∧
      ∀ p < (c.wordSpec k (c.mapW wd) f).1.length, MBitMeans c r w nodeOf (f + (c.wordSpec k (c.mapW wd) f).2.length)
        ((c.wordSpec k (c.mapW wd) f).1.getD p default) (bitOf (wBytes S.toArray V k wd) p) := by
    intro a n hsp hn hb
    have hlast := hS (8 * a + (8 * n - 1)) (by
      rw [hsp]; exact List.mem_map.mpr ⟨8 * n - 1, List.mem_range.mpr (by omega), rfl⟩)
    have hlen : a + n ≤ S.length := by omega
    rw [hsp, hb, slice_length _ _ _ hlen]
    refine ⟨by simp, fun p hp => ?_⟩
    simp only [List.length_map, List.length_range] at hp
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp, Option.map_some,
      Option.getD_some]
    exact ⟨by show 8 * a + p < 8 * S.length; omega, stream_means S a n p hlen hp⟩
  -- A free element.
  have hfree : ∀ id, wd = .node id → (c.wordSpec k (c.mapW wd) f) = ((List.range 192).map (MBit.free f), [c.map.getD id 0]) →
      (c.wordSpec k (c.mapW wd) f).1.length = 8 * (wBytes S.toArray V k wd).length ∧
      ∀ p < (c.wordSpec k (c.mapW wd) f).1.length, MBitMeans c r w nodeOf (f + (c.wordSpec k (c.mapW wd) f).2.length)
        ((c.wordSpec k (c.mapW wd) f).1.getD p default) (bitOf (wBytes S.toArray V k wd) p) := by
    intro id hid hsp
    obtain ⟨hl, hidg⟩ := hlive id hid
    have hn0 := hnodes 0 (by rw [hsp]; simp)
    rw [hsp] at hn0
    simp only [Nat.add_zero, List.getD_cons_zero] at hn0
    have hk : k ≠ 0 := by
      intro h0; subst h0; subst hid; exact hshape
    have hb : wBytes S.toArray V k wd = (UniStatement.elementWord (RecGraph.valE V id)).drop 8 := by
      simp [wBytes, hk, hid, RecGraph.wordBytes]
    have hv : ((c.valsW r w).getD (c.map.getD id 0) default).toE = RecGraph.valE V id :=
      elem_rg hck hE w (live_lt hck hl) hl hidg rfl
    rw [hsp, hb]
    refine ⟨by simp [elementWord_length], fun p hp => ?_⟩
    simp only [List.length_map, List.length_range] at hp
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp, Option.map_some,
      Option.getD_some, List.length_cons, List.length_nil]
    exact ⟨by simp, hp, by rw [hn0, hv]⟩
  cases k with
  | zero =>
    cases wd with
    | stream a =>
      apply hstream a 32 rfl (by norm_num)
      simp only [wBytes, if_pos rfl, RecGraph.wordBytes]
      rw [extract_toList, show a + 32 - a = 32 by omega]
      simp
    | const x => exact hconst (RecGraph.beBytes32 x) rfl (by simp [wBytes, RecGraph.wordBytes])
    | node id => exact (show False from hshape).elim
  | succ k =>
    cases wd with
    | stream a => exact (show False from hshape).elim
    | const x => exact hconst ((RecGraph.beBytes32 x).drop 8) rfl (by simp [wBytes, RecGraph.wordBytes])
    | node id =>
      obtain ⟨hl, hidg⟩ := hlive id rfl
      have hv : ((c.valsW r w).getD (c.map.getD id 0) default).toE = RecGraph.valE V id :=
        elem_rg hck hE w (live_lt hck hl) hl hidg rfl
      have hb : wBytes S.toArray V (k + 1) (.node id) = (UniStatement.elementWord (RecGraph.valE V id)).drop 8 := by
        simp [wBytes, RecGraph.wordBytes]
      cases hq : c.nodes.getD (c.map.getD id 0) default with
      | const c0 c1 c2 =>
        apply hconst ((UniStatement.elementWord (UniStatement.eNew c0 c1 c2)).drop 8)
          (by rw [mapW_node, wordSpec_succ_node, hq])
        rw [hb, ← hE iv (c.pubW w) S id hidg, rgX_const hck iv (c.pubW w) S hl hq]
      | input off len =>
        by_cases hr : c.hashedRead off len = true
        · have hr' := hr
          unfold hashedRead at hr'
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr'
          obtain ⟨h24, -⟩ := hr'
          subst h24
          have hsp : c.wordSpec (k + 1) (c.mapW (.node id)) f =
              ((List.range (8 * 24)).map fun i => MBit.stream (8 * off + i), []) := by
            rw [mapW_node, wordSpec_succ_node, hq]; simp only [hr, ite_true]
          apply hstream off 24 hsp (by norm_num)
          rw [hb, ← hv, valsW_step hck (live_lt hck hl) hl, hq]
          have hlast := hS (8 * off + 191) (by
            rw [hsp]; exact List.mem_map.mpr ⟨191, List.mem_range.mpr (by norm_num), rfl⟩)
          exact input_bytes S off (by omega)
        · exact hfree id rfl (by rw [mapW_node, wordSpec_succ_node, hq]; simp only [hr, Bool.false_eq_true, ite_false])
      | _ => exact hfree id rfl (by rw [mapW_node, wordSpec_succ_node, hq])

/-- **The words' message bits mean their bytes in the encoding** (`claimSpecAux` against `claimWordBytes`), the free
elements numbered from `f`. -/
theorem aux_means (hc : compile (ofRG g rootsAt iv hashed) = .ok c) (w : ℕ → K) (hE : ExpandSound g c)
    (nodeOf : ℕ → ℕ) :
    ∀ (ws0 : List RecGraph.Word) (k f : ℕ),
      (∀ i < ws0.length, wordShape (k + i) (ws0.getD i default)) →
      (∀ id, RecGraph.Word.node id ∈ ws0 → c.live.getD (c.map.getD id 0) false = true ∧ id < g.nodes.size) →
      (∀ i, MBit.stream i ∈ (c.claimSpecAux k f (ws0.map c.mapW)).1 →
        i < 8 * (c.streamW (ofRG g rootsAt iv hashed) w).length) →
      (∀ i < (c.claimSpecAux k f (ws0.map c.mapW)).2.length,
        nodeOf (f + i) = (c.claimSpecAux k f (ws0.map c.mapW)).2.getD i 0) →
      (c.claimSpecAux k f (ws0.map c.mapW)).1.length = 8 * (claimWordBytes
        (c.streamW (ofRG g rootsAt iv hashed) w).toArray
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv hashed) w)) k ws0).length ∧
      ∀ p < (c.claimSpecAux k f (ws0.map c.mapW)).1.length, MBitMeans c (ofRG g rootsAt iv hashed) w nodeOf
        (f + (c.claimSpecAux k f (ws0.map c.mapW)).2.length) ((c.claimSpecAux k f (ws0.map c.mapW)).1.getD p default)
        (bitOf (claimWordBytes (c.streamW (ofRG g rootsAt iv hashed) w).toArray
          (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv hashed) w)) k ws0) p) := by
  intro ws0
  induction ws0 with
  | nil =>
    intro k f _ _ _ _
    refine ⟨by cases k <;> rfl, fun p hp => ?_⟩
    simp [claimSpecAux] at hp
  | cons wd rest ih =>
    intro k f hshape hlive hS hnodes
    set a := c.wordSpec k (c.mapW wd) f with ha
    set b := c.claimSpecAux (k + 1) (f + a.2.length) (rest.map c.mapW) with hb
    have hspec : c.claimSpecAux k f ((wd :: rest).map c.mapW) = (a.1 ++ b.1, a.2 ++ b.2) := rfl
    rw [hspec] at hS hnodes ⊢
    rw [claimWordBytes_cons]
    obtain ⟨hal, ham⟩ := word_means hc w hE (k := k) (f := f) (wd := wd)
      (by have := hshape 0 (by simp); simpa using this)
      (fun id hid => hlive id (by rw [hid]; exact List.mem_cons_self))
      (fun i hi => hS i (List.mem_append_left _ hi)) nodeOf
      (fun i hi => by
        rw [← ha] at hi
        rw [hnodes i (by rw [List.length_append]; omega), List.getD_append _ _ _ _ hi])
    rw [← ha] at hal ham
    obtain ⟨hbl, hbm⟩ := ih (k + 1) (f + a.2.length)
      (fun i hi => by
        have := hshape (i + 1) (by simp; omega)
        simpa [show k + (i + 1) = k + 1 + i by omega] using this)
      (fun id hid => hlive id (List.mem_cons_of_mem _ hid))
      (fun i hi => hS i (List.mem_append_right _ hi))
      (fun i hi => by
        rw [← hb] at hi
        rw [add_assoc, hnodes (a.2.length + i) (by rw [List.length_append]; omega), List.getD_append_right _ _ _ _ (by omega),
          Nat.add_sub_cancel_left])
    rw [← hb] at hbl hbm
    refine ⟨by rw [List.length_append, List.length_append, hal, hbl]; ring, fun p hp => ?_⟩
    simp only [List.length_append] at hp
    by_cases h1 : p < a.1.length
    · rw [List.getD_append _ _ _ _ h1, bitOf_append_left _ _ _ (by omega)]
      exact MBitMeans.mono (by simp) (ham p h1)
    · rw [List.getD_append_right _ _ _ _ (by omega), bitOf_append_right _ _ _ (by omega), ← hal]
      have := hbm (p - a.1.length) (by omega)
      rw [List.length_append, ← add_assoc]
      exact this

/-! ## The claims' checks -/

theorem claimsOk_parts {X : Ctx} {packOf : Array (Option ℕ)} (h : c.claimsOk X r packOf = true) :
    c.circuit.hashed = hashedOf r ∧ c.claims.size = c.circuit.hashed.length ∧
      ∀ j < c.claims.size, (c.claims.getD j default).ci = c.circuit.hashed.getD j 0 ∧ c.claimOk X r packOf j = true := by
  unfold claimsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  have := allBelow_spec h3 j hj
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem claimOk_parts {X : Ctx} {packOf : Array (Option ℕ)} {j : ℕ} (h : c.claimOk X r packOf j = true) :
    let cl := c.claims.getD j default
    let ws := (r.graph.calls.getD cl.ci []).map fun w => match w with
      | .node id => Word.node (c.map.getD id 0)
      | other => other
    let sp := c.claimSpec ws
    3 ≤ ws.length ∧ claimWordsOk ws = true ∧
    (ws.all fun w => match w with
      | .node id => c.live.getD id false
      | _ => true) = true ∧
    cl.message.size = sp.1.length ∧
    (∀ p < sp.1.length, c.mbitOk X cl.frees (cl.message.getD p .zero) (sp.1.getD p (.const false)) = true) ∧
    cl.frees.size = sp.2.length ∧
    (∀ f < cl.frees.size, c.freeOk X packOf (cl.frees.getD f default) (sp.2.getD f 0) = true) ∧
    cl.digest.size = 256 ∧ c.spongeIs cl.digest cl.message = true ∧ cl.limbs4.size = 4 ∧
    (∀ l < 4, c.packIs packOf (cl.limbs4.getD l NONE) (beBits (fun i => cl.digest.getD i NONE) (8 * l) 8) = true) := by
  unfold claimOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h3, -⟩, hwk⟩, hlv⟩, hms⟩, hmb⟩, hfs⟩, hfr⟩, hds⟩, hsp⟩, hls⟩, hpk⟩ := h
  exact ⟨h3, hwk, hlv, hms, allBelow_spec hmb, hfs, allBelow_spec hfr, hds, hsp, hls, allBelow_spec hpk⟩

/-! ## The end: a `claimHash` port carries the claim's Keccak-256 -/

theorem mapW_eq (c : Compiled) (ws : List RecGraph.Word) :
    (ws.map ofRGWord).map (fun w => match w with
      | .node id => Word.node (c.map.getD id 0)
      | other => other) = ws.map c.mapW := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem claimWordsOk_shape (c : Compiled) :
    ∀ (ws : List RecGraph.Word), claimWordsOk (ws.map c.mapW) = true →
      ∀ i < ws.length, wordShape i (ws.getD i default)
  | [], _ => by intro i hi; simp at hi
  | w :: ws, h => by
    intro i hi
    simp only [List.map_cons, claimWordsOk, Bool.and_eq_true, List.all_eq_true, List.mem_map] at h
    obtain ⟨h0, hrest⟩ := h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      cases w <;> simp_all [mapW, wordShape]
    | succ i =>
      simp only [List.getD_cons_succ]
      have hi' : i < ws.length := by simpa using hi
      have hm : ws.getD i default ∈ ws := by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
      have := hrest _ ⟨_, hm, rfl⟩
      revert this
      cases ws.getD i default <;> simp [mapW, wordShape]

/-- **The claims π2's circuit hashes** are `hashed`'s below the calls' count, in order. -/
theorem compile_hashed (hc : compile (ofRG g rootsAt iv hashed) = .ok c) :
    c.circuit.hashed = hashed.filter (· < g.calls.length) := by
  rw [(claimsOk_parts (checked_of_compile hc).claims).1]
  simp [hashedOf, ofRG]

/-- **A satisfied π2 circuit carries the Keccak-256s of π1's hashed claims.** On a satisfied accepted circuit whose zero
ports carry zeros (as π2's verifier reads them), the `claimHash j` port's four limbs are the statement-order words
(limb `l` the big-endian word of bytes `8l .. 8l + 8`) of the Keccak-256 (over Keccak-f[1600]) of the EIP draft's PCS-claim
encoding (`claimEncoding`) of π1's claim `c.circuit.hashed[j]`, built from the graph's call words in `RecGraph`'s
semantics on the stream and public input the witness encodes. -/
theorem claimHash_port (hc : compile (ofRG g rootsAt iv hashed) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w))
    (hz : ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = [0, 0, 0])
    {J j : ℕ} (hJ : J < c.circuit.ports.size) (hs : (c.circuit.ports.getD J default).source = .claimHash j) :
    j < c.circuit.hashed.length ∧ c.circuit.hashed.getD j 0 < g.calls.length ∧
    c.circuit.portLimbs w J = (List.range 4).map fun l => K.ofLane (beWordAt (digestBytes (keccak256
      (claimEncoding (c.streamW (ofRG g rootsAt iv hashed) w).toArray
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv hashed) w))
        (g.calls.getD (c.circuit.hashed.getD j 0) [])))).toArray (8 * l)) := by
  have hck := checked_of_compile hc
  have hsat := satisfied_of_piop _ hw
  have G := hck.good hsat
  have hE := expandSound hc
  set r := ofRG g rootsAt iv hashed with hr
  set S := c.streamW r w
  set V := rgVals g iv (c.pubW w) S
  obtain ⟨hhash, hcsz, hclaims⟩ := claimsOk_parts hck.claims
  have hso := allBelow_spec hck.sources J hJ
  simp only [hs, decide_eq_true_eq] at hso
  obtain ⟨hci, hok⟩ := hclaims j hso
  set cl := c.claims.getD j default with hcl
  have hjh : j < c.circuit.hashed.length := by omega
  have hcig : c.circuit.hashed.getD j 0 < g.calls.length := by
    have hmem : c.circuit.hashed.getD j 0 ∈ c.circuit.hashed := by
      rw [List.getD_eq_getElem _ _ hjh]; exact List.getElem_mem hjh
    generalize c.circuit.hashed.getD j 0 = x at hmem ⊢
    rw [compile_hashed hc] at hmem
    simpa using (List.mem_filter.mp hmem).2
  refine ⟨hjh, hcig, ?_⟩
  set ci := c.circuit.hashed.getD j 0
  set ws0 := g.calls.getD ci []
  obtain ⟨h3, hwk, hlv, hms, hmb, hfs, hfr, hds, hsp, hls, hpk⟩ := claimOk_parts hok
  have hws : (r.graph.calls.getD cl.ci []).map (fun w => match w with
      | .node id => Word.node (c.map.getD id 0)
      | other => other) = ws0.map c.mapW := by
    rw [hci, calls_getD g rootsAt iv hcig, mapW_eq]
  rw [hws] at h3 hwk hlv hms hmb hfs hfr
  simp only [List.length_map] at h3
  set sp := c.claimSpec (ws0.map c.mapW) with hspd
  set nodeOf : ℕ → ℕ := fun f => sp.2.getD f 0
  -- The hashed claims' zero ports: every sum is zero.
  have hsums : ∀ s ∈ c.claimSums, ∀ l < 3, c.ctx.val w (s.getD l NONE) = 0 := by
    intro s hs' l hl
    obtain ⟨m, hm, hsm⟩ := List.getElem_of_mem hs'
    have hcount : (c.circuit.ports.toList.filter fun p => p.source == .zero).length =
        c.claimZeros + c.zeroNodes.length := by
      have h := hck.ports
      unfold portsOk at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have hmz : m < c.claimZeros := hm
    obtain ⟨J', hJ', hpJ, hcJ⟩ := exists_nth_filter (fun p : Port => p.source == .zero) c.circuit.ports.toList m
      (by rw [hcount]; omega)
    have hJ'' : J' < c.circuit.ports.size := by simpa using hJ'
    have hsrc : (c.circuit.ports.getD J' default).source = .zero := by
      rw [← arr_toList_getD]; simpa using hpJ
    have hzi : c.zeroIndex J' = m := hcJ
    have e1 := ports_carry hck hsat J' hJ''
    rw [hz J' hJ'' hsrc, portMeaning, hsrc] at e1
    simp only [hzi, hmz, ite_true] at e1
    have hgs : c.claimSums.getD m #[] = s := by rw [List.getD_eq_getElem _ _ hm, hsm]
    rw [hgs] at e1
    have := congrArg (fun L => L.getD l 0) e1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some] at this
    interval_cases l <;> simpa using this.symm
  -- The free elements' bits.
  have hfree : ∀ f < cl.frees.size, ∀ k < 192, c.ctx.val w (((cl.frees.getD f default).2.1).getD k NONE) =
      ofBool (bitOf ((UniStatement.elementWord ((c.valsW r w).getD (nodeOf f) default).toE).drop 8) k) := by
    intro f hf k hk
    have hfo := hfr f hf
    have hl := (freeOk_parts hfo).2.1
    have hclm : cl ∈ c.claims.toList := by
      rw [hcl, ← arr_toList_getD, List.getD_eq_getElem _ _ (by simpa using hso)]
      exact List.getElem_mem _
    have hfrm : cl.frees.getD f default ∈ cl.frees.toList := by
      rw [← arr_toList_getD, List.getD_eq_getElem _ _ (by simpa using hf)]
      exact List.getElem_mem _
    have hmem : (cl.frees.getD f default).2.2.2 ∈ c.claimSums := by
      unfold claimSums
      exact List.mem_flatMap.mpr ⟨cl, hclm, List.mem_map.mpr ⟨_, hfrm, rfl⟩⟩
    exact free_bit_val hck hsat hfo (live_lt hck hl) (hsums _ hmem) k hk
  -- The words' meaning.
  have hhdr : (constMBits [1, (ws0.length - 3).toUInt8]).length = 16 := by rw [constMBits_length]; rfl
  have hsp1 : sp.1 = constMBits [1, (ws0.length - 3).toUInt8] ++ (c.claimSpecAux 0 0 (ws0.map c.mapW)).1 := by
    simp [hspd, claimSpec]
  have hsp2 : sp.2 = (c.claimSpecAux 0 0 (ws0.map c.mapW)).2 := by simp [hspd, claimSpec]
  obtain ⟨hal, ham⟩ := aux_means hc w hE nodeOf ws0 0 0
    (by intro i hi; simpa using claimWordsOk_shape c ws0 hwk i hi)
    (by
      intro id hid
      have hm : c.mapW (.node id) ∈ ws0.map c.mapW := List.mem_map_of_mem hid
      have hl := List.all_eq_true.mp hlv _ hm
      simp only [mapW] at hl
      obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hid
      exact ⟨hl, call_node_lt hc hcig hk (by rw [List.getD_eq_getElem _ _ hk]; exact hkw)⟩)
    (by
      intro i hi
      obtain ⟨q, hq, hqi⟩ := List.getElem_of_mem hi
      have hp : 16 + q < sp.1.length := by rw [hsp1, List.length_append, hhdr]; omega
      have hget : sp.1.getD (16 + q) (.const false) = .stream i := by
        rw [hsp1, List.getD_append_right _ _ _ _ (by rw [hhdr]; omega), hhdr, Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ hq, hqi]
      have hm := hmb (16 + q) hp
      rw [hget] at hm
      cases hmsg : cl.message.getD (16 + q) .zero with
      | v x =>
        rw [hmsg] at hm
        simp only [mbitOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hm
        have h0 := hm.1 0 (by norm_num)
        have hsz := hck.sizes.2.2.2.1
        have hlt : 8 * (i / 8) < c.bitSelf.size := by
          by_contra hcon
          rw [Nat.add_zero, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hcon)] at h0
          simp at h0
        show i < 8 * (c.streamW r w).length
        rw [streamW_length]; omega
      | zero => rw [hmsg] at hm; simp [mbitOk] at hm
      | one => rw [hmsg] at hm; simp [mbitOk] at hm)
    (by intro i hi; simp [nodeOf, hsp2])
  rw [← hsp2] at ham
  set enc := claimEncoding S.toArray V ws0 with henc
  have hencl : enc.length = 2 + (claimWordBytes S.toArray V 0 ws0).length := by simp [henc, claimEncoding]; omega
  have hsize : cl.message.size = 8 * enc.length := by
    rw [hms, hsp1, List.length_append, hhdr, hal, hencl]; ring
  have hm : Ctx.MsgOk c.ctx w cl.message (bitOf enc) := by
    intro p hp
    have hp' : p < sp.1.length := by rw [← hms]; exact hp
    apply mbit_val hck hsat (nf := cl.frees.size) (nodeOf := nodeOf) hfree (hmb p hp')
    by_cases h16 : p < 16
    · rw [hsp1, List.getD_append _ _ _ _ (by rw [hhdr]; exact h16), constMBits_getD _ _ (by simpa using h16) (.const false)]
      show bitOf [1, (ws0.length - 3).toUInt8] p = bitOf enc p
      rw [henc, claimEncoding, bitOf_append_left _ _ _ (by simp; omega)]
    · have hq : p - 16 < (c.claimSpecAux 0 0 (ws0.map c.mapW)).1.length := by
        rw [hsp1, List.length_append, hhdr] at hp'; omega
      rw [hsp1, List.getD_append_right _ _ _ _ (by rw [hhdr]; omega), hhdr, List.getD_eq_getElem _ _ hq]
      have := ham (p - 16) (by rw [hsp1, List.length_append, hhdr] at hp'; omega)
      rw [List.getD_eq_getElem _ _ hq, Nat.zero_add, ← hfs] at this
      rw [henc, claimEncoding, bitOf_append_right _ _ _ (by simp; omega)]
      simp only [List.length_cons, List.length_nil, show 8 * (0 + 1 + 1) = 16 from rfl]
      exact this
  have hdig := digest_of_message hck G hsp hsize hm
  set D := digestBytes (keccak256 enc)
  have hD : D.length = 32 := PcsCircuit.digestBytes_length _
  rw [ports_carry hck hsat J hJ, portMeaning, hs]
  apply List.map_congr_left
  intro l hl
  rw [List.mem_range] at hl
  have hw8 := packBE_word hck G (fun i => cl.digest.getD i NONE) D (8 * l) 8 (by omega)
    (fun i hi j hj => by
      rw [hdig _ (by omega)]
      simp only [bitOf]
      rw [show (8 * (8 * l + i) + j) / 8 = 8 * l + i by omega, show (8 * (8 * l + i) + j) % 8 = j by omega])
    (hpk l hl)
  rw [← hcl, hw8, beWordAt_eq _ _ (by simp; omega)]
  all_goals simp

end Compiled

end RecCircuit
