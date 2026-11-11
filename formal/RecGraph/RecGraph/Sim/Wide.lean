-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Sim.Chan

/-!
# The wide draw, simulated (π1-rec4)

`Pi1.sampleWide n` (the recorder's `sample_wide`: the hash `h` and its `low h`, then `wide h k` for `k = 1 … n − 1`)
against `UniStatement.sampleWide (Fp π) n` (one Keccak-256 of the state and the bytes since the last challenge, the
digest the new state, challenge `k` the rate's `challengeAt k`):

* `wideFrom_struct`: `wideFrom k m` appends the nodes `wide h k, …, wide h (k + m − 1)` (new: no node `wide h k'` with
  `k' ≥ k` is held, `WideBelow`), each worth `challengeAt (valRate h) k'`;
* **`sim_sampleWide`**: no byte read, `n` challenges drawn, the nodes `h + 1, …, h + n` worth them (`h` the state's
  node count before the draw), `chIds` grown by them.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- **No wide challenge of the hash `h` from `k` on is held.** -/
def WideBelow (st : RecState) (h k : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < st.nodes.size) (k' : Nat), st.nodes[i] = .wide h k' → k' < k

theorem isChal_wide (h k : Nat) : isChal (.wide h k) = true := rfl

/-- **One wide challenge**: a new node, the state's other fields unchanged. -/
theorem wide_struct (st : RecState) (hg : Good st) (k : Nat) (hw : WideBelow st st.state k) :
    (st.wide k).1 = st.nodes.size ∧ (st.wide k).2.nodes = st.nodes.push (.wide st.state k) ∧
      (st.wide k).2.state = st.state ∧ (st.wide k).2.cursor = st.cursor ∧
      (st.wide k).2.absorbed = st.absorbed ∧ (st.wide k).2.zero = st.zero ∧
      (st.wide k).2.kernels = st.kernels := by
  have hnone : st.index[(Node.wide st.state k)]? = none := by
    cases h : st.index[(Node.wide st.state k)]? with
    | none => rfl
    | some j =>
      exfalso
      have hj := hg.inv.index _ _ h
      have hjlt : j < st.nodes.size := by
        rcases Nat.lt_or_ge j st.nodes.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hj
      have hjn : st.nodes[j] = .wide st.state k := by
        rw [Array.getElem?_eq_getElem hjlt] at hj; exact Option.some.inj hj
      have := hw j hjlt k hjn
      omega
  unfold RecState.wide RecState.new
  rw [hnone]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wide_good (st : RecState) (hg : Good st) (k : Nat) (hw : WideBelow st st.state k) : Good (st.wide k).2 := by
  obtain ⟨_, e2, e3, _⟩ := wide_struct st hg k hw
  refine ⟨wide_inv st hg.inv k, ?_⟩
  intro i hi s f u he
  rw [e3]
  have hsz : (st.wide k).2.nodes.size = st.nodes.size + 1 := by rw [e2]; simp
  rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
  · have : (st.wide k).2.nodes[i] = st.nodes[i] := by simp [e2, Array.getElem_push, hlt]
    rw [this] at he
    exact hg.fresh i hlt s f u he
  · have hieq : i = st.nodes.size := by omega
    subst hieq
    have : (st.wide k).2.nodes[st.nodes.size] = .wide st.state k := by simp [e2]
    rw [this] at he
    cases he

theorem wide_wideBelow (st : RecState) (hg : Good st) (k : Nat) (hw : WideBelow st st.state k) :
    WideBelow (st.wide k).2 st.state (k + 1) := by
  obtain ⟨_, e2, _⟩ := wide_struct st hg k hw
  intro i hi k' he
  have hsz : (st.wide k).2.nodes.size = st.nodes.size + 1 := by rw [e2]; simp
  rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
  · have : (st.wide k).2.nodes[i] = st.nodes[i] := by simp [e2, Array.getElem_push, hlt]
    rw [this] at he
    have := hw i hlt k' he
    omega
  · have hieq : i = st.nodes.size := by omega
    subst hieq
    have : (st.wide k).2.nodes[st.nodes.size] = .wide st.state k := by simp [e2]
    rw [this] at he
    cases he
    omega

section Values

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **`wideFrom k m`, recorded**: the nodes `st.nodes.size + j` (`j < m`), the wide challenges `k + j` of the state's
hash, appended; the state's other fields unchanged; each worth `challengeAt` of the hash's rate. -/
theorem wideFrom_struct : ∀ (m k : Nat) (st : RecState), Good st → WideBelow st st.state k →
    let r := (Pi1.wideFrom k m).record st
    r.1 = List.range' st.nodes.size m ∧
      r.2.nodes.toList = st.nodes.toList ++ (List.range' k m).map (Node.wide st.state) ∧
      r.2.state = st.state ∧ r.2.cursor = st.cursor ∧ r.2.absorbed = st.absorbed ∧ r.2.zero = st.zero ∧
      r.2.kernels = st.kernels ∧ Good r.2 ∧ Grows st r.2 ∧
      chIds r.2 = chIds st ++ List.range' st.nodes.size m ∧
      ∀ j < m, val π iv publicInput stream r.2 (st.nodes.size + j) =
        challengeAt (valRate (evalAll π iv publicInput stream st) st.state) (k + j)
  | 0, k, st, hg, _ => by
    intro r
    have h0 : r = ([], st) := by simp only [r, Pi1.wideFrom, record_pure]
    rw [h0]
    refine ⟨rfl, by simp, rfl, rfl, rfl, rfl, rfl, hg, Grows.refl st, by simp, fun j hj ↦ absurd hj (by omega)⟩
  | m + 1, k, st, hg, hw => by
    intro r
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := wide_struct st hg k hw
    have hg1 := wide_good st hg k hw
    have hw1 := wide_wideBelow st hg k hw
    rw [← e3] at hw1
    have ih := wideFrom_struct m (k + 1) (st.wide k).2 hg1 hw1
    have hr : r = ((st.wide k).1 :: ((Pi1.wideFrom (k + 1) m).record (st.wide k).2).1,
        ((Pi1.wideFrom (k + 1) m).record (st.wide k).2).2) := by
      simp only [r, Pi1.wideFrom, record_bind, record_pure, record_op]
      rfl
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, fg, fgr, fch, fval⟩ := ih
    have hsz1 : (st.wide k).2.nodes.size = st.nodes.size + 1 := by rw [e2]; simp
    have hgr1 : Grows st (st.wide k).2 := (op_grows_kinv st (.wide k) hg.inv.kinv).1
    have hk1 := hg1.inv.kinv
    have hstl : st.state < st.nodes.size := hg.inv.state
    rw [hr]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fg, hgr1.trans fgr, ?_, ?_⟩
    · rw [f1, e1, hsz1, List.range'_succ]
    · rw [f2, e2, e3, Array.toList_push, List.range'_succ]; simp
    · rw [f3, e3]
    · rw [f4, e4]
    · rw [f5, e5]
    · rw [f6, e6]
    · rw [f7, e7]
    · rw [fch, chIds_push st (.wide st.state k) _ rfl _ e2, isChal_wide, hsz1, List.range'_succ]
      simp
    · intro j hj
      -- The rate of the hash is the same in the grown state.
      have hrate : valRate (evalAll π iv publicInput stream (st.wide k).2) (st.wide k).2.state =
          valRate (evalAll π iv publicInput stream st) st.state := by
        rw [e3]
        exact valRate_congr (evalAll_grows π iv publicInput stream st _ hg.inv.kinv hgr1 _ hstl)
      rcases j with _ | j
      · have hlt : st.nodes.size < (st.wide k).2.nodes.size := by omega
        have h0 := val_grow π iv publicInput stream hk1 fgr (i := st.nodes.size) hlt
        simp only [Nat.add_zero]
        rw [h0, ← e1]
        unfold val
        rw [wide_val π iv publicInput stream st hg.inv k]
      · have := fval j (by omega)
        rw [hsz1, hrate] at this
        rw [show st.nodes.size + (j + 1) = st.nodes.size + 1 + j by omega, this,
          show k + 1 + j = k + (j + 1) by omega]

end Values

/-- The channel's sponge at a challenge: Keccak-256's last state over `π` of the state and the bytes read since. -/
def spongeOf (π : KeccakState → KeccakState) (c : Chan) : KeccakState :=
  Id.run (keccak256StateWith (Fp π) (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList))

/-- The wide draw's challenges at `c`. -/
def wideChalsOf (π : KeccakState → KeccakState) (n : Nat) (c : Chan) : List E :=
  (List.range n).map (challengeAt (rateBytesOf (spongeOf π c)))

/-- **`sampleWide`'s run**: the challenges, the digest the state, the bytes absorbed, the challenges appended. -/
theorem sampleWide_run (π : KeccakState → KeccakState) (n : Nat) (c : Chan) :
    ((UniStatement.sampleWide (Fp π) n).run).run c =
      (.ok (wideChalsOf π n c),
        { c with
          absorbed := c.cursor
          state := digestOfState (spongeOf π c)
          challenges := c.challenges ++ (wideChalsOf π n c).toArray }) := rfl

/-- `hashOf` is the sponge's digest. -/
theorem hashOf_eq (π : KeccakState → KeccakState) (c : Chan) : hashOf π c = digestOfState (spongeOf π c) := rfl

section Sim

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- After a sample's hash and challenge, no wide challenge of the hash is held. -/
theorem sample_wideBelow (st : RecState) (hg : Good st) :
    WideBelow (st.sample false).2 (st.sample false).2.state 1 := by
  obtain ⟨_, e2, hAn, e3, _⟩ := sample_struct st hg false
  intro i hi k' he
  rw [e3] at he
  have hsz : (st.sample false).2.nodes.size = st.nodes.size + 2 := by rw [e2, hAn]; simp
  have hinv := sample_inv st hg.inv false
  have hb := hinv.before i hi st.nodes.size (by rw [he]; simp [reads, Node.operands])
  -- `i` is past the hash: it is the challenge `low h`.
  have hieq : i = st.nodes.size + 1 := by omega
  subst hieq
  have : (st.sample false).2.nodes[st.nodes.size + 1] = .low st.nodes.size := by
    simp [e2, hAn, Array.getElem_push]
  rw [this] at he
  cases he

/-- **`Channel::sample_wide(n)`** (`1 ≤ n`): no byte read, `n` challenges; the nodes `h + 1, …, h + n` (`h` the node
count before), worth the challenges, `chIds` grown by them. -/
theorem sim_sampleWide (st : RecState) (n : Nat) (hn : 1 ≤ n) :
    Sim π iv publicInput stream st (Pi1.sampleWide n) (UniStatement.sampleWide (Fp π) n) 0 n
      (fun st' is xs ↦ RpL π iv publicInput stream st' is xs ∧ xs.length = n ∧
        chIds st' = chIds st ++ is ∧ is = List.range' (st.nodes.size + 1) n) := by
  intro c hc hle
  refine ⟨fun _ ↦ ?_, fun hr ↦ absurd hr (by omega)⟩
  have hg := hc.good
  obtain ⟨e1, e2, hAn, e3, e4, e5, e6, e7⟩ := sample_struct st hg false
  have hinv1 := sample_inv st hg.inv false
  have hgr1 : Grows st (st.sample false).2 := (op_grows_kinv st (.sample false) hg.inv.kinv).1
  have hgrA : Grows (afterHash st) (st.sample false).2 := by rw [sample_eq]; exact new_grows _ _
  have hx0 : val π iv publicInput stream (st.sample false).2 (st.sample false).1 =
      challengeAt (rateBytesOf (spongeOf π c)) 0 := by
    have := op_val π iv publicInput stream st hg.inv (.sample false) trivial
    have key : valE (evalAll π iv publicInput stream (st.op (.sample false)).2) (st.op (.sample false)).1 =
        challengeAt (rateBytesOf (spongeOf π c)) 0 := by
      rw [this, challengeAt_zero, ← hashOf_eq]
      unfold hashOf
      rw [hc.state, hc.data, hc.absorbed, hc.cursor]
      rfl
    exact key
  have hrec : (Pi1.sampleWide n).record st =
      ((st.sample false).1 :: ((Pi1.wideFrom 1 (n - 1)).record (st.sample false).2).1,
        ((Pi1.wideFrom 1 (n - 1)).record (st.sample false).2).2) := by
    simp only [Pi1.sampleWide, Pi1.sample, record_bind, record_pure, record_op]
    rfl
  have hw1 := sample_wideBelow st hg
  rw [hrec]
  generalize (st.sample false).2 = s1 at e2 e3 e4 e5 e6 e7 hinv1 hgr1 hgrA hx0 hw1 ⊢
  have hg1 : Good s1 := ⟨hinv1, ?fresh⟩
  case fresh =>
    intro i hi s f u he
    rw [e3]
    have hsz : s1.nodes.size = st.nodes.size + 2 := by rw [e2, hAn]; simp
    rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
    · have : s1.nodes[i] = st.nodes[i] := by simp [e2, hAn, Array.getElem_push, hlt, Nat.lt_succ_of_lt hlt]
      rw [this] at he
      have := hg.fresh i hlt s f u he
      have := hg.inv.state
      omega
    · rcases Nat.lt_or_ge i (st.nodes.size + 1) with hlt | hge'
      · omega
      · have hieq : i = st.nodes.size + 1 := by omega
        subst hieq
        have : s1.nodes[st.nodes.size + 1] = .low st.nodes.size := by simp [e2, hAn, Array.getElem_push]
        rw [this] at he
        cases he
  have W := wideFrom_struct π iv publicInput stream (n - 1) 1 s1 hg1 hw1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, fg, fgr, fch, fval⟩ := W
  generalize hs2 : ((Pi1.wideFrom 1 (n - 1)).record s1).2 = s2 at f2 f3 f4 f5 f6 f7 fg fgr fch fval ⊢
  have hgr : Grows st s2 := hgr1.trans fgr
  have hsz1 : s1.nodes.size = st.nodes.size + 2 := by rw [e2, hAn]; simp
  -- The sponge of the hash node.
  have hkA : KInv (afterHash st) := (afterHash_inv st hg.inv).kinv
  have hAs : (afterHash st).state = st.nodes.size := by rw [afterHash_eq st hg]
  have hltA : st.nodes.size < (afterHash st).nodes.size := by rw [hAn]; simp
  have hA1 := evalAll_grows π iv publicInput stream _ _ hkA hgrA st.nodes.size hltA
  have hrate1 : valRate (evalAll π iv publicInput stream s1) s1.state = rateBytesOf (spongeOf π c) := by
    rw [e3, valRate_congr hA1, ← hAs, afterHash_rate π iv publicInput stream st hg.inv]
    unfold spongeOf
    rw [hc.state, hc.data, hc.absorbed, hc.cursor]
    rfl
  have hstate1 : valState (evalAll π iv publicInput stream s1) s1.state = digestOfState (spongeOf π c) := by
    rw [e3, valState_congr hA1, ← hAs, afterHash_val π iv publicInput stream st hg.inv, ← hashOf_eq]
    unfold hashOf
    rw [hc.state, hc.data, hc.absorbed, hc.cursor]
    rfl
  have hk1 := hg1.inv.kinv
  have hx0' : val π iv publicInput stream s2 (st.sample false).1 = challengeAt (rateBytesOf (spongeOf π c)) 0 := by
    rw [val_grow π iv publicInput stream hk1 fgr (by rw [e1, hsz1]; omega), hx0]
  have hxs : wideChalsOf π n c = challengeAt (rateBytesOf (spongeOf π c)) 0 ::
      (List.range' 1 (n - 1)).map (challengeAt (rateBytesOf (spongeOf π c))) := by
    unfold wideChalsOf
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, Nat.add_sub_cancel, List.range'_eq_map_range, List.map_map,
      List.map_map]
    refine congrArg (List.cons _) (List.map_congr_left fun j _ ↦ ?_)
    simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_comm j 1]
  -- The outputs, related.
  have hR : RpL π iv publicInput stream s2 ((st.sample false).1 :: ((Pi1.wideFrom 1 (n - 1)).record s1).1)
      (wideChalsOf π n c) := by
    rw [hxs, f1]
    refine List.Forall₂.cons ⟨?_, hx0'⟩ ?_
    · have : s1.nodes.size ≤ s2.nodes.size := Grows.size_le fgr
      rw [e1]; omega
    · refine List.forall₂_iff_get.mpr ⟨by simp, fun j h1 h2 ↦ ?_⟩
      simp only [List.length_range'] at h1
      simp only [List.get_eq_getElem, List.getElem_range', List.getElem_map, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · have hl : s2.nodes.toList.length = s1.nodes.toList.length + (n - 1) := by rw [f2]; simp
        simp only [Array.length_toList] at hl
        omega
      · rw [fval j h1, hrate1, Nat.add_comm 1 j]
  refine ⟨wideChalsOf π n c, _, sampleWide_run π n c, ?_, (Nat.add_zero _).symm, ?_, hgr, hR, ?_, ?_, ?_⟩
  · refine ⟨fg, hc.data, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show c.cursor = s2.cursor
      rw [f4, e5, hc.cursor]
    · show c.cursor = s2.absorbed
      rw [f5, e4, hc.cursor]
    · show digestOfState (spongeOf π c) = stateVal π iv publicInput stream s2
      unfold stateVal
      rw [f3, ← hstate1]
      exact (valState_congr (evalAll_grows π iv publicInput stream _ _ hk1 fgr _ hg1.inv.state)).symm
    · intro z hz
      rw [f6, e6] at hz
      exact lt_of_lt_of_le (hc.zeroLt z hz) (Grows.size_le hgr)
    · show c.zeros.toList = _
      rw [hc.zeros, f6, e6]
      exact List.map_congr_left fun z hz ↦ (val_grow π iv publicInput stream hg.inv.kinv hgr (hc.zeroLt z hz)).symm
    · show (c.challenges ++ (wideChalsOf π n c).toArray).toList = _
      have hchs : chIds s2 = chIds st ++ ((st.sample false).1 :: ((Pi1.wideFrom 1 (n - 1)).record s1).1) := by
        have c1 := chIds_push st (.hash st.state st.absorbed st.cursor) _ rfl (afterHash st) hAn
        have c2 := chIds_push (afterHash st) (.low st.nodes.size) _ rfl s1 e2
        rw [fch, c2, c1, f1, e1, hsz1]
        simp [isChal, hAn]
      rw [Array.toList_append, hc.chal, hchs, List.map_append, List.toList_toArray]
      congr 1
      · exact List.map_congr_left fun i hi ↦ (val_grow π iv publicInput stream hg.inv.kinv hgr (chIds_lt hi)).symm
      · have hmap : ∀ {is : List Nat} {xs : List E}, RpL π iv publicInput stream s2 is xs →
            is.map (val π iv publicInput stream s2) = xs := by
          intro is xs h
          induction h with
          | nil => rfl
          | cons h _ ih => simp [h.2, ih]
        exact (hmap hR).symm
  · simp [Array.size_append, wideChalsOf]
  · simp [wideChalsOf]
  · have c1 := chIds_push st (.hash st.state st.absorbed st.cursor) _ rfl (afterHash st) hAn
    have c2 := chIds_push (afterHash st) (.low st.nodes.size) _ rfl s1 e2
    rw [fch, c2, c1, f1, e1, hsz1]
    simp [isChal, hAn]
  · rw [f1, e1, hsz1]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [List.range'_succ]
    simp

end Sim

end RecGraph.Sim
