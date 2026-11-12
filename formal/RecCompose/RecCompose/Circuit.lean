-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Part1
import RecCircuit.End

/-!
# `Pi2Layers.circuit` from RecCircuit's end theorem

RecCircuit's `compile_sound_end` (no hypothesis but the compiler's run `hc`), at π1-rec4's graph at π1's setup
commitment (`pi1GraphAt roots`), π1's claims `Data.hashed` hashed in the circuit: on π2's circuit, every witness
satisfying π2's PIOP has ports and rebuilt claims equal to the graph's outputs over Keccak-f[1600] (`EndStatement`: the
statement's words, the zero checks' values, the constant ones `0`, the encoded claims word for word, and, given the
zero ports zero, the `ClaimHash` ports the Keccak-256s of the EIP encodings of the hashed claims). What is left to the
field `Pi2Layers.circuit` is the bridge from that statement, read at π2's public limbs, to RecStatement's
`Pi1GraphAccepts` (`CircuitBridge`).

* `claimHash_words32` (proved): RecStatement's `claimHash` of a graph claim's output bytes, cut into 32-byte words, is
  the digest of RecCircuit's `claimEncoding` of its words, the Keccak-256 a `ClaimHash` port carries: so the ports'
  public limbs (the frame words `frameOf declared j`) name the graph's claims by their hashes.
* `CircuitBridge`: at π2's public limbs `pub`, `EndStatement` gives `Pi1GraphAccepts` (`Bridge.lean`: the statement port
  makes the witness's public input the calldata's; the zero ports' public limbs are zero, so every zero check of the
  graph is; the `ClaimHash` ports' public limbs are the frame words, so `claimHash_words32` gives the claims'
  Keccak-256s the declared ones').
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

/-! ## A claim's hash, from its output bytes -/

theorem length_wordBytes_32 (S : Array UInt8) (V : Array RecGraph.Value) (wd : RecGraph.Word)
    (hS : ∀ a, wd = .stream a → a + 32 ≤ S.size) : (RecGraph.wordBytes S V wd).length = 32 := by
  cases wd with
  | node id => simp [RecGraph.wordBytes, UniStatement.elementWord, UniStatement.be64]
  | const x => simp [RecGraph.wordBytes, RecGraph.beBytes32]
  | stream a => have := hS a rfl; simp [RecGraph.wordBytes]; omega

/-- A concatenation of 32-byte words, cut into 32-byte words. -/
theorem words32_flatten : ∀ (W : List (List UInt8)), (∀ w ∈ W, w.length = 32) → words32 W.flatten = W
  | [], _ => rfl
  | w :: W, h => by
    have hw := h w (List.mem_cons_self ..)
    have ih := words32_flatten W fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    unfold words32 at ih ⊢
    have hl : (w :: W).flatten.length / 32 = W.flatten.length / 32 + 1 := by
      simp only [List.flatten_cons, List.length_append, hw]; omega
    rw [hl, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.mul_zero, List.drop_zero, List.flatten_cons]
    rw [List.take_left' hw]
    congr 1
    conv_rhs => rw [← ih]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Nat.mul_succ, show 32 * j + 32 = w.length + 32 * j by omega, ← List.drop_drop,
      List.drop_left' rfl]

/-- **A graph claim's hash** (RecStatement's `claimHash` of its output bytes cut into words) **is the digest of its
EIP encoding** (`RecCircuit.claimEncoding`), the Keccak-256 a `ClaimHash` port carries. -/
theorem claimHash_words32 (S : Array UInt8) (V : Array RecGraph.Value) (ws : List RecGraph.Word)
    (hS : ∀ a, RecGraph.Word.stream a ∈ ws → a + 32 ≤ S.size) :
    claimHash (words32 (ws.flatMap (RecGraph.wordBytes S V))) =
      digestBytes (keccak256 (RecCircuit.claimEncoding S V ws)) := by
  rw [show ws.flatMap (RecGraph.wordBytes S V) = (ws.map (RecGraph.wordBytes S V)).flatten from
    rfl, words32_flatten _ (by
    intro x hx
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.mp hx
    exact length_wordBytes_32 S V wd fun a ha ↦ hS a (ha ▸ hwd))]
  rw [RecCircuit.claimEncoding_eq]
  unfold claimHash pcsClaimBytes
  cases ws with
  | nil => rfl
  | cons w ws => simp [List.flatMap_map]; rfl

/-! ## π1's graph accepts, from the ports -/

theorem beNat_inj' : ∀ (a b : List UInt8), a.length = b.length → RecCircuit.beNat a = RecCircuit.beNat b → a = b := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
    intro b hl _
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | append_singleton a x ih =>
    intro b hl he
    cases b using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton b y =>
      rw [RecCircuit.beNat_append, RecCircuit.beNat_append] at he
      have h1 : (RecCircuit.beNat a * 256 + x.toNat) % 256 = (RecCircuit.beNat b * 256 + y.toNat) % 256 := by
        rw [he]
      rw [Nat.mul_add_mod_of_lt x.toNat_lt, Nat.mul_add_mod_of_lt y.toNat_lt] at h1
      have hxy : x = y := UInt8.toNat.inj h1
      subst hxy
      have h2 : RecCircuit.beNat a = RecCircuit.beNat b :=
        Nat.eq_of_mul_eq_mul_right (by decide : 0 < 256) (Nat.add_right_cancel he)
      rw [ih b (by simpa using hl) h2]

/-- **Four big-endian words give their 32 bytes back.** -/
theorem bytes_eq_of_words' (a b : List UInt8) (ha : a.length = 32) (hb : b.length = 32)
    (h : ∀ k < 4, K.ofLane (UniStatement.beWordAt a.toArray (8 * k)) =
      K.ofLane (UniStatement.beWordAt b.toArray (8 * k))) : a = b := by
  have hs : ∀ k < 4, RecCircuit.slice a (8 * k) 8 = RecCircuit.slice b (8 * k) 8 := by
    intro k hk
    have e := h k hk
    rw [RecCircuit.beWordAt_eq _ _ (by rw [List.size_toArray, ha]; omega),
      RecCircuit.beWordAt_eq _ _ (by rw [List.size_toArray, hb]; omega)] at e
    have e2 := congrArg K.lane e
    rw [← RecCircuit.ofLane_ofNat, ← RecCircuit.ofLane_ofNat, RecCircuit.lane_ofLane, RecCircuit.lane_ofLane] at e2
    have la : (RecCircuit.slice a (8 * k) 8).length = 8 := RecCircuit.slice_length _ _ _ (by rw [ha]; omega)
    have lb : (RecCircuit.slice b (8 * k) 8).length = 8 := RecCircuit.slice_length _ _ _ (by rw [hb]; omega)
    have hla := RecCircuit.beNat_lt (RecCircuit.slice a (8 * k) 8)
    have hlb := RecCircuit.beNat_lt (RecCircuit.slice b (8 * k) 8)
    rw [la] at hla
    rw [lb] at hlb
    have e3 := congrArg UInt64.toNat e2
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb] at e3
    exact beNat_inj' _ _ (by rw [la, lb]) e3
  apply List.ext_getElem (by rw [ha, hb])
  intro i hi1 hi2
  have hk : i / 8 < 4 := by rw [ha] at hi1; omega
  have e := congrArg (fun l ↦ l.getD (i % 8) 0) (hs (i / 8) hk)
  rw [RecCircuit.slice_getD _ _ _ _ (Nat.mod_lt _ (by norm_num)),
    RecCircuit.slice_getD _ _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod] at e
  rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at e

theorem claimHash_length (words : List (List UInt8)) : (claimHash words).length = 32 :=
  PcsCircuit.digestBytes_length _

theorem limbsL_eq_zero {x : E} (h : RecCircuit.Compiled.limbsL x = [0, 0, 0]) : x = 0 := by
  have h0 : RecCircuit.Compiled.limbsL (0 : E) = [0, 0, 0] := by simp [RecCircuit.Compiled.limbsL]
  rw [← RecCircuit.limbsE_limbsL x, h, ← h0, RecCircuit.limbsE_limbsL]

theorem exists_nth_filter' {α : Type} [Inhabited α] (p : α → Bool) :
    ∀ (l : List α) (m : ℕ), m < (l.filter p).length →
      ∃ J < l.length, p (l.getD J default) = true ∧ ((l.take J).filter p).length = m :=
  RecCircuit.exists_nth_filter p

/-- **π1's graph accepts, read off the ports**: on a satisfied accepted circuit in which every claim of `g` is hashed,
whose statement port carries the public input's words, whose zero ports carry zeros and whose `claimHash j` port carries
the words of `claimHash (declared[j])`, `g` (with no nonzero check, its claims' roots in the stream) accepts the
witness's stream, its claims' Keccak-256s the declared ones' (`Pi1GraphAccepts`). -/
theorem pi1GraphAccepts_of_ports {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8} {hashed : List ℕ}
    {c : RecCircuit.Compiled} (hc : RecCircuit.compile (RecCircuit.ofRG g rootsAt iv hashed) = .ok c)
    {pub : ℕ → List Primitives.F192} {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (RecCircuit.emb w))
    {input : Vector UInt8 32} {declared : List (List (List UInt8))}
    (hstmt : ∃ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .statement ∧
      c.circuit.portLimbs w J = (List.range 4).map fun k ↦ K.ofLane (UniStatement.beWordAt input.toList.toArray (8 * k)))
    (hzero : ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = [0, 0, 0])
    (hnz : g.nonzero = []) (hall : c.circuit.hashed = List.range g.calls.length)
    (hdecl : declared.length = g.calls.length)
    (hroots : ∀ j < g.calls.length, ∀ a, RecGraph.Word.stream a ∈ g.calls.getD j [] → a + 32 ≤ g.streamLen)
    (hclaim : ∀ j < g.calls.length, ∃ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .claimHash j ∧
      c.circuit.portLimbs w J = (List.range 4).map fun l ↦
        K.ofLane (UniStatement.beWordAt (claimHash (declared.getD j [])).toArray (8 * l))) :
    Pi1GraphAccepts g iv input (c.streamW (RecCircuit.ofRG g rootsAt iv hashed) w).toArray declared := by
  have hck := RecCircuit.Compiled.checked_of_compile hc
  have hE := RecCircuit.Compiled.compile_sound_end hc hw
  set r := RecCircuit.ofRG g rootsAt iv hashed with hr
  -- The witness's public input is the input.
  have hpub : c.pubW w = input.toList := by
    obtain ⟨J, hJ, hsrc, hpJ⟩ := hstmt
    have h1 := hE.1 J hJ hsrc
    rw [h1] at hpJ
    refine bytes_eq_of_words' _ _ (RecCircuit.Compiled.decodePublic_length _) (by simp) fun k hk ↦ ?_
    have := congrArg (fun l ↦ l.getD k 0) hpJ
    simpa [List.getD_eq_getElem?_getD, hk] using this
  set S := (c.streamW r w).toArray with hS
  have hsize : S.size = g.streamLen := by
    rw [hS, List.size_toArray, RecCircuit.Compiled.streamW_length]; rfl
  set V := RecCircuit.rgVals g iv (c.pubW w) (c.streamW r w) with hV
  have hVe : (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) g iv input.toList S :
      Array RecGraph.Value) = V := by rw [hV, ← hpub]; rfl
  refine ⟨RecGraph.outputsOf g S V, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RecGraph.evalGraphDeployed RecGraph.evalGraph
    simp only [hsize, ite_true]
    show some (RecGraph.outputsOf g S _) = _
    rw [hVe]
  · -- the zero checks
    intro z hz
    simp only [RecGraph.outputsOf, List.mem_map] at hz
    obtain ⟨id, hid, rfl⟩ := hz
    rcases Bool.eq_false_or_eq_true (RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default))
      with hn | hn
    · have hcount : (c.circuit.ports.toList.filter fun p ↦ p.source == .zero).length =
          c.claimZeros + c.zeroNodes.length := by
        have h := hck.ports
        unfold RecCircuit.Compiled.portsOk at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact h.1
      have hzn : c.zeroNodes.length = (g.zero.filter fun id ↦
          RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)).length := by
        have hz := (RecCircuit.Compiled.graphOk_parts hck.graph).2.1
        unfold RecCircuit.Compiled.zeroNodes
        rw [hz, List.filter_map, List.length_map]
        rfl
      have hmem : id ∈ g.zero.filter fun id ↦
          RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default) := List.mem_filter.mpr ⟨hid, hn⟩
      obtain ⟨m, hm, hmid⟩ := List.getElem_of_mem hmem
      obtain ⟨J, hJ, hpJ, hcJ⟩ := exists_nth_filter' (fun p : RecCircuit.Port ↦ p.source == .zero)
        c.circuit.ports.toList (c.claimZeros + m) (by rw [hcount, hzn]; omega)
      have hJ' : J < c.circuit.ports.size := by simpa using hJ
      have hsrc : (c.circuit.ports.getD J default).source = .zero := by
        rw [← RecCircuit.arr_toList_getD]; simpa using hpJ
      have hzi : c.zeroIndex J = c.claimZeros + m := hcJ
      have e1 := hE.2.2.1 J hJ' hsrc (by omega)
      rw [hzero J hJ' hsrc] at e1
      have e4 : RecCircuit.zeroOrig c r (c.zeroIndex J - c.claimZeros) = id := by
        rw [hzi, Nat.add_sub_cancel_left]
        change (g.zero.filter fun id ↦ RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)).getD m 0 = id
        rw [List.getD_eq_getElem _ _ hm]
        exact hmid
      rw [e4] at e1
      exact (limbsL_eq_zero e1.symm)
    · exact hE.2.2.2.1 id hid hn
  · -- no nonzero check
    intro z hz
    simp only [RecGraph.outputsOf, hnz, List.map_nil, List.not_mem_nil] at hz
  · simp [RecGraph.outputsOf, hdecl]
  · -- the claims' hashes
    intro j hj
    rw [hdecl] at hj
    obtain ⟨J, hJ, hsrc, hpJ⟩ := hclaim j hj
    obtain ⟨-, -, hp⟩ := hE.2.2.2.2.2.2 hzero J hJ j hsrc
    have hj' : c.circuit.hashed.getD j 0 = j := by
      rw [hall]; simp [List.getD_eq_getElem?_getD, hj]
    rw [hj'] at hp
    rw [hp] at hpJ
    have hcalls : (RecGraph.outputsOf g S V).calls.getD j [] = (g.calls.getD j []).flatMap (RecGraph.wordBytes S V) := by
      simp [RecGraph.outputsOf, List.getD_eq_getElem?_getD, hj]
    rw [hcalls, claimHash_words32 S V _ (fun a ha ↦ by rw [hsize]; exact hroots j hj a ha)]
    refine bytes_eq_of_words' _ _ (PcsCircuit.digestBytes_length _) (claimHash_length _) fun k hk ↦ ?_
    have := congrArg (fun l ↦ l.getD k 0) hpJ
    simpa [List.getD_eq_getElem?_getD, hk] using this

/-! ## The bridge -/

/-- **The bridge from RecCircuit's end statement to `Pi1GraphAccepts`**: a witness satisfying π2's circuit at π2's
public limbs `pub`, whose ports and rebuilt calls are the graph's outputs (`EndStatement`), holds a π1 stream
(`D.pi1Stream`) on which π1-rec4's graph at π1's setup commitment accepts, its claims hashing to the declared ones. -/
def CircuitBridge (D : RecDeployment) (rootsAt : List ℕ) (compiled : UniKeccak.SetupRootsK → RecCircuit.Compiled)
    (pub : RecSetupRoots → Vector UInt8 32 → RecProof → ℕ → List Primitives.F192) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (w : ℕ → K),
    proof.pi1Claims.length = 3 →
    ((compiled roots.pi1).circuit.toPiop).Satisfies (pub roots input proof) (RecCircuit.emb w) →
    RecCircuit.Compiled.EndStatement (pi1GraphAt roots.pi1) rootsAt (D.pi1IvAt roots.pi1) Data.hashed
      (compiled roots.pi1) w →
    Pi1GraphAccepts (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input (D.pi1Stream w) proof.pi1Claims

/-- **`Pi2Layers.circuit`, from RecCircuit's end theorem**: given the compiler's run at every setup commitment
(`Pi2Layers.compile_ok`), the bridge gives the field's statement. -/
theorem circuit_of_bridge {D : RecDeployment} {rootsAt : List ℕ} {compiled : UniKeccak.SetupRootsK → RecCircuit.Compiled}
    {pub : RecSetupRoots → Vector UInt8 32 → RecProof → ℕ → List Primitives.F192}
    (hc : ∀ roots, RecCircuit.compile (RecCircuit.ofRG (pi1GraphAt roots) rootsAt (D.pi1IvAt roots) Data.hashed) =
      .ok (compiled roots))
    (hb : CircuitBridge D rootsAt compiled pub) :
    ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (w : ℕ → K),
      proof.pi1Claims.length = 3 →
      ((compiled roots.pi1).circuit.toPiop).Satisfies (pub roots input proof) (RecCircuit.emb w) →
        Pi1GraphAccepts (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input (D.pi1Stream w) proof.pi1Claims :=
  fun roots input proof w hlen hw ↦
    hb roots input proof w hlen hw (RecCircuit.Compiled.compile_sound_end (hc roots.pi1) hw)

end RecCompose

/-- info: 'RecCompose.circuit_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.circuit_of_bridge

/-- info: 'RecCompose.pi1GraphAccepts_of_ports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1GraphAccepts_of_ports

/-- info: 'RecCompose.claimHash_words32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.claimHash_words32
