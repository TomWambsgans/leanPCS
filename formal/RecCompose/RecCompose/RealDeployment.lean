-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md and AGENTS.md.
import RecCompose.Facts
import RecCompose.Circuit

/-!
# The real deployment, and the run-checked inputs that build its circuits

This file exhibits a `D` with `D.Real`, and inhabits `Pi2Circuits D`, whose premises are stated per π1 setup commitment
`roots` and 32-byte IV (quantified over IVs of every length, it would be uninhabited). Here:

* **`realDeployment prog hprog`**: π1's deployment (the Keccak VM's `UniKeccak.KDeployment`) at the 128-signature
  reference shape `RecGraphKeccak.Pi1.keccak128` and leanVM's program IV, for the program `prog` (any Keccak VM program
  of the reference shape's bytecode size; leanVM 9d50c92a3's is not transcribed in Lean); π2's circuit at each setup
  commitment `roots` `pi2CircuitOf` of the Lean compiler's (`compiledAt roots (realIv roots)`: `RecCircuit.compile` on
  the Keccak π1-rec4's emitted graph at that commitment, `emittedAt roots = graphAtSetup Emitted.graph roots`, at π1's
  contract IV there), so `σ`, `κ` are the compiler's by construction; π1's calls `Data.pi1Calls`; π1's stream `streamW` of the
  compiled circuit at π1's reference IV (`realStream`); the Keccak-f block `KeccakFlock.keccakFlockSpec`.
* **`realDeployment_real`**: `(realDeployment prog hprog).Real`, from `GraphsAgreeK4` (the existing run) and two
  evaluated checks of single values: **`DigestChecked`** (the digest of the compiler's `σ`, `κ` at `Data.pi1Iv` is the
  Rust's `Data.digest`) and **`SetupRootChecked`** (their setup tree's root is the Rust's `Data.setupRoot`). These two
  pin the model's `σ`, `κ` to the deployed contract's constants; no proof uses them for anything else.
* **`IvChecked`**: one `Bool` per π1 setup commitment `roots` and 32-byte IV, `ivCheck roots iv`: the compiler accepts
  π1-rec4's emitted graph at `roots` and `iv`, the circuit passes `viewCheck`, and its π1-stream decoding agrees with
  the reference's (`streamAgree`: the same free bits and free reads, each of their values read off the witness the same
  way). **Stated for every `(roots, iv)`, checked by evaluation at three points only** (the reference commitment
  `realRoots` at π1's reference IV, the zero IV and the all-ones IV: `rec-real-check`, `RecComposeTest/RealCheck.lean`),
  assumed at the others. The end theorems use it at π1's setup commitment as the honest setup computes it over `π`,
  almost never `realRoots`: there it is an assumption (uniformity in the IV and the commitment, plausible because the
  commitment enters only through π1's IV and the hashed `F` claim's root and answer words).
* **`pi2Circuits_real`**, **`pi2ViewChecked_real`**: `Pi2Circuits (realDeployment prog hprog)` and its
  `Pi2ViewChecked`, from `GraphsAgreeK4` and `IvChecked`. `stream_eq` at every IV follows from `streamAgree`
  (`streamW_eq_of_streamAgree`), so it is no longer a functional equation no evaluation checks.

**Why `IvChecked` is not proved (IV uniformity).** The IV enters the compiler at one place, the seed's message
(`constantBits NAME ++ constantBits r.iv ++ publicCopy`, one Keccak-f block): its 256 bits are the 256 constants
`fresh 0` / `fresh 1` of the seed's permutation input (`permute`), whose only IV dependence is `setKappa`'s write of
`κ = 1` (a `0` is not stored: the circuit's `κ` is sparse). So κ has exactly one entry more per IV one-bit: 20,611
entries at the reference IV (113 one-bits) and 20,498 at the zero IV (`rec-view-check`, logs `data-viewcheck-ref`,
`data-viewcheck-zero`). Besides `κ`, the IV is in the traces the checker reads (the seed sponge's message and block
input, `nodeOk`'s `seedMessage iv`, `graphOk`'s length check). A proof that the rest of the run (regions, rows, placements, values, σ, the view, the ports, `validB`, the
checker's verdict, `streamW`) does not depend on those 256 constants is a relational simulation of the whole builder
(`compileM`, the templates and `finish`, about 1,200 lines of monadic code) and of the checker (680 lines); it is not
done. The three evaluated IVs set every IV constant both ways (the zero IV all `0`, the all-ones IV all `1`).
`IvUniform.lean` proves `IvChecked` from the builder's half alone (`PatchChecked`: the compile at every IV is the
all-ones IV's with `κ` removed at its zero bits' seed positions) and `ivCheck` at the all-ones and zero IVs: the
checker's half (`viewCheck`, `streamAgree`) is done.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open RecCircuit (NONE)

/-! ## The compiler's circuit at an IV, as the deployment's -/

/-- A compiler's result's circuit (the default one if it rejects). -/
def okOr (e : Except String RecCircuit.Compiled) : RecCircuit.Compiled :=
  match e with
  | .ok c => c
  | .error _ => default

/-- **The Keccak π1-rec4's emitted graph at π1's setup commitment `roots`** (`graphAtSetup`: the setup claim's two
constant words `roots`'). -/
def emittedAt (roots : UniKeccak.SetupRootsK) : RecGraph.Graph :=
  RecGraphKeccak.graphAtSetup RecGraphKeccak.Emitted.graph roots

/-- **The Lean compiler on the Keccak π1-rec4's emitted graph at the setup commitment `roots` and the IV `iv`**, π1's
claims `Data.hashed` hashed in the circuit (the default circuit if it rejects). The proofs never unfold it into a
`match` on the compiler's run (that would make the elaborator evaluate the run): they go through `okOr`'s lemmas. -/
def compiledAt (roots : UniKeccak.SetupRootsK) (iv : List UInt8) : RecCircuit.Compiled :=
  okOr (RecCircuit.compile (RecCircuit.ofRG (emittedAt roots) RecGraphKeccak.Emitted.rootsAt iv Data.hashed))

/-- **The setup roots of the real deployment's reference** (the reference roots, `RecGraphKeccak.Pi1.referenceRootsK`). -/
def realRoots : UniKeccak.SetupRootsK := RecGraphKeccak.Pi1.referenceRootsK

/-- **π1's contract IV at the setup commitment `roots`**, at the reference shape and leanVM's program IV (the real
deployment's `pi1IvAt`). -/
def realIv (roots : UniKeccak.SetupRootsK) : List UInt8 :=
  pi1Iv RecGraphKeccak.Pi1.keccak128 UniStatement.programIv roots

/-- The compiled circuit at the reference setup commitment and π1's reference IV (`realIv realRoots`, which is the
Rust's `Data.pi1Iv`: `rec-real-check` prints both). -/
def refCompiled : RecCircuit.Compiled := compiledAt realRoots (realIv realRoots)

/-- **π2's circuit from a compiled one**: `Data.circuit` as the verifier's view, the compiler's `σ` and `κ` (`κ` read
from its dense column on the positions, which is `kappaAt` there: `pi2CircuitOf_kappa`). -/
def pi2CircuitOf (C : RecCircuit.Circuit) : Pi2Circuit :=
  let kd := RecCircuit.denseKappa C
  ⟨Data.circuit, C.sigmaAt, fun i ↦ if i < C.n then kd.getD i 0 else C.kappaAt i⟩

theorem pi2CircuitOf_kappa (C : RecCircuit.Circuit) : (pi2CircuitOf C).kappa = C.kappaAt := by
  funext i
  show (if i < C.n then (RecCircuit.denseKappa C).getD i 0 else C.kappaAt i) = C.kappaAt i
  split_ifs with h
  · exact RecCircuit.denseKappa_getD C i h
  · rfl

/-- **π1's stream on π2's witness**: the compiler's decoding of the free bits (`streamW`) at the reference. -/
def realStream (w : ℕ → K) : Array UInt8 :=
  (refCompiled.streamW (RecCircuit.ofRG (emittedAt realRoots) RecGraphKeccak.Emitted.rootsAt (realIv realRoots)
    Data.hashed) w).toArray

/-- π2's circuit at each setup commitment: the compiler's there, at π1's contract IV there. -/
def realPi2 (roots : UniKeccak.SetupRootsK) : Pi2Circuit := pi2CircuitOf (compiledAt roots (realIv roots)).circuit

/-- At the reference, π2's circuit is the reference compile's (what `rec-real-check` evaluates). -/
theorem realPi2_ref : realPi2 realRoots = pi2CircuitOf refCompiled.circuit := rfl

/-- The reference shape is valid (`Shape.Valid`: six heights, `validate` with Flock). -/
theorem keccak128_valid : RecGraphKeccak.Pi1.keccak128.Valid := by decide +kernel

/-- π1's deployment at the Keccak reference shape and leanVM's program IV, for the program `prog`. -/
def realPi1 (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) :
    UniKeccak.KDeployment :=
  ⟨prog, RecGraphKeccak.Pi1.keccak128, UniStatement.programIv, keccak128_valid, hprog⟩

/-- **The real deployment**, for π1's program `prog` (`D.pi1.prog` is not pinned by `RecDeployment.Real`: the
end theorems hold for every Keccak VM program of the reference shape). -/
def realDeployment (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) :
    RecDeployment where
  pi1 := realPi1 prog hprog
  pi2 := realPi2
  pi1Calls := Data.pi1Calls
  pi1Stream := realStream
  flock := KeccakFlock.keccakFlockSpec

/-! ## The evaluated checks -/

/-- **The digest of the Lean compiler's `σ`, `κ` at π1's reference IV is the Rust's** (`Circuit::digest`, the constant
from which the Rust computes the deployed contract's π2 IV). A `Prop` about one value: **checked by evaluation**
(`rec-real-check`). -/
def DigestChecked : Prop :=
  Id.run ((realPi2 realRoots).digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest

/-- **The setup root of the Lean compiler's `σ`, `κ` at π1's reference IV is the Rust's** (`Setup::new(circuit).root()`,
a WHIR commitment of `2^25` words). A `Prop` about one value: **checked by evaluation** (`rec-real-check --setup`). -/
def SetupRootChecked : Prop :=
  digestBytes (Id.run ((realPi2 realRoots).setupTreeWith (m := Id)
    fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root = Data.setupRoot

/-- A value is read off the witness the same way in two circuits' views (`Ctx.val`): the same producer, then the same
first forward (a free value) or the same formula, width and `κ` at the producer. -/
def valAgree (X Y : RecCircuit.Ctx) (v : ℕ) : Bool :=
  decide (X.prod v = Y.prod v) &&
    (if X.prod v = NONE then decide ((X.chain v).getD 0 0 = (Y.chain v).getD 0 0)
     else decide (X.prod v < X.n) && decide (X.prod v < Y.n) && decide (X.C.width = Y.C.width) &&
       decide (X.C.formulaAt (X.prod v) = Y.C.formulaAt (X.prod v)) && decide (X.kap (X.prod v) = Y.kap (X.prod v)))

/-- **Two compiled circuits decode π1's stream alike**: the same free bits and free reads (`bitSelf`, `freeReads`),
each of their values (and `NONE`) read off the witness the same way (`valAgree`). -/
def streamAgree (c c0 : RecCircuit.Compiled) : Bool :=
  let X := c.ctx
  let Y := c0.ctx
  decide (c.bitSelf = c0.bitSelf) && decide (c.freeReads = c0.freeReads) && valAgree X Y NONE &&
    c.bitSelf.all (fun o ↦ match o with
      | some v => valAgree X Y v
      | none => true) &&
    c.freeReads.all (fun e ↦ e.2.all (valAgree X Y))

/-- A compiler's result is a circuit that passes the view check and decodes π1's stream as `c0` does. -/
def checkOk (c0 : RecCircuit.Compiled) (e : Except String RecCircuit.Compiled) : Bool :=
  match e with
  | .ok c => viewCheck c && streamAgree c c0
  | .error _ => false

/-- **The per-IV check**: the compiler accepts π1-rec4's emitted graph at the setup commitment `roots` and the IV
`iv`, the circuit passes the view check, and it decodes π1's stream as the reference's circuit does. -/
def ivCheck (roots : UniKeccak.SetupRootsK) (iv : List UInt8) : Bool :=
  checkOk refCompiled
    (RecCircuit.compile (RecCircuit.ofRG (emittedAt roots) RecGraphKeccak.Emitted.rootsAt iv Data.hashed))

/-- **The per-IV check holds at every setup commitment and 32-byte IV.** **Checked by evaluation at three** (the
reference setup commitment with π1's reference IV, the zero IV, the all-ones IV: `rec-real-check`), assumed at the
others (IV uniformity is not proved; see the module docstring; `ivChecked_of_patchChecked` derives it from
`PatchChecked`). -/
def IvChecked : Prop := ∀ (roots : UniKeccak.SetupRootsK) (iv : List UInt8), iv.length = 32 → ivCheck roots iv = true

/-! ## From the checks -/

theorem checkOk_spec {c0 : RecCircuit.Compiled} {e : Except String RecCircuit.Compiled} (h : checkOk c0 e = true) :
    e = .ok (okOr e) ∧ viewCheck (okOr e) = true ∧ streamAgree (okOr e) c0 = true := by
  cases e with
  | error m => exact absurd h Bool.false_ne_true
  | ok c =>
    change (viewCheck c && streamAgree c c0) = true at h
    rw [Bool.and_eq_true] at h
    exact ⟨rfl, h.1, h.2⟩

theorem ivCheck_spec {roots : UniKeccak.SetupRootsK} {iv : List UInt8} (h : ivCheck roots iv = true) :
    RecCircuit.compile (RecCircuit.ofRG (emittedAt roots) RecGraphKeccak.Emitted.rootsAt iv Data.hashed) =
      .ok (compiledAt roots iv) ∧
      viewCheck (compiledAt roots iv) = true ∧ streamAgree (compiledAt roots iv) refCompiled = true := by
  exact checkOk_spec h

theorem val_eq_of_valAgree {X Y : RecCircuit.Ctx} (hX : X.kd = RecCircuit.denseKappa X.C)
    (hY : Y.kd = RecCircuit.denseKappa Y.C) {v : ℕ} (h : valAgree X Y v = true) (w : ℕ → K) :
    X.val w v = Y.val w v := by
  unfold valAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hp, h2⟩ := h
  unfold RecCircuit.Ctx.val
  rw [← hp]
  split_ifs at h2 ⊢ with hn
  · simp only [decide_eq_true_eq] at h2
    rw [h2]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨⟨hlt, hlt'⟩, hw⟩, hf⟩, hk⟩ := h2
    unfold RecCircuit.Circuit.push RecCircuit.Circuit.cells
    rw [hf, hw, ← RecCircuit.Ctx.kap_eq X hX hlt, ← RecCircuit.Ctx.kap_eq Y hY (hp ▸ hlt'), hk, hp]

theorem decodeStream_congr (c : RecCircuit.Compiled) (n : ℕ) (f g : ℕ → K)
    (hS : ∀ k, f (c.streamBit k) = g (c.streamBit k))
    (hR : ∀ e ∈ c.freeReads, ∀ i, f (e.2.getD i NONE) = g (e.2.getD i NONE)) :
    c.decodeStream n f = c.decodeStream n g := by
  unfold RecCircuit.Compiled.decodeStream
  refine List.map_congr_left fun i _ ↦ ?_
  split_ifs
  · simp only [hS]
  · split
    · next off ls heq =>
      simp only [hR _ (Array.mem_of_find?_eq_some heq)]
    · rfl

theorem decodeStream_eq_of (c c0 : RecCircuit.Compiled) (hb : c.bitSelf = c0.bitSelf)
    (hf : c.freeReads = c0.freeReads) (n : ℕ) (g : ℕ → K) : c.decodeStream n g = c0.decodeStream n g := by
  unfold RecCircuit.Compiled.decodeStream RecCircuit.Compiled.streamBit
  rw [hb, hf]

theorem getD_mem_or {a : Array ℕ} {i : ℕ} : a.getD i NONE ∈ a ∨ a.getD i NONE = NONE := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : a[i]? with
  | none => exact .inr rfl
  | some x => exact .inl (Array.mem_of_getElem? h)

/-- **`streamAgree` gives the same π1 stream** on every witness. -/
theorem streamW_eq_of_streamAgree {c c0 : RecCircuit.Compiled} (h : streamAgree c c0 = true)
    (r r0 : RecCircuit.Recorded) (hn : r.graph.streamLen = r0.graph.streamLen) (w : ℕ → K) :
    c.streamW r w = c0.streamW r0 w := by
  unfold streamAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨⟨hb, hf⟩, hN⟩, hbits⟩, hreads⟩ := h
  have hv : ∀ v, valAgree c.ctx c0.ctx v = true → c.ctx.val w v = c0.ctx.val w v :=
    fun v hv ↦ val_eq_of_valAgree rfl rfl hv w
  unfold RecCircuit.Compiled.streamW
  rw [hn, decodeStream_congr c _ _ (c0.ctx.val w), decodeStream_eq_of c c0 hb hf]
  · intro k
    apply hv
    unfold RecCircuit.Compiled.streamBit
    rw [Array.getD_eq_getD_getElem?]
    cases ho : c.bitSelf[k]? with
    | none => exact hN
    | some o =>
      have hm := hbits o (Array.mem_of_getElem? ho)
      cases o with
      | none => exact hN
      | some v => exact hm
  · intro e he i
    apply hv
    rcases getD_mem_or (a := e.2) (i := i) with hm | hm
    · exact hreads e he _ hm
    · rw [hm]; exact hN

/-! ## The real deployment's circuits and `Real` -/

/-- (Generic in the graph, so that no proof compares `RecGraphKeccak.Pi1.pi1GraphK`'s fields by reduction: the kernel
would run the recorder.) -/
theorem ofRG_streamLen' (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) (hashed : List ℕ) :
    (RecCircuit.ofRG g rootsAt iv hashed).graph.streamLen = g.streamLen := rfl

theorem graphAtSetup_streamLen (g : RecGraph.Graph) (roots : UniKeccak.SetupRootsK) :
    (RecGraphKeccak.graphAtSetup g roots).streamLen = g.streamLen := rfl

/-- The graph at a setup commitment, under `GraphsAgreeK4`, is the emitted one there. -/
theorem pi1GraphAt_eq (hg : RecGraphKeccak.GraphsAgreeK4) (roots : UniKeccak.SetupRootsK) :
    pi1GraphAt roots = emittedAt roots := by
  unfold pi1GraphAt emittedAt
  unfold RecGraphKeccak.GraphsAgreeK4 at hg
  rw [hg]

variable (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize)

theorem realDeployment_pi1IvAt (roots : UniKeccak.SetupRootsK) :
    (realDeployment prog hprog).pi1IvAt roots = realIv roots := rfl

theorem compiledAt_of_compile {roots : UniKeccak.SetupRootsK} {iv : List UInt8} {c : RecCircuit.Compiled}
    (hg : RecGraphKeccak.GraphsAgreeK4)
    (hc : RecCircuit.compile (RecCircuit.ofRG (pi1GraphAt roots) RecGraphKeccak.Emitted.rootsAt iv Data.hashed) = .ok c) :
    compiledAt roots iv = c := by
  rw [pi1GraphAt_eq hg] at hc
  exact (congrArg okOr hc).trans rfl

/-- **The real deployment is `Real`**, from `GraphsAgreeK4` and the two evaluated checks (`DigestChecked`,
`SetupRootChecked`). The circuit, the calls, the shape, the program IV, the setup columns and the Keccak-f block hold
by construction. -/
theorem realDeployment_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked) :
    (realDeployment prog hprog).Real :=
  ⟨fun _ ↦ rfl, rfl, rfl, rfl, hd, hs, fun roots c hc ↦ by
    have e : compiledAt roots (realIv roots) = c := compiledAt_of_compile hg hc
    refine ⟨?_, ?_⟩
    · show (compiledAt roots (realIv roots)).circuit.sigmaAt = _
      rw [e]
    · show (pi2CircuitOf (compiledAt roots (realIv roots)).circuit).kappa = _
      rw [pi2CircuitOf_kappa, e], rfl⟩

/-- **The real deployment's compiled circuits** (`Pi2Circuits`), from `GraphsAgreeK4` and `IvChecked`. -/
def pi2Circuits_real (hg : RecGraphKeccak.GraphsAgreeK4) (h : IvChecked) : Pi2Circuits (realDeployment prog hprog) where
  rootsAt := RecGraphKeccak.Emitted.rootsAt
  compiled roots := compiledAt roots (realIv roots)
  compile_ok roots := by
    rw [pi1GraphAt_eq hg]
    exact (ivCheck_spec (h roots (realIv roots) (pi1Iv_length _ _ _))).1
  stream_eq roots w := by
    show (refCompiled.streamW (RecCircuit.ofRG (emittedAt realRoots) RecGraphKeccak.Emitted.rootsAt (realIv realRoots)
      Data.hashed) w).toArray = _
    exact congrArg List.toArray (streamW_eq_of_streamAgree (ivCheck_spec (h roots (realIv roots)
      (pi1Iv_length _ _ _))).2.2
      (RecCircuit.ofRG (pi1GraphAt roots) RecGraphKeccak.Emitted.rootsAt (realIv roots) Data.hashed)
      (RecCircuit.ofRG (emittedAt realRoots) RecGraphKeccak.Emitted.rootsAt (realIv realRoots) Data.hashed)
      (by rw [ofRG_streamLen', ofRG_streamLen', pi1GraphAt_eq hg, emittedAt, emittedAt, graphAtSetup_streamLen,
        graphAtSetup_streamLen]) w).symm

/-- **The real deployment's circuits pass the view check** at every setup commitment, from `IvChecked`. -/
theorem pi2ViewChecked_real (hg : RecGraphKeccak.GraphsAgreeK4) (h : IvChecked) :
    Pi2ViewChecked (pi2Circuits_real prog hprog hg h) :=
  fun roots ↦ (ivCheck_spec (h roots (realIv roots) (pi1Iv_length _ _ _))).2.1

theorem pi2Circuits_real_rootsAt (hg : RecGraphKeccak.GraphsAgreeK4) (h : IvChecked) :
    (pi2Circuits_real prog hprog hg h).rootsAt = RecGraphKeccak.Emitted.rootsAt := rfl

end RecCompose

/-- info: 'RecCompose.realDeployment_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.realDeployment_real

/-- info: 'RecCompose.pi2Circuits_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Circuits_real

/-- info: 'RecCompose.pi2ViewChecked_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2ViewChecked_real
