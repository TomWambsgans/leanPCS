-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `formal/UniComplete/UniComplete/SyncVerifier.lean`
-- (`reduce_steps`, `runWithH_syncs`) for π2: its verifier is `formal/RecStatement`'s (`reduceWith`, `runWith`), its
-- honest prover `RecCompose.Pi2Prover`'s (`pi2ProveStreamWith`); the joint steps are UniComplete's (`Steps`, `StepsE`,
-- `UniKeccakComplete.Reads`, `Writes`, `SyncBasic.lean`).
import RecCompose.Pi2Prover
import RecCompose.Pi2CompleteH
import UniKeccakComplete.K.SyncVerifier

/-!
# π2's verifier reads what π2's honest prover writes

At a pure permutation (`Id`), π2's verifier (`RecStatement.reduceWith`, the contract's arithmetic's inputs) run on the
stream π2's honest prover writes (`pi2ProveStreamWith`, Keccak-256 the sponge over the same permutation) reads back
exactly the prover's inputs (`Pi2Out.inputs`: the public scalars, `α, β, γ, t`, the fold values, `ξ`, `ρ`), and `finish`
finds nothing left (`runWith_honest`): the reads match the writes (`sendPublic`: π1's roots as their halves, π1's
claims' elements as scalars, `ReadMatch`), the roots are read back as their halves (no top limb), the challenges are
the same Keccak-256 of the same bytes (`UniKeccakComplete.Steps.sample`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2S

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniComplete (Wr WrM scalarWire)
open UniKeccakComplete (Reads Writes Steps StepsE rootRead)
open UniStatement (rootWord)

/-! ## The public values -/

/-- **A read and its value agree**: a root's 32 bytes, an element. -/
def ReadMatch : Read → PublicValue → Prop
  | .root, .root b => b.length = 32
  | .scalar, .scalar _ => True
  | _, _ => False

/-- The bytes `sendPublic` writes. -/
def publicWire : List (Read × PublicValue) → List UInt8
  | [] => []
  | (.integer b, .integer x) :: rest => UniComplete.integerWire x b ++ publicWire rest
  | (.root, .root bytes) :: rest => rootWord (halvesOf bytes) ++ publicWire rest
  | (.scalar, .scalar x) :: rest => scalarWire x ++ publicWire rest
  | _ :: rest => publicWire rest

theorem sendPublic_writes : ∀ (ps : List (Read × PublicValue)) (w : Wr),
    Writes (sendPublic (m := Id) ps) w () (publicWire ps)
  | [], w => Writes.pure () w
  | (.integer b, .integer x) :: rest, w =>
    (UniKeccakComplete.sendInteger_writes x b w).bind (sendPublic_writes rest _)
  | (.root, .root _) :: rest, w => (UniKeccakComplete.sendRoot_writes _ w).bind (sendPublic_writes rest _)
  | (.scalar, .scalar x) :: rest, w => (UniKeccakComplete.sendScalar_writes x w).bind (sendPublic_writes rest _)
  | (.integer _, .root _) :: rest, w => sendPublic_writes rest w
  | (.integer _, .scalar _) :: rest, w => sendPublic_writes rest w
  | (.root, .integer _) :: rest, w => sendPublic_writes rest w
  | (.root, .scalar _) :: rest, w => sendPublic_writes rest w
  | (.scalar, .integer _) :: rest, w => sendPublic_writes rest w
  | (.scalar, .root _) :: rest, w => sendPublic_writes rest w

theorem eNew_limb2_zero (a b : UInt64) : (UniStatement.eNew a b 0).limb 2 = 0 := by
  simp [UniStatement.eNew]
  rfl

/-- A root's halves have no top limb: `next_root` reads them back as they are. -/
theorem rootRead_halvesOf (b : List UInt8) : rootRead (halvesOf b) = halvesOf b :=
  UniKeccakComplete.rootRead_of (eNew_limb2_zero _ _) (eNew_limb2_zero _ _)

/-- **The verifier's public reads** read `sendPublic`'s bytes and give the values' scalars after the statement's. -/
theorem loop_reads (body : Read → List E → UniStatement.ChanM Id (ForInStep (List E)))
    (hroot : ∀ (pubs : List E) (h : E × E), UniKeccakComplete.Reads (body .root pubs) (rootWord h)
      (.yield (pubs ++ [(rootRead h).1, (rootRead h).2])) [])
    (hscalar : ∀ (pubs : List E) (x : E), UniKeccakComplete.Reads (body .scalar pubs) (scalarWire x) (.yield (pubs ++ [x])) []) :
    ∀ (rs : List Read) (vs : List PublicValue), List.Forall₂ ReadMatch rs vs → ∀ pubs : List E,
      UniKeccakComplete.Reads (ForIn.forIn rs pubs body) (publicWire (rs.zip vs)) (pubs ++ vs.flatMap PublicValue.scalars) []
  | [], [], .nil, pubs => by simpa [publicWire] using UniKeccakComplete.Reads.pure (α := List E) pubs
  | .root :: rs, .root b :: vs, .cons _ h, pubs => by
    have h1 := hroot pubs (halvesOf b)
    rw [rootRead_halvesOf] at h1
    have h2 := loop_reads body hroot hscalar rs vs h (pubs ++ [(halvesOf b).1, (halvesOf b).2])
    have h3 : UniKeccakComplete.Reads (ForIn.forIn (Read.root :: rs) pubs body) (rootWord (halvesOf b) ++ publicWire (rs.zip vs))
        (pubs ++ [(halvesOf b).1, (halvesOf b).2] ++ vs.flatMap PublicValue.scalars) ([] ++ []) := by
      rw [List.forIn_cons]
      exact UniKeccakComplete.Reads.bind h1 h2
    exact UniKeccakComplete.Reads.congr h3 (by simp [publicWire]) (by simp [PublicValue.scalars]) (by simp)
  | .scalar :: rs, .scalar x :: vs, .cons _ h, pubs => by
    have h1 := hscalar pubs x
    have h2 := loop_reads body hroot hscalar rs vs h (pubs ++ [x])
    have h3 : UniKeccakComplete.Reads (ForIn.forIn (Read.scalar :: rs) pubs body) (scalarWire x ++ publicWire (rs.zip vs))
        (pubs ++ [x] ++ vs.flatMap PublicValue.scalars) ([] ++ []) := by
      rw [List.forIn_cons]
      exact UniKeccakComplete.Reads.bind h1 h2
    exact UniKeccakComplete.Reads.congr h3 (by simp [publicWire]) (by simp [PublicValue.scalars]) (by simp)
  | .integer _ :: _, _ :: _, .cons hm _, _ => by cases hm
  | .root :: _, .integer _ :: _, .cons hm _, _ => by cases hm
  | .root :: _, .scalar _ :: _, .cons hm _, _ => by cases hm
  | .scalar :: _, .integer _ :: _, .cons hm _, _ => by cases hm
  | .scalar :: _, .root _ :: _, .cons hm _, _ => by cases hm

/-! ## The joint steps -/

/-- **A challenge on both sides**, the verifier's `sample` over a permutation `F` whose Keccak-256 is `Hk`. -/
theorem stepsE_sample {γ δ : Type} (Hk : List UInt8 → Digest) {f : E → UniStatement.ChanM Id γ} {g : E → WrM Id δ}
    {pos : ℕ} {w : Wr} {K : γ → δ → ℕ → Wr → List E → Prop} (e : pos = w.stream.size)
    (h2 : StepsE (f (Wr.sampled Hk w).1) (g (Wr.sampled Hk w).1) w.stream.size (Wr.sampled Hk w).2
      (fun c d p2 w2 z2 ↦ K c d p2 w2 ([] ++ z2))) :
    StepsE (UniKeccakComplete.sampleH (m := Id) (Pure.pure ∘ Hk) >>= f) (UniComplete.sampleW (m := Id) (Pure.pure ∘ Hk) >>= g)
      pos w K := by
  exact StepsE.bind_pos e (Steps.sample Hk w) h2

/-- **A verifier-only read of the last bytes written**, at a position equal to the writer's end. -/
theorem vreadEndAt {α γ δ : Type} {v : UniStatement.ChanM Id α} {f : α → UniStatement.ChanM Id γ} {p : WrM Id δ}
    {pos : ℕ} {w : Wr} {B : List UInt8} {a : α} {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop}
    (e : pos = w.stream.size) (h1 : UniKeccakComplete.Reads v B a zs1)
    (h2 : StepsE (f a) p (w.stream.size + B.length) (w.append B) (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p pos (w.append B) K :=
  StepsE.pos_start e (StepsE.vreadEnd h1 h2)

/-- **The fold values and `ξ`, read back**: the prover has just written the scalars `xs ++ [x]`; the verifier, at the
writer's end before them, reads `xs` (`next_scalars`) then `x` (`next_scalar`). -/
theorem vreadValuesEnd {γ δ : Type} {f : List E → E → UniStatement.ChanM Id γ} {p : WrM Id δ} {pos n : ℕ} {w : Wr}
    {xs : List E} {x : E} {K : γ → δ → ℕ → Wr → List E → Prop} (hn : xs.length = n) (e : pos = w.stream.size)
    (h2 : StepsE (f xs x) p (w.stream.size + ((xs ++ [x]).flatMap scalarWire).length)
      (w.append ((xs ++ [x]).flatMap scalarWire)) (fun c d p2 w2 z2 ↦ K c d p2 w2 ([] ++ ([] ++ z2)))) :
    StepsE (UniStatement.nextScalars (m := Id) n >>= fun a ↦ UniStatement.nextScalar (m := Id) >>= fun ξ ↦ f a ξ) p pos
      (w.append ((xs ++ [x]).flatMap scalarWire)) K := by
  subst hn e
  have hr := UniKeccakComplete.nextScalars_reads xs
  refine StepsE.vread (P := w.stream.toList) (B := xs.flatMap scalarWire) (Q := scalarWire x) hr
    (by simp [List.flatMap_append]) ?_ |> StepsE.pos_start (by simp)
  refine StepsE.vread (P := w.stream.toList ++ xs.flatMap scalarWire) (B := scalarWire x) (Q := [])
    (UniKeccakComplete.nextScalar_reads x) (by simp [List.flatMap_append]) ?_ |> StepsE.pos_start (by simp)
  refine StepsE.pos_start ?_ h2
  simp [List.flatMap_append]
  omega

/-- **The fold values, `ξ` and `s`, read back**: the prover has just written the scalars `xs ++ [x, y]`; the verifier,
at the writer's end before them, reads `xs` (`next_scalars`), then `x`, then `y` (`next_scalar`). -/
theorem vreadValuesEnd2 {γ δ : Type} {f : List E → E → E → UniStatement.ChanM Id γ} {p : WrM Id δ} {pos n : ℕ}
    {w : Wr} {xs : List E} {x y : E} {K : γ → δ → ℕ → Wr → List E → Prop} (hn : xs.length = n)
    (e : pos = w.stream.size)
    (h2 : StepsE (f xs x y) p (w.stream.size + ((xs ++ [x, y]).flatMap scalarWire).length)
      (w.append ((xs ++ [x, y]).flatMap scalarWire)) (fun c d p2 w2 z2 ↦ K c d p2 w2 ([] ++ ([] ++ ([] ++ z2))))) :
    StepsE (UniStatement.nextScalars (m := Id) n >>= fun a ↦ UniStatement.nextScalar (m := Id) >>= fun ξ ↦
      UniStatement.nextScalar (m := Id) >>= fun sv ↦ f a ξ sv) p pos
      (w.append ((xs ++ [x, y]).flatMap scalarWire)) K := by
  subst hn e
  have hr := UniKeccakComplete.nextScalars_reads xs
  refine StepsE.vread (P := w.stream.toList) (B := xs.flatMap scalarWire) (Q := scalarWire x ++ scalarWire y) hr
    (by simp [List.flatMap_append]) ?_ |> StepsE.pos_start (by simp; try omega)
  refine StepsE.vread (P := w.stream.toList ++ xs.flatMap scalarWire) (B := scalarWire x) (Q := scalarWire y)
    (UniKeccakComplete.nextScalar_reads x) (by simp [List.flatMap_append]) ?_ |> StepsE.pos_start (by simp; try omega)
  refine StepsE.vread (P := w.stream.toList ++ xs.flatMap scalarWire ++ scalarWire x) (B := scalarWire y) (Q := [])
    (UniKeccakComplete.nextScalar_reads y) (by simp [List.flatMap_append]) ?_ |> StepsE.pos_start (by simp; try omega)
  refine StepsE.pos_start ?_ h2
  simp [List.flatMap_append]
  omega

/-- **The verifier's run and the honest prover's, in step**: on the prover's stream, π2's verifier reads the public
values, `W`'s and `Q`'s roots and out-of-domain answers, the fold values, `ξ` and `s` the prover writes, and draws its
challenges; it ends at the end of the prover's stream, its arithmetic's inputs the prover's. -/
theorem reduce_steps (Hk : List UInt8 → Digest) (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E)
    (view : Circuit) (setupStack : Array K) (input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (seed : Digest) (hmatch : List.Forall₂ ReadMatch view.reads values) (hrow : view.logRow = G.logW) :
    StepsE (Pi2H.reduceWithH (m := Id) (Pure.pure ∘ Hk) (Spec.of view) (UniStatement.publicWordsOf input))
      (pi2ProveStreamWith (m := Id) (Pure.pure ∘ Hk) G (Spec.of view).core (pureZ zf) view.reads setupStack input values w)
      0 (Wr.start seed)
      (fun r out pos w' _ ↦ pos = w'.stream.size ∧ out.stream = w'.stream ∧ r.inputs = out.inputs ∧
        r.scalars = out.inputs.scalars ∧ r.out = (Spec.of view).core.run r.inputs ∧
        r.oods = (pi2OodAt out.wStack (zf (stackVars G.logN).1 out.wTree.root),
          pi2OodAt out.qStack (zf (stackVars G.logN).2.1 out.qTree.root)) ∧
        w'.stream.toList = publicWire (view.reads.zip values) ++ rootWord (UniStatement.rootHalves out.wTree.root) ++
          scalarWire (pi2OodAt out.wStack (zf (stackVars G.logN).1 out.wTree.root)) ++
          rootWord (UniStatement.rootHalves out.qTree.root) ++
          scalarWire (pi2OodAt out.qStack (zf (stackVars G.logN).2.1 out.qTree.root)) ++
          (out.inputs.a ++ [out.inputs.ξ, out.inputs.s]).flatMap scalarWire ∧
        out.wTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (stackVars G.logN).1 out.wStack ∧
        out.qTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (stackVars G.logN).2.1 out.qStack ∧
        out.inputs = ⟨publicScalarsOf input values, out.inputs.α, out.inputs.β, out.inputs.γ, out.inputs.t,
          foldValues G.logN G.logW (wTableB G w) out.inputs.t, xiOf G.logN setupStack out.inputs.β out.inputs.t,
          sOf G.logN (pNovel G w) out.inputs.t, out.inputs.ρ⟩ ∧
        out.wStack = padStack (stackVars G.logN).1 (fun i ↦ (wTableB G w).getD i 0) ∧
        out.qStack = padStack (stackVars G.logN).2.1 (qEntry G.logN (hNovel G w out.inputs.α out.inputs.β)
          (qNovel G w out.inputs.α out.inputs.β out.inputs.γ
            (phiOn (Spec.of view).core (publicScalarsOf input values) out.inputs.γ))
          (pNovel G w) (qpNovel G w out.inputs.γ)) ∧
        out.wPoint = zf (stackVars G.logN).1 out.wTree.root ∧ out.qPoint = zf (stackVars G.logN).2.1 out.qTree.root) := by
  unfold Pi2H.reduceWithH pi2ProveStreamWith
  dsimp only
  apply StepsE.pbind (sendPublic_writes _ _)
  apply StepsE.pos_start (pos0 := (Wr.start seed).stream.size) rfl
  apply StepsE.vreadEnd (loop_reads _ ?hroot ?hscalar view.reads values hmatch (UniStatement.publicWordsOf input))
  case hroot =>
    intro pubs h
    exact UniKeccakComplete.Reads.congr ((UniKeccakComplete.nextRoot_reads h).bind (UniKeccakComplete.Reads.pure _)) (by simp) rfl (by simp)
  case hscalar =>
    intro pubs x
    exact UniKeccakComplete.Reads.congr ((UniKeccakComplete.nextScalar_reads x).bind (UniKeccakComplete.Reads.pure _)) (by simp) rfl (by simp)
  apply StepsE.plift
  apply StepsE.plift (x := zf _ _)
  apply StepsE.pbind (UniKeccakComplete.sendRoot_writes _ _)
  apply StepsE.pos_start (pos0 := ((Wr.start seed).append (publicWire (view.reads.zip values))).stream.size)
    (by simp)
  apply StepsE.vreadEnd (UniKeccakComplete.nextRoot_reads _)
  apply StepsE.pbind (UniKeccakComplete.sendScalar_writes _ _)
  apply vreadEndAt (by simp; try omega) (UniKeccakComplete.nextScalar_reads _)
  apply stepsE_sample Hk
  case e => simp; omega
  apply stepsE_sample Hk
  case e => simp only [UniKeccakComplete.Wr.sampled_stream]
  apply stepsE_sample Hk
  case e => simp only [UniKeccakComplete.Wr.sampled_stream]
  apply StepsE.plift
  apply StepsE.plift (x := zf _ _)
  apply StepsE.pbind (UniKeccakComplete.sendRoot_writes _ _)
  apply vreadEndAt (by simp only [UniKeccakComplete.Wr.sampled_stream]) (UniKeccakComplete.nextRoot_reads _)
  apply StepsE.pbind (UniKeccakComplete.sendScalar_writes _ _)
  apply vreadEndAt (by simp; try omega) (UniKeccakComplete.nextScalar_reads _)
  apply stepsE_sample Hk
  case e => simp; omega
  apply StepsE.pbind (UniKeccakComplete.sendScalars_writes _ _)
  apply vreadValuesEnd2
  case hn => simp [foldValues, Spec.of, hrow]
  case e => simp only [UniKeccakComplete.Wr.sampled_stream]
  apply stepsE_sample Hk
  case e => simp; omega
  apply StepsE.pget
  apply StepsE.pure
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [publicScalarsOf]
  · simp [publicScalarsOf]
  · simp [Wr.start]

/-- **The honest prover's output** over Keccak-256 `Hk`, from the seed of the IV and the public input. -/
def proverOut (Hk : List UInt8 → Digest) (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E) (view : Circuit)
    (setupStack : Array K) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) : Pi2Out :=
  ((pi2ProveStreamWith (m := Id) (Pure.pure ∘ Hk) G (Spec.of view).core (pureZ zf) view.reads setupStack input values w).run
    (Wr.start (Hk (RecStatement.name ++ iv ++ input)))).1

/-- **π2's verifier accepts the run of the honest prover's stream**: over a pure permutation `F` (Keccak-256 `Hk`), at
the seed of the IV and the public input, `runWith` returns the arithmetic on the prover's inputs, nothing of the stream
left; the stream is the public values, `W`'s and `Q`'s roots' words and answers and the values' scalars; the trees are
the stacks' commitments. -/
theorem runWith_honest (Hk : List UInt8 → Digest) (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E)
    (view : Circuit) (setupStack : Array K) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (hmatch : List.Forall₂ ReadMatch view.reads values) (hrow : view.logRow = G.logW) :
    let o := proverOut Hk G zf view setupStack iv input values w
    ∃ r, (Pi2H.runWithH (m := Id) (Pure.pure ∘ Hk) (Spec.of view) iv input o.stream).result = .ok r ∧
      r.inputs = o.inputs ∧ r.scalars = o.inputs.scalars ∧ r.out = (Spec.of view).core.run r.inputs ∧
      r.oods = (pi2OodAt o.wStack (zf (stackVars G.logN).1 o.wTree.root), pi2OodAt o.qStack (zf (stackVars G.logN).2.1 o.qTree.root)) ∧
      o.stream.toList = publicWire (view.reads.zip values) ++ rootWord (UniStatement.rootHalves o.wTree.root) ++
          scalarWire (pi2OodAt o.wStack (zf (stackVars G.logN).1 o.wTree.root)) ++
          rootWord (UniStatement.rootHalves o.qTree.root) ++
          scalarWire (pi2OodAt o.qStack (zf (stackVars G.logN).2.1 o.qTree.root)) ++
          (o.inputs.a ++ [o.inputs.ξ, o.inputs.s]).flatMap scalarWire ∧
      o.wTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (stackVars G.logN).1 o.wStack ∧
      o.qTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (stackVars G.logN).2.1 o.qStack ∧
      o.inputs = ⟨publicScalarsOf input values, o.inputs.α, o.inputs.β, o.inputs.γ, o.inputs.t,
          foldValues G.logN G.logW (wTableB G w) o.inputs.t, xiOf G.logN setupStack o.inputs.β o.inputs.t,
          sOf G.logN (pNovel G w) o.inputs.t, o.inputs.ρ⟩ ∧
      o.wStack = padStack (stackVars G.logN).1 (fun i ↦ (wTableB G w).getD i 0) ∧
      o.qStack = padStack (stackVars G.logN).2.1 (qEntry G.logN (hNovel G w o.inputs.α o.inputs.β)
          (qNovel G w o.inputs.α o.inputs.β o.inputs.γ
            (phiOn (Spec.of view).core (publicScalarsOf input values) o.inputs.γ))
          (pNovel G w) (qpNovel G w o.inputs.γ)) := by
  intro o
  set seed := Hk (RecStatement.name ++ iv ++ input) with hseed
  obtain ⟨r, b, pos', w', zs, ⟨hp, -, hv⟩, hpos, hstream, hinp, hsc, hout, hoods, hws, hwt, hqt, hi, hwsk, hqsk, -, -⟩ :=
    reduce_steps Hk G zf view setupStack input values w seed hmatch hrow
  have hb : o = b := by
    show proverOut Hk G zf view setupStack iv input values w = b
    unfold proverOut
    rw [← hseed, hp]
  rw [hb]
  refine ⟨r, ?_, hinp, hsc, hout, hoods, by rw [hstream, hws], hwt, hqt, hi, hwsk, hqsk⟩
  have e := hv b.stream #[] (by rw [hstream])
  rw [← UniKeccakComplete.chan_start_eq] at e
  unfold Pi2H.runWithH
  show (((do
      let r ← Pi2H.reduceWithH (m := Id) (Pure.pure ∘ Hk) (Spec.of view) (UniStatement.publicWordsOf input)
      UniStatement.finish (m := Id)
      return r : UniStatement.ChanM Id RecStatement.Reduced).run).run (UniStatement.Chan.start seed b.stream)).1 = _
  rw [UniKeccakComplete.chan_run_bind, e]
  dsimp only
  rw [UniKeccakComplete.chan_run_bind]
  have hf : (UniStatement.finish (m := Id)).run.run (UniKeccakComplete.chanAt b.stream pos' w' (#[] ++ zs.toArray)) =
      (.ok (), UniKeccakComplete.chanAt b.stream pos' w' (#[] ++ zs.toArray)) := by
    have hc : pos' = b.stream.size := by rw [hpos, hstream]
    simp only [UniStatement.finish, UniKeccakComplete.chan_run_bind, UniKeccakComplete.chan_run_get, UniKeccakComplete.chanAt, hc,
      ↓reduceIte]
    rfl
  rw [hf]
  rfl

/-- **The honest prover's out-of-domain points** are the point function's at its roots. -/
theorem proverOut_points (Hk : List UInt8 → Digest) (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E)
    (view : Circuit) (setupStack : Array K) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (hmatch : List.Forall₂ ReadMatch view.reads values) (hrow : view.logRow = G.logW) :
    let o := proverOut Hk G zf view setupStack iv input values w
    o.wPoint = zf (stackVars G.logN).1 o.wTree.root ∧ o.qPoint = zf (stackVars G.logN).2.1 o.qTree.root := by
  intro o
  obtain ⟨r, b, pos', w', zs, ⟨hp, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, hwp, hqp⟩ :=
    reduce_steps Hk G zf view setupStack input values w (Hk (RecStatement.name ++ iv ++ input)) hmatch hrow
  have hb : o = b := by
    show proverOut Hk G zf view setupStack iv input values w = b
    unfold proverOut
    rw [hp]
  rw [hb]
  exact ⟨hwp, hqp⟩

end RecCompose.Pi2S

/-- info: 'RecCompose.Pi2S.reduce_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2S.reduce_steps

/-- info: 'RecCompose.Pi2S.runWith_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2S.runWith_honest

/-- info: 'RecCompose.Pi2S.proverOut_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2S.proverOut_points
