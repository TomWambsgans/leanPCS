-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/SyncVerifier.lean`.
import UniKeccakComplete.K.SyncTable
import UniComplete.DomainCount
import UniKeccakComplete.K.Honest

/-!
# The Keccak verifier reads back the honest prover's stream

At a pure Keccak-256 `H` (`Id`, `pure ∘ H`), `reduceWithKH … keccakMain .point` run on the stream `proveStreamWith`
writes from the seed reads every message the prover wrote and draws the same challenges, in `reduceWithK`'s order:

0. the six counts (`countBits_reads`: the counts, their bits `countBitsOf`, their range checks `countChecks`
   collected); 1. `C1`'s root (`nextRoot_reads`: the halves without top limbs, `rootRead`); `α ∈ E^4`
   (`drawRunH .main` = `samplesH`, `drawRunH_main`), `β`, `γ` (`Steps.samples`, `Steps.sample`); 2. Flock on the
   Keccak-f block (the hypothesis `FlockSyncs`, against `verifyWalkedKH`: one value collected, the lincheck's
   terminal `zero` at the writer where Flock starts, `flockWriterOf`; its end is a ring switch's,
   `verifyWalkedKH_end`); 3. `C2`'s root; `t`; 4. the values at `t` (each table's through `tablePart`, as `atTOf`
   runs it on its own bytes: `tablesLoop_reads` over `tablesKeccak`; the memory's three, the bytecode's two, `T(t)`,
   `Q_W(t)`: `tailAtT`, `atTOf_values`); 5.–7. the pure `constraintRelationK`, `heapRelations` and Flock's ring
   term: the verifier's relations and `C2`'s columns are `atTOf`'s (both unfold to the same terms once `atTOf`'s
   loop is a fold, `atTLoop_eq`, `atTFold_snd`, and the active rows' polynomials agree, `countBits_zip_map`); 8. `ρ`,
   the combined claims (the prover's `combined`); the batching sumcheck (the hypothesis `BatchSyncsAt`: `BatchSyncs`
   against `batchKH .main` at the prover's state when the batch starts, `frontOf`); `finish`.

Headline theorems:

* `reduce_steps`: the joint steps, with the run's ends: the openings are the prover's point claims (`pointOpening`,
  in the combined claims' order), no matrices' claim, the roots its halves (`rootRead`), the position the end of the
  prover's final stream, the collected values the counts' checks, Flock's value, then the batch's terminal.
* `runWithKH_syncs`: `runWithKH` returns `.ok R` with those `R`, its channel at the end of the prover's stream
  (`finish` succeeded) with the prover's final sponge and challenges.
* `runWithKH_accepts`: the verdict is `true` when Flock's value and the batch's terminal are zero (the counts'
  checks vanish: `countChecks_zero`, from `RowsFit`).

Against the BLAKE2s VM's file: no `Blake2s` switch (the prover always runs Flock, at `keccakMain`), no pending
matrices (`Reduced.matrices = none`), Flock collects one value, three openings downstream.

Decisions:

* **`StepsE`** (the ends existential) is what the main proofs step: a `Steps` whose result, prover result, position,
  writer and collected values are only known at the end, the property `K` accumulating the collected values. Step
  lemmas are applied to the unfolded `reduceWithKH`/`proveStreamWith` (`apply`, the loop bodies unified from the
  goal), the intermediate values named by `set` (let-bound, so defeq to what `frontOf` computes).
* **`frontOf`** restates the prover's steps 0–8 as a pure function of the writer, in the step lemmas' normal forms
  (`Wr.append`, `Wr.sampled`, `samplesW`'s run, Flock's run), so that `BatchSyncsAt` names the batch's inputs and
  the writer where it starts: the downstream algebra reads them off `frontOf`. `flockWriterOf` is the writer where
  Flock starts (`frontOf_flockOut`).
* `BatchSyncs` and `FlockSyncs` take their collected values as functions of the writer: their provers prove the
  read-back, the algebra that they vanish (`runWithKH_accepts`'s `hzero`, `hterm`).
* The matches the verifier and `atTOf` take on Flock's end are reduced by `fo.end_ = .ring map target`
  (`verifyWalkedKH_end`, from `FlockSyncs`' run), never by unfolding the Flock prover.
-/

namespace UniKeccakComplete

open UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## More steps -/

namespace Steps

variable {α β γ δ : Type}

/-- **A verifier-only read at a known place of the writer's stream**: the stream is `P ++ B ++ Q`, the verifier at
`P`'s end reads `B`. -/
theorem vread {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos2 : ℕ} {w w2 : Wr}
    {P B Q : List UInt8} {a : α} {c : γ} {d : δ} {zs1 zs2 : List E}
    (h1 : Reads v B a zs1) (hw : w.stream.toList = P ++ (B ++ Q))
    (h2 : Steps (f a) p (P.length + B.length) w c d pos2 w2 zs2) :
    Steps (v >>= f) p P.length w c d pos2 w2 (zs1 ++ zs2) := by
  refine vbind h1 ?_ ?_ h2
  · have := congrArg List.length hw
    simp only [List.length_append, Array.length_toList] at this
    omega
  · rw [hw, List.drop_left]
    exact List.prefix_append _ _

/-- **A verifier-only read of the last bytes written**: the writer is `w.append B`, the verifier at `w`'s end. -/
theorem vreadEnd {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos2 : ℕ} {w w2 : Wr} {B : List UInt8}
    {a : α} {c : γ} {d : δ} {zs1 zs2 : List E} (h1 : Reads v B a zs1)
    (h2 : Steps (f a) p (w.stream.size + B.length) (w.append B) c d pos2 w2 zs2) :
    Steps (v >>= f) p w.stream.size (w.append B) c d pos2 w2 (zs1 ++ zs2) :=
  vread (P := w.stream.toList) (Q := []) h1 (by simp) h2

/-- **A verifier-only read, the bytes left after `pos` known**: they start with `B`, the read's; the continuation
knows the rest. -/
theorem vreadD {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {B R : List UInt8}
    {a : α} {c : γ} {d : δ} {zs1 zs2 : List E} (h1 : Reads v B a zs1) (hpos : pos ≤ w.stream.size)
    (hd : w.stream.toList.drop pos = B ++ R)
    (h2 : w.stream.toList.drop (pos + B.length) = R → Steps (f a) p (pos + B.length) w c d pos2 w2 zs2) :
    Steps (v >>= f) p pos w c d pos2 w2 (zs1 ++ zs2) := by
  refine vbind h1 hpos (by rw [hd]; exact List.prefix_append _ _) (h2 ?_)
  rw [← List.drop_drop, hd, List.drop_left]

/-- **The next scalar**, the scalars left after `pos` known. -/
theorem vscalarD {f : E → ChanM Id γ} {p : WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {x : E} {xs : List E} {c : γ}
    {d : δ} {zs : List E} (hd : w.stream.toList.drop pos = (x :: xs).flatMap scalarWire)
    (h2 : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire → Steps (f x) p (pos + 24) w c d pos2 w2 zs) :
    Steps (nextScalar (m := Id) >>= f) p pos w c d pos2 w2 zs := by
  have hpos : pos ≤ w.stream.size := by
    by_contra hlt
    have h0 : w.stream.toList.drop pos = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [h0, List.flatMap_cons] at hd
    have := congrArg List.length hd
    simp at this
    omega
  have h := vreadD (nextScalar_reads x) hpos (by rw [hd, List.flatMap_cons]) (by simpa using h2)
  simpa using h

/-- The verifier's start position, rewritten. -/
theorem pos_start {v : ChanM Id α} {p : WrM Id β} {pos pos0 pos' : ℕ} {w w' : Wr} {a : α} {b : β} {zs : List E}
    (e : pos = pos0) (h : Steps v p pos0 w a b pos' w' zs) : Steps v p pos w a b pos' w' zs := by
  subst e; exact h

/-- **A commitment on the prover's side** (`StateT.lift` in `Id`): no byte written. -/
theorem plift {v : ChanM Id α} {x : Id β} {g : β → WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {c : α} {d : δ}
    {zs : List E} (h : Steps v (g x) pos w c d pos2 w2 zs) :
    Steps v ((StateT.lift x : WrM Id β) >>= g) pos w c d pos2 w2 zs := h

/-- The prover's result mapped (`f <$> p`). -/
theorem pmap {v : ChanM Id α} {p : WrM Id β} {g : β → δ} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β}
    {zs : List E} (h : Steps v p pos w a b pos' w' zs) : Steps v (g <$> p) pos w a (g b) pos' w' zs := by
  obtain ⟨p1, m1, e1⟩ := h
  refine ⟨?_, m1, e1⟩
  show (g (p.run w).1, (p.run w).2) = _
  rw [p1]

/-- `get` on the prover's side. -/
theorem pget {v : ChanM Id α} {g : Wr → WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {c : α} {d : δ} {zs : List E}
    (h : Steps v (g w) pos w c d pos2 w2 zs) : Steps v ((get : WrM Id Wr) >>= g) pos w c d pos2 w2 zs := h

/-- Both sides one after the other, the first from the end of the stream (`pos` rewritten to it). -/
theorem bind_pos {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 pos2 : ℕ}
    {w w1 w2 : Wr} {a : α} {b : β} {c : γ} {d : δ} {zs1 zs2 : List E} (e : pos = w.stream.size)
    (h1 : Steps v p w.stream.size w a b pos1 w1 zs1) (h2 : Steps (f a) (g b) pos1 w1 c d pos2 w2 zs2) :
    Steps (v >>= f) (p >>= g) pos w c d pos2 w2 (zs1 ++ zs2) := by
  subst e; exact h1.bind h2

/-- A pure first action on the verifier's side. -/
theorem vpure {f : α → ChanM Id γ} {p : WrM Id δ} {x : α} {pos pos2 : ℕ} {w w2 : Wr} {c : γ} {d : δ}
    {zs : List E} (h : Steps (f x) p pos w c d pos2 w2 zs) : Steps ((Pure.pure x : ChanM Id α) >>= f) p pos w c d pos2 w2 zs :=
  h

/-- The verifier's two pure ends, as one. -/
theorem vite {b : Bool} {R1 R2 : α} {p : WrM Id δ} {pos pos' : ℕ} {w w' : Wr} {d : δ} {zs : List E}
    (h : Steps (Pure.pure (if b = true then R1 else R2) : ChanM Id α) p pos w (if b = true then R1 else R2) d pos' w'
      zs) :
    Steps (if b = true then (Pure.pure R1 : ChanM Id α) else Pure.pure R2) p pos w (if b = true then R1 else R2) d
      pos' w' zs := by
  cases b
  · exact h
  · exact h

/-- The prover's program, rewritten. -/
theorem prog_eq {v : ChanM Id α} {p p' : WrM Id β} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β} {zs : List E}
    (e : p = p') (h : Steps v p' pos w a b pos' w' zs) : Steps v p pos w a b pos' w' zs := by
  subst e; exact h

/-- The verifier's first action, rewritten. -/
theorem bind_veq {v v' : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 pos2 : ℕ}
    {w w1 w2 : Wr} {a : α} {b : β} {c : γ} {d : δ} {zs1 zs2 : List E} (e : v = v')
    (h1 : Steps v' p pos w a b pos1 w1 zs1) (h2 : Steps (f a) (g b) pos1 w1 c d pos2 w2 zs2) :
    Steps (v >>= f) (p >>= g) pos w c d pos2 w2 (zs1 ++ zs2) := by
  subst e; exact h1.bind h2

end Steps

/-! ## Steps with their ends unnamed -/

/-- **`Steps` with its ends unnamed**: some result, prover result, end position, writer and collected values,
satisfying `K`. -/
def StepsE {α β : Type} (v : ChanM Id α) (p : WrM Id β) (pos : ℕ) (w : Wr)
    (K : α → β → ℕ → Wr → List E → Prop) : Prop :=
  ∃ a b pos' w' zs, Steps v p pos w a b pos' w' zs ∧ K a b pos' w' zs

namespace StepsE

variable {α β γ δ : Type}

theorem pure {a : α} {b : β} {pos : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop} (h : K a b pos w []) :
    StepsE (Pure.pure a : ChanM Id α) (Pure.pure b : WrM Id β) pos w K :=
  ⟨a, b, pos, w, [], Steps.pure a b pos w, h⟩

theorem bind_pos {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 : ℕ}
    {w w1 : Wr} {a : α} {b : β} {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (e : pos = w.stream.size)
    (h1 : Steps v p w.stream.size w a b pos1 w1 zs1)
    (h2 : StepsE (f a) (g b) pos1 w1 (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.bind_pos e h1 hs, hq⟩

theorem bind_veq {v v' : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 : ℕ}
    {w w1 : Wr} {a : α} {b : β} {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (e : v = v')
    (h1 : Steps v' p pos w a b pos1 w1 zs1)
    (h2 : StepsE (f a) (g b) pos1 w1 (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.bind_veq e h1 hs, hq⟩

theorem vread {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {w : Wr} {P B Q : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1) (hw : w.stream.toList = P ++ (B ++ Q))
    (h2 : StepsE (f a) p (P.length + B.length) w (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p P.length w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vread h1 hw hs, hq⟩

theorem vreadEnd {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {w : Wr} {B : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1)
    (h2 : StepsE (f a) p (w.stream.size + B.length) (w.append B) (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p w.stream.size (w.append B) K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vreadEnd h1 hs, hq⟩

theorem vreadD {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos : ℕ} {w : Wr} {B R : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1) (hpos : pos ≤ w.stream.size)
    (hd : w.stream.toList.drop pos = B ++ R)
    (h2 : w.stream.toList.drop (pos + B.length) = R →
      StepsE (f a) p (pos + B.length) w (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p pos w K := by
  have hd' : w.stream.toList.drop (pos + B.length) = R := by rw [← List.drop_drop, hd, List.drop_left]
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2 hd'
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vreadD h1 hpos hd (fun _ ↦ hs), hq⟩

theorem vscalarD {f : E → ChanM Id γ} {p : WrM Id δ} {pos : ℕ} {w : Wr} {x : E} {xs : List E}
    {K : γ → δ → ℕ → Wr → List E → Prop} (hd : w.stream.toList.drop pos = (x :: xs).flatMap scalarWire)
    (h2 : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire → StepsE (f x) p (pos + 24) w K) :
    StepsE (nextScalar (m := Id) >>= f) p pos w K := by
  have hd' : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire := by
    rw [← List.drop_drop, hd, List.flatMap_cons, show 24 = (scalarWire x).length by simp, List.drop_left]
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2 hd'
  exact ⟨c, d, p2, w2, z2, Steps.vscalarD hd (fun _ ↦ hs), hq⟩

theorem pos_start {v : ChanM Id α} {p : WrM Id β} {pos pos0 : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop}
    (e : pos = pos0) (h : StepsE v p pos0 w K) : StepsE v p pos w K := by
  subst e; exact h

theorem pbind {v : ChanM Id α} {p : WrM Id β} {g : β → WrM Id δ} {pos : ℕ} {w : Wr} {B : List UInt8} {b : β}
    {K : α → δ → ℕ → Wr → List E → Prop} (h1 : Writes p w b B) (h2 : StepsE v (g b) pos (w.append B) K) :
    StepsE v (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, z2, Steps.pbind h1 hs, hq⟩

theorem plift {v : ChanM Id α} {x : Id β} {g : β → WrM Id δ} {pos : ℕ} {w : Wr}
    {K : α → δ → ℕ → Wr → List E → Prop} (h : StepsE v (g x) pos w K) :
    StepsE v ((StateT.lift x : WrM Id β) >>= g) pos w K := h

theorem pget {v : ChanM Id α} {g : Wr → WrM Id δ} {pos : ℕ} {w : Wr} {K : α → δ → ℕ → Wr → List E → Prop}
    (h : StepsE v (g w) pos w K) : StepsE v ((get : WrM Id Wr) >>= g) pos w K := h

theorem vpure {f : α → ChanM Id γ} {p : WrM Id δ} {x : α} {pos : ℕ} {w : Wr} {K : γ → δ → ℕ → Wr → List E → Prop}
    (h : StepsE (f x) p pos w K) : StepsE ((Pure.pure x : ChanM Id α) >>= f) p pos w K := h

theorem ppure {v : ChanM Id α} {g : β → WrM Id δ} {x : β} {pos : ℕ} {w : Wr} {K : α → δ → ℕ → Wr → List E → Prop}
    (h : StepsE v (g x) pos w K) : StepsE v ((Pure.pure x : WrM Id β) >>= g) pos w K := h

theorem prog_eq {v : ChanM Id α} {p p' : WrM Id β} {pos : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop}
    (e : p = p') (h : StepsE v p' pos w K) : StepsE v p pos w K := by
  subst e; exact h

theorem vite {b : Bool} {R1 R2 : α} {p : WrM Id δ} {pos : ℕ} {w : Wr} {K : α → δ → ℕ → Wr → List E → Prop}
    (h : StepsE (Pure.pure (if b = true then R1 else R2) : ChanM Id α) p pos w K) :
    StepsE (if b = true then (Pure.pure R1 : ChanM Id α) else Pure.pure R2) p pos w K := by
  cases b
  · exact h
  · exact h

end StepsE

/-- The rows loop writes the counts (`proveStreamWith`, step 0). -/
theorem rows_writes (rows : List ℕ) (body : ℕ → PUnit → WrM Id (ForInStep PUnit))
    (hbody : ∀ n s, body n s = (sendInteger (m := Id) n 4 >>= fun _ ↦ Pure.pure (ForInStep.yield PUnit.unit)))
    (w : Wr) : Writes (ForIn.forIn rows PUnit.unit body) w PUnit.unit (rows.flatMap fun n ↦ integerWire n 4) := by
  have h := Writes.forIn (fun _ _ ↦ PUnit.unit) (fun _ n ↦ integerWire n 4) body rows (fun n _ s w ↦ by
    rw [hbody]
    exact ((sendInteger_writes n 4 w).bind (g := fun _ ↦ Pure.pure (ForInStep.yield PUnit.unit))
      (Writes.pure _ _)).congr rfl (List.append_nil _)) PUnit.unit w
  rw [loopBytes_const] at h
  exact h

/-! ## Flock's end is a ring switch's -/

theorem err_ne_ok {α : Type} {e : UniError} {a : α} {c c' : Chan} :
    ((.error e, c) : Except UniError α × Chan) ≠ (.ok a, c') := by
  intro h; cases h

/-- `ringEndH` ends with a ring switch's map and target. -/
theorem ringEndH_ring (H : List UInt8 → Digest) (variant : Flock.Variant) (s : List E) (c : Chan) (e : Flock.End)
    (c' : Chan) (h : (Flock.ringEndH (m := Id) (Pure.pure ∘ H) variant s).run.run c = (.ok e, c')) :
    ∃ map target, e = .ring map target := by
  unfold Flock.ringEndH at h
  rw [chan_run_bind] at h
  generalize (samplesH (m := Id) (Pure.pure ∘ H) UniStatement.Flock.ringMapShifts.length).run.run c = r at h
  rcases r with ⟨r, c1⟩
  cases r with
  | error err => exact absurd h err_ne_ok
  | ok map =>
    cases h
    exact ⟨_, _, rfl⟩

/-- **`verifyWalkedKH`'s end, when it returns, is a ring switch's.** -/
theorem verifyWalkedKH_end (H : List UInt8 → Digest) (logN : ℕ) (v : UniKeccak.KeccakVariant) (c : Chan)
    {pt : List E} {e : Flock.End} {c' : Chan}
    (h : (verifyWalkedKH (m := Id) (Pure.pure ∘ H) logN v).run.run c = (.ok (pt, e), c')) :
    ∃ map target, e = .ring map target := by
  unfold verifyWalkedKH at h
  rw [chan_run_bind] at h
  generalize (frontKH (m := Id) (Pure.pure ∘ H) logN v).run.run c = r at h
  rcases r with ⟨r, c1⟩
  cases r with
  | error err => exact absurd h err_ne_ok
  | ok fr =>
    dsimp only at h
    rw [chan_run_bind] at h
    generalize (requireZero (m := Id) _).run.run c1 = r1 at h
    rcases r1 with ⟨r1, c2⟩
    cases r1 with
    | error err => exact absurd h err_ne_ok
    | ok u =>
      dsimp only at h
      rw [chan_run_bind] at h
      generalize hr : (Flock.ringEndH (m := Id) (Pure.pure ∘ H) v.flock (fr.slices.getD [])).run.run c2 = r2 at h
      rcases r2 with ⟨r2, c3⟩
      cases r2 with
      | error err => exact absurd h err_ne_ok
      | ok e' =>
        cases h
        exact ringEndH_ring H _ _ c2 _ _ hr

/-- **Flock's prover, synchronising, ends with a ring switch** (its map and target). -/
theorem flock_ring {H : List UInt8 → Digest} {flock : FlockProver Id} {logN : ℕ} {v : UniKeccak.KeccakVariant}
    {q : Array K} {zero : Wr → E} (hflock : FlockSyncs H flock logN v q zero) (w : Wr) :
    ∃ map target, ((flock logN v q).run w).1.end_ = .ring map target :=
  verifyWalkedKH_end H _ _ _ (((hflock w).steps).2.2 _ #[] (List.prefix_refl _))

/-! ## The values at `t`, as `atTOf` sends them -/

section AtT

variable (tr : Trace) (c2 : C2Data) (alphas : List E) (beta t : E)

/-- The digits at `t` (`reduceWithK`'s `w`). -/
def wOf : List E := digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2)

/-- The memory's column `k` at `t`. -/
def memAtT (k : ℕ) : E :=
  evalB ((bCoefficients tr.shape.logMemory (tr.memory.getD k #[])).map ofK) tr.shape.logMemory (wOf tr t)

/-- The addresses at `t`. -/
def addressAtT : E :=
  evalB ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).map ofK) tr.shape.logMemory (wOf tr t)

/-- The memory's pull fingerprint at `t`. -/
def memoryPullAtT : E :=
  memoryFp (eqKernel alphas) beta (addressAtT tr t) (memAtT tr t 3) ((List.range 3).map (memAtT tr t))

/-- The bytecode's final counts at `t`. -/
def bytecodeFinalAtT : E :=
  evalB ((bCoefficients tr.shape.logBytecode tr.bytecodeFinal).map ofK) tr.shape.logBytecode (wOf tr t)

/-- The bytecode's pull fingerprint at `t`. -/
def bytecodePullAtT : E :=
  bytecodeFp (eqKernel alphas) beta fun s ↦ if s = 2 then bytecodeFinalAtT tr t else
    evalB ((bCoefficients tr.shape.logBytecode (tr.slots.getD s #[])).map ofK) tr.shape.logBytecode (wOf tr t)

/-- `T(t)`. -/
def heapAtT : E := evalB c2.heapB tr.shape.heap.h (wOf tr t)

/-- `Q_W(t)`. -/
def constraintAtT : E :=
  ((c2.constraintChunks.zip c2.constraintSizes).foldl (fun (acc : E × E) (x : Array E × ℕ) ↦
    (acc.1 + acc.2 * evalB x.1 x.2 (wOf tr t), acc.2 * (wOf tr t).getD x.2 0)) (0, 1)).1

/-- **The values after the tables'**: the memory's three, the bytecode's two, `T(t)`, `Q_W(t)`. -/
def tailAtT : List E :=
  [memAtT tr t 3, addressAtT tr t, memoryPullAtT tr alphas beta t, bytecodeFinalAtT tr t,
    bytecodePullAtT tr alphas beta t, heapAtT tr c2 t, constraintAtT tr c2 t]

/-- **What the prover sends at `t`**: every table's values (`tvals`), then `tailAtT`. -/
theorem atTOf_values (gamma : E) (fo : Option FlockOut) :
    (atTOf tr c2 alphas beta gamma t fo).values =
      tablesKeccak.flatMap (tvals tr (eqKernel alphas) beta (wOf tr t)) ++ tailAtT tr c2 alphas beta t := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rw [pure_bind]
  have hL := atTFold_fst tr (eqKernel alphas) beta (wOf tr t) tablesKeccak (#[], #[], #[])
  rcases fo with _ | out
  · dsimp only
    rw [hL]
    simp [tailAtT, memAtT, addressAtT, memoryPullAtT, bytecodeFinalAtT, bytecodePullAtT, heapAtT, constraintAtT, wOf]
    rfl
  · dsimp only
    rcases out.end_ with ⟨map, target⟩ | ⟨ws, value⟩
    all_goals
      dsimp only
      rw [hL]
      simp [tailAtT, memAtT, addressAtT, memoryPullAtT, bytecodeFinalAtT, bytecodePullAtT, heapAtT, constraintAtT, wOf]
      rfl

/-- **The ring map `atTOf` leaves**, Flock's end a ring switch's. -/
theorem atTOf_ringMap (gamma : E) (fo : FlockOut) {map : List E} {target : E} (h : fo.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some fo)).ringMap = some map := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rw [pure_bind, h]
  rfl

end AtT

/-- The active rows' vanishing polynomials from the counts' bits the verifier reads are the prover's. -/
theorem countBits_zip_map (w : List E) : ∀ (rows heights : List ℕ), rows.length = heights.length →
    ((countBitsOf rows heights).zip heights).map (fun x ↦ activeVanishingFromBits w x.1 x.2) =
      (rows.zip heights).map (fun x ↦
        activeVanishingFromBits w ((List.range (x.2 + 1)).map fun b ↦ intBits x.1 b 1) x.2)
  | [], [], _ => rfl
  | n :: rows, r :: heights, h => by
    simp only [countBitsOf, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons]
    rw [← countBitsOf, countBits_zip_map w rows heights (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `batchKH`'s inputs, rewritten. -/
theorem batchKH_congr (H : List UInt8 → Digest) {fs1 fs2 : FsShape} {c1 c2 : List (Commitment × Combined)}
    {l1 l2 : List (Commitment × StackLayout)} (r : Option (List E)) (hf : fs1 = fs2) (hc : c1 = c2)
    (hl : l1 = l2) :
    batchKH (m := Id) (Pure.pure ∘ H) fs1 c1 l1 r = batchKH (m := Id) (Pure.pure ∘ H) fs2 c2 l2 r := by
  subst hf hc hl; rfl

/-! ## The prover's state when the batching sumcheck starts -/

/-- **The prover's state when the batching sumcheck starts** (`proveStreamWith`, steps 0–8): `C1`'s stack and
commitment, `α β γ`, Flock's output, `C2`'s data and commitment, `t`, the values and relations at `t`, `ρ`, the
combined claims, the stacks' layouts, the setup's stack. -/
structure FrontOut where
  stack1 : Array K
  committed1 : Committed
  alphas : List E
  beta : E
  gamma : E
  flockOut : Option FlockOut
  c2 : C2Data
  committed2 : Committed
  t : E
  atT : AtT
  rho : E
  combined : List (Commitment × Combined)
  stackLayouts : List (Commitment × StackLayout)
  stack3 : Array K

/-- Three stacks as a function of the commitment. -/
def stacksOf (s1 s2 s3 : Array K) : Commitment → Array K := fun c ↦
  match c with
  | .c1 => s1
  | .c2 => s2
  | .setup => s3

/-- The three stacks (`proveStreamWith`'s `stackOf`). -/
def FrontOut.stackOf (F : FrontOut) : Commitment → Array K := stacksOf F.stack1 F.c2.stack F.stack3

section Front

variable (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)

/-- **The writer where Flock starts** (`proveStreamWith`'s steps 0–1, at `Id` with `pure ∘ H`, from `w0`): the
counts and `C1`'s root written, `α β γ` drawn. Flock's collected value (`FlockSyncs`' `zero`) is taken here. -/
def flockWriterOf (tr : Trace) (w0 : Wr) : Wr :=
  let shape := tr.shape
  let w1 := w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)
  let stack1 := c1Stack tr
  let committed1 : Committed := commit .c1 (UniKeccak.c1LayoutK shape).vars stack1
  let w2 := w1.append (rootWord committed1.halves)
  let w3 := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).2
  let w4 := (Wr.sampled H w3).2
  (Wr.sampled H w4).2

/-- **The prover's run up to `ρ`** (`proveStreamWith`'s steps 0–8, at `Id` with `pure ∘ H`), from the writer `w0`:
its state, and the writer when the batching sumcheck starts. -/
def frontOf (tr : Trace) (w0 : Wr) : FrontOut × Wr :=
  let shape := tr.shape
  let w1 := w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)
  let stack1 := c1Stack tr
  let committed1 : Committed := commit .c1 (UniKeccak.c1LayoutK shape).vars stack1
  let w2 := w1.append (rootWord committed1.halves)
  let alphas := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).1
  let w3 := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).2
  let beta := (Wr.sampled H w3).1
  let w4 := (Wr.sampled H w3).2
  let gamma := (Wr.sampled H w4).1
  let w5 := (Wr.sampled H w4).2
  let logN := keccakR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut := some ((flock logN UniKeccak.keccakMain tr.qflock).run w5).1
  let w6 := ((flock logN UniKeccak.keccakMain tr.qflock).run w5).2
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((UniKeccak.layoutsOfK shape).lookup .c2).getD default).vars c2.stack
  let w7 := w6.append (rootWord committed2.halves)
  let t := (Wr.sampled H w7).1
  let w8 := (Wr.sampled H w7).2
  let a := atTOf tr c2 alphas beta gamma t flockOut
  let w9 := w8.append (a.values.flatMap scalarWire)
  let rho := (Wr.sampled H w9).1
  let w10 := (Wr.sampled H w9).2
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := UniKeccak.layoutsK shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, flockOut, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, w10)

/-- Flock's output in `frontOf` is the Flock prover's run from `flockWriterOf`. -/
theorem frontOf_flockOut (tr : Trace) (w0 : Wr) :
    (frontOf H commit flock tr w0).1.flockOut = some ((flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0)
      UniKeccak.keccakMain tr.qflock).run (flockWriterOf H commit tr w0)).1 := rfl

/-- **The batching sumcheck's hypothesis at the prover's state** (`BatchSyncs` at `frontOf`'s): the combined claims,
the layouts, the stacks, the ring map. -/
def BatchSyncsAt (tr : Trace) (seed : Digest) (terminal : Wr → E) : Prop :=
  BatchSyncs H (frontOf H commit flock tr (Wr.start seed)).1.combined
    (frontOf H commit flock tr (Wr.start seed)).1.stackLayouts
    (frontOf H commit flock tr (Wr.start seed)).1.stackOf
    (frontOf H commit flock tr (Wr.start seed)).1.atT.ringMap terminal

end Front

/-- `drawRunH` on the main line is `samplesH`. -/
theorem drawRunH_main (H : List UInt8 → Digest) (n : ℕ) :
    drawRunH (m := Id) (Pure.pure ∘ H) UniKeccak.keccakMain.fs n = samplesH (m := Id) (Pure.pure ∘ H) n := rfl

set_option maxHeartbeats 4000000 in
/-- **The joint steps of the main line**: `reduceWithKH … keccakMain .point` against `proveStreamWith`, from the
seed, with the run's ends. -/
theorem reduce_steps (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (seed : Digest) (hvalid : tr.shape.validate true = true)
    (hlen : tr.rows.length = tr.shape.heights.length) (h32 : ∀ n ∈ tr.rows, n < 2 ^ 32) (zero : Wr → E)
    (hflock : FlockSyncs H flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain
      tr.qflock zero)
    (terminal : Wr → E) (hbatch : BatchSyncsAt H commit flock tr seed terminal) :
    StepsE (reduceWithKH (m := Id) (Pure.pure ∘ H) tr.shape (publicWordsOf tr.publicInput) UniKeccak.keccakMain
        .point)
      (proveStreamWith (m := Id) (Pure.pure ∘ H) commit flock tr) 0 (Wr.start seed)
      (fun R out posF wF zs ↦ posF = wF.stream.size ∧ out.stream = wF.stream ∧
        R.openings = out.claims.map pointOpening ∧ R.matrices = none ∧
        R.roots = (rootRead out.c1.2.halves, rootRead out.c2.2.halves) ∧
        zs = countChecks tr.rows tr.shape.heights ++
          [zero (flockWriterOf H commit tr (Wr.start seed)),
            terminal (frontOf H commit flock tr (Wr.start seed)).2]) := by
  unfold reduceWithKH proveStreamWith
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, drawRunH_main]
  apply StepsE.pbind (rows_writes tr.rows _ (fun _ _ ↦ rfl) _)
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vread (P := [])
    (Q := rootWord (commit .c1 (UniKeccak.c1LayoutK tr.shape).vars (c1Stack tr)).halves)
    (countBits_reads hlen h32)
  · simp [Wr.start]
  apply StepsE.pos_start (pos0 := (tr.rows.flatMap fun n ↦ integerWire n 4).length) (by simp)
  apply StepsE.vread (Q := []) (nextRoot_reads (commit .c1 (UniKeccak.c1LayoutK tr.shape).vars (c1Stack tr)).halves)
  · simp [Wr.start]
  apply StepsE.bind_pos (h1 := Steps.samples H 4 _)
  case e => simp [Wr.start]
  set w2 := ((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
    (rootWord (commit .c1 (UniKeccak.c1LayoutK tr.shape).vars (c1Stack tr)).halves) with hw2
  set alphas := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).1 with halphas
  set w3 := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).2 with hw3
  apply StepsE.bind_pos (h1 := Steps.sample H w3)
  case e => rw [hw3, samplesW_stream]
  set beta := (Wr.sampled H w3).1 with hbeta
  set w4 := (Wr.sampled H w3).2 with hw4
  apply StepsE.bind_pos (h1 := Steps.sample H w4)
  case e => rfl
  set gamma := (Wr.sampled H w4).1 with hgamma
  set w5 := (Wr.sampled H w4).2 with hw5
  apply StepsE.bind_pos (h1 := Steps.pmap (g := some) (hflock w5).steps)
  case e => rfl
  set fo := ((flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain tr.qflock).run
    w5).1 with hfo
  set w6 := ((flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain tr.qflock).run
    w5).2 with hw6
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vreadEnd (nextRoot_reads _)
  set c2 := c2DataOf tr (eqKernel alphas) beta gamma with hc2
  set committed2 := commit .c2 (((UniKeccak.layoutsOfK tr.shape).lookup .c2).getD default).vars c2.stack
    with hcm2
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp
  set w7 := w6.append (rootWord committed2.halves) with hw7
  set t := (Wr.sampled H w7).1 with ht
  set w8 := (Wr.sampled H w7).2 with hw8
  set a := atTOf tr c2 alphas beta gamma t (some fo) with ha
  have hvals := atTOf_values tr c2 alphas beta t gamma (some fo)
  apply StepsE.pbind (sendScalars_writes _ _)
  apply StepsE.vreadD (R := (tailAtT tr c2 alphas beta t).flatMap scalarWire)
    (tablesLoop_reads tr (eqKernel alphas) beta (wOf tr t) _ ?hb tablesKeccak (#[], #[]))
  case hb => intro _ _; rfl
  case hpos => simp [hw8, ha, hvals]
  case hd => simp [hw8, ha, hvals, List.flatMap_append]
  intro hd0
  unfold tailAtT at hd0
  apply StepsE.vscalarD hd0; intro hd1
  apply StepsE.vscalarD hd1; intro hd2
  apply StepsE.vscalarD hd2; intro hd3
  apply StepsE.vscalarD hd3; intro hd4
  apply StepsE.vscalarD hd4; intro hd5
  apply StepsE.vscalarD hd5; intro hd6
  apply StepsE.vscalarD hd6; intro _
  obtain ⟨map, target, hend⟩ : ∃ map target, fo.end_ = .ring map target :=
    verifyWalkedKH_end H _ _ _ (((hflock w5).steps).2.2 w6.stream #[] (List.prefix_refl _))
  have hcond : (ClaimsMode.point == ClaimsMode.point) = true := rfl
  simp only [hend, hcond, ↓reduceIte]
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp [hw8, ha, hvals, tailAtT, List.flatMap_append]; omega
  set w9 := w8.append (a.values.flatMap scalarWire) with hw9
  set rho := (Wr.sampled H w9).1 with hrho
  set w10 := (Wr.sampled H w9).2 with hw10
  have hring : a.ringMap = some map := atTOf_ringMap tr c2 alphas beta t gamma fo hend
  simp only [hring]
  have hB := hbatch w10
  generalize hF : (frontOf H commit flock tr (Wr.start seed)).1 = F at hB
  have hFr : F.atT.ringMap = some map := by rw [← hF]; exact hring
  have hFc : F.combined = commitments.filterMap (fun c ↦ (combine a.relations c rho).map (c, ·)) := by
    rw [← hF]; rfl
  have hFl : F.stackLayouts = UniKeccak.layoutsK tr.shape a.c2Columns := by rw [← hF]; rfl
  have hFs : F.stackOf = stacksOf (c1Stack tr) c2.stack (setupStackOf tr) := by rw [← hF]; rfl
  rw [hFr, hFc, hFl, hFs] at hB
  apply StepsE.prog_eq (p' := batchProver (Pure.pure ∘ H)
    (commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)) (UniKeccak.layoutsK tr.shape a.c2Columns)
    (stacksOf (c1Stack tr) c2.stack (setupStackOf tr)) (some map) >>=
      fun cm ↦ (get : WrM Id Wr) >>= fun c ↦ Pure.pure ⟨c.stream, (c1Stack tr,
        commit .c1 (UniKeccak.c1LayoutK tr.shape).vars (c1Stack tr)), (c2.stack, committed2), setupStackOf tr, cm,
        commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·), c2.heapVals⟩)
  case e =>
    simp only [batchProver, bind_assoc, pure_bind]
    rfl
  apply StepsE.bind_veq (h1 := hB.steps)
  case e =>
    refine batchKH_congr H _ rfl ?_ ?_
    · refine congrArg (fun rels ↦ commitments.filterMap fun c ↦ (combine rels c rho).map (c, ·)) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
    · refine congrArg (UniKeccak.layoutsK tr.shape) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
  apply StepsE.pget
  apply StepsE.pure
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [List.nil_append, List.append_nil, List.cons_append]
  rfl

/-! ## The counts' checks are zero -/

/-- **The counts' range checks vanish** for counts `c ≤ 2^r`, `r ≤ 31` (the domain's `intBits_high`,
`intBits_range`). -/
theorem countChecks_zero : ∀ (rows heights : List ℕ), (∀ p ∈ rows.zip heights, p.1 ≤ 2 ^ p.2 ∧ p.2 ≤ 31) →
    ∀ z ∈ countChecks rows heights, z = 0
  | [], _, _ => by simp [countChecks]
  | _ :: _, [], _ => by simp [countChecks]
  | n :: rows, r :: heights, h => by
    intro z hz
    simp only [countChecks, List.zipWith_cons_cons, List.flatten_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    have h0 := h (n, r) (by simp)
    rcases hz with (rfl | rfl) | hz
    · exact Domain.intBits_high h0.1
    · exact Domain.intBits_range h0.1 h0.2
    · exact countChecks_zero rows heights (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) z hz

/-- Row counts that fit a shape of six heights, each at most `31` (`Shape.validate`): each `c ≤ 2^r`, `r ≤ 31`. -/
theorem rowsFit_zip {s : Shape} {rows : List ℕ} {b : Bool} (hl : s.heights.length = 6) (hv : s.validate b = true)
    (hf : s.RowsFit rows) : ∀ p ∈ rows.zip s.heights, p.1 ≤ 2 ^ p.2 ∧ p.2 ≤ 31 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  simp only [List.length_zip] at hi
  have hi1 : i < rows.length := by omega
  have hi2 : i < s.heights.length := by omega
  have h6 : i < 6 := by rw [hf.1] at hi1; exact hi1
  have hfit := (hf.2 i h6).2
  rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hfit
  simp only [Shape.validate, Bool.not_eq_true', Bool.or_eq_false_iff, List.any_eq_false, decide_eq_false_iff_not,
    not_lt] at hv
  refine ⟨by simpa using hfit, ?_⟩
  have := hv.1.2 (s.heights[i]) (List.getElem_mem hi2)
  simpa using this

/-- Counts that fit are below `2^32`. -/
theorem rows_lt_32 {s : Shape} {rows : List ℕ} {b : Bool} (hl6 : s.heights.length = 6) (hv : s.validate b = true)
    (hf : s.RowsFit rows) : ∀ n ∈ rows, n < 2 ^ 32 := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
  have hl : rows.length = s.heights.length := by rw [hf.1, hl6]
  have hz := rowsFit_zip hl6 hv hf (rows[i], s.heights[i]'(hl ▸ hi)) (by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp only [List.length_zip]; omega, by simp⟩)
  calc rows[i] ≤ 2 ^ s.heights[i]'(hl ▸ hi) := hz.1
    _ ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) hz.2
    _ < 2 ^ 32 := by norm_num

/-! ## The run on calldata -/

/-- The seed of the contract's IV and the public input, at `H`. -/
def seedAt (H : List UInt8 → Digest) (iv publicInput : List UInt8) : Digest := H (name ++ iv ++ publicInput)

/-- **The honest prover's run** from the seed (`proveStreamWith` at `pure ∘ H`): its output and its final writer. -/
def proverRun (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)
    (tr : Trace) (iv : List UInt8) : CoreOut × Wr :=
  (proveStreamWith (m := Id) (Pure.pure ∘ H) commit flock tr).run (Wr.start (seedAt H iv tr.publicInput))

/-- `runWithKH` at `pure ∘ H`: the walk and `finish` from the seed. -/
theorem runWithKH_eq (H : List UInt8 → Digest) (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    runWithKH (m := Id) (Pure.pure ∘ H) shape iv publicInput stream v mode =
      ⟨((reduceWithKH (m := Id) (Pure.pure ∘ H) shape (publicWordsOf publicInput) v mode >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).1,
        ((reduceWithKH (m := Id) (Pure.pure ∘ H) shape (publicWordsOf publicInput) v mode >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).2⟩ :=
  rfl

/-- The walk then `finish`, from steps ending at the end of the data. -/
theorem walk_finish {β : Type} {v : ChanM Id Reduced} {p : WrM Id β} {seed : Digest} {R : Reduced} {b : β}
    {posF : ℕ} {wF : Wr} {zs : List E} (h : Steps v p 0 (Wr.start seed) R b posF wF zs)
    (hpos : posF = wF.stream.size) :
    (v >>= fun r ↦ finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start seed wF.stream) =
      (.ok R, chanAt wF.stream wF.stream.size wF zs.toArray) := by
  rw [chan_run_bind, h.run_start, hpos]
  dsimp only
  rw [chan_run_bind, finish_chanAt]
  rfl

/-- **The Keccak verifier on the honest prover's stream, main line** (`keccakMain`, `PCS_OPEN`'s point claims), at a
pure Keccak-256 `H`, from a valid shape and row counts that fit, any commitment function, Flock's prover synchronising
(`FlockSyncs`, its collected value `zero`) and the batching sumcheck's (`BatchSyncsAt`, its terminal `terminal`): the
run returns `R`, its openings the prover's point claims (in the combined claims' order), no matrices' claim, its roots
the prover's halves (`rootRead`); the channel is at the end of the stream (so `finish` succeeded), synchronised with
the prover's final writer, and has collected the counts' checks, Flock's value at the writer where Flock starts, then
the batch's terminal at the writer where the batch starts. -/
theorem runWithKH_syncs (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows) (zero : Wr → E)
    (hflock : FlockSyncs H flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain
      tr.qflock zero)
    (terminal : Wr → E) (hbatch : BatchSyncsAt H commit flock tr (seedAt H iv tr.publicInput) terminal) :
    ∃ R : Reduced,
      runWithKH (m := Id) (Pure.pure ∘ H) tr.shape iv tr.publicInput (proverRun H commit flock tr iv).1.stream
          UniKeccak.keccakMain .point =
        ⟨.ok R, chanAt (proverRun H commit flock tr iv).1.stream (proverRun H commit flock tr iv).1.stream.size
          (proverRun H commit flock tr iv).2
          (countChecks tr.rows tr.shape.heights ++
            [zero (flockWriterOf H commit tr (Wr.start (seedAt H iv tr.publicInput))),
              terminal (frontOf H commit flock tr (Wr.start (seedAt H iv tr.publicInput))).2]).toArray⟩ ∧
      R.openings = (proverRun H commit flock tr iv).1.claims.map pointOpening ∧
      R.matrices = none ∧
      R.roots = (rootRead (proverRun H commit flock tr iv).1.c1.2.halves,
        rootRead (proverRun H commit flock tr iv).1.c2.2.halves) := by
  have hlen : tr.rows.length = tr.shape.heights.length := by rw [hfit.1, hvalid.1]
  obtain ⟨R, out, posF, wF, zs, hs, hpos, hstr, hop, hmat, hroot, hzs⟩ :=
    reduce_steps H commit flock tr _ hvalid.2 hlen (rows_lt_32 hvalid.1 hvalid.2 hfit) zero hflock terminal hbatch
  have hP : proverRun H commit flock tr iv = (out, wF) := hs.1
  rw [hP]
  refine ⟨R, ?_, hop, hmat, hroot⟩
  dsimp only
  rw [hstr, runWithKH_eq, walk_finish hs hpos, hzs]

/-- **The main line accepts** when Flock's collected value and the batch's terminal vanish: no error, every
collected value zero. -/
theorem runWithKH_accepts (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows) (zero : Wr → E)
    (hflock : FlockSyncs H flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain
      tr.qflock zero)
    (terminal : Wr → E) (hbatch : BatchSyncsAt H commit flock tr (seedAt H iv tr.publicInput) terminal)
    (hzero : zero (flockWriterOf H commit tr (Wr.start (seedAt H iv tr.publicInput))) = 0)
    (hterm : terminal (frontOf H commit flock tr (Wr.start (seedAt H iv tr.publicInput))).2 = 0) :
    (runWithKH (m := Id) (Pure.pure ∘ H) tr.shape iv tr.publicInput (proverRun H commit flock tr iv).1.stream
      UniKeccak.keccakMain .point).accepts = true := by
  obtain ⟨R, hrun, -⟩ := runWithKH_syncs H commit flock tr iv hvalid hfit zero hflock terminal hbatch
  rw [hrun]
  simp only [Outcome.accepts, chanAt, Bool.true_and, Array.all_eq_true', beq_iff_eq]
  intro z hz
  rw [List.mem_toArray, List.mem_append, List.mem_cons, List.mem_singleton] at hz
  rcases hz with hz | rfl | rfl
  · exact countChecks_zero _ _ (rowsFit_zip hvalid.1 hvalid.2 hfit) z hz
  · exact hzero
  · exact hterm

/-- `runWithKH_syncs` for an honest trace (`TraceHonest`: a valid shape, row counts that fit). -/
theorem runWithKH_syncs_honest (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (iv : List UInt8) (htr : TraceHonest tr) (zero : Wr → E)
    (hflock : FlockSyncs H flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) UniKeccak.keccakMain
      tr.qflock zero)
    (terminal : Wr → E) (hbatch : BatchSyncsAt H commit flock tr (seedAt H iv tr.publicInput) terminal) :
    ∃ R : Reduced,
      runWithKH (m := Id) (Pure.pure ∘ H) tr.shape iv tr.publicInput (proverRun H commit flock tr iv).1.stream
          UniKeccak.keccakMain .point =
        ⟨.ok R, chanAt (proverRun H commit flock tr iv).1.stream (proverRun H commit flock tr iv).1.stream.size
          (proverRun H commit flock tr iv).2
          (countChecks tr.rows tr.shape.heights ++
            [zero (flockWriterOf H commit tr (Wr.start (seedAt H iv tr.publicInput))),
              terminal (frontOf H commit flock tr (Wr.start (seedAt H iv tr.publicInput))).2]).toArray⟩ ∧
      R.openings = (proverRun H commit flock tr iv).1.claims.map pointOpening ∧
      R.matrices = none ∧
      R.roots = (rootRead (proverRun H commit flock tr iv).1.c1.2.halves,
        rootRead (proverRun H commit flock tr iv).1.c2.2.halves) :=
  runWithKH_syncs H commit flock tr iv htr.valid htr.rowsFit zero hflock terminal hbatch

end UniKeccakComplete

/-- info: 'UniKeccakComplete.reduce_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.reduce_steps

/-- info: 'UniKeccakComplete.runWithKH_syncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.runWithKH_syncs

/-- info: 'UniKeccakComplete.runWithKH_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.runWithKH_accepts

/-- info: 'UniKeccakComplete.countChecks_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.countChecks_zero

/-- info: 'UniKeccakComplete.verifyWalkedKH_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.verifyWalkedKH_end
