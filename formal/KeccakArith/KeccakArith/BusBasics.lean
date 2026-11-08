-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The lemmas are `formal/Lv42`'s
-- `Arithmetization/Completeness/{Bus,Satisfied}.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), which hold
-- for any instruction set.
module

public import KeccakArith.Rows

/-!
# The channels of a list of sends

What a list of `(channel name, message)` pairs carries on one channel (`chanOf`), and what a row of the opcode-table
shape (`sendsOf`) sends on each of the six channels. Lv42 has these next to its instruction set's witness builder;
they are about messages only.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization
open Lv42.Semantics (Regs)

/-- Mapping the singletons of a list and then a function is mapping the composition. -/
theorem map_flatMap_singleton {α β γ : Type} (f : α → β) (h : β → γ) (l : List α) :
    (l.flatMap fun a ↦ [f a]).map h = l.map fun a ↦ h (f a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A list of singletons is a map. -/
theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    (l.flatMap fun a ↦ [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A row sends one state pull, `(pc, fp)`. -/
theorem sendsOf_statePull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = StatePull.name)).map (·.2) =
      [#[pc, fp]] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one state push, the successor. -/
theorem sendsOf_statePush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = StatePush.name)).map (·.2) =
      [#[next.pc, next.fp]] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one bytecode pull, the entry with the count `rbc`. -/
theorem sendsOf_bcPull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = BytecodePull.name)).map (·.2) =
      [bcMsgOf pc rbc e] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one bytecode push, the entry with the count `g · rbc`. -/
theorem sendsOf_bcPush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = BytecodePush.name)).map (·.2) =
      [bcMsgOf pc (g * rbc) e] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends a memory pull per read. -/
theorem sendsOf_memPull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = MemPull.name)).map (·.2) =
      reads.map fun x ↦ memMsgOf x.1 x.2.1 x.2.2 := by
  simp only [sendsOf, List.filter_append, List.map_append, List.filter_flatMap]
  simp [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    map_flatMap_singleton]

/-- A row sends a memory push per read, with the count `g · count`. -/
theorem sendsOf_memPush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = MemPush.name)).map (·.2) =
      reads.map fun x ↦ memMsgOf x.1 (g * x.2.1) x.2.2 := by
  simp only [sendsOf, List.filter_append, List.map_append, List.filter_flatMap]
  simp [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    map_flatMap_singleton]

/-- The messages of the channel named `n` among a list of sends. -/
def chanOf (n : String) (l : List (String × Array K)) : List (Array K) :=
  (l.filter (·.1 = n)).map (·.2)

/-- The messages of a concatenation. -/
theorem chanOf_append (n : String) (l₁ l₂ : List (String × Array K)) :
    chanOf n (l₁ ++ l₂) = chanOf n l₁ ++ chanOf n l₂ := by
  simp only [chanOf, List.filter_append, List.map_append]

/-- The messages of a `flatMap`. -/
theorem chanOf_flatMap {α : Type} (n : String) (l : List α) (F : α → List (String × Array K)) :
    chanOf n (l.flatMap F) = l.flatMap fun a ↦ chanOf n (F a) := by
  simp only [chanOf, List.filter_flatMap, List.map_flatMap]

/-- The messages on a channel of a list of interactions, as the filter of their name and message pairs. -/
theorem msgs_eq_sends (l : List (Interaction K)) (c : RawChannel K) :
    (l.filter (·.channel.name = c.name)).map (·.msg) =
      (((l.map fun i ↦ (i.channel.name, i.msg)).filter (·.1 = c.name)).map (·.2)) := by
  induction l with
  | nil => rfl
  | cons i l ih => by_cases h : i.channel.name = c.name <;> simp [h, ih]

end KeccakArith

end
