-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverStatement.lean` (the statement read as `formal/Completeness`'s, the
-- reduction's target) to the PCS claims' Statement (`formal/Statement/PcsQuotient/Reduction.lean`: the target
-- `Σ_J γ^J · statementWords_J`), with `Statement::halves` as `Compose.Reduce`'s from
-- `PcsBridge/Claims.lean` (`halves_eq`, `statement_halves`, after `Bridge/Claims/Reduce.lean`). Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- Keccak-256 (`keccak256`, `Digest.toBytes`), the fields.
import E2ECompleteness.PcsCircuit
import Compose.Reduce

/-!
# The Statement's statement is `formal/Completeness`'s (the PCS claims)

A witness of the Statement (`PcsQuotient.Secret`, `Vector`s) read as `formal/Completeness`'s
(`secretOf`, functions on `Fin 32`, `PcsCircuit.lean`) proves the same statement (`secretOf_statement`:
both hash with leanerVM's `keccak256` and fold the path the same way). The Statement's halves are
`Compose.Reduce`'s (`halves_eq`, `statement_halves`), and the target the reduction computes,
`Σ_J γ^J · statementWords_J` by Horner's rule (`claimsAt`, `Reduction.lean`), is F1's target of the
deployed instance on Completeness's statement words (**`target_stmt`**; `target_stmt_reduce`, the same for
`Compose.Reduce.target`).
-/

open LeanVM LeanVM.Parameters Finset
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-- **`pair`, transcribed twice.** -/
theorem pair_secretOf (a b : PcsQuotient.Bytes32) :
    Completeness.pair (fun i ↦ a[i]) (fun i ↦ b[i]) = fun i ↦ (PcsQuotient.pair a b)[i] := by
  funext i
  simp only [Completeness.pair, PcsQuotient.pair, ofFn_getElem_vector]

theorem replicate_fn (c : UInt8) : (fun _ : Fin 32 ↦ c) = fun i : Fin 32 ↦ (Vector.replicate 32 c)[i] := by
  funext i
  simp

/-- The path folded twice: the same nodes. -/
theorem foldl_root (w : PcsQuotient.Secret) :
    ∀ (L : List (Fin 32)) (node : PcsQuotient.Bytes32),
      L.foldl (fun nd i ↦ if (secretOf w).directions i then Completeness.pair ((secretOf w).siblings i) nd
          else Completeness.pair nd ((secretOf w).siblings i)) (fun j ↦ node[j]) =
        fun j ↦ (L.foldl (fun nd i ↦ if w.directions[i] then PcsQuotient.pair w.siblings[i] nd
          else PcsQuotient.pair nd w.siblings[i]) node)[j]
  | [], _ => rfl
  | i :: L, node => by
    simp only [List.foldl_cons]
    rw [← foldl_root w L]
    congr 1
    have hs : (secretOf w).siblings i = fun j ↦ w.siblings[i][j] := rfl
    have hd : (secretOf w).directions i = w.directions[i] := rfl
    rw [hs, hd]
    split_ifs <;> rw [pair_secretOf]

/-- **The statement of a witness, read as Completeness's**, is the Statement's. -/
theorem secretOf_statement (w : PcsQuotient.Secret) :
    (secretOf w).statement = ⟨fun i ↦ w.statement.y[i], fun i ↦ w.statement.root[i]⟩ := by
  have hx : (secretOf w).x = fun i ↦ w.x[i] := rfl
  unfold Completeness.Secret.statement Completeness.Secret.root Completeness.Secret.leaf
  rw [hx, show (fun _ : Fin 32 ↦ Completeness.yPad) = fun i : Fin 32 ↦
      (Vector.replicate 32 PcsQuotient.yPad)[i] from replicate_fn _,
    show (fun _ : Fin 32 ↦ Completeness.leafPad) = fun i : Fin 32 ↦
      (Vector.replicate 32 PcsQuotient.leafPad)[i] from replicate_fn _,
    pair_secretOf, pair_secretOf]
  show _ = (⟨fun i ↦ (PcsQuotient.pair w.x (Vector.replicate 32 PcsQuotient.yPad))[i],
    fun i ↦ ((List.finRange PcsQuotient.depth).foldl _ (PcsQuotient.pair w.x
      (Vector.replicate 32 PcsQuotient.leafPad)))[i]⟩ : Completeness.Statement)
  rw [foldl_root]
  rfl

/-! ## `Statement::halves` -/

section Halves

open PcsQuotient (Statement Statement.halves)
open PcsQuotient.Domain PcsQuotient.Transcript

/-- The big-endian value of `n` bytes of `l` from `s`. -/
def beN (l : List UInt8) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => beN l s n * 256 + (l.getD (s + n) 0).toNat

theorem beN_lt (l : List UInt8) (s : ℕ) : ∀ n, beN l s n < 256 ^ n
  | 0 => by simp [beN]
  | n + 1 => by
    have := beN_lt l s n
    have hb := (l.getD (s + n) 0).toNat_lt
    rw [beN, pow_succ]
    omega

theorem beN_add (l : List UInt8) (s n : ℕ) : ∀ m, beN l s (n + m) = beN l s n * 256 ^ m + beN l (s + n) m
  | 0 => by simp [beN]
  | m + 1 => by
    rw [← Nat.add_assoc, beN, beN_add l s n m, beN, pow_succ, Nat.add_assoc s n m]
    ring

theorem beN_sum (l : List UInt8) (s : ℕ) : ∀ n,
    beN l s n = ∑ t ∈ Finset.range n, (l.getD (s + t) 0).toNat * 256 ^ (n - 1 - t)
  | 0 => by simp [beN]
  | n + 1 => by
    rw [beN, beN_sum l s n, Finset.sum_range_succ, Finset.sum_mul,
      show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := Finset.mem_range.mp ht
    rw [mul_assoc, ← pow_succ, show n - 1 - t + 1 = n + 1 - 1 - t by omega]

/-- The statement's `beWord` reads `beN` of eight bytes. -/
theorem beWordAux_toNat (l : List UInt8) (s : ℕ) : ∀ n ≤ 8,
    ((List.range n).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| (l.getD (s + k) 0).toUInt64) 0).toNat =
      beN l s n
  | 0, _ => by simp [beN]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, beN,
      ← beWordAux_toNat l s n (by omega)]
    generalize hx : (List.range n).foldl
      (fun (acc : UInt64) k ↦ (acc <<< 8) ||| (l.getD (s + k) 0).toUInt64) 0 = x
    have hxlt : x.toNat < 256 ^ n := by
      rw [← hx, beWordAux_toNat l s n (by omega)]
      exact beN_lt l s n
    have hb := (l.getD (s + n) 0).toNat_lt
    have hpow : 256 ^ n ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
    have hx56 : x.toNat < 72057594037927936 := lt_of_lt_of_le hxlt (by simpa using hpow)
    have hlt : x.toNat <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; norm_num; omega
    have hb8 : (l.getD (s + n) 0).toUInt64.toNat < 2 ^ 8 := by
      rw [UInt8.toNat_toUInt64]; exact hb
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h8, Nat.mod_eq_of_lt hlt,
      ← Nat.shiftLeft_add_eq_or_of_lt hb8, Nat.shiftLeft_eq, UInt8.toNat_toUInt64]

theorem beWord_toNat (l : List UInt8) (s : ℕ) : (beWord l s).toNat = beN l s 8 :=
  beWordAux_toNat l s 8 le_rfl

theorem ofLane_eq_ofBits (w : UInt64) (n : ℕ) (h : w.toNat = n % 2 ^ 64) :
    K.ofLane w = K.ofBits n := by
  unfold K.ofLane K.ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h]
  rfl

/-- `halfValue` of a vector's bytes is `beN` of sixteen bytes. -/
theorem halfValue_eq (b : Vector UInt8 32) (h : Fin 2) :
    QuotientSecurity.halfValue (fun i ↦ b.get i) h = beN b.toList (16 * h) 16 := by
  rw [beN_sum, QuotientSecurity.halfValue]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have ht' := Finset.mem_range.mp ht
  have hlt : 16 * (h : ℕ) + t < 32 := by omega
  rw [QuotientSecurity.byteAt, dif_pos hlt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some, Vector.getElem_toList,
    show 16 - 1 - t = 15 - t by omega]
  rfl

theorem halfValue_split (b : Vector UInt8 32) (h : Fin 2) :
    QuotientSecurity.halfValue (fun i ↦ b.get i) h =
      beN b.toList (16 * h) 8 * 2 ^ 64 + beN b.toList (16 * h + 8) 8 := by
  rw [halfValue_eq, show (16 : ℕ) = 8 + 8 from rfl, beN_add]
  norm_num

theorem half_lo (b : Vector UInt8 32) (h : Fin 2) :
    K.ofLane (beWord b.toList (16 * h + 8)) =
      K.ofBits (QuotientSecurity.halfValue (fun i ↦ b.get i) h % 2 ^ 64) := by
  apply ofLane_eq_ofBits
  have hB : beN b.toList (16 * h + 8) 8 < 2 ^ 64 := by simpa using beN_lt b.toList (16 * h + 8) 8
  rw [beWord_toNat, halfValue_split, Nat.mod_mod]
  generalize beN b.toList (16 * h) 8 = A at *
  generalize beN b.toList (16 * h + 8) 8 = B at *
  rw [show A * 2 ^ 64 + B = B + A * 2 ^ 64 from Nat.add_comm _ _, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hB]

theorem half_hi (b : Vector UInt8 32) (h : Fin 2) :
    K.ofLane (beWord b.toList (16 * h)) =
      K.ofBits (QuotientSecurity.halfValue (fun i ↦ b.get i) h >>> 64) := by
  apply ofLane_eq_ofBits
  have hlo := beN_lt b.toList (16 * h + 8) 8
  have hhi := beN_lt b.toList (16 * h) 8
  have hB : beN b.toList (16 * h + 8) 8 < 2 ^ 64 := by simpa using hlo
  have hA : beN b.toList (16 * h) 8 < 2 ^ 64 := by simpa using hhi
  rw [beWord_toNat, halfValue_split, Nat.shiftRight_eq_div_pow]
  generalize beN b.toList (16 * h) 8 = A at *
  generalize beN b.toList (16 * h + 8) 8 = B at *
  rw [show A * 2 ^ 64 + B = B + A * 2 ^ 64 from Nat.add_comm _ _,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hB, Nat.zero_add,
    Nat.mod_eq_of_lt hA]

/-- **One of `Statement::halves`** is `stmtHalf`'s. -/
theorem halves_eq (b : Vector UInt8 32) :
    PcsQuotient.halves b = (Compose.Reduce.stmtHalf (fun i ↦ b.get i) 0,
      Compose.Reduce.stmtHalf (fun i ↦ b.get i) 1) := by
  have l0 := half_lo b 0
  have h0 := half_hi b 0
  have l1 := half_lo b 1
  have h1 := half_hi b 1
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add, Nat.mul_one] at l0 h0 l1 h1
  simp only [PcsQuotient.halves, Compose.Reduce.stmtHalf, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    l0, h0, l1, h1]

/-- **`Statement::halves`** of the statement are `stmtHalves` of its 64 bytes. -/
theorem statement_halves (stmt : Statement) (k : Fin 4) :
    (Statement.halves stmt).getD k 0 = Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) k := by
  have hy : Compose.Reduce.yOf (stmt.y ++ stmt.root) = fun i ↦ stmt.y.get i := by
    funext i
    simp [Compose.Reduce.yOf, Vector.get_eq_getElem, Vector.getElem_append_left i.2]
  have hr : Compose.Reduce.rootOf (stmt.y ++ stmt.root) = fun i ↦ stmt.root.get i := by
    funext i
    simp only [Compose.Reduce.rootOf, Vector.get_eq_getElem]
    rw [Vector.getElem_append_right (by omega) (Nat.le_add_right 32 (i : ℕ))]
    simp
  fin_cases k <;>
    simp [Statement.halves, Compose.Reduce.stmtHalves, hy, hr, halves_eq]

end Halves

/-! ## The target -/

theorem ofU64_ofNat (n : ℕ) : Primitives.F64.ofU64 (UInt64.ofNat n) = K.ofBits n := rfl

theorem ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n := by
  unfold K.ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_mod_of_dvd]

/-- **A half of the statement, transcribed twice.** -/
theorem half_eq_stmtHalf (b : Fin 32 → UInt8) (h : Fin 2) :
    half Primitives.F192.G Primitives.F192.Y b h = Compose.Reduce.stmtHalf b h := by
  rw [half_G_Y]
  unfold rustHalf Compose.Reduce.stmtHalf Primitives.F192.new
  rw [ofU64_ofNat, ofU64_ofNat, ofBits_mod]
  rfl

theorem yOf_append (a b : PcsQuotient.Bytes32) : Compose.Reduce.yOf (a ++ b) = fun i ↦ a[i] := by
  funext i
  show (a ++ b)[(i : ℕ)]'(by omega) = a[i]
  exact Vector.getElem_append_left i.isLt

theorem rootOf_append (a b : PcsQuotient.Bytes32) : Compose.Reduce.rootOf (a ++ b) = fun i ↦ b[i] := by
  funext i
  show (a ++ b)[32 + (i : ℕ)]'(by omega) = b[i]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  simp

/-- **`Compose.Reduce`'s target is F1's**, on Completeness's statement words of the witness. -/
theorem target_stmt_reduce (w : PcsQuotient.Secret) (stmt : PcsQuotient.Statement)
    (hrel : PcsQuotient.Relation stmt w) (γ : E) :
    Completeness.deployedInstanceE.params.target
        (statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
          (secretOf w).statement.root) γ =
      Compose.Reduce.target (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) γ := by
  have I := Completeness.deployedInstanceE
  rw [statementWords_eq]
  have ht := membership_target Completeness.deployedInstanceE.basis le24
    Completeness.deployedInstanceE.wiring (invSeq Completeness.deployedInstanceE.basis.β)
    Completeness.deployedInstanceE.c (invSeq_zero _)
    (fun d hd _ ↦ invSeq_sum Completeness.deployedInstanceE.basis.β
      Completeness.deployedInstanceE.basis.zero d hd)
    (halves Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y (secretOf w).statement.root) γ
  refine ht.trans ?_
  rw [secretOf_statement, hrel]
  simp only [halves, Compose.Reduce.target, Compose.Reduce.stmtHalves, yOf_append, rootOf_append,
    half_eq_stmtHalf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  ring

/-- **The Statement's target is F1's**: the reduction's `Σ_J γ^J · statementWords_J` (Horner's rule,
`claimsAt`) is F1's target of the deployed instance on Completeness's statement words of a witness. -/
theorem target_stmt (w : PcsQuotient.Secret) (stmt : PcsQuotient.Statement)
    (hrel : PcsQuotient.Relation stmt w) (γ : E) :
    Completeness.deployedInstanceE.params.target
        (statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
          (secretOf w).statement.root) γ =
      (PcsQuotient.statementWords stmt).foldr (fun word acc ↦ word + γ * acc) 0 := by
  rw [target_stmt_reduce w stmt hrel γ]
  have h0 := statement_halves stmt 0
  have h1 := statement_halves stmt 1
  have h2 := statement_halves stmt 2
  have h3 := statement_halves stmt 3
  simp only [PcsQuotient.Statement.halves, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3
  have h3' : (PcsQuotient.halves stmt.root).2 = Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) 3 := h3
  simp only [PcsQuotient.statementWords, PcsQuotient.Statement.halves, List.cons_append,
    List.nil_append, List.foldr_cons, List.foldr_nil, Compose.Reduce.target, h0, h1, h2, h3']
  ring

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.secretOf_statement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.secretOf_statement

/-- info: 'E2ECompleteness.Pcs.target_stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.target_stmt
