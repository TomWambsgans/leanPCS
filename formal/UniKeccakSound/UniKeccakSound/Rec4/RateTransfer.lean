-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Instantiates leanerVM's generic two-oracle transfer
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `common/Common/Transfer2.lean`'s `transfer2`) at Keccak-256 with its whole rate as the output, following
-- `common/Common/Keccak.lean`'s `keccak256_transfer2` (its bound, its non-final blocks).
import Common.Keccak

/-!
# The rate-extended transfer (π1-rec4's wide draws): `Keccak256RateTransfer`

π1-rec4's wide draws (`UniStatement.sampleWide`) read the sponge's whole rate after Keccak-256's last permutation (136
bytes: the digest, then lanes `4 … 16`), not the digest alone. leanerVM's transfer (`Common.keccak256_transfer2`) moves
an RPM game to the two-oracle random-oracle model where `H` answers the **digest** (`DigestBytes`, 32 bytes). Its proof
is generic in how the rate splits into an output part and the rest (`Padding Msg (Dg × E)`, `SpState Dg E C`); here it
is instantiated with the **whole rate as the output** (`Dg = RateBytes`, 136 bytes; `E = Rate0`, no bytes; `C` the
capacity's 64): `H` then answers 136 uniform bytes, whose first 32 are Keccak-256's digest.

* `kBlockEquiv : KBlock ≃ RBlock`: a Keccak block (`DigestBytes × KRest`) as the rate's 136 bytes;
* `keccakPaddingR`: Keccak-256's padding on those blocks (`keccakPadding` mapped by `kBlockEquiv`), lawful;
* `keccakNFR`: a non-final block (byte 135's top bit clear), as `keccakNF`; `not_keccakNFR_of_pad`;
* **`Keccak256RateTransfer`** (the statement) and **`keccak256RateTransfer`** (its proof, `transfer2` at these): for
  a game with an honest part hashing through `H`, an adversary with `H`, `π`, `π⁻¹`, and an honest part hashing through
  `H` and calling `F = π` in a duplex, of cost `q` in all, every event has probabilities in the RPM over `RState` (the
  200 bytes split as rate, nothing, capacity) and in the two-oracle ROM with `H : List UInt8 → RateBytes` within
  `q² / 2^508`, as for the digest.

What it does not do: π1-rec4's Fiat–Shamir chain (`Compose.ListChainK` generalised to rounds whose challenges are one
call's rate) is not written, so nothing consumes this yet (`UniKeccakSound/README.md`, "π1-rec4").
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace UniKeccakSound.Rec4

open Common

/-- The rate's 136 bytes, the output of a wide draw's hash. -/
abbrev RateBytes := Vector UInt8 136

/-- Nothing: the rate past the output, when the output is the whole rate. -/
abbrev Rate0 := Vector UInt8 0

/-- A block as the rate's 136 bytes. -/
abbrev RBlock := RateBytes × Rate0

/-- The Keccak state as the whole rate, nothing, the capacity. -/
abbrev RState := SpState RateBytes Rate0 KCap

/-- The zero state. -/
def RState.zero : RState := ((Vector.replicate 136 0, Vector.replicate 0 0), Vector.replicate 64 0)

/-- A Keccak block (digest bytes, then the rest of the rate) as the rate's 136 bytes. -/
def toRBlock (B : KBlock) : RBlock :=
  (Vector.ofFn fun i : Fin 136 ↦ if h : i.val < 32 then B.1[i.val] else B.2[i.val - 32], Vector.replicate 0 0)

/-- The rate's 136 bytes as a Keccak block. -/
def ofRBlock (R : RBlock) : KBlock :=
  (Vector.ofFn fun i : Fin 32 ↦ R.1[i.val], Vector.ofFn fun i : Fin 104 ↦ R.1[32 + i.val])

theorem rate0_eq (v w : Rate0) : v = w := by
  apply Vector.ext
  intro i hi
  omega

/-- **A Keccak block is the rate's 136 bytes.** -/
def kBlockEquiv : KBlock ≃ RBlock where
  toFun := toRBlock
  invFun := ofRBlock
  left_inv B := by
    obtain ⟨a, b⟩ := B
    refine Prod.ext ?_ ?_
    · apply Vector.ext; intro i hi
      simp [ofRBlock, toRBlock]
    · apply Vector.ext; intro i hi
      simp [ofRBlock, toRBlock]
  right_inv R := by
    obtain ⟨a, b⟩ := R
    refine Prod.ext ?_ (rate0_eq _ _)
    apply Vector.ext; intro i hi
    simp only [toRBlock, ofRBlock, Vector.getElem_ofFn]
    split
    · rfl
    · congr 1; omega

/-- **Keccak-256's padding on the rate's bytes**: `keccakPadding`'s blocks, each as 136 bytes. -/
def keccakPaddingR : Padding (List UInt8) RBlock :=
  ⟨fun m ↦ (keccakPadding.pad m).map kBlockEquiv, fun β ↦ keccakPadding.unpad (β.map kBlockEquiv.symm)⟩

instance : keccakPaddingR.Lawful where
  unpad_eq_some_iff β m := by
    show keccakPadding.unpad (β.map kBlockEquiv.symm) = some m ↔ (keccakPadding.pad m).map kBlockEquiv = β
    rw [Padding.unpad_eq_some_iff]
    constructor
    · intro h; rw [h, List.map_map]; simp
    · intro h; rw [← h, List.map_map]; simp
  pad_ne_nil m := by
    show (keccakPadding.pad m).map kBlockEquiv ≠ []
    simpa using Padding.pad_ne_nil keccakPadding m

/-- A **non-final** block: its last byte (byte 135) has its top bit clear (`keccakNF`'s). -/
def keccakNFR (B : RBlock) : Prop := B.1[135] < 0x80

instance : DecidablePred keccakNFR := fun B ↦ by unfold keccakNFR; infer_instance

theorem keccakNFR_iff (B : KBlock) : keccakNFR (kBlockEquiv B) ↔ keccakNF B := by
  simp [keccakNFR, keccakNF, kBlockEquiv, toRBlock]

/-- The last block of a padded message is final. -/
theorem not_keccakNFR_of_pad (m : List UInt8) (β : List RBlock) (B : RBlock)
    (h : keccakPaddingR.pad m = β ++ [B]) : ¬ keccakNFR B := by
  have h' : keccakPadding.pad m = β.map kBlockEquiv.symm ++ [kBlockEquiv.symm B] := by
    have := congrArg (List.map kBlockEquiv.symm) h
    simpa [keccakPaddingR, List.map_map] using this
  have := not_keccakNF_of_pad m _ _ h'
  rwa [← keccakNFR_iff, Equiv.apply_symm_apply] at this

theorem card_rState : Fintype.card RState = 2 ^ 1600 := by
  simp only [RState, SpState, Fintype.card_prod, card_vector_uInt8]
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

/-- **The rate-extended bound**: `indiffBound2 ≤ q² / 2^508`, as for the digest. -/
theorem rate_indiffBound2_le (q : ℕ) :
    indiffBound2 (Fintype.card RState) (Fintype.card KCap) q ≤ (q ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  rw [card_rState, ← card_kState]
  exact keccak_indiffBound2_le q

/-- **The rate-extended two-oracle transfer for Keccak-256** (the statement): Keccak-256 over a random permutation, its
whole rate after the last permutation as the output, is the two-oracle random-oracle model with `H` answering 136
uniform bytes, within `q² / 2^508`, for every game of the transfer's form (an honest part hashing through `H`, an
adversary with `H`, `π`, `π⁻¹`, an honest part hashing through `H` and calling `F = π` in a duplex). -/
def Keccak256RateTransfer : Prop :=
  ∀ {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec (List UInt8) RateBytes) β)
    (A : β → OracleComp (dSpec (List UInt8) RateBytes RState) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec (List UInt8) RateBytes RState) δ),
    (∀ x a, Duplex RState.zero keccakNFR (post x a) []) → ∀ (q : ℕ),
    QueryCostAtMost (rpmGame2 pre A post) (queryCost2 (Dg := RateBytes) keccakPaddingR) q → ∀ (p : δ → Prop),
    Pr{let a ← realGame2 keccakPaddingR RState.zero (rpmGame2 pre A post)}[p a] ≤
        Pr{let a ← romRun2 (simulateQ (hInF (E := Rate0) (C := KCap)) pre >>= fun x ↦
          advS2 keccakPaddingR RState.zero (A x) >>= fun a ↦ post x a)}[p a] + (q ^ 2 : ℝ≥0∞) / 2 ^ 508 ∧
      Pr{let a ← romRun2 (simulateQ (hInF (E := Rate0) (C := KCap)) pre >>= fun x ↦
          advS2 keccakPaddingR RState.zero (A x) >>= fun a ↦ post x a)}[p a] ≤
        Pr{let a ← realGame2 keccakPaddingR RState.zero (rpmGame2 pre A post)}[p a] + (q ^ 2 : ℝ≥0∞) / 2 ^ 508

/-- **`Keccak256RateTransfer` holds**: leanerVM's `transfer2` at the rate split, with the Keccak bound. -/
theorem keccak256RateTransfer : Keccak256RateTransfer := by
  intro β γ δ pre A post hpost q hq p
  obtain ⟨h1, h2⟩ := transfer2 keccakPaddingR RState.zero keccakNFR not_keccakNFR_of_pad pre A post hpost q hq p
  exact ⟨h1.trans (by gcongr; exact rate_indiffBound2_le q), h2.trans (by gcongr; exact rate_indiffBound2_le q)⟩

end UniKeccakSound.Rec4
