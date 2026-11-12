-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/pcs_claim/src/lib.rs` (`PcsClaim::decode`, `element_of`, `verify`; the EIP draft's
-- `pcs_verify(PCS_claim, opening_proof)`, `docs/PCS_CLAIM.md`).
import Implementation.Verifier

/-!
# A declared PCS claim, and what the block proves of it

The contract checks that its transaction declares three PCS claims (`Implementation.calls`): payload `k` of
the frame of PCS claims is the Keccak-256 of claim `k`'s bytes, `1 ‖ n ‖ root ‖ ood ‖ point ‖ value`. The
block proves a declared claim by verifying an opening of it (the EIP draft's `pcs_verify`).

**What the block proves of a declared claim** (`pcsOpen`), its named model: the claim's bytes read as
the block reads them (`decodeClaim`, `PcsClaim::decode`: version `1`, `1 ≤ n ≤ 32`, exactly
`82 + 24 n` bytes; the root's `32` bytes, then the out-of-domain answer, the `n` coordinates and the
value, `24` bytes each, `element_of`), then the Statement's opening check `PcsQuotient.pcsOpening`
(`pcs_claim::verify_claim` over Keccak-f[1600]) of that claim on that commitment, with the opening proof
the block carries for payload `k` (here the proof's opening of claim `k`, `openingFor`); bytes the block
does not read as a claim are proved by nothing. `decodeClaim_pcsClaimBytes`: the block reads back exactly
the claim `pcsClaimBytes` encodes.

That the deployed block proves a declared claim by an opening `pcs_claim::verify` accepts, and that this
is `PcsQuotient.pcsOpening`, is tested, not proved (`crates/membership/evm`'s tests with the mock frame,
`formal/Statement`'s differential tests).
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Rpm PcsQuotient
  PcsQuotient.Transcript Implementation

local notation "W" => word limbsEquiv

/-! ## Reading a claim -/

/-- The digest of 32 bytes: its four little-endian words. -/
def digestOf (b : List UInt8) : Digest := #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3]

/-- **How the block reads a declared claim** (`PcsClaim::decode`): version `1`, `1 ≤ n ≤ 32`, exactly
`82 + 24 n` bytes; the commitment (the root's bytes, the out-of-domain answer) and the claim (the `n`
coordinates, the value). -/
def decodeClaim : List UInt8 → Option (Commitment × Claim)
  | v :: n :: rest =>
    if v = 1 ∧ 1 ≤ n.toNat ∧ n.toNat ≤ 32 ∧ rest.length = 32 + 24 * (n.toNat + 2) then
      some (⟨digestOf (rest.take 32), elementOf ((rest.drop 32).take 24)⟩,
        ⟨(List.range n.toNat).map fun j => elementOf ((rest.drop (56 + 24 * j)).take 24),
          elementOf ((rest.drop (56 + 24 * n.toNat)).take 24)⟩)
    else none
  | _ => none

/-- The opening the block carries for payload `k`: the proof's opening of claim `k`, in the order of
`Claims::on`. -/
def openingFor (o : Openings) : ℕ → Compile.Proof
  | 0 => o.witness
  | 1 => o.wiring
  | _ => o.copy

/-- **What the block proves of declared claim `k`**: the claim as the block reads it (`decodeClaim`),
checked by the Statement's opening check (`PcsQuotient.pcsOpening`, over Keccak-f[1600]) with the block's
opening for it; nothing else is proved. -/
def pcsOpen (o : Openings) (k : ℕ) (bytes : List UInt8) : Bool :=
  match decodeClaim bytes with
  | some (c, claim) => pcsOpening c claim (openingFor o k)
  | none => false

/-! ## Reading back what was written -/

theorem digestOf_digestBytes (d : Digest) : digestOf (digestBytes d) = d := by
  have hlb : digestBytes d = lanesBytes d.toList := rfl
  unfold digestOf
  rw [hlb]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] <;> rw [leLane_lanesBytes _ _ (by simp)] <;> simp

theorem beWord_eq_of_slice (bs : List UInt8) (s : ℕ) (w : UInt64) (h : s + 8 ≤ bs.length)
    (hs : (bs.drop s).take 8 = Transcript.beBytes w) : beWord bs s = w := by
  apply UInt64.toNat_inj.mp
  rw [beWord_slice bs s h, hs, beNat_beBytes8]

theorem elementOf_elementBytes (x : E) : elementOf (elementBytes x) = x := by
  have h8 := length_beBytes8
  have e2 : beWord (elementBytes x) 0 = (x.limb 2).lane :=
    beWord_eq_of_slice _ _ _ (by simp [length_elementBytes]) (by
      rw [List.drop_zero, elementBytes, List.append_assoc]; exact List.take_left' (h8 _))
  have e1 : beWord (elementBytes x) 8 = (x.limb 1).lane :=
    beWord_eq_of_slice _ _ _ (by simp [length_elementBytes]) (by
      rw [elementBytes, List.append_assoc, List.drop_left' (h8 _)]; exact List.take_left' (h8 _))
  have e0 : beWord (elementBytes x) 16 = (x.limb 0).lane :=
    beWord_eq_of_slice _ _ _ (by simp [length_elementBytes]) (by
      rw [elementBytes, show 16 = 8 + 8 from rfl, ← List.drop_drop, List.append_assoc,
        List.drop_left' (h8 _), List.drop_left' (h8 _)]
      exact List.take_of_length_le (by simp [h8]))
  apply word_injective (limbs := limbsEquiv)
  rw [elementOf, e0, e1, e2, word_ofLimbs, word_eq]

theorem elementOf_append (x : E) (rest : List UInt8) : elementOf ((elementBytes x ++ rest).take 24) = x := by
  rw [List.take_left' (length_elementBytes x), elementOf_elementBytes]

/-- **The block reads back exactly the claim `pcsClaimBytes` encodes**, when its point has `1` to `32`
coordinates. -/
theorem decodeClaim_pcsClaimBytes (c : Commitment) (claim : Claim) (h1 : 1 ≤ claim.point.length)
    (h32 : claim.point.length ≤ 32) : decodeClaim (pcsClaimBytes c claim) = some (c, claim) := by
  set n := claim.point.length with hn
  have hn8 : n.toUInt8.toNat = n := by
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  set rest := digestBytes c.root ++ elementBytes c.ood ++ claim.point.flatMap elementBytes ++
    elementBytes claim.value with hrest
  have hpb : pcsClaimBytes c claim = 1 :: n.toUInt8 :: rest := by
    simp [pcsClaimBytes, hrest, hn, List.append_assoc]
    rfl
  have hfl : (claim.point.flatMap elementBytes).length = 24 * n := by
    rw [List.length_flatMap]
    simp [length_elementBytes, hn, List.sum_replicate, Nat.mul_comm]
  have hlen : rest.length = 32 + 24 * (n + 2) := by
    simp only [hrest, List.length_append, length_digestBytes, length_elementBytes, hfl]
    ring
  have h56 : rest.drop 56 = claim.point.flatMap elementBytes ++ elementBytes claim.value := by
    rw [hrest, show 56 = 32 + 24 from rfl, ← List.drop_drop, List.append_assoc, List.append_assoc,
      List.drop_left' (length_digestBytes _), List.drop_left' (length_elementBytes _)]
  rw [hpb, decodeClaim, hn8, if_pos ⟨rfl, h1, h32, hlen⟩]
  have hroot : digestOf (rest.take 32) = c.root := by
    rw [hrest, List.append_assoc, List.append_assoc, List.take_left' (length_digestBytes _),
      digestOf_digestBytes]
  have hood : elementOf ((rest.drop 32).take 24) = c.ood := by
    rw [hrest, List.append_assoc, List.append_assoc, List.drop_left' (length_digestBytes _),
      elementOf_append]
  have hpt : ((List.range n).map fun j => elementOf ((rest.drop (56 + 24 * j)).take 24)) = claim.point := by
    apply List.ext_getElem (by simp [hn])
    intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    rw [← List.drop_drop, h56,
      flatMap_chunk elementBytes 24 length_elementBytes claim.point j hj2 _, elementOf_elementBytes]
  have hval : elementOf ((rest.drop (56 + 24 * n)).take 24) = claim.value := by
    rw [← List.drop_drop, h56, ← hfl, List.drop_left' rfl,
      List.take_of_length_le (by simp [length_elementBytes]), elementOf_elementBytes]
  rw [hroot, hood, hpt, hval]

/-- **`pcsOpen` on a claim `pcsClaimBytes` encodes** is the Statement's opening check of that claim. -/
theorem pcsOpen_pcsClaimBytes (o : Openings) (k : ℕ) (c : Commitment) (claim : Claim)
    (h1 : 1 ≤ claim.point.length) (h32 : claim.point.length ≤ 32) :
    pcsOpen o k (pcsClaimBytes c claim) = pcsOpening c claim (openingFor o k) := by
  rw [pcsOpen, decodeClaim_pcsClaimBytes c claim h1 h32]

end Evm
