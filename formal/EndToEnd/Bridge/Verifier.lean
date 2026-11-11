-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Bridge.Opening
import Bridge.Chain
import Compose.Claims
import Compose.Rpm
import PcsQuotient.Security
import QuotientSecurity.DeployedConcrete
import Shared.SoundnessDefs

/-!
# Opening calls as F2 sees them

`openingWith_eq_ourVerifier'` (the opening's bridge in the form the callers use), `toStmt_claims_of` (a claim list
as F2's statement) and `ofB_toB` (Compose's bytes of a digest read back).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile QuotientRpm QuotientSecurity OracleComp

/-! ## The three openings -/

/-- `openingWith_eq_ourVerifier` at a layout given up to `layoutTr`. -/
theorem openingWith_eq_ourVerifier' {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (L : PcsQuotient.Layout) (L' : WhirBridge.Layout)
    (hLL : layoutTr L = L') (hL : LayoutOK L) (hw : Whir.Admissible L.logN WhirBridge.logInvRate)
    (root : Digest) (x : WhirBridge.Stmt L'.stacking) (claims : List PcsQuotient.Claim)
    (hx : x.claims = claims.map claimTr) (proof : Proof) :
    PcsQuotient.openingWith F L root claims proof =
      simulateQ (keccakCallsWith F)
        (Soundness.ourVerifierEarly L' WhirBridge.logInvRate ((root, x), proof)) := by
  subst hLL
  exact openingWith_eq_ourVerifier F L hL hw root x claims hx proof

theorem toStmt_claims_of {L : WhirBridge.Layout} {cs : List WhirBridge.Claim}
    (hshort : cs.length ≤ 2) (hwide : ∀ c ∈ cs, c.point.length = L.vars) :
    (Compose.toStmt L cs).claims = cs := by
  have he := Compose.extra_length_le L
  unfold Compose.toStmt
  rw [dif_pos ⟨by simp only [WhirBridge.Layout.stacking]; omega, hwide⟩]

theorem ofB_toB (d : Digest) : Compose.ofB (Compose.toB d) = d :=
  LeanVM.Rpm.digestOfRpm_toRpm d

end Bridge
