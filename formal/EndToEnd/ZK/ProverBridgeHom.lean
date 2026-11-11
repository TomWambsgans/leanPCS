-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsQuotient.Security
import Common.Fold
import Common.Indiff.Main
import Common.Keccak
import Common.PiOnly
import Common.Prob
import Common.Rerun
import Common.Transfer2
import QuotientRpm.Bytes
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
import Mathlib.Order.CompletePartialOrder

/-!
# Monad morphisms

**A monad morphism** `MHom m n`: a map of computations preserving `pure` and `bind`.

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec

namespace PcsQuotient.EndToEnd

/-- **A monad morphism**: a map of computations preserving `pure` and `bind`. -/
structure MHom (m n : Type → Type) [Monad m] [Monad n] where
  app : {α : Type} → m α → n α
  app_pure : ∀ {α : Type} (a : α), app (pure a) = pure a
  app_bind : ∀ {α β : Type} (x : m α) (f : α → m β), app (x >>= f) = app x >>= fun a ↦ app (f a)

namespace MHom

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : MHom m n)

end MHom

end PcsQuotient.EndToEnd
