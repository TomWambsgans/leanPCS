-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniStatement.Run
import UniStatement.Opening
import UniStatement.Mapping
import UniStatement.Security

/-!
# UniStatement: the univariate PIOP's verifier, transcribed

`crates/leanvm/univariate`'s verifier as computable Lean, the shared part of the Keccak VM's verifier
(`formal/UniKeccak`; `README.md` here: the reading order, the correspondence with the Rust).

The build fails if a guarded definition uses an axiom beyond Lean's three standard ones.
-/

