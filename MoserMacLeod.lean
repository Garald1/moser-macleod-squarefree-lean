import MoserMacLeod.Proof
import MoserMacLeod.SharpBound

/-!
# The Moser--MacLeod square-root estimate

This module exports the fully formalized theorem `MoserMacLeod.abs_R_lt_sqrt`.
See `MOSER_MACLEOD_LEAN_COMPANION.md` for the complete human proof and the
correspondence between the paper and the Lean declarations.

`MoserMacLeod.SharpBound` additionally provides the sharpened large-`x` estimate
`MoserMacLeod.abs_R_lt_thirteen_eighteenths_sqrt`, whose leading constant
`13/18 ≈ 0.722` improves on the `13/16 ≈ 0.813` implicit in the headline bound.
-/
