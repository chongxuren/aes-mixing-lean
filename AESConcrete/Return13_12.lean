import AESConcrete.ResidualLinePlane
import AESConcrete.Return13_12Composition

/-!
# direct return (13,12) facade

This facade only exposes the exact Return13_12Composition interfaces,
including system_composition_norm and system_return_cap. It adds no theorem,
analytic premise or step cell.

Constructive fixed AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/
-- Maintenance: keep this import-only facade separate from the construction,
-- scalar proof, intended API, axiom requests and later acceptance evidence.
