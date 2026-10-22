import AESConcrete.Return13_12
import AESConcrete.Return13_11

/-!
# Facade for two high return entries

This import-only facade exposes the actual returns (13,12) and (13,11). The
imported (13,13) result is inherited. Other entries of row13 are outside this
facade. It adds no proof declaration or analytic premise.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/
-- Maintenance: keep this facade import-only. Keep proofs in their owning
-- sources and query/Audit requests separate from returned checking evidence.
