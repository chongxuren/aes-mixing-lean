import AESMixing.ByteProfile
import AESMixing.ByteWalshCertificate

/-!
# Fifth-moment integer arithmetic on existing verified byte data

The ordinary profile and inversion Walsh lookup are frozen imported
definitions with existing correctness proofs. These two new finite facts
only sum their fifth and tenth powers. Actual probability normalization,
AES relabeling and all nonzero row/column transport are separate.
Constructive mathematics only; no attacks or historical-source edits.
-/

namespace AESConcrete.ByteFifthFinite
open scoped BigOperators

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem inversion_profile_fifth_sum :
    (∑ b : Fin 256, AESMixing.AES.inversionProfile (BitVec.ofFin b)^5) = 5056 := by
  decide

theorem inversion_walsh_tenth_sum :
    (∑ v : Fin 256, AESMixing.AES.inversionWalshLookup (BitVec.ofFin v)^10) =
      (48193441 : ℤ)*2^28 := by
  decide

end AESConcrete.ByteFifthFinite
