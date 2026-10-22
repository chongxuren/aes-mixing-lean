import AESConcrete.TwoOutputThreeUniformCaps
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Scalar comparison after the physical factor24 for (8,7)

This module does not provide an analytic premise to Geometry or Caps. It
compares only the complete physical coefficient, leaving the actual
Certificate.L unchanged. Constructive fixed AES10/14/16.
-/

noncomputable section
namespace AESConcrete.TwoOutputThreeUniformScalar
open AESConcrete.TwoOutputThreeUniformCaps (pieceSquaredBound)
open AESConcrete.ActivityCodeScalar (q s)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

theorem certificate_8_7_entry :
    L (8 : Fin 14) (7 : Fin 14) = (4383651537615139 : ℝ) / 1541137695312500000000 := rfl

theorem physical_coefficient_scaled :
    (2 : ℝ) ^ 128 * (24 * pieceSquaredBound) =
      (1764 / 5 : ℝ) * (1 + 3 / s) ^ 2 * (q / (q - 1)) ^ 3 := by
  norm_num [pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q, s]

-- User boundary: compare only after the input4 * output6 physical factor.
-- The rational tactic bodies have not been executed; the route has an
--
theorem certificate_8_7_bound :
    0 ≤ lambda * L 8 7 ∧ 24 * pieceSquaredBound < (lambda * L 8 7) ^ 2 := by
  rw [certificate_8_7_entry]
  norm_num [lambda, pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q, s]

end AESConcrete.TwoOutputThreeUniformScalar
