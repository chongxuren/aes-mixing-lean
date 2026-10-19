import AESConcrete.WordFourierVariants

/-!
LocalAES: auxiliary lemmas for the concrete AES mixing proof.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
open scoped BigOperators
namespace AESPaper.LocalAES
open AESMixing AESConcrete AESConcrete.WordFourierVariants

theorem local_column_energy (adjoint fourier : Bool) (a : AES.Word) :
    (∑ y, variant adjoint fourier y a ^ 2) < (2 / (15 * 2^32) : ℝ) := by
  simpa only [show (2 : ℝ)^32 = 4294967296 by norm_num] using
    variant_column_energy_lt adjoint fourier a

theorem local_gram_moment (adjoint fourier : Bool) :
    (∑ x, ∑ z, (∑ y, variant adjoint fourier y x * variant adjoint fourier y z)^2) ≤
      (300 / 2^32 : ℝ)^2 := by
  simpa only [show (2 : ℝ)^32 = 4294967296 by norm_num] using
    (variant_gram_moment_lt adjoint fourier).le

theorem local_operator_norm (adjoint fourier : Bool) :
    ‖kernelOperator (variant adjoint fourier)‖ ≤ 21 / (2 * Real.sqrt ((2:ℝ)^32)) := by
  have hs : Real.sqrt ((2:ℝ)^32) = 65536 := by
    rw [show (2:ℝ)^32 = 65536^2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 65536)]
  rw [hs]
  norm_num only [show (2 : ℝ) * 65536 = 131072 by norm_num]
  exact variant_operator_norm_le adjoint fourier

end AESPaper.LocalAES
