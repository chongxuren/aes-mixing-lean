import AESMixing.ByteActivityBounds
import AESMixing.ByteActivityInverseBounds
import AESMixing.ByteResidualConcrete
import AESMixing.DampedWordNorm

/-! Adapted read-only source: historical AESMixing/ByteDiffusionBounds.lean.
The historical file was written but unsubmitted.  This new module requires a
fresh kernel check against the restored, hash-bound supporting modules.
It closes the concrete byte-degree assembly for the weaker 11/65536 word norm;
it does not establish the current certificate constant 21/131072.
Constructive scope only: no cryptanalytic attack development or reproduction.
-/

/-! All twenty-five byte-degree diffusion bounds, for the actual forward
and inverse MixColumns maps. Activity blocks come from the checked Gram
tables; residual blocks come from the MDS incidence argument. Reversed
blocks use adjoints. The remaining blocks use orthogonal contraction. -/
noncomputable section
open scoped BigOperators
namespace AESConcrete.WordNormSupport
open AESMixing

theorem aes_activity_zero_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, degreeTransfer 0 0 0 (byteDiffusionOrientation inverse) f x^2) ≤
      (1/10400 : ℝ)^2*∑ x, degreeComponent 0 0 f x^2 := by
  cases inverse
  · exact forward_activity_degree_zero_energy f hz hs
  · exact inverse_activity_degree_zero_energy f hz hs

theorem aes_activity_one_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 1 0 (byteDiffusionOrientation inverse) f x^2) ≤
      (0 : ℝ)^2*∑ x, degreeComponent 0 0 f x^2 := by
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul]
  cases inverse
  · exact forward_activity_degree_one_energy f
  · exact inverse_activity_degree_one_energy f

theorem aes_activity_two_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 2 0 (byteDiffusionOrientation inverse) f x^2) ≤
      (7/500 : ℝ)^2*∑ x, degreeComponent 0 0 f x^2 := by
  cases inverse
  · exact forward_activity_degree_two_energy f
  · exact inverse_activity_degree_two_energy f

theorem aes_activity_three_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 3 0 (byteDiffusionOrientation inverse) f x^2) ≤
      (9/50 : ℝ)^2*∑ x, degreeComponent 0 0 f x^2 := by
  cases inverse
  · exact forward_activity_degree_three_energy f
  · exact inverse_activity_degree_three_energy f

theorem aes_reverse_activity_one_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 0 1 (byteDiffusionOrientation inverse) f x^2) ≤
      (0 : ℝ)^2*∑ x, degreeComponent 0 1 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    1 0 (byteDiffusionOrientation (!inverse)) 0 (aes_activity_one_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

theorem aes_reverse_activity_two_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 0 2 (byteDiffusionOrientation inverse) f x^2) ≤
      (7/500 : ℝ)^2*∑ x, degreeComponent 0 2 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    2 0 (byteDiffusionOrientation (!inverse)) (7/500) (aes_activity_two_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

theorem aes_reverse_activity_three_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 0 3 (byteDiffusionOrientation inverse) f x^2) ≤
      (9/50 : ℝ)^2*∑ x, degreeComponent 0 3 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    3 0 (byteDiffusionOrientation (!inverse)) (9/50) (aes_activity_three_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

theorem aes_degree_universal_energy (inverse : Bool) (i j : Fin 5)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 i j (byteDiffusionOrientation inverse) f x^2) ≤
      (1 : ℝ)^2*∑ x, degreeComponent 0 j f x^2 := by
  simpa only [one_pow, one_mul, degreeTransfer] using degree_block_energy_le 0
    (by norm_num [BinaryWord.card]) i j (byteDiffusionOrientation inverse).symm f

set_option maxRecDepth 16384 in
theorem aes_byte_diffusion_comparison (inverse : Bool) (i j : Fin 5)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, degreeTransfer 0 i j (byteDiffusionOrientation inverse) f x^2) ≤
      (byteComparison i j)^2*∑ x, degreeComponent 0 j f x^2 := by
  fin_cases i <;> fin_cases j
  · simpa [byteComparison] using aes_activity_zero_energy inverse f hz hs
  · simpa [byteComparison] using aes_reverse_activity_one_energy inverse f
  · simpa [byteComparison] using aes_reverse_activity_two_energy inverse f
  · simpa [byteComparison] using aes_reverse_activity_three_energy inverse f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 0 4 f
  · simpa [byteComparison] using aes_activity_one_energy inverse f
  · simpa [byteComparison] using aes_residual_11_energy inverse f
  · simpa [byteComparison] using aes_residual_12_energy inverse f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 1 3 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 1 4 f
  · simpa [byteComparison] using aes_activity_two_energy inverse f
  · simpa [byteComparison] using aes_residual_21_energy inverse f
  · simpa [byteComparison] using aes_residual_22_energy inverse f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 2 3 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 2 4 f
  · simpa [byteComparison] using aes_activity_three_energy inverse f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 3 1 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 3 2 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 3 3 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 3 4 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 4 0 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 4 1 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 4 2 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 4 3 f
  · simpa [byteComparison] using aes_degree_universal_energy inverse 4 4 f

theorem aes_oriented_word_energy {D E : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (hE : ByteResources E) (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (twoSubstitutionKernel D E (byteDiffusionOrientation inverse)) f x^2) ≤
      (11/65536 : ℝ)^2*∑ x, f x^2 :=
  twoSubstitution_centered_energy hD hE _ (aes_byte_diffusion_comparison inverse) f hz hs

end AESConcrete.WordNormSupport
