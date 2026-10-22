import AES8.Estimates.Word.PaperSubsetArrayNumbers
import AES8.Estimates.Word.PaperSubsetSupportBridge

/-! Actual AES forward/inverse residual-energy bounds through the printed
subset arrays. Every denominator retains the input degree projection. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSubsetArrayConsumers
open AESMixing PaperKernelBounds PaperActivityArrayBlocks PaperSubsetSupportBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

theorem support11_energy : EnergyBound (supportIncidenceComparison 1 1) printed11 :=
  energyBound_of_norm _ _ printed11_nonneg support11_printed
theorem support12_energy : EnergyBound (supportIncidenceComparison 1 2) printed12 :=
  energyBound_of_norm _ _ printed12_nonneg support12_printed
theorem support22_energy : EnergyBound (supportIncidenceComparison 2 2) printed22 :=
  energyBound_of_norm _ _ printed22_nonneg support22_printed

theorem aes_residual_11_printed_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 1 1 (byteDiffusionOrientation inverse) f y^2) ≤
      printed11^2 * ∑ x, degreeComponent 0 1 f x^2 := by
  have h := byte_residual_degree_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) 1 1 (by decide)
    printed11 printed11_nonneg support11_energy f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem aes_residual_12_printed_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 1 2 (byteDiffusionOrientation inverse) f y^2) ≤
      printed12^2 * ∑ x, degreeComponent 0 2 f x^2 := by
  have h := byte_residual_degree_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) 1 2 (by decide)
    printed12 printed12_nonneg support12_energy f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem aes_residual_21_printed_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 1 (byteDiffusionOrientation inverse) f y^2) ≤
      printed12^2 * ∑ x, degreeComponent 0 1 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    1 2 (byteDiffusionOrientation (!inverse)) printed12
    (aes_residual_12_printed_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

theorem aes_residual_22_printed_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 2 (byteDiffusionOrientation inverse) f y^2) ≤
      printed22^2 * ∑ x, degreeComponent 0 2 f x^2 := by
  have h := byte_residual_degree_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) 2 2 (by decide)
    printed22 printed22_nonneg support22_energy f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem aes_residual_11_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 1 1 (byteDiffusionOrientation inverse) f y^2) ≤
      (4/1125:ℝ)^2 * ∑ x, degreeComponent 0 1 f x^2 := by
  simpa only [printed11_eq] using aes_residual_11_printed_energy inverse f

theorem enlarge_projected_energy {a b E F : ℝ} (ha : 0≤a) (hab : a≤b)
    (hF : 0≤F) (h : E≤a^2*F) : E≤b^2*F :=
  h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hF)

theorem aes_residual_12_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 1 2 (byteDiffusionOrientation inverse) f y^2) ≤
      (64/729:ℝ)^2 * ∑ x, degreeComponent 0 2 f x^2 :=
  enlarge_projected_energy printed12_nonneg printed12_le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (aes_residual_12_printed_energy inverse f)

theorem aes_residual_21_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 1 (byteDiffusionOrientation inverse) f y^2) ≤
      (64/729:ℝ)^2 * ∑ x, degreeComponent 0 1 f x^2 :=
  enlarge_projected_energy printed12_nonneg printed12_le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (aes_residual_21_printed_energy inverse f)

theorem aes_residual_22_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 2 (byteDiffusionOrientation inverse) f y^2) ≤
      (9/10:ℝ)^2 * ∑ x, degreeComponent 0 2 f x^2 :=
  enlarge_projected_energy printed22_nonneg printed22_lt.le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (aes_residual_22_printed_energy inverse f)

end AES8.PaperSubsetArrayConsumers
