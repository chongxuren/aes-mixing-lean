import AESMixing.ByteResidualConcrete

/-!
# Vanishing activity/degree-one transfer

For one marked coordinate there is no integer shortened dimension strictly
between zero and one. Thus every scalar shortening term vanishes. The
generic support-to-degree expansion and exact projected adjoint identity
transport this zero to the physical AES maps. No activity Gram certificate
or weighted Schur estimate is used.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityOnePrinted
open AESMixing
set_option autoImplicit false
set_option maxRecDepth 100000

theorem incidence_zero (m : ℝ) (n : ℕ) : incidenceNormCoefficient m n 0 1 = 0 := by
  have h : 4 ≤ n ∨ n + 0 + 1 ≤ 4 := by omega
  simp only [incidenceNormCoefficient, if_pos h]

theorem support_comparison_zero (p : SupportIndex 0) (q : SupportIndex 1) :
    supportIncidenceComparison 0 1 p q = 0 := by
  simp [supportIncidenceComparison, incidenceSupportRaw]

theorem reverse_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, degreeTransfer 0 0 1 (byteDiffusionOrientation inverse) f y^2) ≤
      (0 : ℝ)^2 * ∑ x, degreeComponent 0 1 f x^2 := by
  have h := byte_residual_degree_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) 0 1 (by decide) 0 (le_refl 0)
    (fun v => by simp [action, support_comparison_zero]) f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem forward_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, degreeTransfer 0 1 0 (byteDiffusionOrientation inverse) f y^2) ≤
      (0 : ℝ)^2 * ∑ x, degreeComponent 0 0 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    0 1 (byteDiffusionOrientation (!inverse)) 0 (reverse_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

end AES8.PaperActivityOnePrinted
