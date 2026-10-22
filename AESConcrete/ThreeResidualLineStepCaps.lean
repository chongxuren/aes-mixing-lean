import AESConcrete.ThreeResidualLineCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Individual physical/system (11,8) cap

The input support sum charges six signed pieces once. Four genuinely
orthogonal output support energies add, giving physical factor24. Only then is
rho^2*kappa^2 compared with the unchanged actual Certificate.L(11,8).

The hand scalar argument is exact: for N=131427780297652 and C=lambda*L(11,8),
2^48*C=N/5^19>687/100, whereas 2^96*(24*rho^2*kappa^2)=1176/25<(687/100)^2.

Fixed independent uniform retained keys, whitening, omitted final MixColumns
and ordered-distinct reference law; constructive AES10/14/16. No return cap or
complete AES theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeResidualLineStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ThreeResidualLineCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Six actual input supports are charged once by signed Cauchy--Schwarz. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 2 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 3 p) 2 2 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => ThreeResidualLineCaps.selected_piece_energy p pIn g) f

/-- Four orthogonal output energies give physical factor 4*6=24. -/
theorem physical_line_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 8) f y ^ 2) ≤
      (24 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 11 8 (by decide) f]
  change (∑ p : SelectedSupport 3 3, ∑ y,
    action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 3,
        (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 2 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 3 (by decide)]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      ring

/-- Bind the actual coefficient L, not another certificate matrix. -/
theorem certificate_11_8_entry :
    L (11 : Fin 14) (8 : Fin 14) = (131427780297652 : ℝ) / 1926422119140625 := rfl

/-- The unchanged coefficient is compared only after the physical factor24.
The exact rational comparison retains kappa rather than an odd-root envelope. -/
theorem certificate_line_bound :
    0 ≤ lambda * L 11 8 ∧
      24 * pieceSquaredBound ≤ (lambda * L 11 8) ^ 2 := by
  rw [certificate_11_8_entry]
  norm_num [lambda, pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa]

theorem physical_11_8_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 8) f y ^ 2) ≤
      (lambda * L 11 8) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_line_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_line_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_8_step_cap :
    ‖kernelOperator (physicalBlock 11 8)‖ ≤ lambda * L 11 8 :=
  kernelOperator_norm_le _ certificate_line_bound.1 physical_11_8_energy

theorem system_11_8_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 8‖ ≤ lambda * L 11 8 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_8_step_cap

end AESConcrete.ThreeResidualLineStepCaps
