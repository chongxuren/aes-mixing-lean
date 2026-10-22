import AESConcrete.ThreeResidualPlaneCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Individual physical/system (11,11) cap

The input aggregation charges four signed support pieces once. Four genuine
orthogonal output support energies then add, giving physical factor16. Only
afterwards is rho^4*kappa compared with the unchanged actual L(11,11). No
complete AES10/14/16 theorem or new return cap is asserted by this individual
interface.

Fixed independent uniform retained keys, whitening, omitted final MixColumns
and ordered-distinct reference law; constructive scope only.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeResidualPlaneStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ThreeResidualPlaneCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Four actual input supports are charged once by signed Cauchy--Schwarz. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 3 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 3 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 3 p) 3 3 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => ThreeResidualPlaneCaps.selected_piece_energy p pIn g) f

/-- Four orthogonal output energies give physical factor 4*4=16. -/
theorem physical_plane_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 11) f y ^ 2) ≤
      (16 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 11 11 (by decide) f]
  change (∑ p : SelectedSupport 3 3, ∑ y,
    action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 3 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 3,
        (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 3 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 3 (by decide)]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      ring

/-- Bind the actual coefficient L, not another certificate matrix. -/
theorem certificate_11_11_entry :
    L (11 : Fin 14) (11 : Fin 14) = (80703 : ℝ) / 50500 := rfl

/-- The unchanged coefficient is compared only after the physical factor16.
The exact rational comparison retains kappa rather than an odd-root envelope. -/
theorem certificate_plane_bound :
    0 ≤ lambda * L 11 11 ∧
      16 * pieceSquaredBound ≤ (lambda * L 11 11) ^ 2 := by
  rw [certificate_11_11_entry]
  norm_num [lambda, pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa]

theorem physical_11_11_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 11) f y ^ 2) ≤
      (lambda * L 11 11) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_plane_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_plane_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_11_step_cap :
    ‖kernelOperator (physicalBlock 11 11)‖ ≤ lambda * L 11 11 :=
  kernelOperator_norm_le _ certificate_plane_bound.1 physical_11_11_energy

theorem system_11_11_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 11‖ ≤ lambda * L 11 11 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_11_step_cap

end AESConcrete.ThreeResidualPlaneStepCaps
