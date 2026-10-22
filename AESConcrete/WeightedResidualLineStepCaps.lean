import AESConcrete.WeightedResidualLineCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Weighted actual-line physical/system Lemmas for (8,9) and (8,6)

The input support sum charges twelve pieces once; the six orthogonal output
energies then give factor72. Only the resulting physical coefficient is
compared with the actual unchanged Certificate.L entry.
No return cap or complete AES theorem is asserted by this module.

Exact pencil comparisons: with t=q/(q-1), the scaled physical coefficients are
(5292/5)*t and (5292/5)*t^2, both below (163/5)^2. The corresponding scaled
lambda*L entries exceed163/5; their exact positive numerator gaps
are1704468726160 and106529340638981. No certificate entry is an assumption of
the source, minor or analytic energy arguments.

Constructive AES10/14/16 with independent uniform retained round keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedResidualLineStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.WeightedResidualLineCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Input Cauchy is charged once; the residual source remains arbitrary signed. -/
theorem selected_refined_input_energy (e : Fin 5) (he : 1 ≤ e.val)
    (heb : e ≤ (3 : Fin 5)) (p : SelectedSupport 2 2) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 2 p)
      (fun x => action (refinedKernel (0 : AES.Word) e 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e 3 : ℝ) *
        pieceSquaredBound e * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 2 p) e 3 heb (pieceSquaredBound e) (pieceSquaredBound_nonneg e)
    (fun pIn g => WeightedResidualLineCaps.selected_piece_energy p pIn he g) f

/-- This cardinality is restricted to the two weighted input types. -/
theorem input_multiplicity (e : Fin 5) (he : e = 1 ∨ e = 2) :
    ResidualIncidenceCoefficient.multiplicity e 3 = 12 := by
  rcases he with rfl | rfl <;>
    norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- The output sum is an exact orthogonal-energy sum, not a second Cauchy loss. -/
theorem physical_line_energy (e : Fin 5) (j : Fin 14) (he : e = 1 ∨ e = 2)
    (hj : blockType j = (e, 3)) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 j) f y ^ 2) ≤
      (72 * pieceSquaredBound e) * ∑ x, f x ^ 2 := by
  have hpos : 1 ≤ e.val := by rcases he with rfl | rfl <;> decide
  have heb : e ≤ (3 : Fin 5) := by rcases he with rfl | rfl <;> decide
  rw [physicalBlock_selected_tensor_energy 8 j (by decide) f]
  change (∑ p : SelectedSupport 2 2, ∑ y,
    action (selectedWordTensor 2 2 p)
      (fun x => action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  rw [hj]
  calc
    _ ≤ ∑ _p : SelectedSupport 2 2,
        (ResidualIncidenceCoefficient.multiplicity e 3 : ℝ) *
          pieceSquaredBound e * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy e hpos heb p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 2 2 (by decide), input_multiplicity e he]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose] <;> ring

theorem physical_8_9_line_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 9) f y ^ 2) ≤
      (72 * pieceSquaredBound 2) * ∑ x, f x ^ 2 :=
  physical_line_energy 2 9 (Or.inr rfl) (by decide) f

theorem physical_8_6_line_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 6) f y ^ 2) ≤
      (72 * pieceSquaredBound 1) * ∑ x, f x ^ 2 :=
  physical_line_energy 1 6 (Or.inl rfl) (by decide) f

/-- Bind the actual L entries, not the earlier auxiliary matrix table. -/
theorem certificate_8_9_entry :
    L (8 : Fin 14) (9 : Fin 14) = (621966101169491 : ℝ) / 1926422119140625 := rfl

theorem certificate_8_6_entry :
    L (8 : Fin 14) (6 : Fin 14) = (1518471926860101 : ℝ) / 308227539062500000000 := rfl

/-- The first exact scaled coefficient; the remaining denominator is the input weight. -/
theorem coefficient_8_9_scaled :
    (2 : ℝ) ^ 96 * (72 * pieceSquaredBound 2) = (5292 / 5 : ℝ) * (q / (q - 1)) := by
  norm_num [pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem coefficient_8_6_scaled :
    (2 : ℝ) ^ 128 * (72 * pieceSquaredBound 1) =
      (5292 / 5 : ℝ) * (q / (q - 1)) ^ 2 := by
  norm_num [pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

-- Editorial dependency: perform these comparisons only AFTER factor72.
-- The exact numerator checks are mathematical proof text in norm_num;
-- no runtime or certificate value is used to establish the analytic estimate.
theorem certificate_8_9_bound :
    0 ≤ lambda * L 8 9 ∧ 72 * pieceSquaredBound 2 < (lambda * L 8 9) ^ 2 := by
  rw [certificate_8_9_entry]
  norm_num [lambda, pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem certificate_8_6_bound :
    0 ≤ lambda * L 8 6 ∧ 72 * pieceSquaredBound 1 < (lambda * L 8 6) ^ 2 := by
  rw [certificate_8_6_entry]
  norm_num [lambda, pieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem physical_8_9_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 9) f y ^ 2) ≤
      (lambda * L 8 9) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_8_9_line_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_8_9_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_8_6_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 6) f y ^ 2) ≤
      (lambda * L 8 6) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_8_6_line_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_8_6_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_8_9_step_cap :
    ‖kernelOperator (physicalBlock 8 9)‖ ≤ lambda * L 8 9 :=
  kernelOperator_norm_le _ certificate_8_9_bound.1 physical_8_9_energy

theorem physical_8_6_step_cap :
    ‖kernelOperator (physicalBlock 8 6)‖ ≤ lambda * L 8 6 :=
  kernelOperator_norm_le _ certificate_8_6_bound.1 physical_8_6_energy

theorem system_8_9_step_cap :
    ‖PhysicalProjectionSystem.system.step 8 9‖ ≤ lambda * L 8 9 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_8_9_step_cap

theorem system_8_6_step_cap :
    ‖PhysicalProjectionSystem.system.step 8 6‖ ≤ lambda * L 8 6 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_8_6_step_cap

end AESConcrete.WeightedResidualLineStepCaps
