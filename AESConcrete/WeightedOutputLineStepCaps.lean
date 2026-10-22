import AESConcrete.WeightedOutputLineCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Individual output-weighted actual-line caps (9,5) and (9,8)

The same signed normalized joint input source and its genuine omitted output
uniform are bounded in WeightedOutputLineCaps. One input Cauchy factor is12
for (1,2),6 for (2,2). The twelve orthogonal output supports of type(2,3) give
physical factors 144 and72, respectively. Only after this composition are the
resulting physical coefficients compared with the actual unchanged
Certificate.L.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.

No complete AES theorem or return cap is claimed by this module.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedOutputLineStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.WeightedOutputLineCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Input Cauchy is charged once, to the actual signed support pieces. -/
theorem selected_refined_input_energy (e : Fin 5) (he : e = 1 ∨ e = 2)
    (p : SelectedSupport 2 3) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) e 2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e 2 : ℝ) *
        pieceSquaredBound e * ∑ x, f x ^ 2 := by
  have heb : e ≤ (2 : Fin 5) := by rcases he with rfl | rfl <;> decide
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 3 p) e 2 heb (pieceSquaredBound e) (pieceSquaredBound_nonneg e)
    (fun pIn g => WeightedOutputLineCaps.selected_piece_energy p pIn he g) f

theorem input_multiplicity_one : ResidualIncidenceCoefficient.multiplicity 1 2 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem input_multiplicity_two : ResidualIncidenceCoefficient.multiplicity 2 2 = 6 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem output_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 3 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- The output sum uses exact orthogonal energy, with no second Cauchy factor. -/
theorem physical_line_energy (e : Fin 5) (j : Fin 14) (he : e = 1 ∨ e = 2)
    (hj : blockType j = (e, 2)) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 j) f y ^ 2) ≤
      (12 * (ResidualIncidenceCoefficient.multiplicity e 2 : ℝ) * pieceSquaredBound e) *
        ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 9 j (by decide) f]
  change (∑ p : SelectedSupport 2 3, ∑ y,
    action (selectedWordTensor 2 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  rw [hj]
  calc
    _ ≤ ∑ _p : SelectedSupport 2 3,
        (ResidualIncidenceCoefficient.multiplicity e 2 : ℝ) *
          pieceSquaredBound e * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy e he p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 2 3 (by decide), output_multiplicity]
      norm_num <;> ring

theorem physical_9_5_line_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 5) f y ^ 2) ≤
      (144 * pieceSquaredBound 1) * ∑ x, f x ^ 2 := by
  have ht := physical_line_energy 1 5 (Or.inl rfl) (by decide) f
  norm_num [input_multiplicity_one] at ht
  exact ht

theorem physical_9_8_line_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 8) f y ^ 2) ≤
      (72 * pieceSquaredBound 2) * ∑ x, f x ^ 2 := by
  have ht := physical_line_energy 2 8 (Or.inr rfl) (by decide) f
  norm_num [input_multiplicity_two] at ht
  exact ht

/-- The full physical squared coefficients, with their exact uniform savings. -/
theorem coefficient_9_5_formula :
    144 * pieceSquaredBound 1 = 144 * rho ^ 2 * kappa / (q - 1) ^ 2 := by
  norm_num [pieceSquaredBound] <;> ring

theorem coefficient_9_8_formula :
    72 * pieceSquaredBound 2 = 72 * rho ^ 2 * kappa / (q - 1) := by
  norm_num [pieceSquaredBound] <;> ring

/-- Bind the actual L entries, preserving their original rational literals. -/
theorem certificate_9_5_entry :
    L (9 : Fin 14) (5 : Fin 14) = (1073721796524181 : ℝ) / 154113769531250000000 := rfl

theorem certificate_9_8_entry :
    L (9 : Fin 14) (8 : Fin 14) = (621966101169491 : ℝ) / 1926422119140625 := rfl

theorem coefficient_9_5_scaled :
    (2 : ℝ) ^ 128 * (144 * pieceSquaredBound 1) =
      (10584 / 5 : ℝ) * (q / (q - 1)) ^ 2 := by
  norm_num [pieceSquaredBound, rho, kappa, q]

theorem coefficient_9_8_scaled :
    (2 : ℝ) ^ 96 * (72 * pieceSquaredBound 2) =
      (5292 / 5 : ℝ) * (q / (q - 1)) := by
  norm_num [pieceSquaredBound, rho, kappa, q]

-- User boundary: compare after physical factors144/72 and never alter L.
-- Corrected informal route numerator1907349912791095 is not an assumption;
-- the exact rational comparisons below are Lean proof text.
theorem certificate_9_5_bound :
    0 ≤ lambda * L 9 5 ∧ 144 * pieceSquaredBound 1 < (lambda * L 9 5) ^ 2 := by
  rw [certificate_9_5_entry]
  norm_num [lambda, pieceSquaredBound, rho, kappa, q]

theorem certificate_9_8_bound :
    0 ≤ lambda * L 9 8 ∧ 72 * pieceSquaredBound 2 < (lambda * L 9 8) ^ 2 := by
  rw [certificate_9_8_entry]
  norm_num [lambda, pieceSquaredBound, rho, kappa, q]

theorem physical_9_5_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 5) f y ^ 2) ≤
      (lambda * L 9 5) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_9_5_line_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_9_5_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_9_8_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 8) f y ^ 2) ≤
      (lambda * L 9 8) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_9_8_line_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_9_8_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_9_5_step_cap :
    ‖kernelOperator (physicalBlock 9 5)‖ ≤ lambda * L 9 5 :=
  kernelOperator_norm_le _ certificate_9_5_bound.1 physical_9_5_energy

theorem physical_9_8_step_cap :
    ‖kernelOperator (physicalBlock 9 8)‖ ≤ lambda * L 9 8 :=
  kernelOperator_norm_le _ certificate_9_8_bound.1 physical_9_8_energy

theorem system_9_5_step_cap :
    ‖PhysicalProjectionSystem.system.step 9 5‖ ≤ lambda * L 9 5 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_9_5_step_cap

theorem system_9_8_step_cap :
    ‖PhysicalProjectionSystem.system.step 9 8‖ ≤ lambda * L 9 8 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_9_8_step_cap

end AESConcrete.WeightedOutputLineStepCaps
