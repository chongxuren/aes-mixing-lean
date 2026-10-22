import AESConcrete.WeightedThreeOutputCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Individual weighted three-output physical and system caps

Lemmas for (11,5), (11,6), (11,9). The twelve actual input pieces incur one
Cauchy multiplicity. Four actual orthogonal output support energies are then
summed, giving factor48. The resulting physical coefficient, rather than a
selected-piece coefficient, is compared with each unchanged actual
AESRound.Certificate.L entry.

With t=q/(q-1), the scaled physical coefficients are (2352/25)*t for (11,5),
and (388962/5)*t for both (11,6) and (11,9). The certificate proofs below use
exact rationals directly; no certificate entry is an analytic premise.
Geometry, exact minor, selected energy and physical aggregation remain
separate.
This module does not assert the complete AES theorem.

Fixed independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference and constructive AES10/14/16.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedThreeOutputStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.WeightedThreeOutputCaps
  (linePieceSquaredBound planePieceSquaredBound
    linePieceSquaredBound_nonneg planePieceSquaredBound_nonneg)
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

/-- One Cauchy factor on the twelve actual (1,2) input supports. -/
theorem selected_refined_line_input_energy (p : SelectedSupport 3 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 1 2 : ℝ) *
        linePieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 3 p) 1 2 (by decide) linePieceSquaredBound linePieceSquaredBound_nonneg
    (fun pIn g => WeightedThreeOutputCaps.selected_piece_line_energy p pIn g) f

theorem selected_refined_plane_input_energy (e : Fin 5) (he : e = 1 ∨ e = 2)
    (p : SelectedSupport 3 3) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) e 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e 3 : ℝ) *
        planePieceSquaredBound * ∑ x, f x ^ 2 := by
  have heb : e ≤ (3 : Fin 5) := by rcases he with rfl | rfl <;> decide
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 3 p) e 3 heb planePieceSquaredBound planePieceSquaredBound_nonneg
    (fun pIn g => WeightedThreeOutputCaps.selected_piece_plane_energy p pIn he g) f

theorem line_input_multiplicity : ResidualIncidenceCoefficient.multiplicity 1 2 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem plane_input_multiplicity (e : Fin 5) (he : e = 1 ∨ e = 2) :
    ResidualIncidenceCoefficient.multiplicity e 3 = 12 := by
  rcases he with rfl | rfl <;>
    norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- Four orthogonal output energies, with no second input Cauchy charge. -/
theorem physical_11_5_code_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 5) f y ^ 2) ≤
      (48 * linePieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 11 5 (by decide) f]
  change (∑ p : SelectedSupport 3 3, ∑ y,
    action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 3,
        (ResidualIncidenceCoefficient.multiplicity 1 2 : ℝ) *
          linePieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_line_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 3 (by decide), line_input_multiplicity]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose] <;> ring

theorem physical_plane_energy (e : Fin 5) (j : Fin 14) (he : e = 1 ∨ e = 2)
    (hj : blockType j = (e, 3)) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 j) f y ^ 2) ≤
      (48 * planePieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 11 j (by decide) f]
  change (∑ p : SelectedSupport 3 3, ∑ y,
    action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  rw [hj]
  calc
    _ ≤ ∑ _p : SelectedSupport 3 3,
        (ResidualIncidenceCoefficient.multiplicity e 3 : ℝ) *
          planePieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_plane_input_energy e he p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 3 (by decide), plane_input_multiplicity e he]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose] <;> ring

theorem physical_11_6_code_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 6) f y ^ 2) ≤
      (48 * planePieceSquaredBound) * ∑ x, f x ^ 2 :=
  physical_plane_energy 1 6 (Or.inl rfl) (by decide) f

theorem physical_11_9_code_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 9) f y ^ 2) ≤
      (48 * planePieceSquaredBound) * ∑ x, f x ^ 2 :=
  physical_plane_energy 2 9 (Or.inr rfl) (by decide) f

/-- Actual unchanged certificate entries, with their exact source denominators. -/
theorem certificate_11_5_entry :
    L (11 : Fin 14) (5 : Fin 14) = (2268883659560163 : ℝ) / 1541137695312500000000 := rfl

theorem certificate_11_6_entry :
    L (11 : Fin 14) (6 : Fin 14) = (6509099390792479 : ℝ) / 154113769531250000000 := rfl

theorem certificate_11_9_entry :
    L (11 : Fin 14) (9 : Fin 14) = (6735980831907303 : ℝ) / 154113769531250000000 := rfl

theorem coefficient_11_5_scaled :
    (2 : ℝ) ^ 128 * (48 * linePieceSquaredBound) = (2352 / 25 : ℝ) * (q / (q - 1)) := by
  norm_num [linePieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem coefficient_plane_scaled :
    (2 : ℝ) ^ 128 * (48 * planePieceSquaredBound) = (388962 / 5 : ℝ) * (q / (q - 1)) := by
  norm_num [planePieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

-- User boundary: compare only after physical factor48, never edit L.
-- The following norm_num bodies are prospective exact proofs, not execution evidence.
theorem certificate_11_5_bound :
    0 ≤ lambda * L 11 5 ∧ 48 * linePieceSquaredBound < (lambda * L 11 5) ^ 2 := by
  rw [certificate_11_5_entry]
  norm_num [lambda, linePieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem certificate_11_6_bound :
    0 ≤ lambda * L 11 6 ∧ 48 * planePieceSquaredBound < (lambda * L 11 6) ^ 2 := by
  rw [certificate_11_6_entry]
  norm_num [lambda, planePieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem certificate_11_9_bound :
    0 ≤ lambda * L 11 9 ∧ 48 * planePieceSquaredBound < (lambda * L 11 9) ^ 2 := by
  rw [certificate_11_9_entry]
  norm_num [lambda, planePieceSquaredBound, UniformGraphScalar.rho, UniformGraphScalar.kappa, q]

theorem physical_11_5_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 5) f y ^ 2) ≤
      (lambda * L 11 5) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_11_5_code_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_11_5_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_6_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 6) f y ^ 2) ≤
      (lambda * L 11 6) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_11_6_code_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_11_6_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_9_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 9) f y ^ 2) ≤
      (lambda * L 11 9) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_11_9_code_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_11_9_bound.2.le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_5_step_cap :
    ‖kernelOperator (physicalBlock 11 5)‖ ≤ lambda * L 11 5 :=
  kernelOperator_norm_le _ certificate_11_5_bound.1 physical_11_5_energy

theorem physical_11_6_step_cap :
    ‖kernelOperator (physicalBlock 11 6)‖ ≤ lambda * L 11 6 :=
  kernelOperator_norm_le _ certificate_11_6_bound.1 physical_11_6_energy

theorem physical_11_9_step_cap :
    ‖kernelOperator (physicalBlock 11 9)‖ ≤ lambda * L 11 9 :=
  kernelOperator_norm_le _ certificate_11_9_bound.1 physical_11_9_energy

theorem system_11_5_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 5‖ ≤ lambda * L 11 5 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_5_step_cap

theorem system_11_6_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 6‖ ≤ lambda * L 11 6 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_6_step_cap

theorem system_11_9_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 9‖ ≤ lambda * L 11 9 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_9_step_cap

end AESConcrete.WeightedThreeOutputStepCaps
