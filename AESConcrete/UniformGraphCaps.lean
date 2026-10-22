import AESConcrete.UniformGraphTermBounds
import AESConcrete.OrdinaryGraphCaps

/-!
# Multi-uniform graph bounds for the actual four-residual output row

Each support piece is normalized once to one arbitrary signed joint
residual. Its Boolean expansion is bounded by `UniformGraphTermBounds`.
Input support orthogonality and output Cauchy--Schwarz then give exactly one
selected-support multiplicity. Scalar certificate comparison remains in
`UniformGraphScalar`, and pair inventory remains in `UniformGraphStepCaps`.

Constructive bounds only; no attacks, workloads, manuscript or historical
edits, goals or schedules. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and 10/14/16 stay fixed.
No return, initialization or complete AES theorem is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.UniformGraphCaps
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.MultiUniformExpansion
open AESConcrete.UniformGraphScalar
open AESConcrete.UniformGraphTermBounds
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.FourResidualStep (residualStepKernel)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

/-- The normalized component has exactly `b-e` nonzero-uniform positions. -/
theorem selected_uniformPositions_card (e b : Fin 5) (p : SelectedSupport e b) :
    Fintype.card (UniformPositions p.val.val.2 p.val.val.1) = b.val - e.val := by
  rw [uniformPositions_card _ _ p.val.property.1]
  have hp := p.property
  have he := p.val.property.2
  omega

/-- One genuine support component receives the exact size-grouped bound.
The extraction and its input-energy identity both concern the same `h`. -/
theorem selected_piece_energy (e b : Fin 5) (p : SelectedSupport e b)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤
      (numerator e.val (b.val - e.val) ^ 2 /
        (4294967295 : ℝ) ^ (b.val - e.val)) *
          ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
  obtain ⟨h, _, hc, he⟩ := supportIndexComponent_multi_uniform p.val
    (by rw [AES.word_card]; norm_num) f
  have ht := word_multiUniform_energy p.val.val.2 p.val.val.1 h
  rw [p.val.property.2, selected_uniformPositions_card e b p] at ht
  rw [he, hc]
  exact ht

/-- Generic support aggregation: arbitrary piece coefficient, one output
Cauchy--Schwarz loss, and exact orthogonality only on the input side. -/
theorem selected_output_energy_of_piece_energy
    (e b : Fin 5) (heb : e ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (hpiece : ∀ (p : SelectedSupport e b) (f : AES.WordState → ℝ),
      (∑ y, action residualStepKernel
        (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤
        C * ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2)
    (f : AES.WordState → ℝ) :
    (∑ y, (∑ p : SelectedSupport e b,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y) ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e b : ℝ) * C * ∑ x, f x ^ 2 := by
  let n : ℝ := Fintype.card (SelectedSupport e b)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ∑ y, n * ∑ p : SelectedSupport e b,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 :=
      Finset.sum_le_sum (fun y _ => OrdinaryGraphCaps.sum_sq_le_card
        (fun p : SelectedSupport e b =>
          action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y))
    _ = n * ∑ p : SelectedSupport e b, ∑ y,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ n * ∑ p : SelectedSupport e b,
        C * ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hn
      exact Finset.sum_le_sum (fun p _ => hpiece p f)
    _ = (n * C) * ∑ p : SelectedSupport e b, ∑ x,
        supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (n * C) * ∑ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hn hC)
      exact OrdinaryGraphCaps.selected_input_energy_le (0 : AES.Word)
        (by rw [AES.word_card]; norm_num) e b f
    _ = (ResidualIncidenceCoefficient.multiplicity e b : ℝ) * C * ∑ x, f x ^ 2 := by
      rw [show n = (ResidualIncidenceCoefficient.multiplicity e b : ℝ) by
        simp only [n, selectedSupport_card e b heb]]

/-- Size-grouped expansion and selected-support aggregation, before the
three certificate comparisons. -/
theorem selected_output_energy (e b : Fin 5) (heb : e ≤ b)
    (f : AES.WordState → ℝ) :
    (∑ y, (∑ p : SelectedSupport e b,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y) ^ 2) ≤
      squaredBound e b * ∑ x, f x ^ 2 := by
  have he := selected_output_energy_of_piece_energy e b heb
    (numerator e.val (b.val - e.val) ^ 2 / (4294967295 : ℝ) ^ (b.val - e.val))
    (div_nonneg (sq_nonneg _) (by positivity))
    (fun p g => selected_piece_energy e b p g) f
  convert he using 1
  unfold squaredBound
  ring

private theorem blockType_valid : ∀ j : Fin 14,
    (blockType j).1 ≤ (blockType j).2 := by decide

/-- The physical identity includes centering and output projection. The
remaining coefficient is the scalar bound for the actual input type. -/
theorem physical_thirteen_uniform_graph_energy (j : Fin 14) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      squaredBound (blockType j).1 (blockType j).2 * ∑ x, f x ^ 2 := by
  rw [OrdinaryGraphCaps.physical_thirteen_action_sum]
  exact selected_output_energy (blockType j).1 (blockType j).2 (blockType_valid j) f

abbrev uniformColumn := UniformGraphScalar.uniformColumn

/-- Energy form of the three unchanged certificate entries. -/
theorem physical_thirteen_energy (j : Fin 14) (hj : uniformColumn j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      (lambda * L 13 j) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_thirteen_uniform_graph_energy j f).trans
    (mul_le_mul_of_nonneg_right (certificate_uniform_bounds j hj).2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

/-- Actual physical-kernel norm cap; admission still requires the complete
source, compiled artifact and independent review gates. -/
theorem physical_thirteen_step_cap (j : Fin 14) (hj : uniformColumn j) :
    ‖kernelOperator (physicalBlock 13 j)‖ ≤ lambda * L 13 j :=
  kernelOperator_norm_le _ (certificate_uniform_bounds j hj).1 (physical_thirteen_energy j hj)

theorem system_thirteen_step_cap (j : Fin 14) (hj : uniformColumn j) :
    ‖PhysicalProjectionSystem.system.step 13 j‖ ≤ lambda * L 13 j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_thirteen_step_cap j hj

theorem physical_thirteen_six_step_cap :
    ‖kernelOperator (physicalBlock 13 6)‖ ≤ lambda * L 13 6 :=
  physical_thirteen_step_cap 6 (by decide)

theorem physical_thirteen_seven_step_cap :
    ‖kernelOperator (physicalBlock 13 7)‖ ≤ lambda * L 13 7 :=
  physical_thirteen_step_cap 7 (by decide)

theorem physical_thirteen_ten_step_cap :
    ‖kernelOperator (physicalBlock 13 10)‖ ≤ lambda * L 13 10 :=
  physical_thirteen_step_cap 10 (by decide)

theorem system_thirteen_six_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 6‖ ≤ lambda * L 13 6 :=
  system_thirteen_step_cap 6 (by decide)

theorem system_thirteen_seven_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 7‖ ≤ lambda * L 13 7 :=
  system_thirteen_step_cap 7 (by decide)

theorem system_thirteen_ten_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 10‖ ≤ lambda * L 13 10 :=
  system_thirteen_step_cap 10 (by decide)

end AESConcrete.UniformGraphCaps
