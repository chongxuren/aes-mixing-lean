import AESConcrete.DegreeThreeFrameEnergy
import AESConcrete.ActivityGramDominance
import AESConcrete.WeightedDiagonalDominance
import AESConcrete.KernelOperator
import AESMixing.DegreeAdjoint

/-!
# Direct damped forward degree-three AES block

This composes the actual Gram intervals, exact finite row comparison,
weighted diagonal-dominance theorem and effective input metric. It proves
the forward P3 K P0 block on arbitrary degree-zero inputs, without assuming
a word-level norm or a raw undamped degree-three cap. The reverse block and
the complete word/round theorem remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.DampedDegreeThree
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActualDegreeThreeGram
open AESConcrete.DegreeThreeFrameEnergy
open AESConcrete.ActivityEffectiveMetric
open AESConcrete.ActivityGramDominance

set_option maxRecDepth 100000

theorem actual_entry_bounds (left right : Orientation) (inverse : Bool) :
    EntryBounds (degreeThreeGram left right inverse) := by
  intro A B
  exact actual_degreeThreeGram_mem left right inverse A.val B.val

theorem effectiveMetric_symmetric (A B : Fin 16) : effectiveMetric A B = effectiveMetric B A := by
  unfold effectiveMetric rankCorrection
  rw [activityMetric_symmetric A B]
  ring

theorem actual_gram_domination (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    qForm u (degreeThreeGram left right inverse) ≤ comparisonLambda*fullEnergy u := by
  let G := degreeThreeGram left right inverse
  let M : Interior → Interior → ℝ := fun A B => comparisonLambda*effectiveMetric A.val B.val-G A.val B.val
  have hM : ∀ A B, M A B = M B A := by
    intro A B
    dsimp [M, G]
    rw [effectiveMetric_symmetric, degreeThreeGram_symmetric]
  have hrow (A : Interior) :
      (∑ B : Interior, if A = B then 0 else |M A B| * rowWeight B.val) ≤ M A A * rowWeight A.val := by
    have h := weighted_row_dominance G (actual_entry_bounds left right inverse) A
    have he (B : Interior) :
        (if B.val = A.val then (0 : ℝ) else rowWeight B.val*|comparisonLambda*effectiveMetric A.val B.val-G A.val B.val|) =
        if A = B then 0 else |M A B| * rowWeight B.val := by
      by_cases hab : A = B
      · subst B
        simp
      · have hv : B.val ≠ A.val := fun hv => hab (Subtype.ext hv.symm)
        simp only [hv, hab, if_false, M]
        ring
    simp_rw [he] at h
    dsimp [M] at *
    linarith
  have hp := WeightedDiagonalDominance.weighted_diagonal_nonneg M
    (fun A => rowWeight A.val) hM (fun A => rowWeight_pos A.val) hrow (fun A => u A.val)
  have he : (∑ A : Interior, ∑ B : Interior, u A.val*u B.val*M A B) =
      comparisonLambda*effectiveEnergy u -
        qForm (fun A : Interior => u A.val) (fun A B => G A.val B.val) := by
    simp only [M, effectiveEnergy, qForm, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    ring
  rw [he] at hp
  rw [degreeThreeGram_interior]
  calc
    _ ≤ comparisonLambda*effectiveEnergy u := by linarith
    _ ≤ comparisonLambda*fullEnergy u := mul_le_mul_of_nonneg_left
      (effectiveEnergy_le_fullEnergy u) (by norm_num [comparisonLambda])

theorem actual_frame_energy_bound (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    (∑ y, (outputSynthesis left right inverse u y)^2) ≤
      (33 / (10*65536) : ℝ)^2 * ∑ x, (frameSynthesis u x)^2 := by
  have h := actual_gram_domination left right inverse u
  rw [← outputSynthesis_energy, ← frameSynthesis_energy] at h
  norm_num [comparisonLambda] at h ⊢
  linarith

theorem actual_forward_degree_three_energy (left right : Orientation) (inverse : Bool)
    (f : (Fin 4 → Byte) → ℝ) :
    (∑ y, (degreeComponent 0 3 (action (residualMatrix (wordKernel left right inverse) 0)
      (degreeComponent 0 0 f)) y)^2) ≤
      (33 / (10*65536) : ℝ)^2 * ∑ x, (degreeComponent 0 0 f x)^2 := by
  have h := actual_frame_energy_bound left right inverse (normalizedCoefficients f)
  simp only [outputSynthesis_eq, ← normalized_reconstruction] at h
  exact h

def forwardBlockKernel (left right : Orientation) (inverse : Bool) :
    (Fin 4 → Byte) → (Fin 4 → Byte) → ℝ :=
  kernelCompose (degreeKernel 0 3)
    (kernelCompose (residualMatrix (wordKernel left right inverse) 0) (degreeKernel 0 0))

theorem forwardBlock_energy (left right : Orientation) (inverse : Bool)
    (f : (Fin 4 → Byte) → ℝ) :
    (∑ y, (action (forwardBlockKernel left right inverse) f y)^2) ≤
      (33 / (10*65536) : ℝ)^2 * ∑ x, (f x)^2 := by
  simp only [forwardBlockKernel, kernelCompose_action, degreeKernel_action]
  exact (actual_forward_degree_three_energy left right inverse f).trans
    (mul_le_mul_of_nonneg_left
      (degreeComponent_energy_le (0 : Byte) (by norm_num [BinaryWord.card]) 0 f) (sq_nonneg _))

theorem forwardBlock_operator_norm (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (forwardBlockKernel left right inverse)‖ ≤ (33 / (10*65536) : ℝ) :=
  kernelOperator_norm_le _ (by norm_num) (forwardBlock_energy left right inverse)

end AESConcrete.DampedDegreeThree
