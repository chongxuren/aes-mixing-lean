import AES8.Estimates.Word.PaperActivityOnePrinted
import AES8.Estimates.Word.PaperSubsetArrayConsumers
import AES8.Estimates.Word.PaperActivityZeroPrinted
import AES8.Estimates.Word.PaperDegreeThreeParityEndpoint
import AES8.Estimates.Word.PaperSlopeConcrete
import AES8.Estimates.Word.PaperWordComparisonNumbers
import AESConcrete.DegreeHilbertSchmidt
import AESConcrete.DegreeCentering

/-!
# Paper-route directly damped degree blocks

The two exceptional blocks use the literal parity endpoints, applied to the
projected input before any norm is enlarged. The other blocks retain the
original two-substitution cap argument. General centering and projection
machinery is restated here so public paper consumers share this proof route.
The two raw degree-two boundary caps use the literal slope endpoint at
71/5000. Activity zero uses the printed full activity spectrum. The three
positive-degree array cases use their printed subset norms. The zero activity/
degree-one cases use the impossible shortened-dimension condition. All remaining
raw blocks use orthogonal contraction; the degree-three boundary is replaced
separately by its direct damped parity proof. The final comparison table is unchanged.
Constructive source preparation only; no attacks or manuscript/vendor edits.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperDampedDegreeBounds
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.DegreeHilbertSchmidt (block block_action)
open AESConcrete.WordFourierDiffusion (permutationKernel permutationKernel_action)
open PaperWordDegreeComparison (comparison normalizedComparison
  normalizedComparison_nonneg)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- General centering commutation; no numerical word bound is used. -/
theorem pointed_residual_commute {V : Type*} [Fintype V] [DecidableEq V]
    {D : V → V → ℝ} {z : V} (h : PointedBistochastic D z) (f : V → ℝ) :
    wordResidual z (action D f) = action D (wordResidual z f) := by
  simp only [wordResidual, action_sub, h.average_action, h.action_average]

theorem degree_idempotent (j : Fin 5) (f : AES.Word → ℝ) :
    degreeComponent 0 j (degreeComponent 0 j f) = degreeComponent 0 j f := by
  simp only [← degreeKernel_action, ← kernelCompose_action,
    degreeKernel_compose (0 : BinaryWord 8) (by norm_num [BinaryWord.card])]

/-- The Euclidean operator bound is applied to the projected input; the
second projection is removed by idempotence, with no denominator weakening. -/
theorem projected_diffusion_energy_of_norm
    (e : Equiv.Perm AES.Word) (i j : Fin 5) (cap : ℝ) (hc : 0 ≤ cap)
    (hnorm : ‖PaperKernelBounds.kernelOperator (block 0 (permutationKernel e) i j)‖ ≤ cap)
    (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 i j e f y^2) ≤
      cap^2 * ∑ x, degreeComponent 0 j f x^2 := by
  let v : EuclideanSpace ℝ AES.Word := WithLp.toLp 2 (degreeComponent 0 j f)
  have hn := (PaperKernelBounds.kernelOperator (block 0 (permutationKernel e) i j)).le_opNorm v
  have hb : ‖PaperKernelBounds.kernelOperator (block 0 (permutationKernel e) i j) v‖ ≤
      cap * ‖v‖ := hn.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg v))).mpr hb
  have he : (∑ y, action (block 0 (permutationKernel e) i j)
      (degreeComponent 0 j f) y^2) ≤ cap^2 * ∑ x, degreeComponent 0 j f x^2 := by
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq,
      PaperKernelBounds.kernelOperator_apply, PaperKernelBounds.kernelAction,
      Real.norm_eq_abs, sq_abs, v, action] using hs
  simpa only [block_action, permutationKernel_action, degree_idempotent,
    degreeTransfer] using he

/-- Ordinary 2-by-0 boundary from the literal slope spectral route. -/
theorem forward_activity_two_energy (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 0 (byteDiffusionOrientation false) f y^2) ≤
      (71/5000 : ℝ)^2 * ∑ x, degreeComponent 0 0 f x^2 :=
  projected_diffusion_energy_of_norm _ 2 0 (71/5000) (by norm_num)
    PaperSlopeConcrete.aes_norms.2.1.le f

/-- Ordinary 0-by-2 boundary from the literal slope reversal endpoint. -/
theorem forward_reverse_activity_two_energy (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 0 2 (byteDiffusionOrientation false) f y^2) ≤
      (71/5000 : ℝ)^2 * ∑ x, degreeComponent 0 2 f x^2 :=
  projected_diffusion_energy_of_norm _ 0 2 (71/5000) (by norm_num)
    PaperSlopeConcrete.aes_norms.2.2.2.le f

/-- The inverse boundary follows by the exact projected adjoint transfer. -/
theorem activity_two_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 2 0 (byteDiffusionOrientation inverse) f y^2) ≤
      (71/5000 : ℝ)^2 * ∑ x, degreeComponent 0 0 f x^2 := by
  cases inverse
  · exact forward_activity_two_energy f
  · have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
      0 2 (byteDiffusionOrientation false) (71/5000) forward_reverse_activity_two_energy f
    have he : (byteDiffusionOrientation false).symm =
        byteDiffusionOrientation true := by rfl
    simpa only [he] using h

theorem reverse_activity_two_energy (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ y, degreeTransfer 0 0 2 (byteDiffusionOrientation inverse) f y^2) ≤
      (71/5000 : ℝ)^2 * ∑ x, degreeComponent 0 2 f x^2 := by
  cases inverse
  · exact forward_reverse_activity_two_energy f
  · have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
      2 0 (byteDiffusionOrientation false) (71/5000) forward_activity_two_energy f
    have he : (byteDiffusionOrientation false).symm =
        byteDiffusionOrientation true := by rfl
    simpa only [he] using h

/-- Raw caps on the printed route. The degree-three boundary is bounded
by one here and replaced by the direct damped parity endpoint below. -/
def rawCaps (i j : Fin 5) : ℝ :=
  if i = 0 ∧ j = 0 then 63/655360
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 71/5000
  else if i = 1 ∧ j = 1 then 4/1125
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 64/729
  else if i = 2 ∧ j = 2 then 9/10
  else 1

theorem rawCaps_nonneg (i j : Fin 5) : 0 ≤ rawCaps i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rawCaps, Fin.ext_iff]

theorem rawCaps_energy (inverse : Bool) (i j : Fin 5) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, degreeTransfer 0 i j (byteDiffusionOrientation inverse) f y^2) ≤
      (rawCaps i j)^2 * ∑ x, degreeComponent 0 j f x^2 := by
  fin_cases i <;> fin_cases j
  · simpa [rawCaps] using PaperActivityZeroPrinted.energy inverse f hz hs
  · simpa [rawCaps] using PaperActivityOnePrinted.reverse_energy inverse f
  · simpa [rawCaps] using reverse_activity_two_energy inverse f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 0 3 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 0 4 f
  · simpa [rawCaps] using PaperActivityOnePrinted.forward_energy inverse f
  · simpa [rawCaps] using PaperSubsetArrayConsumers.aes_residual_11_energy inverse f
  · simpa [rawCaps] using PaperSubsetArrayConsumers.aes_residual_12_energy inverse f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 1 3 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 1 4 f
  · simpa [rawCaps] using activity_two_energy inverse f
  · simpa [rawCaps] using PaperSubsetArrayConsumers.aes_residual_21_energy inverse f
  · simpa [rawCaps] using PaperSubsetArrayConsumers.aes_residual_22_energy inverse f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 2 3 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 2 4 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 3 0 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 3 1 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 3 2 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 3 3 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 3 4 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 4 0 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 4 1 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 4 2 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 4 3 f
  · simpa [rawCaps] using WordNormSupport.aes_degree_universal_energy inverse 4 4 f

/-- In particular, the new boundary value is 4.6008/65536, below 4.601/65536. -/
theorem dampedCaps_le_comparison (i j : Fin 5)
    (h03 : ¬ (i = 0 ∧ j = 3)) (h30 : ¬ (i = 3 ∧ j = 0)) :
    WordNorm.dampedCaps rawCaps i j ≤ normalizedComparison i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [WordNorm.dampedCaps, rawCaps,
      normalizedComparison, comparison, Fin.ext_iff] at *

/-- Remove the residual only after proving the projected input is centered. -/
theorem residual_action_degree_eq (left right : Orientation) (inverse : Bool)
    (j : Fin 5) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (residualMatrix (wordKernel left right inverse) 0)
        (degreeComponent 0 j f) =
      action (wordKernel left right inverse) (degreeComponent 0 j f) := by
  have hc := degreeComponent_centered (0 : BinaryWord 8)
    (by norm_num [BinaryWord.card]) j f hz hs
  rw [residualMatrix_action (word_kernel_pointed left right inverse),
    wordResidual_eq_self 0 _ hc.1 hc.2]

/-- Every block keeps its projected-input norm. The two exceptional cases
instantiate the literal parity scalars on that projected input itself. -/
theorem direct_degree_bound (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    l2 (degreeComponent 0 i
      (action (wordKernel left right inverse) (degreeComponent 0 j f))) ≤
      normalizedComparison i j * l2 (degreeComponent 0 j f) := by
  by_cases h03 : i = 0 ∧ j = 3
  · rcases h03 with ⟨rfl, rfl⟩
    obtain ⟨c, hc, hcap, henergy⟩ :=
      PaperDegreeThreeParityEndpoint.exists_reverse_energy_scalar left right inverse
    have h := henergy (degreeComponent 0 3 f)
    simp only [ReverseDegreeThree.reverseBlockKernel, kernelCompose_action,
      degreeKernel_action, degree_idempotent] at h
    rw [residual_action_degree_eq left right inverse 3 f hz hs] at h
    have hcap2 : c^2 ≤ (33 / (10 * 65536) : ℝ)^2 :=
      pow_le_pow_left₀ hc hcap.le 2
    have he := h.trans (mul_le_mul_of_nonneg_right hcap2
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    simpa [normalizedComparison, comparison, div_div] using
      (l2_le_of_energy _ _ (33 / (10 * 65536)) (by norm_num) he)
  · by_cases h30 : i = 3 ∧ j = 0
    · rcases h30 with ⟨rfl, rfl⟩
      obtain ⟨c, hc, hcap, henergy⟩ :=
        PaperDegreeThreeParityEndpoint.exists_forward_energy_scalar left right inverse
      have h := henergy (degreeComponent 0 0 f)
      simp only [DampedDegreeThree.forwardBlockKernel, kernelCompose_action,
        degreeKernel_action, degree_idempotent] at h
      rw [residual_action_degree_eq left right inverse 0 f hz hs] at h
      have hcap2 : c^2 ≤ (33 / (10 * 65536) : ℝ)^2 :=
        pow_le_pow_left₀ hc hcap.le 2
      have he := h.trans (mul_le_mul_of_nonneg_right hcap2
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      simpa [normalizedComparison, comparison, div_div] using
        (l2_le_of_energy _ _ (33 / (10 * 65536)) (by norm_num) he)
    · have h := WordNorm.two_substitution_degree_bound_of_caps
        (channel_resources left) (channel_resources right)
        (byteDiffusionOrientation inverse) rawCaps rawCaps_nonneg
        (rawCaps_energy inverse) i j f hz hs
      have h' := h.trans (mul_le_mul_of_nonneg_right (dampedCaps_le_comparison i j h03 h30)
        (l2_nonneg (degreeComponent 0 j f)))
      simpa only [wordKernel] using h'

/-- General residual/projection assembly, now using the owned paper route. -/
theorem residual_block_l2 (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    l2 (action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f) ≤
      normalizedComparison i j * l2 f := by
  rw [block_action, residualMatrix_action (word_kernel_pointed left right inverse)]
  have hb : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have hw : 1 < Fintype.card AES.Word := by
    norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]
  have hd := normalizedComparison_nonneg i j
  by_cases hj : j = 0
  · subst j
    have hc : wordResidual (0 : AES.Word) (degreeComponent 0 0 f) =
        degreeComponent 0 0 (wordResidual 0 f) := by
      have hp : PointedBistochastic (degreeKernel (0 : BinaryWord 8) 0)
          (0 : AES.Word) := degree_zero_pointed (0 : BinaryWord 8) hb
      simpa only [degreeKernel_action] using pointed_residual_commute hp f
    rw [hc]
    have h := direct_degree_bound left right inverse i 0
      (wordResidual 0 f) (wordResidual_at_zero 0 f) (wordResidual_sum 0 f hw)
    have he := (degreeComponent_energy_le (0 : BinaryWord 8) hb 0 (wordResidual 0 f)).trans
      (residual_energy_le 0 f hw)
    exact h.trans (mul_le_mul_of_nonneg_left
      (l2_le_of_energy _ _ 1 (by norm_num) (by simpa using he) |>.trans_eq (one_mul _)) hd)
  · have hc := DegreeCentering.positive_degree_centered (0 : BinaryWord 8) hb j hj f
    have hz : degreeComponent 0 j f (0 : AES.Word) = 0 := hc.1
    rw [wordResidual_eq_self 0 _ hz hc.2]
    have h := direct_degree_bound left right inverse i j (degreeComponent 0 j f) hz hc.2
    rw [degree_idempotent] at h
    have he := degreeComponent_energy_le (0 : BinaryWord 8) hb j f
    exact h.trans (mul_le_mul_of_nonneg_left
      (l2_le_of_energy _ _ 1 (by norm_num) (by simpa using he) |>.trans_eq (one_mul _)) hd)

theorem residual_block_table_l2 (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    l2 (action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f) ≤
      (comparison i j / 65536) * l2 f :=
  residual_block_l2 left right inverse i j f

theorem residual_block_table_energy (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    (∑ y, action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f y ^ 2) ≤
      (comparison i j / 65536)^2 * ∑ x, f x^2 := by
  have hs := mul_self_le_mul_self (l2_nonneg _)
    (residual_block_table_l2 left right inverse i j f)
  simp only [← pow_two] at hs
  simpa only [mul_pow, l2_sq] using hs

end AES8.PaperDampedDegreeBounds
