import AES8.Reductions.Return.PaperAESFixedStepFibers
import AES8.Reductions.Source.PaperAESLocalResources
import AES8.Recurrence.PaperComparisonPowers

/-!
# Literal scaled fixed-step coefficient

Frozen paper f902bb94, `eq:step-closed-form`. Both incidence fibers belong
to the same reduced code. The identity below retains their shared rank
`min s (min i j)`; it never multiplies separately rounded step caps.
The analytic result acts on arbitrary signed real or complex inputs.
Physical shortening, Fourier choice and projection transport are separate.
Constructive proof validation only; no attacks or numerical searches.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESFixedStepBounds
open AESMixing PaperMDSGram PaperKernelBounds PaperGraphResponseMatrix
open PaperAESIncidence AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable

/-- The common rank is a property of one code with two coordinate sides. -/
theorem common_rank (i j s : ℕ) (hfit : 2 * s ≤ i + j) :
    s + min s (min i j) = min s i + min s j := by
  omega

/-- The paper's exact cancellation, with all subtractions in the real
exponent justified from their original natural multiplicities. -/
theorem scaled_fiber_coefficient (i j s : ℕ) (hfit : 2 * s ≤ i + j) :
    (4294967296 : ℝ) *
      (graphCoefficient i j s *
        Real.sqrt ((4294967296 : ℝ) ^ (s - min s i))) *
        Real.sqrt ((4294967296 : ℝ) ^ (s - min s j)) =
      Real.rpow (4294967296 : ℝ)
        (((i : ℝ) + j - 2 - (min s (min i j) : ℕ)) / 2) := by
  have hq : (0 : ℝ) < 4294967296 := by norm_num
  rw [word_sqrt_multiplicity, word_sqrt_multiplicity]
  unfold graphCoefficient
  have hr := common_rank i j s hfit
  have hr' : (s : ℝ) + (min s (min i j) : ℕ) =
      (min s i : ℕ) + (min s j : ℕ) := by exact_mod_cast hr
  have hL : ((s - min s i : ℕ) : ℝ) = (s : ℝ) - (min s i : ℕ) :=
    Nat.cast_sub (Nat.min_le_left _ _)
  have hR : ((s - min s j : ℕ) : ℝ) = (s : ℝ) - (min s j : ℕ) :=
    Nat.cast_sub (Nat.min_le_left _ _)
  rw [hL, hR]
  calc
    _ = Real.rpow (4294967296 : ℝ)
        (1 + (((i : ℝ) + j - 4 - s) / 2) +
          (((s : ℝ) - (min s i : ℕ)) / 2) +
          (((s : ℝ) - (min s j : ℕ)) / 2)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_add hq, Real.rpow_add hq, Real.rpow_add hq, Real.rpow_one]
      ring
    _ = _ := by congr 1; linarith

/-- The actual local AES resources, in the normalization used by the step. -/
theorem local_caps (adjoint fourier : Bool) :
    ‖kernelOperator (variant adjoint fourier)‖ ≤ nu ∧
      ∀ x, ‖kernelOperator (variant adjoint fourier)
        (PaperEncoding.basisVector x)‖ ^ 2 ≤ PaperWordMixedGram.delta := by
  constructor
  · have h := (PaperAESLocalResources.local_resources adjoint fourier).1.le
    have hs : Real.sqrt ((2 : ℝ) ^ 32) = 65536 := by
      rw [show (2 : ℝ) ^ 32 = 65536 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hop : kernelOperator (variant adjoint fourier) =
        AESConcrete.kernelOperator (variant adjoint fourier) := by ext f y; rfl
    rw [hop]
    simpa only [hs, nu] using h
  · intro x
    exact (PaperAESSource.residualVariant_basis_norm_sq_lt_current adjoint fourier x).le.trans
      (by norm_num [PaperWordMixedGram.delta])

/-- The smaller-dimension MDS step has the literal paper coefficient. No
operator bound or input-distribution property occurs among its premises. -/
theorem reduced_real_norm {i j : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin j) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hfit : 2 * s ≤ i + j) (adjoint fourier : Bool) :
    (4294967296 : ℝ) *
      ‖kernelOperator (outsideMappedMatrix C (graphCoefficient i j s)
        (variant adjoint fourier))‖ ≤ PaperComparisonPowers.stepCoefficient i j s := by
  have h := PaperAESFixedStepFibers.outsideMapped_norm C s hC
    (by simpa only [Fintype.card_sum, Fintype.card_fin] using (show s ≤ i + j by omega))
    (graphCoefficient i j s) nu PaperWordMixedGram.delta
    (Real.rpow_nonneg (by norm_num) _) nu_nonneg PaperWordMixedGram.delta_nonneg
    (variant adjoint fourier) (local_caps adjoint fourier).1
    (local_caps adjoint fourier).2
  simp only [Fintype.card_fin, AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat] at h
  have hc : (4294967296 : ℝ) *
      ((graphCoefficient i j s * Real.sqrt ((4294967296 : ℝ) ^ (s - min s i))) *
        ((nu ^ min s i * Real.rpow PaperWordMixedGram.delta (((i : ℝ) - (min s i : ℕ)) / 2)) *
        Real.sqrt ((4294967296 : ℝ) ^ (s - min s j)))) =
      PaperComparisonPowers.stepCoefficient i j s := by
    calc
      _ = ((4294967296 : ℝ) *
          (graphCoefficient i j s * Real.sqrt ((4294967296 : ℝ) ^ (s - min s i))) *
          Real.sqrt ((4294967296 : ℝ) ^ (s - min s j))) *
          (nu ^ min s i * Real.rpow PaperWordMixedGram.delta (((i : ℝ) - (min s i : ℕ)) / 2)) := by ring
      _ = _ := by
        rw [scaled_fiber_coefficient i j s hfit]
        simp only [PaperComparisonPowers.stepCoefficient, PaperComparison.q,
          PaperComparison.C, PaperComparison.sqrtQ, PaperComparison.E,
          Rat.cast_div, Rat.cast_ofNat, nu, PaperWordMixedGram.delta, min_comm i s]
        ring
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans_eq hc

theorem stepCoefficient_nonneg (i j s : ℕ) :
    0 ≤ PaperComparisonPowers.stepCoefficient i j s := by
  unfold PaperComparisonPowers.stepCoefficient
  dsimp only
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num [PaperComparison.q]) _)
    (pow_nonneg (by norm_num [PaperComparison.C, PaperComparison.sqrtQ]) _))
    (Real.rpow_nonneg (div_nonneg (sq_nonneg _)
      (by norm_num [PaperComparison.q])) _)

/-- Arbitrary complex coefficients preserve their signed-real cancellations. -/
theorem reduced_complex_energy {i j : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin j) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hfit : 2 * s ≤ i + j) (adjoint fourier : Bool)
    (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖kernelAction (fun y x =>
      (((4294967296 : ℝ) * outsideMappedMatrix C (graphCoefficient i j s)
        (variant adjoint fourier) y x : ℝ) : ℂ)) f y‖ ^ 2) ≤
      PaperComparisonPowers.stepCoefficient i j s ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
  refine PaperWholeGraphReturn.complex_energy_of_real
    (fun y x => (4294967296 : ℝ) * outsideMappedMatrix C (graphCoefficient i j s)
      (variant adjoint fourier) y x)
    (PaperComparisonPowers.stepCoefficient i j s ^ 2) ?_ f
  intro g
  have hn : ‖kernelOperator (fun y x => (4294967296 : ℝ) *
      outsideMappedMatrix C (graphCoefficient i j s) (variant adjoint fourier) y x)‖ ≤
      PaperComparisonPowers.stepCoefficient i j s := by
    have he : kernelOperator (fun y x => (4294967296 : ℝ) *
        outsideMappedMatrix C (graphCoefficient i j s) (variant adjoint fourier) y x) =
        (4294967296 : ℝ) • kernelOperator
          (outsideMappedMatrix C (graphCoefficient i j s) (variant adjoint fourier)) := by
      ext v y
      change (∑ x, (4294967296 : ℝ) *
        outsideMappedMatrix C (graphCoefficient i j s) (variant adjoint fourier) y x * v x) =
        (4294967296 : ℝ) * ∑ x,
          outsideMappedMatrix C (graphCoefficient i j s) (variant adjoint fourier) y x * v x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4294967296)]
    exact reduced_real_norm C s hC hfit adjoint fourier
  exact PaperEncoding.local_energy_of_norm _ _ (stepCoefficient_nonneg i j s) hn g

/-- Operator-norm spelling of the same all-complex-input statement. -/
theorem reduced_complex_norm {i j : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin j) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hfit : 2 * s ≤ i + j) (adjoint fourier : Bool) :
    ‖kernelOperator (fun y x =>
      (((4294967296 : ℝ) * outsideMappedMatrix C (graphCoefficient i j s)
        (variant adjoint fourier) y x : ℝ) : ℂ))‖ ≤
      PaperComparisonPowers.stepCoefficient i j s := by
  have hn := operator_norm_sq_le_of_energy _
    (PaperComparisonPowers.stepCoefficient i j s ^ 2) (sq_nonneg _)
    (reduced_complex_energy C s hC hfit adjoint fourier)
  exact (sq_le_sq₀ (norm_nonneg _) (stepCoefficient_nonneg i j s)).mp hn

end AES8.PaperAESFixedStepBounds
