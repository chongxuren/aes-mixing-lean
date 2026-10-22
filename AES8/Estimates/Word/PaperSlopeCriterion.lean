import AES8.Math.LiteralSlopeActual
import AES8.Reductions.Graph.PaperSlopePhysicalEnergy
import AES8.Math.PaperSlopeEndpoints
import AES8.Reductions.Support.PaperCirculantReverse

/-! The degree-two norm bound for an actual linear MDS permutation with the
specified geometric slope classes. Actual input and output energy interfaces
are discharged here; no scalar norm or Gram estimate is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeCriterion
open AESMixing WordActivityFrame
open AESMixing.AES (maskBit)
open PaperSlopeCoincidenceMatrix PaperSlopeMetricComparison PaperSlopeMask
open PaperSlopeLinearGraph PaperSlopeEnergyLabels PaperSlopePhysicalFamily
open PaperSlopePhysicalEnergy PaperSlopeFrameInput PaperSlopeEndpoints
open PaperKernelBounds AESConcrete.DegreeHilbertSchmidt AESConcrete.WordFourierDiffusion
set_option autoImplicit false
set_option maxRecDepth 100000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem sign_twice (n : ℕ) (x : ℝ) : (-1 : ℝ)^n * ((-1 : ℝ)^n*x) = x := by
  rw [← mul_assoc, ← pow_two, ← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

theorem signedDiffusion_from_coefficients
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (u : Fin 16 → ℝ) (y : Fin 4 → F) :
    signedDiffusion L (signedCoefficients u) y =
      ∑ A : Interior, frameColumn 0 (maskBit (mask A.val)) (L.symm y) * u (mask A.val) := by
  unfold signedDiffusion signedCoefficients diffusionColumn
  apply Finset.sum_congr rfl
  intro A _
  rw [sign_twice]
  have hb : inputBits A = maskBit (mask A.val) := by
    funext i
    exact (mask_bit A.val i).symm
  rw [hb, mul_comm]

theorem signed_projection
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (u : Fin 16 → ℝ) (y : Fin 4 → F) :
    degreeComponent 0 2 (signedDiffusion L (signedCoefficients u)) y =
      ∑ A : Interior, projectedColumn L.toEquiv (mask A.val) y * u (mask A.val) := by
  simp only [signedDiffusion_from_coefficients, projectedColumn,
    ← degreeKernel_action, action, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  change degreeKernel 0 2 y x * (frameColumn 0 (maskBit (mask A.val)) (L.symm x) * u (mask A.val)) = _
  rw [mul_assoc]
  rfl

theorem block_action_eq_signed (hq : Fintype.card F = 256)
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (f : (Fin 4 → F) → ℝ) :
    action (block 0 (permutationKernel L.toEquiv) 2 0) f =
      degreeComponent 0 2 (signedDiffusion L (signedCoefficients (coefficients f))) := by
  rw [block_action, permutationKernel_action]
  have hf : (fun y => degreeComponent 0 0 f (L.symm y)) =
      fun y => ∑ A : Fin 16, frameColumn 0 (maskBit A) (L.symm y) * coefficients f A := by
    funext y
    exact degree_zero_synthesis hq f (L.symm y)
  change degreeComponent 0 2 (fun y => degreeComponent 0 0 f (L.symm y)) = _
  rw [hf]
  funext y
  exact (projected_synthesis_interior (by omega) L.toEquiv (by exact map_zero L)
    (coefficients f) y).trans (signed_projection L (coefficients f) y).symm

theorem block_energy_eq_scaledGram (hq : Fintype.card F = 256)
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hc : SameSlopeClasses (graphCode L.toLinearMap) hL) (f : (Fin 4 → F) → ℝ) :
    (256 : ℝ)^2 * (∑ y, action (block 0 (permutationKernel L.toEquiv) 2 0) f y^2) =
      PaperSlopeClassGram.scaledGram (signedCoefficients (coefficients f)) := by
  rw [block_action_eq_signed hq]
  exact degree2_energy_scaledGram L hL hq hc _

theorem forward_norm_sq_lt (hq : Fintype.card F = 256)
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hc : SameSlopeClasses (graphCode L.toLinearMap) hL) :
    ‖kernelOperator (block 0 (permutationKernel L.toEquiv) 2 0)‖^2 <
      (66/(5*256^2) : ℝ) := by
  apply PaperSlopeLiteral.operator_norm_sq_lt _ (fun f => signedCoefficients (coefficients (fun x => f x)))
  · intro f
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using
      coefficient_metric_le_input hq (fun x => f x)
  · intro f
    have he := block_energy_eq_scaledGram hq L hL hc (fun x => f x)
    have hb := classGram_le_comparison (signedCoefficients (coefficients (fun x => f x)))
    rw [← he] at hb
    simpa only [EuclideanSpace.norm_sq_eq, kernelOperator_apply, kernelAction,
      Real.norm_eq_abs, sq_abs, action] using hb

theorem forward_norm_lt (hq : Fintype.card F = 256)
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hc : SameSlopeClasses (graphCode L.toLinearMap) hL) :
    ‖kernelOperator (block 0 (permutationKernel L.toEquiv) 2 0)‖ < (71/5000 : ℝ) := by
  have h := (forward_norm_sq_lt hq L hL hc).trans PaperSlopeGroupBounds.squared_norm_comparison
  exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 71/5000)).mp h

/-- Both boundary blocks for every represented circulant MDS map on the
canonical256-element byte field. The only analytic assumptions are the
original graph MDS property and its literal geometric slope classes. -/
theorem circulant_norms
    (c : Fin 4 → AESMixing.BinaryWord 8)
    (L : (Fin 4 → AESMixing.BinaryWord 8) ≃ₗ[AESMixing.BinaryWord 8]
      (Fin 4 → AESMixing.BinaryWord 8))
    (he : ∀ x, L x = fieldMatrix (PaperCirculantReverse.circulant c) x)
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hc : SameSlopeClasses (graphCode L.toLinearMap) hL) :
    (‖kernelOperator (block 0 (permutationKernel L.toEquiv) 2 0)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel L.toEquiv) 2 0)‖ < (71/5000 : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel L.toEquiv) 0 2)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel L.toEquiv) 0 2)‖ < (71/5000 : ℝ)) := by
  have hq : Fintype.card (AESMixing.BinaryWord 8) = 256 := by
    norm_num [AESMixing.BinaryWord.card]
  have hr := PaperCirculantReverse.circulant_boundary_norm_eq c L.toEquiv he 2 0
  exact ⟨forward_norm_sq_lt hq L hL hc, forward_norm_lt hq L hL hc,
    by rw [hr]; exact forward_norm_sq_lt hq L hL hc,
    by rw [hr]; exact forward_norm_lt hq L hL hc⟩

end AES8.PaperSlopeCriterion
