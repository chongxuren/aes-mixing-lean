import AES8.Estimates.Word.PaperDegreeThreeEndpointCoupling
import AES8.Estimates.Word.PaperDegreeThreeParityResponse
import AES8.Math.PaperKernelComposition
import AES8.Math.PaperFiberKernel

/-!
# Printed intermediate deductions in the degree-three parity proof

The endpoint branch proves some estimates through stronger interval/row bounds.
This companion checks the paper's explicit rounded row brackets and the
coupling-times-inverse norm deduction on the actual endpoint correction.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreePrintedDeductions
open AESMixing AESConcrete
open AESConcrete.ActivityEffectiveMetric
open AESConcrete.ActivityGramDominance AESConcrete.ActivityPairIntervals
open PaperDegreeThreeParityCounts PaperDegreeThreeParityResponse
open PaperDegreeThreeEndpointCoupling PaperDegreeThreeEndpointMetric
open PaperKernelBounds PaperKernelComposition PaperFiberKernel
set_option autoImplicit false
set_option maxRecDepth 100000

def oddBracket : ℝ := 1081/1000 + 3*(305/100000) + (1/16)*(3*(53/1000)+222/1000)
def evenBracket : ℝ := 2*(1081/1000) + 8*(305/100000) +
  8*(1/16)*(53/1000) + 2*(23/1000) + 2*(1/16)*(222/1000)

theorem printed_brackets :
    oddBracket = (11139625/10000000 : ℝ) ∧
    evenBracket = (228665/100000 : ℝ) ∧ oddBracket < 9/8 ∧ evenBracket < 229/100 := by
  norm_num [oddBracket, evenBracket]

theorem radius_below_printed_brackets :
    PaperDegreeThreeParityCounts.oddRow responseRadius 1 < (1024/255 : ℝ)*oddBracket ∧
    PaperDegreeThreeParityCounts.oddRow responseRadius 3 < (1024/255 : ℝ)*oddBracket ∧
    PaperDegreeThreeParityCounts.evenRow responseRadius 2 < (1024/255 : ℝ)*evenBracket := by
  norm_num [PaperDegreeThreeParityCounts.oddRow, PaperDegreeThreeParityCounts.evenRow,
    responseRadius, sizeInterval, scaleInterval, compressedInterval, concreteResources,
    frameFactor, ActivityPairIntervals.xi, oddBracket, evenBracket,
    ByteLineBounds.a3, ByteLineBounds.cubeBound, ByteGramResources.cubeNumerator,
    ByteLineBounds.b3, ByteLineBounds.mixedCubeBound, LineOverlap.eta1,
    LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag, MixedCodeBounds.f3,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3]

theorem odd_rows_printed (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Odd) :
    (∑ B : Odd, |G A.val B.val|) < (1024/255 : ℝ)*oddBracket := by
  have h := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset Odd)) =>
    entry_abs_le_radius G hG ⟨A.val, odd_interior A⟩ ⟨B.val, odd_interior B⟩)
  rw [odd_row_classification responseRadius A.val (Or.inl A.property)] at h
  rcases A.property with ha | ha
  · rw [ha] at h
    exact h.trans_lt radius_below_printed_brackets.1
  · rw [ha] at h
    exact h.trans_lt radius_below_printed_brackets.2.1

theorem even_rows_printed (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Even) :
    (∑ B : Even, |G A.val B.val|) < (1024/255 : ℝ)*evenBracket := by
  have h := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset Even)) =>
    entry_abs_le_radius G hG ⟨A.val, even_interior A⟩ ⟨B.val, even_interior B⟩)
  rw [even_row_classification responseRadius A.val (Or.inr A.property), A.property] at h
  exact h.trans_lt radius_below_printed_brackets.2.2

/-- The finite correction factorization gives the paper's norm-product bound,
without using its alternate absolute-row proof. -/
theorem correction_norm_product {I : Type*} [Fintype I] [DecidableEq I]
    (index : I → Fin 16) :
    ‖PaperKernelBounds.kernelOperator (fun i j : I => correction (index i) (index j))‖ ≤
      ‖PaperKernelBounds.kernelOperator (fun i : I => coupling (index i))‖^2 *
        ‖PaperKernelBounds.kernelOperator endpointInverse‖ := by
  let C : I → Bool → ℝ := fun i => coupling (index i)
  have he : (fun i j : I => correction (index i) (index j)) =
      kernelCompose C (kernelCompose endpointInverse (Matrix.conjTranspose C)) := by
    funext i j
    rw [correction_factorization]
    simp only [kernelCompose, Matrix.conjTranspose_apply, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    dsimp [C]
    ring
  rw [he, operator_comp, operator_comp, ← kernelOperator_adjoint]
  calc
    _ ≤ ‖PaperKernelBounds.kernelOperator C‖ *
        ‖(PaperKernelBounds.kernelOperator endpointInverse).comp (PaperKernelBounds.kernelOperator C).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖PaperKernelBounds.kernelOperator C‖ * (‖PaperKernelBounds.kernelOperator endpointInverse‖ *
        ‖(PaperKernelBounds.kernelOperator C).adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by simp only [LinearIsometryEquiv.norm_map]; ring

theorem odd_correction_norm :
    ‖PaperKernelBounds.kernelOperator (fun A B : Odd => correction A.val B.val)‖ ≤ oddCorrectionCap := by
  have h := correction_norm_product (fun A : Odd => A.val)
  rw [odd_coupling_norm_sq, endpoint_inverse_norm] at h
  simpa [oddCorrectionCap, div_eq_mul_inv, mul_assoc] using h

theorem even_correction_norm :
    ‖PaperKernelBounds.kernelOperator (fun A B : Even => correction A.val B.val)‖ ≤ evenCorrectionCap := by
  have h := correction_norm_product (fun A : Even => A.val)
  rw [even_coupling_norm_sq, endpoint_inverse_norm] at h
  simpa [evenCorrectionCap, div_eq_mul_inv, mul_assoc] using h

end AES8.PaperDegreeThreePrintedDeductions
