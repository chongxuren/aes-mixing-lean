import AES8.Estimates.Word.PaperDegreeThreeEndpointMetric
import AES8.Math.PaperKernelBounds

/-! Literal endpoint coupling norms from the frozen parity argument.
The two endpoint coordinates are Bool, and their columns are the actual k0,k1.
Rectangular Schur bounds are tight on the constant vector. The inverse endpoint
metric is checked by its exact two-by-two inverse and its (1,-1) eigenvector. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeEndpointCoupling
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric
open PaperDegreeThreeParityCounts
set_option autoImplicit false
set_option maxRecDepth 100000

def coupling (A : Fin 16) (b : Bool) : ℝ := if b then k1 A else k0 A

theorem coupling_nonneg (A : Fin 16) (b : Bool) : 0 ≤ coupling A b := by
  cases b <;> dsimp [coupling, k0, k1, xi] <;> positivity

theorem odd_card : Fintype.card Odd = 8 := by decide
theorem even_card : Fintype.card Even = 6 := by decide

def oddRow : ℝ := xi+xi^3
def evenRow : ℝ := 2*xi^2

theorem odd_row (A : Odd) : (∑ b : Bool, coupling A.val b) = oddRow := by
  rcases A.property with hA | hA <;>
    norm_num [coupling, k0, k1, hA, oddRow, xi]

theorem even_row (A : Even) : (∑ b : Bool, coupling A.val b) = evenRow := by
  have hA : maskSize A.val = 2 := A.property
  norm_num [coupling, k0, k1, hA, evenRow, xi]

theorem odd_column (b : Bool) : (∑ A : Odd, coupling A.val b) = 4*oddRow := by
  rw [sum_subtype IsOdd (fun A => coupling A b), sum_fin_sixteen]
  cases b <;> norm_num [coupling, k0, k1, IsOdd, mask_size_numeric, bitCount, oddRow, xi]

theorem even_column (b : Bool) : (∑ A : Even, coupling A.val b) = 6*xi^2 := by
  rw [sum_subtype IsEven (fun A => coupling A b), sum_fin_sixteen]
  cases b <;> norm_num [coupling, k0, k1, IsEven, mask_size_numeric, bitCount, xi]

/-- The same upper/lower norm argument applies to both actual endpoint blocks. -/
theorem coupling_norm_sq {I : Type*} [Fintype I] (K : I → Bool → ℝ)
    (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hK : ∀ i b, 0 ≤ K i b) (hrow : ∀ i, (∑ b : Bool, K i b) = r)
    (hcol : ∀ b, (∑ i : I, K i b) = c)
    (hcount : (Fintype.card I : ℝ)*r^2 = 2*(r*c)) :
    ‖PaperKernelBounds.kernelOperator K‖^2 = r*c := by
  have hupper := PaperKernelBounds.schur_operator_norm_sq K K r c hr hc hK
    (fun i b => by rw [Real.norm_eq_abs, abs_of_nonneg (hK i b)])
    (fun i => (hrow i).le) (fun b => (hcol b).le)
  let v : EuclideanSpace ℝ Bool := WithLp.toLp 2 (fun _ => 1)
  have hout (i : I) : PaperKernelBounds.kernelOperator K v i = r := by
    simpa [PaperKernelBounds.kernelOperator_apply, PaperKernelBounds.kernelAction, v]
      using hrow i
  have h := (PaperKernelBounds.kernelOperator K).le_opNorm v
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg v))).mpr h
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  simp only [hout, Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have hv : (∑ b : Bool, (v b)^2) = 2 := by norm_num [v]
  rw [hv] at hs
  nlinarith

theorem odd_coupling_norm_sq :
    ‖PaperKernelBounds.kernelOperator (fun A : Odd => coupling A.val)‖^2 =
      4*xi^2*(1+xi^2)^2 := by
  have h := coupling_norm_sq (fun A : Odd => coupling A.val) oddRow (4*oddRow)
    (by norm_num [oddRow, xi]) (by norm_num [oddRow, xi])
    (fun A b => coupling_nonneg A.val b) odd_row odd_column
    (by rw [odd_card]; ring)
  norm_num [oddRow, xi] at h ⊢
  exact h

theorem even_coupling_norm_sq :
    ‖PaperKernelBounds.kernelOperator (fun A : Even => coupling A.val)‖^2 = 12*xi^4 := by
  have h := coupling_norm_sq (fun A : Even => coupling A.val) evenRow (6*xi^2)
    (by norm_num [evenRow, xi]) (by norm_num [xi])
    (fun A b => coupling_nonneg A.val b) even_row even_column
    (by rw [even_card]; norm_num [evenRow, xi])
  norm_num [evenRow, xi] at h ⊢
  exact h

def endpointMetric (b c : Bool) : ℝ := if b = c then 1 else t
def endpointInverse (b c : Bool) : ℝ := (if b = c then 1 else -t)/det

/-- The displayed two-by-two block uses the actual empty/full coordinates. -/
theorem endpointMetric_actual (b c : Bool) : endpointMetric b c =
    activityMetric (if b then 15 else 0) (if c then 15 else 0) := by
  cases b <;> cases c
  · exact (activityMetric_self 0).symm
  · exact activityMetric_empty_full.symm
  · change t = activityMetric 15 0
    rw [activityMetric_symmetric]
    exact activityMetric_empty_full.symm
  · exact (activityMetric_self 15).symm

theorem endpoint_inverse (b c : Bool) :
    (∑ d : Bool, endpointMetric b d*endpointInverse d c) = if b = c then 1 else 0 := by
  cases b <;> cases c <;> norm_num [endpointMetric, endpointInverse, t, det, xi]

/-- Literal factorization of the correction already used by the metric leaf. -/
theorem correction_factorization (A B : Fin 16) :
    PaperDegreeThreeEndpointMetric.correction A B =
      ∑ b : Bool, ∑ c : Bool, coupling A b*endpointInverse b c*coupling B c := by
  unfold PaperDegreeThreeEndpointMetric.correction effectiveMetric
  norm_num [coupling, endpointInverse]
  unfold rankCorrection
  field_simp [ne_of_gt det_pos]
  ring

theorem endpoint_inverse_norm :
    ‖PaperKernelBounds.kernelOperator endpointInverse‖ = 1/(1-xi^4) := by
  let r : ℝ := 1/(1-xi^4)
  have hr : 0 ≤ r := by norm_num [r, xi]
  have hrow (b : Bool) : (∑ c : Bool, |endpointInverse b c|) = r := by
    cases b <;> norm_num [endpointInverse, r, t, det, xi]
  have hcol (c : Bool) : (∑ b : Bool, |endpointInverse b c|) = r := by
    cases c <;> norm_num [endpointInverse, r, t, det, xi]
  have hu := PaperKernelBounds.schur_operator_norm_sq endpointInverse
    (fun b c => |endpointInverse b c|) r r hr hr (fun _ _ => abs_nonneg _)
    (fun _ _ => by rw [Real.norm_eq_abs]) (fun b => (hrow b).le) (fun c => (hcol c).le)
  have hu' : ‖PaperKernelBounds.kernelOperator endpointInverse‖ ≤ r := by
    nlinarith [norm_nonneg (PaperKernelBounds.kernelOperator endpointInverse)]
  let v : EuclideanSpace ℝ Bool := WithLp.toLp 2 (fun b => if b then -1 else 1)
  have hv : 0 < ‖v‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hh := congrArg (fun f : EuclideanSpace ℝ Bool => f false) h
    norm_num [v] at hh
  have he : PaperKernelBounds.kernelOperator endpointInverse v = r • v := by
    ext b
    cases b <;> norm_num [PaperKernelBounds.kernelOperator_apply,
      PaperKernelBounds.kernelAction, endpointInverse, v, r, t, det, xi]
  have hl := (PaperKernelBounds.kernelOperator endpointInverse).le_opNorm v
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hl
  have hl' : r ≤ ‖PaperKernelBounds.kernelOperator endpointInverse‖ :=
    (mul_le_mul_iff_left₀ hv).mp (by simpa only [mul_comm] using hl)
  exact le_antisymm hu' hl'

end AES8.PaperDegreeThreeEndpointCoupling
