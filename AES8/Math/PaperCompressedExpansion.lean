import AES8.Math.PaperTensorCompression
import AES8.Math.PaperKernelComposition

/-! Bilinearity of actual outside-vector compression, before taking norms. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperCompressedExpansion
open AESMixing PaperKernelBounds PaperKernelLinear PaperTensorCompression PaperKernelComposition
set_option autoImplicit false
variable {X Y U W S T : Type*} [Fintype X] [Fintype Y] [Fintype U] [Fintype W]
  [Fintype S] [Fintype T] [DecidableEq X]

theorem compressed_expansion (K : (Y × U) → (X × W) → ℝ)
    (a : S → U → ℝ) (b : T → W → ℝ) (c : S → ℝ) (d : T → ℝ) :
    compressed K (fun u => ∑ s, c s * a s u) (fun v => ∑ t, d t * b t v) =
      fun y x => ∑ s, ∑ t, (c s * d t) * compressed K (a s) (b t) y x := by
  funext y x
  unfold compressed
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset W)) (t := (Finset.univ : Finset S))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset U)) (t := (Finset.univ : Finset S))]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset W)) (t := (Finset.univ : Finset T))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset U)) (t := (Finset.univ : Finset T))]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- The residual projections remain inside each term. -/
theorem sandwich_expansion [DecidableEq Y]
    (K : (Y × U) → (X × W) → ℝ) (R : Y → Y → ℝ) (L : X → X → ℝ)
    (a : S → U → ℝ) (b : T → W → ℝ) (c : S → ℝ) (d : T → ℝ) :
    kernelOperator (kernelCompose R (kernelCompose
      (compressed K (fun u => ∑ s, c s * a s u) (fun v => ∑ t, d t * b t v)) L)) =
      ∑ s, ∑ t, (c s * d t) •
        kernelOperator (kernelCompose R (kernelCompose (compressed K (a s) (b t)) L)) := by
  rw [compressed_expansion]
  simp_rw [compose_sum_right, compose_scale_right, compose_sum_left, compose_scale_left,
    operator_sum, operator_smul]

end AES8.PaperCompressedExpansion
