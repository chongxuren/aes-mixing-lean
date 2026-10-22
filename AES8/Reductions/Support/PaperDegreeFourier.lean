import AES8.Reductions.Support.PaperDegreeReverse
import AES8.Math.PaperKernelReindex
import AESConcrete.WordFourierCore

/-! Exact Fourier invariance of every byte-degree projection and counting
operator norm. These identities apply to arbitrary word kernels. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeFourier
open AESMixing AESConcrete.WordFourierCore AESConcrete.ByteGramFourier
open AESConcrete.DegreeHilbertSchmidt PaperKernelBounds
set_option autoImplicit false
set_option maxRecDepth 100000

theorem byte_identity : byteConjugate (identityKernel : Byte → Byte → ℝ) = identityKernel := by
  apply kernel_action_ext
  intro f
  simp only [byteConjugate, kernelCompose_action, identityKernel_action, byteFourier_twice]

theorem byte_degree (b : Bool) : byteConjugate (degreePiece (0 : Byte) b) = degreePiece 0 b := by
  cases b
  · exact activity_fourier_fixed
  · change byteConjugate (identityKernel - activityMatrix (0 : Byte)) =
      identityKernel - activityMatrix (0 : Byte)
    rw [byteConjugate_sub, byte_identity, activity_fourier_fixed]

theorem coordinate_conjugate (T : Fin 4 → Byte → Byte → ℝ) :
    wordConjugate (coordinateKernel T) = coordinateKernel (fun i => byteConjugate (T i)) := by
  change kernelCompose wordFourier (kernelCompose (coordinateKernel T) wordFourier) = _
  rw [wordFourier_tensor, coordinateKernel_compose, coordinateKernel_compose]
  rfl

theorem projection_fixed (a : Fin 4 → Bool) :
    wordConjugate (productProjection (0 : Byte) a) = productProjection 0 a := by
  change wordConjugate (coordinateKernel (fun i => degreePiece (0 : Byte) (a i))) = _
  rw [coordinate_conjugate]
  simp_rw [byte_degree]
  rfl

theorem conjugate_sum {I : Type*} [Fintype I] (K : I → Word → Word → ℝ) :
    wordConjugate (fun y x => ∑ i, K i y x) = fun y x => ∑ i, wordConjugate (K i) y x := by
  funext y x
  change (∑ a, wordFourier y a * ∑ b, (∑ i, K i a b) * wordFourier b x) = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Word))
    (t := (Finset.univ : Finset I))]
  simp only [wordConjugate, fourierConjugate, kernelCompose, Finset.mul_sum, wordFourier]

theorem degree_fixed (j : Fin 5) : wordConjugate (degreeKernel (0 : Byte) j) = degreeKernel 0 j := by
  unfold degreeKernel
  rw [conjugate_sum]
  funext y x
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : degreeIndex a = j
  · simp only [if_pos h, projection_fixed]
  · simp only [if_neg h, wordConjugate, fourierConjugate, kernelCompose, mul_zero,
      Finset.sum_const_zero, zero_mul]

theorem block_conjugate (K : Word → Word → ℝ) (i j : Fin 5) :
    wordConjugate (block 0 K i j) = block 0 (wordConjugate K) i j := by
  simp only [block, wordConjugate_compose, degree_fixed]

theorem fourier_norm (f : Word → ℝ) :
    ‖WithLp.toLp 2 (action wordFourier f)‖ = ‖WithLp.toLp 2 f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using wordFourier_energy f

theorem conjugate_norm_le (K : Word → Word → ℝ) :
    ‖kernelOperator (wordConjugate K)‖ ≤ ‖kernelOperator K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  let g : EuclideanSpace ℝ Word := WithLp.toLp 2 (action wordFourier (fun x => f x))
  have he : kernelOperator (wordConjugate K) f =
      WithLp.toLp 2 (action wordFourier (fun x => kernelOperator K g x)) := by
    ext y
    exact congrFun (wordConjugate_action K (fun x => f x)) y
  rw [he, fourier_norm]
  have hg : ‖g‖ = ‖f‖ := fourier_norm (fun x => f x)
  simpa only [hg] using (kernelOperator K).le_opNorm g

theorem conjugate_norm (K : Word → Word → ℝ) :
    ‖kernelOperator (wordConjugate K)‖ = ‖kernelOperator K‖ := by
  apply le_antisymm (conjugate_norm_le K)
  simpa only [wordConjugate_twice] using conjugate_norm_le (wordConjugate K)

theorem block_conjugate_norm (K : Word → Word → ℝ) (i j : Fin 5) :
    ‖kernelOperator (block 0 (wordConjugate K) i j)‖ = ‖kernelOperator (block 0 K i j)‖ := by
  rw [← block_conjugate, conjugate_norm]

end AES8.PaperDegreeFourier
