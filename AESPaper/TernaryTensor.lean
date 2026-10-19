import AESPaper.UniformBias
import AESMixing.ProductProjection

/-!
# Orthogonal J/Z/R tensor projections on arbitrary joint vectors

The labels 0, 1, and 2 select full uniform, activity bias, and residual
projection. Each coordinate has three orthogonal projections summing to the
identity. Their tensor products therefore give a complete orthogonal
decomposition. No product-law assumption is made about the input vector.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.TernaryTensor
open AESMixing
open AESPaper.UniformBias (piece channelPiece)

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- A literal ternary output projector, with every coordinate label retained. -/
def tensorProjection (z : V) (a : I → Fin 3) (y x : I → V) : ℝ :=
  ∏ i, piece z (a i) (y i) (x i)

/-- The channel term selected by the same literal ternary pattern. -/
def tensorChannel (D : I → V → V → ℝ) (z : V) (a : I → Fin 3) :
    (I → V) → (I → V) → ℝ :=
  coordinateKernel (fun i => channelPiece (D i) z (a i))

theorem tensorProjection_symmetric (z : V) (a : I → Fin 3) (x y : I → V) :
    tensorProjection z a x y = tensorProjection z a y x := by
  unfold tensorProjection
  apply Finset.prod_congr rfl
  intro i _
  exact UniformBias.piece_symmetric z (a i) (x i) (y i)

theorem tensorProjection_compose (z : V) (hn : 1 < Fintype.card V)
    (a b : I → Fin 3) :
    kernelCompose (tensorProjection z a) (tensorProjection z b) =
      if a=b then tensorProjection z a else 0 := by
  funext y x
  have hprod : kernelCompose (tensorProjection z a) (tensorProjection z b) y x =
      ∏ i, kernelCompose (piece z (a i)) (piece z (b i)) (y i) (x i) := by
    unfold kernelCompose tensorProjection
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => piece z (a i) (y i) v *
      piece z (b i) v (x i))).symm
  rw [hprod]
  simp_rw [UniformBias.piece_compose z hn]
  by_cases hab : a=b
  · subst b
    simp [tensorProjection]
  · simp only [hab, if_false, Pi.zero_apply]
    have hw : ∃ i, a i ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem tensorProjection_sum (z : V) (x y : I → V) :
    (∑ a : I → Fin 3, tensorProjection z a x y) = identityKernel x y := by
  change (∑ a : I → Fin 3, ∏ i, piece z (a i) (x i) (y i)) = _
  rw [← Fintype.prod_sum (fun i b => piece z b (x i) (y i))]
  simp_rw [UniformBias.piece_sum_apply]
  by_cases hxy : x=y
  · subst y
    simp [identityKernel]
  · simp only [identityKernel, hxy, if_false]
    have hw : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem tensorProjection_decomposition (z : V) (f : (I → V) → ℝ) :
    (fun x => ∑ a : I → Fin 3, action (tensorProjection z a) f x) = f := by
  funext x
  have h : (∑ a : I → Fin 3, action (tensorProjection z a) f x) =
      action identityKernel f x := by
    unfold action
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, tensorProjection_sum]
  rw [h, identityKernel_action]

theorem tensorProjection_orthogonal (z : V) (hn : 1 < Fintype.card V)
    (a b : I → Fin 3) (hab : a ≠ b) (f g : (I → V) → ℝ) :
    (∑ y, action (tensorProjection z a) f y * action (tensorProjection z b) g y) = 0 := by
  rw [kernel_bilinear]
  have hc (x w : I → V) :
      (∑ y, tensorProjection z a y x * tensorProjection z b y w) = 0 := by
    simp_rw [tensorProjection_symmetric z a _ x]
    change kernelCompose (tensorProjection z a) (tensorProjection z b) x w = 0
    rw [tensorProjection_compose z hn, if_neg hab]
    rfl
  simp_rw [hc, mul_zero, Finset.sum_const_zero]

theorem tensorProjection_pythagoras (z : V) (hn : 1 < Fintype.card V)
    (f : (I → V) → ℝ) :
    (∑ y, f y ^ 2) = ∑ a : I → Fin 3, ∑ y, action (tensorProjection z a) f y ^ 2 := by
  have h := orthogonal_family_energy (fun a => action (tensorProjection z a) f)
    (fun a b hab => tensorProjection_orthogonal z hn a b hab f f)
  have hd := tensorProjection_decomposition z f
  simpa only [congrFun hd] using h

/-- Output projection composes with the actual coordinate channel factors. -/
theorem tensorProjection_channel (D : I → V → V → ℝ) (z : V)
    (h : ∀ i, PointedBistochastic (D i) z) (a : I → Fin 3) :
    kernelCompose (tensorProjection z a) (coordinateKernel D) = tensorChannel D z a := by
  change kernelCompose (coordinateKernel (fun i => piece z (a i))) (coordinateKernel D) = _
  rw [coordinateKernel_compose]
  exact congrArg (fun T : I → V → V → ℝ => coordinateKernel T)
    (funext (fun i => UniformBias.piece_channel (D i) z (h i) (a i)))

theorem project_channel (D : I → V → V → ℝ) (z : V)
    (h : ∀ i, PointedBistochastic (D i) z) (a : I → Fin 3) (f : (I → V) → ℝ) :
    action (tensorProjection z a) (action (coordinateKernel D) f) =
      action (tensorChannel D z a) f := by
  rw [← kernelCompose_action, tensorProjection_channel D z h a]

theorem channel_decomposition (D : I → V → V → ℝ) (z : V)
    (h : ∀ i, PointedBistochastic (D i) z) (f : (I → V) → ℝ) :
    (fun y => ∑ a : I → Fin 3, action (tensorChannel D z a) f y) =
      action (coordinateKernel D) f := by
  simpa only [project_channel D z h] using
    tensorProjection_decomposition z (action (coordinateKernel D) f)

theorem channel_orthogonal (D : I → V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (h : ∀ i, PointedBistochastic (D i) z)
    (a b : I → Fin 3) (hab : a ≠ b) (f g : (I → V) → ℝ) :
    (∑ y, action (tensorChannel D z a) f y * action (tensorChannel D z b) g y) = 0 := by
  rw [← project_channel D z h a f, ← project_channel D z h b g]
  exact tensorProjection_orthogonal z hn a b hab
    (action (coordinateKernel D) f) (action (coordinateKernel D) g)

theorem channel_pythagoras (D : I → V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (h : ∀ i, PointedBistochastic (D i) z)
    (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel D) f y ^ 2) =
      ∑ a : I → Fin 3, ∑ y, action (tensorChannel D z a) f y ^ 2 := by
  simpa only [project_channel D z h] using
    tensorProjection_pythagoras z hn (action (coordinateKernel D) f)

end AESPaper.TernaryTensor
