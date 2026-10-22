import AES8.Math.PaperThinLinesRaw

/-!
# Literal coordinate inclusions for thin-code overlaps

The ambient tensor action is its usual product-coordinate matrix. Restricting
it through the actual coordinate inclusions gives the product kernel, by a
finite-sum identity. No operator correspondence is assumed as a premise.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperThinLines
open PaperKernelBounds PaperFiberKernel

variable {𝕜 A B L R : Type*} [RCLike 𝕜]
  [Fintype A] [Fintype B] [Fintype L] [Fintype R]
  [DecidableEq A] [DecidableEq B] [DecidableEq L] [DecidableEq R]

/-- Counting coordinate inclusion. For an injective `e`, this is extension
by zero from the literal code image. -/
def coordinateInclusion (e : L → A) : EuclideanSpace 𝕜 L →L[𝕜] EuclideanSpace 𝕜 A :=
  kernelOperator (fun a x => if e x = a then 1 else 0)

/-- At an actual code label, the injective inclusion preserves its coefficient. -/
theorem coordinateInclusion_apply_image (e : L → A) (he : Function.Injective e)
    (f : EuclideanSpace 𝕜 L) (x : L) : coordinateInclusion e f (e x) = f x := by
  change (∑ y, (if e y = e x then (1 : 𝕜) else 0) * f y) = f x
  simp only [he.eq_iff, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Outside the code image, counting inclusion is zero. -/
theorem coordinateInclusion_apply_outside (e : L → A) (f : EuclideanSpace 𝕜 L)
    (a : A) (ha : a ∉ Set.range e) : coordinateInclusion e f a = 0 := by
  change (∑ y, (if e y = a then (1 : 𝕜) else 0) * f y) = 0
  apply Finset.sum_eq_zero
  intro y _
  have hy : e y ≠ a := fun hy => ha ⟨y, hy⟩
  simp only [hy, if_false, zero_mul]

@[simp] theorem coordinateInclusion_adjoint_apply (e : L → A)
    (g : EuclideanSpace 𝕜 A) (x : L) :
    (coordinateInclusion e).adjoint g x = g (e x) := by
  rw [coordinateInclusion, kernelOperator_adjoint]
  change (∑ a, star (if e x = a then (1 : 𝕜) else 0) * g a) = _
  simp [ite_mul]

/-- The actual ambient composition equals restriction of the matrix entries.
The identity is valid for any maps; injectivity identifies them as inclusions. -/
theorem coordinateInclusion_compression (eL : L → A) (eR : R → B)
    (T : A → B → 𝕜) :
    (coordinateInclusion eL).adjoint.comp
      ((kernelOperator T).comp (coordinateInclusion eR)) =
        kernelOperator (fun x y => T (eL x) (eR y)) := by
  ext f x
  simp only [ContinuousLinearMap.comp_apply, coordinateInclusion_adjoint_apply,
    kernelOperator_apply, kernelAction]
  change (∑ a, T (eL x) a *
    (∑ y, (if eR y = a then (1 : 𝕜) else 0) * f y)) =
      ∑ y, T (eL x) (eR y) * f y
  calc
    _ = ∑ y, ∑ a, T (eL x) a *
        ((if eR y = a then (1 : 𝕜) else 0) * f y) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      simp [mul_ite, ite_mul]

/-- The coordinate tensor map's matrix, with counting normalization. -/
def coordinateTensorOperator {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (T : Fin n → V → V → 𝕜) :
    EuclideanSpace 𝕜 (Fin n → V) →L[𝕜] EuclideanSpace 𝕜 (Fin n → V) :=
  kernelOperator (fun x y => ∏ j, T j (x j) (y j))

/-- `I_C^* (⊗ T_j) I_D` is precisely the literal line kernel. -/
theorem coordinateTensor_compression {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (T : Fin n → V → V → 𝕜)
    (left : L → Fin n → V) (right : R → Fin n → V) :
    (coordinateInclusion left).adjoint.comp
      ((coordinateTensorOperator T).comp (coordinateInclusion right)) =
        kernelOperator (lineKernel T left right) :=
  coordinateInclusion_compression left right _

/-- Attaching the outside indicators yields the full overlap in the paper.
All five factors are literal continuous linear maps. -/
theorem normalized_overlap_correspondence {n : ℕ} {V X Y : Type*}
    [Fintype V] [DecidableEq V] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Fin n → V → V → 𝕜) (left : L → Fin n → V) (right : R → Fin n → V)
    (p : L → X) (t : R → Y) (m k : ℕ) :
    (fiberLift p m).adjoint.comp
      (((coordinateInclusion left).adjoint.comp
        ((coordinateTensorOperator T).comp (coordinateInclusion right))).comp
          (fiberLift t k)) =
    (fiberLift p m).adjoint.comp
      ((kernelOperator (lineKernel T left right)).comp (fiberLift t k)) := by
  rw [coordinateTensor_compression]

end AES8.PaperThinLines
