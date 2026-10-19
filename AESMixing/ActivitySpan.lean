import AESMixing.ActivityGram

/-! The sixteen support indicators span degree zero. Thus a certified bound
on their arbitrary linear combinations covers every activity component,
including correlated inputs. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES

set_option maxRecDepth 100000 in
theorem maskBits_injective : Function.Injective (fun a : Fin 16 => maskBit a) := by decide

def maskBitsEquiv : Fin 16 ≃ (Fin 4 → Bool) :=
  Equiv.ofBijective (fun a => maskBit a)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨maskBits_injective, by simp⟩)

set_option maxRecDepth 100000 in
theorem degreeIndex_zero_iff : ∀ a : Fin 4 → Bool,
    degreeIndex a = 0 ↔ a = fun _ => false := by decide

theorem degreeKernel_zero {V : Type*} [Fintype V] [DecidableEq V] (z : V) :
    degreeKernel z 0 = productProjection z (fun _ : Fin 4 => false) := by
  funext x y
  simp only [degreeKernel, degreeIndex_zero_iff]
  simp

variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

def activityBasisFactor (b : Bool) (x : V) : ℝ :=
  if b then 1 else identityKernel x 0

def activityDualFactor (b : Bool) (x : V) : ℝ :=
  if b then (1-identityKernel x 0)/((Fintype.card V : ℝ)-1)
  else identityKernel x 0 - (1-identityKernel x 0)/((Fintype.card V : ℝ)-1)

theorem activityMatrix_basis (x y : V) :
    activityMatrix 0 x y = ∑ b : Bool, activityBasisFactor b x * activityDualFactor b y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [activityMatrix, activityBasisFactor, activityDualFactor, identityKernel, hx, hy]

omit [Fintype V] in
theorem activity_basis_product (a : Fin 16) (x : Fin 4 → V) :
    (∏ i, activityBasisFactor (maskBit a i) (x i)) = activityColumn a x := by
  have hp (i : Fin 4) : activityBasisFactor (maskBit a i) (x i) =
      if maskBit a i ≠ true → x i = 0 then 1 else 0 := by
    cases maskBit a i <;> simp [activityBasisFactor, identityKernel]
  simp_rw [hp]
  rw [product_indicator]
  simp only [activityColumn, maskProjection_fixed_iff]
  split_ifs <;> rfl

def activityCoefficient (a : Fin 16) (f : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ y, (∏ i, activityDualFactor (maskBit a i) (y i)) * f y

theorem activity_projection_expansion (x y : Fin 4 → V) :
    productProjection 0 (fun _ : Fin 4 => false) x y =
      ∑ a : Fin 16, activityColumn a x * ∏ i, activityDualFactor (maskBit a i) (y i) := by
  simp only [productProjection, degreePiece, Bool.false_eq_true, if_false]
  simp_rw [activityMatrix_basis]
  rw [Fintype.prod_sum (fun i b => activityBasisFactor b (x i) * activityDualFactor b (y i))]
  rw [← maskBitsEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  change (∏ i, activityBasisFactor (maskBit a i) (x i) * activityDualFactor (maskBit a i) (y i)) = _
  rw [Finset.prod_mul_distrib, activity_basis_product]

theorem degree_zero_reconstruction (f : (Fin 4 → V) → ℝ) :
    degreeComponent 0 0 f =
      fun x => ∑ a : Fin 16, activityColumn a x * activityCoefficient a f := by
  rw [← degreeKernel_action, degreeKernel_zero]
  funext x
  unfold action
  simp_rw [activity_projection_expansion, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [activityCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end AESMixing
