import AESPaper.RectangularBounds
import AESMixing.L2Sums

/-!
# Scalar majorants for finite rectangular block arrays

The block comparison applies the finite L2 triangle inequality to each
output section, then the scalar majorant's signed-input energy bound.
The joint input is arbitrary; no independence or product representation
is assumed. All index types may be empty. The residual-first wrapper is an
exact permutation of the two product indices, preserving counting measure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RectangularArrays
open AESMixing AESPaper.RectangularFourier

section Reindex
variable {Y X Y' X' : Type*} [Fintype Y] [Fintype X]
  [Fintype Y'] [Fintype X']

/-- Two explicit finite coordinate equivalences preserve the arbitrary-input
energy bound, including its counting normalization. -/
theorem energyBound_reindex (M : Y → X → ℝ) (c : ℝ)
    (eY : Y' ≃ Y) (eX : X' ≃ X) (hM : EnergyBound M c) :
    EnergyBound (fun y x => M (eY y) (eX x)) c := by
  intro f
  have ha (y : Y') :
      rectAction (fun y x => M (eY y) (eX x)) f y =
        rectAction M (fun x => f (eX.symm x)) (eY y) := by
    simpa only [rectAction, eX.symm_apply_apply] using
      eX.sum_comp (fun x => M (eY y) x * f (eX.symm x))
  have hi : (∑ x : X, f (eX.symm x) ^ 2) = ∑ x : X', f x ^ 2 :=
    eX.symm.sum_comp (fun x => f x ^ 2)
  have hb := hM (fun x => f (eX.symm x))
  rw [hi] at hb
  calc
    _ = ∑ y : Y', rectAction M (fun x => f (eX.symm x)) (eY y) ^ 2 := by
      simp_rw [ha]
    _ = ∑ y : Y, rectAction M (fun x => f (eX.symm x)) y ^ 2 :=
      eY.sum_comp (fun y => rectAction M (fun x => f (eX.symm x)) y ^ 2)
    _ ≤ c ^ 2 * ∑ x : X', f x ^ 2 := hb

end Reindex

section BlockArray
variable {O I Y X : Type*} [Fintype O] [Fintype I] [Fintype Y] [Fintype X]

/-- Stack the output and input choices as the first product coordinates. -/
def blockKernel (T : O → I → Y → X → ℝ) : (O × Y) → (I × X) → ℝ :=
  fun oy ix => T oy.1 ix.1 oy.2 ix.2

theorem blockKernel_action (T : O → I → Y → X → ℝ)
    (f : I × X → ℝ) (o : O) (y : Y) :
    rectAction (blockKernel T) f (o,y) =
      ∑ i : I, rectAction (T o i) (fun x => f (i,x)) y := by
  simp only [rectAction, blockKernel, Fintype.sum_prod_type]

/-- An entrywise nonnegative scalar majorant bounds the full block operator
on every signed joint input, without any independence premise. -/
theorem energyBound_blockKernel (T : O → I → Y → X → ℝ)
    (F : O → I → ℝ) (n : ℝ) (hF : ∀ o i, 0 ≤ F o i)
    (hT : ∀ o i, EnergyBound (T o i) (F o i)) (hScalar : EnergyBound F n) :
    EnergyBound (blockKernel T) n := by
  classical
  intro f
  let q : I → ℝ := fun i => l2 (fun x : X => f (i,x))
  have hblock (o : O) (i : I) :
      l2 (rectAction (T o i) (fun x => f (i,x))) ≤ F o i * q i :=
    l2_le_of_energy _ _ (F o i) (hF o i) (hT o i (fun x => f (i,x)))
  have hrow (o : O) :
      l2 (fun y => rectAction (blockKernel T) f (o,y)) ≤ rectAction F q o := by
    have ha : (fun y => rectAction (blockKernel T) f (o,y)) =
        (fun y => ∑ i : I, rectAction (T o i) (fun x => f (i,x)) y) :=
      funext (fun y => blockKernel_action T f o y)
    rw [ha]
    exact (l2_finset_sum_le Finset.univ
      (fun i => rectAction (T o i) (fun x => f (i,x)))).trans
      (Finset.sum_le_sum (fun i _ => hblock o i))
  have hs (o : O) :
      (∑ y : Y, rectAction (blockKernel T) f (o,y) ^ 2) ≤ rectAction F q o ^ 2 := by
    have hp : 0 ≤ rectAction F q o :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hF o i) (l2_nonneg _))
    simpa only [l2_sq] using (sq_le_sq₀ (l2_nonneg _) hp).mpr (hrow o)
  calc
    _ = ∑ o : O, ∑ y : Y, rectAction (blockKernel T) f (o,y) ^ 2 :=
      Fintype.sum_prod_type _
    _ ≤ ∑ o : O, rectAction F q o ^ 2 :=
      Finset.sum_le_sum (fun o _ => hs o)
    _ ≤ n ^ 2 * ∑ i : I, q i ^ 2 := hScalar q
    _ = n ^ 2 * ∑ ix : I × X, f ix ^ 2 := by
      simp only [q, l2_sq, Fintype.sum_prod_type]

/-- Residual-first indexing used by the physical activity-frame operators. -/
def residualBlockKernel (T : O → I → Y → X → ℝ) :
    (Y × O) → (X × I) → ℝ := fun yo xi => T yo.2 xi.2 yo.1 xi.1

theorem residualBlockKernel_action (T : O → I → Y → X → ℝ)
    (f : X × I → ℝ) (y : Y) (o : O) :
    rectAction (residualBlockKernel T) f (y,o) =
      ∑ i : I, rectAction (T o i) (fun x => f (x,i)) y := by
  simp only [rectAction, residualBlockKernel, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem energyBound_residualBlockKernel (T : O → I → Y → X → ℝ)
    (F : O → I → ℝ) (n : ℝ) (hF : ∀ o i, 0 ≤ F o i)
    (hT : ∀ o i, EnergyBound (T o i) (F o i)) (hScalar : EnergyBound F n) :
    EnergyBound (residualBlockKernel T) n := by
  exact energyBound_reindex (blockKernel T) n (Equiv.prodComm Y O) (Equiv.prodComm X I)
    (energyBound_blockKernel T F n hF hT hScalar)

end BlockArray

section Family
variable {P A B : Type*} [Fintype P] [DecidableEq P] [Fintype A] [Fintype B]

/-- Apply the same rectangular kernel to each fixed first-coordinate section. -/
def familyKernel (M : A → B → ℝ) : (P × A) → (P × B) → ℝ :=
  fun pa pb => if pa.1 = pb.1 then M pa.2 pb.2 else 0

theorem familyKernel_action (M : A → B → ℝ) (f : P × B → ℝ) (p : P) (a : A) :
    rectAction (familyKernel M) f (p,a) = rectAction M (fun b => f (p,b)) a := by
  classical
  simp only [rectAction, familyKernel, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Left composition sums only within the actual fixed family section. -/
theorem familyKernel_compose_left {Z : Type*} (M : A → B → ℝ)
    (N : (P × B) → Z → ℝ) (p : P) (a : A) (z : Z) :
    kernelCompose (familyKernel M) N (p,a) z = ∑ b : B, M a b * N (p,b) z := by
  exact familyKernel_action M (fun pb => N pb z) p a

/-- Right composition uses the same family section, with no relabeling of
the inner source coordinate. -/
theorem familyKernel_compose_right {Z : Type*} (M : Z → (P × A) → ℝ)
    (N : A → B → ℝ) (z : Z) (p : P) (b : B) :
    kernelCompose M (familyKernel N) z (p,b) = ∑ a : A, M z (p,a) * N a b := by
  classical
  simp only [kernelCompose, familyKernel, Fintype.sum_prod_type, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- The family matrix transpose preserves its first coordinate exactly. -/
theorem familyKernel_transpose (M : A → B → ℝ) :
    RectangularBounds.transpose (familyKernel (P := P) M) =
      familyKernel (P := P) (RectangularBounds.transpose M) := by
  funext pb pa
  simp only [RectangularBounds.transpose, familyKernel, eq_comm]

/-- A same-index family keeps the single-kernel coefficient, for arbitrary
joint inputs across the family and inner coordinates. -/
theorem energyBound_family (M : A → B → ℝ) (c : ℝ) (hM : EnergyBound M c) :
    EnergyBound (familyKernel (P := P) M) c := by
  intro f
  rw [Fintype.sum_prod_type]
  simp_rw [familyKernel_action]
  calc
    _ ≤ ∑ p : P, c ^ 2 * ∑ b : B, f (p,b) ^ 2 :=
      Finset.sum_le_sum (fun p _ => hM (fun b => f (p,b)))
    _ = c ^ 2 * ∑ pb : P × B, f pb ^ 2 := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type]

end Family
end AESPaper.RectangularArrays
