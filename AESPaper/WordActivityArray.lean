import AESPaper.WordFrameOperator
import AESPaper.RectangularArrays

/-!
# Two-sided activity-array comparison with both actual frame factors

Untouched residual indices and activity coordinates form arbitrary joint
signed inputs. The compressed entries are V_out* M V_in, not canonical
coefficients. Actual input activity insensitivity and output fixedness give
the exact factorization M = C_out* compressed M C_in. Each canonical map
costs one proved conditioning factor. Empty activity coordinate types are
included. These are raw operator bounds; q^2 scaling for S and b is separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordActivityArray
open AESMixing
open AESPaper.WordActivityFrame
open AESPaper.WordFrameCoordinates
open AESPaper.WordFrameOperator
open AESPaper.RectangularFourier (rectAction EnergyBound)
open AESPaper.RectangularArrays (familyKernel)

section FamilyProjection
variable {X AI : Type*} [Fintype X] [DecidableEq X]
  [Fintype AI] [DecidableEq AI]

/-- Actual tensor activity projection of each fixed residual-index section. -/
def inputProject (f : (X × (AI → AES.Word)) → ℝ) : (X × (AI → AES.Word)) → ℝ :=
  fun xv => projectActivity (fun v => f (xv.1,v)) xv.2

/-- The same-index input canonical coordinates reconstruct the projected
joint family, with no factorization of its entries. -/
theorem synthesis_canonical_family_action (f : (X × (AI → AES.Word)) → ℝ) :
    rectAction (familyKernel (P := X) (synthesisKernel (I := AI)))
        (rectAction (familyKernel (P := X) (canonicalKernel (I := AI))) f) =
      inputProject f := by
  funext xv
  rcases xv with ⟨x,v⟩
  rw [RectangularArrays.familyKernel_action]
  simp_rw [RectangularArrays.familyKernel_action]
  change synthesize (rectAction canonicalKernel (fun w => f (x,w))) v =
    projectActivity (fun w => f (x,w)) v
  rw [canonicalKernel_action, synthesize_coefficients]

/-- The transposed canonical map reverses analysis to the actual physical
projection. It supplies the output frame factor. -/
theorem canonicalTranspose_analysis_family_action (f : (X × (AI → AES.Word)) → ℝ) :
    rectAction (familyKernel (P := X)
        (RectangularBounds.transpose (canonicalKernel (I := AI))))
      (rectAction (familyKernel (P := X) (analysisKernel (I := AI))) f) =
        inputProject f := by
  funext xv
  rcases xv with ⟨x,v⟩
  rw [RectangularArrays.familyKernel_action]
  simp_rw [RectangularArrays.familyKernel_action]
  change rectAction (RectangularBounds.transpose canonicalKernel)
      (analyze (fun w => f (x,w))) v = projectActivity (fun w => f (x,w)) v
  rw [canonicalTranspose_action]
  change synthesize (coefficients (fun w => f (x,w))) v = _
  rw [synthesize_coefficients]

end FamilyProjection

section TwoSided
variable {X Y AI AO : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype AI] [DecidableEq AI]
  [Fintype AO] [DecidableEq AO]

/-- Both frame legs are analysis/synthesis columns, before inverse Grams. -/
def contraction
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (s : AO → Bool) (t : AI → Bool) (y : Y) (x : X) : ℝ :=
  ∑ u : AO → AES.Word, ∑ v : AI → AES.Word,
    frameColumn s u * M (y,u) (x,v) * frameColumn t v

def compressedMatrix
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ) :
    (Y × (AO → Bool)) → (X × (AI → Bool)) → ℝ :=
  RectangularArrays.residualBlockKernel (contraction M)

/-- The double frame contraction is exactly the physical compressed matrix. -/
theorem compressedMatrix_eq
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ) :
    compressedMatrix M =
      kernelCompose (familyKernel (P := Y) (analysisKernel (I := AO)))
        (kernelCompose M (familyKernel (P := X) (synthesisKernel (I := AI)))) := by
  funext ys xt
  rcases ys with ⟨y,s⟩
  rcases xt with ⟨x,t⟩
  change contraction M s t y x = _
  rw [RectangularArrays.familyKernel_compose_left]
  simp_rw [RectangularArrays.familyKernel_compose_right]
  unfold contraction analysisKernel synthesisKernel
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem compressedMatrix_action
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (f : (X × (AI → Bool)) → ℝ) :
    rectAction (compressedMatrix M) f =
      rectAction (familyKernel (P := Y) (analysisKernel (I := AO)))
        (rectAction M (rectAction (familyKernel (P := X) (synthesisKernel (I := AI))) f)) := by
  rw [compressedMatrix_eq]
  change action (kernelCompose _ (kernelCompose _ _)) f = _
  rw [kernelCompose_action, kernelCompose_action]
  rfl

theorem compressed_canonical_action
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (f : (X × (AI → AES.Word)) → ℝ) :
    rectAction (compressedMatrix M)
        (rectAction (familyKernel (P := X) (canonicalKernel (I := AI))) f) =
      rectAction (familyKernel (P := Y) (analysisKernel (I := AO)))
        (rectAction M (inputProject f)) := by
  rw [compressedMatrix_action, synthesis_canonical_family_action]

/-- Physical row fixedness implies input activity insensitivity, using the
actual projector's symmetry. This holds for every joint signed input. -/
theorem input_insensitive_of_rows
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (hrow : ∀ a x, projectActivity (fun v => M a (x,v)) = fun v => M a (x,v))
    (f : (X × (AI → AES.Word)) → ℝ) :
    rectAction M f = rectAction M (inputProject f) := by
  funext a
  change (∑ xv : X × (AI → AES.Word), M a xv * f xv) =
    ∑ xv : X × (AI → AES.Word), M a xv * inputProject f xv
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have h := projectActivity_inner (fun v => M a (x,v)) (fun v => f (x,v))
  rw [hrow a x] at h
  exact h

/-- Physical column fixedness survives arbitrary signed finite combination. -/
theorem output_fixed_of_columns
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (hcol : ∀ y b, projectActivity (fun u => M (y,u) b) = fun u => M (y,u) b)
    (f : (X × (AI → AES.Word)) → ℝ) (y : Y) :
    projectActivity (fun u => rectAction M f (y,u)) =
      fun u => rectAction M f (y,u) := by
  change projectActivity (fun u => ∑ b : X × (AI → AES.Word), M (y,u) b * f b) =
    fun u => ∑ b : X × (AI → AES.Word), M (y,u) b * f b
  rw [projectActivity_weighted_sum]
  funext u
  apply Finset.sum_congr rfl
  intro b _
  rw [hcol y b]

/-- Input insensitivity and output fixedness justify both inverse-frame
maps in the exact factorization. They are physical hypotheses, not desired
operator bounds. -/
theorem activity_factorization
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (hin : ∀ f, rectAction M f = rectAction M (inputProject f))
    (hout : ∀ f y, projectActivity (fun u => rectAction M f (y,u)) =
      fun u => rectAction M f (y,u)) :
    M = kernelCompose
      (familyKernel (P := Y) (RectangularBounds.transpose (canonicalKernel (I := AO))))
      (kernelCompose (compressedMatrix M) (familyKernel (P := X) (canonicalKernel (I := AI)))) := by
  classical
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, kernelCompose_action]
  change rectAction M f = rectAction
    (familyKernel (P := Y) (RectangularBounds.transpose (canonicalKernel (I := AO))))
      (rectAction (compressedMatrix M)
        (rectAction (familyKernel (P := X) (canonicalKernel (I := AI))) f))
  rw [compressed_canonical_action, ← hin f, canonicalTranspose_analysis_family_action]
  funext yu
  exact (congrFun (hout f yu.1) yu.2).symm

/-- The scalar array norm and both actual frame factors control the whole
operator for arbitrary joint signed residual/activity input families. -/
theorem activity_array_bound
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (F : (AO → Bool) → (AI → Bool) → ℝ) (n : ℝ)
    (hin : ∀ f, rectAction M f = rectAction M (inputProject f))
    (hout : ∀ f y, projectActivity (fun u => rectAction M f (y,u)) =
      fun u => rectAction M f (y,u))
    (hF : ∀ s t, 0 ≤ F s t)
    (hT : ∀ s t, EnergyBound (contraction M s t) (F s t))
    (hScalar : EnergyBound F n) :
    EnergyBound M
      ((conditioningFactor (Fintype.card AO) * conditioningFactor (Fintype.card AI)) * n) := by
  have ht : EnergyBound (compressedMatrix M) n :=
    RectangularArrays.energyBound_residualBlockKernel (contraction M) F n hF hT hScalar
  have hi := RectangularArrays.energyBound_family (P := X)
    (canonicalKernel (I := AI)) (conditioningFactor (Fintype.card AI)) canonicalKernel_energyBound
  have ho := RectangularArrays.energyBound_family (P := Y)
    (RectangularBounds.transpose (canonicalKernel (I := AO)))
    (conditioningFactor (Fintype.card AO)) canonicalTranspose_energyBound
  have hc := RectangularBounds.energyBound_compose _ _ n
    (conditioningFactor (Fintype.card AI)) ht hi
  have h := RectangularBounds.energyBound_compose _ _
    (conditioningFactor (Fintype.card AO))
    (n * conditioningFactor (Fintype.card AI)) ho hc
  have he : conditioningFactor (Fintype.card AO) *
      (n * conditioningFactor (Fintype.card AI)) =
      (conditioningFactor (Fintype.card AO) * conditioningFactor (Fintype.card AI)) * n := by ring
  rw [he, ← activity_factorization M hin hout] at h
  exact h

/-- Section-wise physical activity fixedness discharges both semantic
hypotheses of the generic two-sided activity-array estimate. -/
theorem activity_array_bound_of_sections
    (M : (Y × (AO → AES.Word)) → (X × (AI → AES.Word)) → ℝ)
    (F : (AO → Bool) → (AI → Bool) → ℝ) (n : ℝ)
    (hrow : ∀ a x, projectActivity (fun v => M a (x,v)) = fun v => M a (x,v))
    (hcol : ∀ y b, projectActivity (fun u => M (y,u) b) = fun u => M (y,u) b)
    (hF : ∀ s t, 0 ≤ F s t)
    (hT : ∀ s t, EnergyBound (contraction M s t) (F s t))
    (hScalar : EnergyBound F n) :
    EnergyBound M
      ((conditioningFactor (Fintype.card AO) * conditioningFactor (Fintype.card AI)) * n) :=
  activity_array_bound M F n (input_insensitive_of_rows M hrow)
    (output_fixed_of_columns M hcol) hF hT hScalar

end TwoSided
end AESPaper.WordActivityArray
