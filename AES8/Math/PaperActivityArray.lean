import AES8.Math.PaperActivityArrayCoordinates

/-!
# Literal two-sided activity-array bound

Candidate source; diagnostic and review status is recorded in adjacent receipts. This is the support-equation version of the historical
AESPaper.WordActivityArray argument. Residual indices are untouched by the
frame maps, and all kernels and joint signed inputs are arbitrary. The support
premise is the actual equation `M = Pout M Pin`, not a desired norm estimate.
The main endpoint uses ordinary Euclidean operator norms and the paper's
exact combined exponent. The alphabet may be any finite type of size > 1.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace AES8.PaperActivityArray
open AESMixing WordActivityFrame PaperActivityArrayFrame
  PaperActivityArrayCoordinates PaperActivityArrayBlocks PaperKernelBounds

section FamilyProjection
variable {X I V : Type*} [Fintype X] [DecidableEq X]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- Identity on the residual label; actual activity projection on each section. -/
def projectionKernel (z : V) : (X × (I → V)) → (X × (I → V)) → ℝ :=
  familyKernel (tensorActivityKernel z)

def inputProject (z : V) (f : (X × (I → V)) → ℝ) : (X × (I → V)) → ℝ :=
  fun xv => projectActivity z (fun v => f (xv.1,v)) xv.2

theorem projection_action (z : V) (f : (X × (I → V)) → ℝ) :
    action (projectionKernel z) f = inputProject z f := by
  funext xv
  exact familyKernel_action (tensorActivityKernel z) f xv.1 xv.2

theorem synthesis_canonical_family_action (z : V) (hq : 1 < Fintype.card V)
    (f : (X × (I → V)) → ℝ) :
    action (familyKernel (P := X) (synthesisKernel (I := I) z))
      (action (familyKernel (P := X) (canonicalKernel (I := I) z)) f) =
        inputProject z f := by
  funext xv
  rcases xv with ⟨x,v⟩
  rw [familyKernel_action]
  simp_rw [familyKernel_action]
  exact congrFun (synthesis_canonical_action z hq (fun w => f (x,w))) v

theorem canonicalTranspose_analysis_family_action (z : V)
    (hq : 1 < Fintype.card V) (f : (X × (I → V)) → ℝ) :
    action (familyKernel (P := X) (transpose (canonicalKernel (I := I) z)))
      (action (familyKernel (P := X) (analysisKernel (I := I) z)) f) =
        inputProject z f := by
  funext xv
  rcases xv with ⟨x,v⟩
  rw [familyKernel_action]
  simp_rw [familyKernel_action]
  change action (transpose (canonicalKernel z))
      (action (analysisKernel z) (fun w => f (x,w))) v = _
  rw [← kernelCompose_action, canonicalTranspose_analysis_eq_project z hq]
  rfl
end FamilyProjection

section TwoSided
variable {X Y AI AO V : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype AI] [DecidableEq AI]
  [Fintype AO] [DecidableEq AO] [Fintype V] [DecidableEq V]

/-- Entry of `Φout* M Φin`, as an operator on the untouched residual indices. -/
def contraction (z : V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (s : AO → Bool) (t : AI → Bool) (y : Y) (x : X) : ℝ :=
  ∑ u : AO → V, ∑ v : AI → V,
    frameColumn z s u * M (y,u) (x,v) * frameColumn z t v

def compressedMatrix (z : V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ) :
    (Y × (AO → Bool)) → (X × (AI → Bool)) → ℝ :=
  residualBlockKernel (contraction z M)

theorem compressedMatrix_eq (z : V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ) :
    compressedMatrix z M =
      kernelCompose (familyKernel (P := Y) (analysisKernel (I := AO) z))
        (kernelCompose M (familyKernel (P := X) (synthesisKernel (I := AI) z))) := by
  funext ys xt
  rcases ys with ⟨y,s⟩
  rcases xt with ⟨x,t⟩
  change contraction z M s t y x = _
  rw [familyKernel_compose_left]
  simp_rw [familyKernel_compose_right]
  unfold contraction analysisKernel synthesisKernel
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem compressedMatrix_action (z : V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (f : (X × (AI → Bool)) → ℝ) :
    action (compressedMatrix z M) f =
      action (familyKernel (P := Y) (analysisKernel (I := AO) z))
        (action M (action (familyKernel (P := X) (synthesisKernel (I := AI) z)) f)) := by
  rw [compressedMatrix_eq, kernelCompose_action, kernelCompose_action]

/-- Both inverse-frame legs follow from the literal two-sided support equation. -/
theorem activity_factorization (z : V) (hq : 1 < Fintype.card V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (hsupport : M = kernelCompose (projectionKernel z)
      (kernelCompose M (projectionKernel z))) :
    M = kernelCompose
      (familyKernel (P := Y) (transpose (canonicalKernel (I := AO) z)))
      (kernelCompose (compressedMatrix z M)
        (familyKernel (P := X) (canonicalKernel (I := AI) z))) := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, kernelCompose_action, compressedMatrix_action,
    synthesis_canonical_family_action z hq, canonicalTranspose_analysis_family_action z hq]
  have h := congrArg (fun K => action K f) hsupport
  simpa only [kernelCompose_action, projection_action] using h

/-- Finite scalar block comparison and two actual inverse-frame estimates. -/
theorem activity_array_energy (z : V) (hq : 1 < Fintype.card V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (P : (AO → Bool) → (AI → Bool) → ℝ) (c : ℝ)
    (hsupport : M = kernelCompose (projectionKernel z)
      (kernelCompose M (projectionKernel z)))
    (hP : ∀ s t, 0 ≤ P s t)
    (hblock : ∀ s t, EnergyBound (contraction z M s t) (P s t))
    (hscalar : EnergyBound P c) :
    EnergyBound M
      ((conditioningFactor V (Fintype.card AO) * conditioningFactor V (Fintype.card AI)) * c) := by
  have ht : EnergyBound (compressedMatrix z M) c :=
    energyBound_residualBlockKernel (contraction z M) P c hP hblock hscalar
  have hi := energyBound_family (P := X) (canonicalKernel (I := AI) z)
    (conditioningFactor V (Fintype.card AI)) (canonicalKernel_energyBound z hq)
  have ho := energyBound_family (P := Y) (transpose (canonicalKernel (I := AO) z))
    (conditioningFactor V (Fintype.card AO)) (canonicalTranspose_energyBound z hq)
  have hc := energyBound_compose _ _ c (conditioningFactor V (Fintype.card AI)) ht hi
  have h := energyBound_compose _ _ (conditioningFactor V (Fintype.card AO))
    (c * conditioningFactor V (Fintype.card AI)) ho hc
  have he : conditioningFactor V (Fintype.card AO) *
      (c * conditioningFactor V (Fintype.card AI)) =
      (conditioningFactor V (Fintype.card AO) * conditioningFactor V (Fintype.card AI)) * c := by ring
  rw [he, ← activity_factorization z hq M hsupport] at h
  exact h

/-- Literal `lem:activity-array`, with arbitrary supported real operator blocks. -/
theorem activity_array_norm (z : V) (hq : 1 < Fintype.card V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (P : (AO → Bool) → (AI → Bool) → ℝ)
    (hsupport : M = kernelCompose (projectionKernel z)
      (kernelCompose M (projectionKernel z)))
    (hP : ∀ s t, 0 ≤ P s t)
    (hblock : ∀ s t, ‖kernelOperator (contraction z M s t)‖ ≤ P s t) :
    ‖kernelOperator M‖ ≤
      (1 - xi V) ^ (-((Fintype.card AI + Fintype.card AO : ℕ) : ℝ) / 2) *
        ‖kernelOperator P‖ := by
  have h := norm_le_of_energyBound M
    ((conditioningFactor V (Fintype.card AO) * conditioningFactor V (Fintype.card AI)) *
      ‖kernelOperator P‖)
    (mul_nonneg (mul_nonneg (conditioningFactor_nonneg _) (conditioningFactor_nonneg _))
      (norm_nonneg _))
    (activity_array_energy z hq M P ‖kernelOperator P‖ hsupport hP
      (fun s t => energyBound_of_norm _ _ (hP s t) (hblock s t))
      (energyBound_of_norm P _ (norm_nonneg _) le_rfl))
  rw [conditioningFactor_mul, conditioningFactor_eq_rpow hq,
    Nat.add_comm (Fintype.card AO) (Fintype.card AI)] at h
  exact h

/-- Row/column physical fixedness is an alternative, sufficient support interface. -/
theorem support_of_sections (z : V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (hrow : ∀ a x, projectActivity z (fun v => M a (x,v)) = fun v => M a (x,v))
    (hcol : ∀ y b, projectActivity z (fun u => M (y,u) b) = fun u => M (y,u) b) :
    M = kernelCompose (projectionKernel z) (kernelCompose M (projectionKernel z)) := by
  apply kernel_action_ext
  intro f
  have hin : action M f = action M (inputProject z f) := by
    funext a
    unfold action
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    have h := projectActivity_inner z (fun v => M a (x,v)) (fun v => f (x,v))
    rw [hrow a x] at h
    exact h
  have hout : inputProject z (action M f) = action M f := by
    funext yu
    change projectActivity z (fun u => ∑ b, M (yu.1,u) b * f b) yu.2 = _
    rw [projectActivity_weighted_sum]
    simp_rw [hcol]
    rfl
  rw [kernelCompose_action, kernelCompose_action, projection_action,
    projection_action, ← hin, hout]

theorem activity_array_bound_of_sections (z : V) (hq : 1 < Fintype.card V)
    (M : (Y × (AO → V)) → (X × (AI → V)) → ℝ)
    (P : (AO → Bool) → (AI → Bool) → ℝ)
    (hrow : ∀ a x, projectActivity z (fun v => M a (x,v)) = fun v => M a (x,v))
    (hcol : ∀ y b, projectActivity z (fun u => M (y,u) b) = fun u => M (y,u) b)
    (hP : ∀ s t, 0 ≤ P s t)
    (hblock : ∀ s t, ‖kernelOperator (contraction z M s t)‖ ≤ P s t) :
    ‖kernelOperator M‖ ≤
      (1 - xi V) ^ (-((Fintype.card AI + Fintype.card AO : ℕ) : ℝ) / 2) *
        ‖kernelOperator P‖ :=
  activity_array_norm z hq M P (support_of_sections z M hrow hcol) hP hblock

end TwoSided
end AES8.PaperActivityArray
