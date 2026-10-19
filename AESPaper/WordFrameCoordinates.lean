import AESPaper.WordActivityFrame

/-!
# Canonical coordinates for the actual word activity frame

The physical projection is defined from the actual tensor activity kernel.
Canonical coefficients are the exact signed inverse Gram times frame analysis.
Reconstruction follows from the accepted exact projector identity, rather than
from a reconstruction hypothesis. The extra family index remains arbitrary.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordFrameCoordinates
open AESMixing
open AESPaper.WordActivityFrame

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Counting-measure analysis against the actual normalized word columns. -/
def analyze (f : (I → AES.Word) → ℝ) : (I → Bool) → ℝ :=
  action (fun s x => frameColumn s x) f

/-- Canonical signed coordinates: exact inverse Gram times frame analysis. -/
def coefficients (f : (I → AES.Word) → ℝ) : (I → Bool) → ℝ :=
  action frameInverse (analyze f)

/-- The actual tensor activity kernel, including an empty coordinate type. -/
def tensorActivityKernel (x y : I → AES.Word) : ℝ :=
  ∏ i, activityMatrix 0 (x i) (y i)

/-- Projection of a physical vector by the actual tensor activity kernel. -/
def projectActivity (f : (I → AES.Word) → ℝ) : (I → AES.Word) → ℝ :=
  action tensorActivityKernel f

/-- The accepted projector expansion has exactly the synthesis-inverse-analysis
orientation used by canonical coordinates. -/
theorem tensorActivityKernel_factorization :
    tensorActivityKernel (I := I) =
      kernelCompose (fun x s => frameColumn s x)
        (kernelCompose frameInverse (fun s x => frameColumn s x)) := by
  funext x y
  simpa only [tensorActivityKernel, kernelCompose, Finset.mul_sum, mul_assoc]
    using (frame_projection x y)

/-- Synthesis of canonical coefficients equals the actual physical projection
for every physical vector, without an activity-range premise. -/
theorem synthesize_coefficients (f : (I → AES.Word) → ℝ) :
    synthesize (coefficients f) = projectActivity f := by
  change action (fun x s => frameColumn s x)
      (action frameInverse (action (fun s x => frameColumn s x) f)) =
    action tensorActivityKernel f
  rw [tensorActivityKernel_factorization, kernelCompose_action, kernelCompose_action]

/-- Frame analysis after synthesis is multiplication by the exact Gram. -/
theorem analyze_synthesize (c : (I → Bool) → ℝ) :
    analyze (synthesize c) = action frameMetric c := by
  have hgram :
      kernelCompose (fun (s : I → Bool) (x : I → AES.Word) => frameColumn s x)
        (fun x t => frameColumn t x) = frameMetric := by
    funext s t
    exact frame_gram s t
  change action (fun s x => frameColumn s x)
      (action (fun x s => frameColumn s x) c) = action frameMetric c
  rw [← kernelCompose_action, hgram]

/-- Symmetry converts the accepted right Gram inverse into the left inverse
needed for recovery of arbitrary signed synthesis coefficients. -/
theorem frame_inverse_left (s t : I → Bool) :
    (∑ u : I → Bool, frameInverse s u * frameMetric u t) =
      if s = t then 1 else 0 := by
  calc
    _ = ∑ u : I → Bool, frameMetric t u * frameInverse u s := by
      apply Finset.sum_congr rfl
      intro u _
      rw [frameInverse_symmetric s u, frameMetric_symmetric u t]
      ring
    _ = if t = s then 1 else 0 := frame_inverse t s
    _ = if s = t then 1 else 0 := by simp only [eq_comm]

/-- Every arbitrary signed synthesis coefficient array is recovered exactly. -/
theorem coefficients_synthesize (c : (I → Bool) → ℝ) :
    coefficients (synthesize c) = c := by
  have hinv : kernelCompose (frameInverse (I := I)) frameMetric = identityKernel := by
    funext s t
    exact frame_inverse_left s t
  change action frameInverse (analyze (synthesize c)) = c
  rw [analyze_synthesize, ← kernelCompose_action, hinv, identityKernel_action]

/-- Canonical coordinates depend only on the actual activity projection. -/
theorem coefficients_projectActivity (f : (I → AES.Word) → ℝ) :
    coefficients (projectActivity f) = coefficients f := by
  rw [← synthesize_coefficients f, coefficients_synthesize]

/-- Frame analysis also depends only on the actual activity projection. The
right Gram inverse here has its accepted orientation `G B = I`. -/
theorem analyze_projectActivity (f : (I → AES.Word) → ℝ) :
    analyze (projectActivity f) = analyze f := by
  have hinv : kernelCompose (frameMetric (I := I)) frameInverse = identityKernel := by
    funext s t
    exact frame_inverse s t
  rw [← synthesize_coefficients f, analyze_synthesize]
  change action frameMetric (action frameInverse (analyze f)) = analyze f
  rw [← kernelCompose_action, hinv, identityKernel_action]

theorem synthesize_injective :
    Function.Injective (synthesize (I := I)) := by
  intro c d h
  calc
    c = coefficients (synthesize c) := (coefficients_synthesize c).symm
    _ = coefficients (synthesize d) := congrArg coefficients h
    _ = d := coefficients_synthesize d

/-- The actual projection fixes every synthesized vector. -/
theorem projectActivity_synthesize (c : (I → Bool) → ℝ) :
    projectActivity (synthesize c) = synthesize c := by
  rw [← synthesize_coefficients (synthesize c), coefficients_synthesize]

/-- Idempotence is derived from the exact projector factorization and inverse,
without adding any projector or conditioning hypothesis. -/
theorem projectActivity_idempotent (f : (I → AES.Word) → ℝ) :
    projectActivity (projectActivity f) = projectActivity f := by
  rw [← synthesize_coefficients f]
  exact projectActivity_synthesize (coefficients f)

theorem projectActivity_fixed_of_mem_range (f : (I → AES.Word) → ℝ)
    (hf : f ∈ Set.range (projectActivity (I := I))) :
    projectActivity f = f := by
  rcases hf with ⟨g, rfl⟩
  exact projectActivity_idempotent g

/-- Every vector fixed by the actual activity projection is reconstructed. -/
theorem reconstruct_of_fixed (f : (I → AES.Word) → ℝ)
    (hf : projectActivity f = f) : synthesize (coefficients f) = f := by
  exact (synthesize_coefficients f).trans hf

/-- In particular, every actual activity-range vector is reconstructed. -/
theorem reconstruct_of_mem_range (f : (I → AES.Word) → ℝ)
    (hf : f ∈ Set.range (projectActivity (I := I))) :
    synthesize (coefficients f) = f := by
  exact reconstruct_of_fixed f (projectActivity_fixed_of_mem_range f hf)

/-- The canonical coefficients are the unique coordinates of any reconstructed
physical vector; no existence premise is hidden in this uniqueness statement. -/
theorem coefficients_eq_of_synthesize_eq (f : (I → AES.Word) → ℝ)
    (c : (I → Bool) → ℝ) (hc : synthesize c = f) : coefficients f = c := by
  rw [← hc, coefficients_synthesize]

/-- The actual activity range equals the synthesis image. -/
theorem range_projectActivity_eq_range_synthesize :
    Set.range (projectActivity (I := I)) = Set.range (synthesize (I := I)) := by
  apply Set.ext
  intro f
  constructor
  · intro hf
    exact ⟨coefficients f, reconstruct_of_mem_range f hf⟩
  · rintro ⟨c, rfl⟩
    exact ⟨synthesize c, projectActivity_synthesize c⟩

/-- The already proved word conditioning applies to the canonical coefficients
of every projected physical vector. -/
theorem coefficients_energy_projection (f : (I → AES.Word) → ℝ) :
    (∑ s : I → Bool, coefficients f s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ x : I → AES.Word, projectActivity f x ^ 2 := by
  simpa only [synthesize_coefficients] using frame_coefficient_energy (coefficients f)

theorem coefficients_energy_of_fixed (f : (I → AES.Word) → ℝ)
    (hf : projectActivity f = f) :
    (∑ s : I → Bool, coefficients f s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I * ∑ x : I → AES.Word, f x ^ 2 := by
  simpa only [hf] using coefficients_energy_projection f

theorem coefficients_energy_of_mem_range (f : (I → AES.Word) → ℝ)
    (hf : f ∈ Set.range (projectActivity (I := I))) :
    (∑ s : I → Bool, coefficients f s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I * ∑ x : I → AES.Word, f x ^ 2 := by
  exact coefficients_energy_of_fixed f (projectActivity_fixed_of_mem_range f hf)

theorem coefficients_norm_of_fixed (f : (I → AES.Word) → ℝ)
    (hf : projectActivity f = f) :
    l2 (coefficients f) ≤
      (1 - 1 / 65536 : ℝ) ^ (-(Fintype.card I : ℝ) / 2) * l2 f := by
  simpa only [reconstruct_of_fixed f hf] using frame_coefficient_norm (coefficients f)

section ResidualFamilies

variable {Y : Type*} [Fintype Y]

/-- An arbitrary residual-coordinate family is reconstructed pointwise. No
factorization or independence premise is imposed on the joint array. -/
theorem reconstruct_family_of_fixed (f : Y → (I → AES.Word) → ℝ)
    (hf : ∀ y, projectActivity (f y) = f y) :
    (fun y => synthesize (coefficients (f y))) = f := by
  funext y
  exact reconstruct_of_fixed (f y) (hf y)

theorem coefficients_family_energy_projection (f : Y → (I → AES.Word) → ℝ) :
    (∑ y, ∑ s : I → Bool, coefficients (f y) s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ y, ∑ x : I → AES.Word, projectActivity (f y) x ^ 2 := by
  simpa only [synthesize_coefficients] using
    frame_coefficient_family_energy (fun y => coefficients (f y))

/-- Arbitrary untouched residual indices retain exactly the accepted tensor
conditioning factor, counted only in activity coordinates. -/
theorem coefficients_family_energy_of_fixed (f : Y → (I → AES.Word) → ℝ)
    (hf : ∀ y, projectActivity (f y) = f y) :
    (∑ y, ∑ s : I → Bool, coefficients (f y) s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ y, ∑ x : I → AES.Word, f y x ^ 2 := by
  simpa only [hf] using coefficients_family_energy_projection f

theorem coefficients_family_energy_of_mem_range (f : Y → (I → AES.Word) → ℝ)
    (hf : ∀ y, f y ∈ Set.range (projectActivity (I := I))) :
    (∑ y, ∑ s : I → Bool, coefficients (f y) s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ y, ∑ x : I → AES.Word, f y x ^ 2 := by
  exact coefficients_family_energy_of_fixed f
    (fun y => projectActivity_fixed_of_mem_range (f y) (hf y))

end ResidualFamilies

/-- For the actual four-word block, this is exactly the accepted degree-zero
component, not a newly assumed notion of activity. -/
theorem projectActivity_fin4 (f : (Fin 4 → AES.Word) → ℝ) :
    projectActivity f = degreeComponent (0 : AES.Word) 0 f := by
  change action tensorActivityKernel f = degreeComponent (0 : AES.Word) 0 f
  rw [← degreeKernel_action (0 : AES.Word) 0 f]
  congr 1
  funext x y
  rw [degreeKernel_zero]
  rfl

theorem reconstruct_degree_zero (f : (Fin 4 → AES.Word) → ℝ)
    (hf : degreeComponent (0 : AES.Word) 0 f = f) :
    synthesize (coefficients f) = f := by
  apply reconstruct_of_fixed
  rw [projectActivity_fin4, hf]

end AESPaper.WordFrameCoordinates
