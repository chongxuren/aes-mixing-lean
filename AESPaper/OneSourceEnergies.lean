import AESPaper.OneSourceProjection
import AESPaper.OneSourceResidual
import AESPaper.SecondResponse
import AESPaper.OneSourceActivity

/-!
# Actual mixed Gram sums for one active source word

An inactive projection factor is uniform on nonzero words. The actual
source weights vanish at zero, so its Gram factor can be replaced by
1/(q-1) inside the weighted sum. Active factors retain the signed residual
Gram and their shared source pair. No entrywise boundary invariance or
independence of output coordinates is assumed.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.OneSourceEnergies
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.OneSourceResidual (R)

def G (k i : Fin 4) (x z : AES.Word) : ℝ :=
  gram R (BoundarySourceCoordinates.outputEquiv k i x)
    (BoundarySourceCoordinates.outputEquiv k i z)

theorem activity_gram {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (hn : 1 < Fintype.card V) (x z : V) :
    gram (activityMatrix v) x z = activityMatrix v x z := by
  have hs : gram (activityMatrix v) x z =
      kernelCompose (activityMatrix v) (activityMatrix v) x z := by
    unfold gram kernelCompose
    apply Finset.sum_congr rfl
    intro y _
    rw [activityMatrix_symmetric v y x]
  rw [hs, activityMatrix_idempotent v hn]

theorem boundary_activity_gram (k i : Fin 4) (x z : AES.Word) (hx : x ≠ 0) (hz : z ≠ 0) :
    gram (activityMatrix (0 : AES.Word)) (BoundarySourceCoordinates.outputEquiv k i x)
      (BoundarySourceCoordinates.outputEquiv k i z) = 1/(q-1) := by
  rw [activity_gram 0 ProfileSpace.word_card_gt_one]
  simp only [activityMatrix, OneSourceLaw.outputEquiv_ne_zero k i x hx,
    OneSourceLaw.outputEquiv_ne_zero k i z hz, if_false, ← StartingWord.q_eq_word_card]

/-- Only terms with nonzero source weights use the all-active column identity. -/
theorem pattern_energy (b : Fin 4 → Bool) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, action (productProjection (0 : AES.Word) b) (OneSourceLaw.law k a) y ^ 2) =
      ∑ x, ∑ z, wordLaw a x * wordLaw a z *
        ∏ i, if b i then G k i x z else 1/(q-1) := by
  rw [OneSourceProjection.projected_law_energy]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : x = 0
  · subst x
    simp only [StartingWord.wordLaw_zero a ha, zero_mul]
  by_cases hz : z = 0
  · subst z
    simp only [StartingWord.wordLaw_zero a ha, mul_zero, zero_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hb : b i
  · simp only [OneSourceProjection.piece, hb, Bool.false_eq_true, if_false,
      boundary_activity_gram k i x z hx hz]
  · rfl

/-- The global second Gram moment survives each source permutation. -/
theorem G_moment (k i : Fin 4) :
    (∑ x, ∑ z, G k i x z ^ 2) ≤ (300/q)^2 := by
  change (∑ x, ∑ z, gram R (BoundarySourceCoordinates.outputEquiv k i x)
    (BoundarySourceCoordinates.outputEquiv k i z)^2) ≤ _
  rw [CappedSourceGram.gram_moment_relabel]
  exact OneSourceResidual.R_moment

theorem G_entry (k i : Fin 4) (x z : AES.Word) : |G k i x z| ≤ 2/(15*q) :=
  gram_entry_bound R (2/(15*q)) (by norm_num [q]) OneSourceResidual.R_column _ _

/-- Reindex the transported source law before expanding its squared response. -/
theorem relabeled_response_energy {V : Type*} [Fintype V]
    (T : V → V → ℝ) (e : Equiv.Perm V) (mu : V → ℝ) :
    (∑ y, action T (lawRelabel e mu) y ^ 2) =
      ∑ x, ∑ z, mu x * mu z * gram T (e x) (e z) := by
  have he (y : V) : action T (lawRelabel e mu) y = ∑ x, T y (e x) * mu x := by
    simpa only [action, lawRelabel, Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun x => T y x * mu (e.symm x))).symm
  simp only [he]
  exact gram_quadratic (fun y x => T y (e x)) mu

/-- Degree-one signed Gram contraction is the checked local second response. -/
theorem G_weighted_lt (k i : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ x, ∑ z, wordLaw a x * wordLaw a z * G k i x z) < 49/(5*q^2) := by
  have h := SecondResponse.boundary_source_energy_lt k i a ha
  rw [SecondResponse.response, relabeled_response_energy] at h
  exact h

/-- The whole-state uniform reference contributes only to degree zero. -/
theorem uniform_positive_degree (j : Fin 5) (hj : j ≠ 0) :
    degreeComponent (0 : AES.Word) j (uniformExcept (0 : AES.WordState)) = 0 := by
  calc
    _ = degreeComponent (0 : AES.Word) j
        (degreeComponent (0 : AES.Word) 0 (uniformExcept (0 : AES.WordState))) :=
      congrArg (degreeComponent (0 : AES.Word) j) OneSourceActivity.activity_uniformExcept.symm
    _ = 0 := by
      rw [degreeComponent_compose (0 : AES.Word) ProfileSpace.word_card_gt_one, if_neg hj]

theorem centered_positive_degree (j : Fin 5) (hj : j ≠ 0) (k : Fin 4) (a : AES.Word) :
    degreeComponent (0 : AES.Word) j (OneSourceLaw.law k a-uniformExcept (0 : AES.WordState)) =
      degreeComponent (0 : AES.Word) j (OneSourceLaw.law k a) := by
  simp only [← degreeKernel_action, action_sub]
  rw [degreeKernel_action, degreeKernel_action, uniform_positive_degree j hj, sub_zero]

/-- A degree-one pattern selects exactly one output position. -/
theorem one_pattern (b : Fin 4 → Bool) (hb : degreeIndex b = 1) :
    ∃ i : Fin 4, b = fun c => decide (c=i) := by
  have h : ∀ b : Fin 4 → Bool, degreeIndex b = 1 →
      ∃ i : Fin 4, b = fun c => decide (c=i) := by decide
  exact h b hb

theorem one_pattern_product (i : Fin 4) (f : Fin 4 → ℝ) (c : ℝ) :
    (∏ j, if decide (j=i) then f j else c) = f i * c^3 := by
  fin_cases i <;> simp [Fin.prod_univ_four] <;> ring

/-- Three uniform activity factors accompany the single residual response. -/
theorem pattern_one_energy_le (b : Fin 4 → Bool) (hb : degreeIndex b = 1)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, action (productProjection (0 : AES.Word) b) (OneSourceLaw.law k a) y ^ 2) ≤
      (49/(5*q^2)) * (1/(q-1))^3 := by
  obtain ⟨i, rfl⟩ := one_pattern b hb
  rw [pattern_energy _ k a ha]
  simp_rw [one_pattern_product]
  calc
    _ = (∑ x, ∑ z, wordLaw a x * wordLaw a z * G k i x z) * (1/(q-1))^3 := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ (49/(5*q^2)) * (1/(q-1))^3 :=
      mul_le_mul_of_nonneg_right (G_weighted_lt k i a ha).le (by norm_num [q])

end AESPaper.OneSourceEnergies
