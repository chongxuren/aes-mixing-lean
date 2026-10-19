import AESPaper.StartingWordDegrees
import AESPaper.CenteredConvolution

/-!
# Exact activity correction between the two state references

The activity projection preserves total mass and the distinguished state
value. It fixes both full uniform and uniform on non-distinguished states.
For a unit-mass vector vanishing at that state, the two centered activity
energies therefore differ by exactly `1/(N-1)-1/N`, where N is the full
four-coordinate state count. The vector may be signed and correlated.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActivityReferenceCorrection
open AESMixing AESConcrete
open AESPaper.StartingWord (q)

section Generic
variable {V : Type*} [Fintype V] [AddCommGroup V] [DecidableEq V]

theorem state_card_gt_one (hn : 1 < Fintype.card V) :
    1 < Fintype.card (Fin 4 → V) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  exact Nat.one_lt_pow (by decide) hn

theorem degree_zero_uniformExcept (z : V) (hn : 1 < Fintype.card V) :
    degreeComponent z 0 (uniformExcept (fun _ : Fin 4 => z)) =
      uniformExcept (fun _ : Fin 4 => z) := by
  rw [← degreeKernel_action]
  exact StartingWordDegrees.pointed_uniformExcept (degree_zero_pointed z hn)

theorem degree_zero_full_uniform (z : V) (hn : 1 < Fintype.card V) :
    degreeComponent z 0 (CenteredConvolution.uniform : (Fin 4 → V) → ℝ) =
      CenteredConvolution.uniform := by
  rw [← degreeKernel_action]
  funext y
  change (∑ x : Fin 4 → V, degreeKernel z 0 y x *
      (1/(Fintype.card (Fin 4 → V) : ℝ))) = 1/(Fintype.card (Fin 4 → V) : ℝ)
  rw [← Finset.sum_mul, (degree_zero_pointed z hn).row_sum, one_mul]

/-- Exact signed-vector correction, with the full state cardinality explicit. -/
theorem activity_energy_correction (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (hz : f (fun _ => z) = 0) (hm : (∑ x, f x) = 1) :
    (∑ y, degreeComponent z 0 (f-uniformExcept (fun _ : Fin 4 => z)) y ^ 2) =
      (∑ y, degreeComponent z 0
        (f-(CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) y ^ 2) -
      (1/(Fintype.card (Fin 4 → V)-1 : ℝ) - 1/(Fintype.card (Fin 4 → V) : ℝ)) := by
  let p := degreeComponent z 0 f
  have hp0 : p (fun _ : Fin 4 => z) = 0 := by
    change degreeComponent z 0 f (fun _ : Fin 4 => z) = 0
    rw [← degreeKernel_action, (degree_zero_pointed z hn).action_zero]
    exact hz
  have hpm : (∑ x, p x) = 1 := by
    change (∑ x, degreeComponent z 0 f x) = 1
    rw [← degreeKernel_action, (degree_zero_pointed z hn).action_sum]
    exact hm
  have he : degreeComponent z 0 (f-uniformExcept (fun _ : Fin 4 => z)) =
      p-uniformExcept (fun _ : Fin 4 => z) := by
    rw [← degreeKernel_action, action_sub, degreeKernel_action, degreeKernel_action,
      degree_zero_uniformExcept z hn]
  have hu : degreeComponent z 0
      (f-(CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) =
      p-CenteredConvolution.uniform := by
    rw [← degreeKernel_action, action_sub, degreeKernel_action, degreeKernel_action,
      degree_zero_full_uniform z hn]
  have heE := centered_energy p (fun _ : Fin 4 => z) (state_card_gt_one hn) hp0 hpm
  have huE := CenteredConvolution.centeredEnergy_eq_collision_sub p hpm
  rw [he, hu]
  change energy p (uniformExcept (fun _ : Fin 4 => z)) =
    CenteredConvolution.centeredEnergy p -
      (1/(Fintype.card (Fin 4 → V)-1 : ℝ) - 1/(Fintype.card (Fin 4 → V) : ℝ))
  rw [heE, huE]
  ring

end Generic

theorem reference_difference_pos (N : ℝ) (hN : 1 < N) :
    0 < 1/(N-1)-1/N := by
  have hp : 0 < N := lt_trans (by norm_num) hN
  have hm : 0 < N-1 := sub_pos.mpr hN
  have he : 1/(N-1)-1/N = 1/(N*(N-1)) := by
    field_simp [ne_of_gt hp, ne_of_gt hm] <;> ring
  rw [he]
  exact one_div_pos.mpr (mul_pos hp hm)

section GenericComparison
variable {V : Type*} [Fintype V] [AddCommGroup V] [DecidableEq V]

theorem activity_energy_lt_full_uniform (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (hz : f (fun _ => z) = 0) (hm : (∑ x, f x) = 1) :
    (∑ y, degreeComponent z 0 (f-uniformExcept (fun _ : Fin 4 => z)) y ^ 2) <
      ∑ y, degreeComponent z 0
        (f-(CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) y ^ 2 := by
  rw [activity_energy_correction z hn f hz hm]
  exact sub_lt_self _ (reference_difference_pos _ (by exact_mod_cast state_card_gt_one hn))

theorem activity_energy_le_full_uniform (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (hz : f (fun _ => z) = 0) (hm : (∑ x, f x) = 1) :
    (∑ y, degreeComponent z 0 (f-uniformExcept (fun _ : Fin 4 => z)) y ^ 2) ≤
      ∑ y, degreeComponent z 0
        (f-(CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) y ^ 2 :=
  (activity_energy_lt_full_uniform z hn f hz hm).le

end GenericComparison

theorem grouped_one_zero (b : AES.State) (hb : b ≠ 0) :
    GroupedLaw.groupedLaw 1 b (0 : AES.WordState) = 0 := by
  have h := GroupedLaw.error_zero 1 b hb
  simpa only [GroupedLaw.error, uniformExcept, if_true, sub_zero] using h

/-- The reference correction for the actual four-round centered activity. -/
theorem actual_energy_correction (b : AES.State) (hb : b ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) =
      (∑ y, degreeComponent (0 : AES.Word) 0
        (GroupedLaw.groupedLaw 1 b-(CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2) -
      (1/(q^4-1)-1/q^4) := by
  have h := activity_energy_correction (0 : AES.Word) AES.word_card_gt_one
    (GroupedLaw.groupedLaw 1 b) (grouped_one_zero b hb) (GroupedLaw.grouped_total 1 b)
  have hc : (Fintype.card AES.WordState : ℝ) = q^4 := by
    change (Fintype.card (Fin 4 → AES.Word) : ℝ) = q^4
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← StartingWord.q_eq_word_card]
  rw [hc] at h
  exact h

theorem actual_energy_lt_full_uniform (b : AES.State) (hb : b ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) <
      ∑ y, degreeComponent (0 : AES.Word) 0
        (GroupedLaw.groupedLaw 1 b-(CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2 :=
  activity_energy_lt_full_uniform (0 : AES.Word) AES.word_card_gt_one
    (GroupedLaw.groupedLaw 1 b) (grouped_one_zero b hb) (GroupedLaw.grouped_total 1 b)

theorem actual_energy_le_full_uniform (b : AES.State) (hb : b ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) ≤
      ∑ y, degreeComponent (0 : AES.Word) 0
        (GroupedLaw.groupedLaw 1 b-(CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2 :=
  (actual_energy_lt_full_uniform b hb).le

/-- Conditional transfer only: the full-uniform activity budget is a premise. -/
theorem actual_scaled_energy_lt_of_full_uniform (b : AES.State) (hb : b ≠ 0) (C : ℝ)
    (hfull : q^5 * (∑ y, degreeComponent (0 : AES.Word) 0
      (GroupedLaw.groupedLaw 1 b-(CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2) ≤ C) :
    q^5 * (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) < C := by
  have h := mul_lt_mul_of_pos_left (actual_energy_lt_full_uniform b hb)
    (pow_pos (by norm_num [q] : 0 < q) 5)
  exact h.trans_le hfull

end AESPaper.ActivityReferenceCorrection
