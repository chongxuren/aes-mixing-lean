import AESMixing.L2Sums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Counting-measure activity-to-TV estimate. A zero-sum function constant on one
large cell has all its signed mass there cancelled by the complement. This
proves the coefficient needed by the paper without its sharper m/n factor.
No AES dynamics or initialization estimate is assumed or proved in this file.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AESPaper.RareActivity
open AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

def l1 (f : V → ℝ) : ℝ := ∑ x, |f x|

theorem restricted_l1_sq (s : Finset V) (f : V → ℝ) :
    (∑ x ∈ s, |f x|)^2 ≤ (s.card : ℝ) * (l2 f)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun x => |f x|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  have he : (∑ x ∈ s, (f x)^2) ≤ ∑ x, (f x)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)
  rw [l2_sq]
  exact h.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))

theorem l1_le_of_card (f : V → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcard : (Fintype.card V : ℝ) ≤ c^2) : l1 f ≤ c*l2 f := by
  have h := restricted_l1_sq (Finset.univ : Finset V) f
  simp only [Finset.card_univ] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (mul_nonneg hc (l2_nonneg f))).mp
  change (∑ x, |f x|)^2 ≤ (c*l2 f)^2
  rw [mul_pow]
  exact h.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))

theorem constant_cell_cancellation (s : Finset V) (f : V → ℝ) (c : ℝ)
    (hconst : ∀ x ∈ s, f x = c) (hzero : (∑ x, f x) = 0) :
    l1 f ≤ 2 * ∑ x ∈ sᶜ, |f x| := by
  have hsum : (∑ x ∈ s, f x) + (∑ x ∈ sᶜ, f x) = 0 := by
    rw [Finset.sum_add_sum_compl, hzero]
  have habs : (∑ x ∈ s, |f x|) = |∑ x ∈ s, f x| := by
    have h1 : (∑ x ∈ s, f x) = (s.card : ℝ)*c := by
      calc
        _ = ∑ _x ∈ s, c := Finset.sum_congr rfl hconst
        _ = _ := by simp
    have h2 : (∑ x ∈ s, |f x|) = (s.card : ℝ)*|c| := by
      calc
        _ = ∑ _x ∈ s, |c| := Finset.sum_congr rfl (fun x hx => congrArg abs (hconst x hx))
        _ = _ := by simp
    rw [h1, h2]
    simp [abs_mul]
  have hneg : (∑ x ∈ s, f x) = -(∑ x ∈ sᶜ, f x) := by linarith
  have hbound : (∑ x ∈ s, |f x|) ≤ ∑ x ∈ sᶜ, |f x| := by
    rw [habs, hneg, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsplit : l1 f = (∑ x ∈ s, |f x|) + (∑ x ∈ sᶜ, |f x|) := by
    exact (Finset.sum_add_sum_compl s (fun x => |f x|)).symm
  rw [hsplit]
  linarith

theorem rare_cell_l1 (s : Finset V) (f : V → ℝ) (c h : ℝ)
    (hconst : ∀ x ∈ s, f x = c) (hzero : (∑ x, f x) = 0)
    (hh : 0 ≤ h) (hcard : ((sᶜ).card : ℝ) ≤ h^2) :
    l1 f ≤ 2*h*l2 f := by
  have hb := restricted_l1_sq sᶜ f
  have hs : (∑ x ∈ sᶜ, |f x|) ≤ h*l2 f := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (mul_nonneg hh (l2_nonneg f))).mp
    rw [mul_pow]
    exact hb.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
  have hc := constant_cell_cancellation s f c hconst hzero
  nlinarith

theorem l1_add (f g : V → ℝ) : l1 (f+g) ≤ l1 f + l1 g := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_add_le (f x) (g x)

end AESPaper.RareActivity
