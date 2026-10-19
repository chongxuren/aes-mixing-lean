import AESMixing.Scalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Counting-measure total variation and energy, as in Section 2. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def tv (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2
def energy (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2
def action (K : κ → ι → ℝ) (p : ι → ℝ) : κ → ℝ :=
  fun y => ∑ x, K y x * p x

theorem tv_nonneg (p q : ι → ℝ) : 0 ≤ tv p q := by
  unfold tv
  positivity

theorem energy_nonneg (p q : ι → ℝ) : 0 ≤ energy p q := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Counting-measure Cauchy--Schwarz, with the paper's factor 1/2. -/
theorem tv_sq_le_energy (p q : ι → ℝ) :
    (tv p q) ^ 2 ≤ (Fintype.card ι : ℝ) / 4 * energy p q := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι => (1 : ℝ)) (fun i => |p i - q i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at h
  unfold tv energy
  nlinarith

omit [Fintype κ] in
theorem action_sub (K : κ → ι → ℝ) (p q : ι → ℝ) :
    action K (p - q) = action K p - action K q := by
  funext y
  simp [action, mul_sub, Finset.sum_sub_distrib]

/-- Data processing under a column-stochastic matrix. -/
theorem tv_action_le (K : κ → ι → ℝ)
    (nonnegative : ∀ y x, 0 ≤ K y x)
    (column_sum : ∀ x, ∑ y, K y x = 1)
    (p q : ι → ℝ) : tv (action K p) (action K q) ≤ tv p q := by
  unfold tv action
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    (∑ y, |(∑ x, K y x * p x) - ∑ x, K y x * q x|)
        = ∑ y, |∑ x, K y x * (p x - q x)| := by
            simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ x, K y x * |p x - q x| := by
      apply Finset.sum_le_sum
      intro y _
      calc
        |∑ x, K y x * (p x - q x)|
            ≤ ∑ x, |K y x * (p x - q x)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, K y x * |p x - q x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (nonnegative y x)]
    _ = ∑ x, |p x - q x| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, column_sum, one_mul]

theorem tv_relabel (e : ι ≃ κ) (p q : κ → ℝ) :
    tv (p ∘ e) (q ∘ e) = tv p q := by
  unfold tv
  congr 1
  exact e.sum_comp (fun i => |p i - q i|)

theorem energy_relabel (e : ι ≃ κ) (p q : κ → ℝ) :
    energy (p ∘ e) (q ∘ e) = energy p q := by
  exact e.sum_comp (fun i => (p i - q i) ^ 2)

end AESMixing
