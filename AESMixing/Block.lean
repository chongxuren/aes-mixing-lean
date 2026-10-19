import AESMixing.MatrixEstimate
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! General block comparison in explicit Euclidean coordinates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def l2 (f : ι → ℝ) : ℝ := Real.sqrt (∑ i, f i ^ 2)

theorem l2_nonneg (f : ι → ℝ) : 0 ≤ l2 f := Real.sqrt_nonneg _

theorem l2_sq (f : ι → ℝ) : l2 f ^ 2 = ∑ i, f i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem l2_add_le (f g : ι → ℝ) : l2 (f + g) ≤ l2 f + l2 g := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hinner : (∑ i, f i * g i) ≤ l2 f * l2 g := by
    have hab : |∑ i, f i * g i| ≤ l2 f * l2 g := by
      apply (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (l2_nonneg _) (l2_nonneg _))).mp
      rw [sq_abs, mul_pow, l2_sq, l2_sq]
      exact hc
    exact (le_abs_self _).trans hab
  apply (sq_le_sq₀ (l2_nonneg _) (add_nonneg (l2_nonneg _) (l2_nonneg _))).mp
  rw [l2_sq]
  have he : (∑ i, (f + g) i ^ 2) =
      (∑ i, f i ^ 2) + 2 * (∑ i, f i * g i) + (∑ i, g i ^ 2) := by
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  nlinarith [l2_sq f, l2_sq g]

theorem block_comparison (a : ι → ℝ) (b : κ → ℝ)
    (aa ar : ι → ℝ) (ra rr : κ → ℝ)
    (scale : ℝ) (hs : 0 ≤ scale)
    (hAA : l2 aa ≤ scale * 7 * l2 a)
    (hAR : l2 ar ≤ scale / 2 * l2 b)
    (hRA : l2 ra ≤ scale / 2 * l2 a)
    (hRR : l2 rr ≤ scale * (15 / 2) * l2 b) :
    (∑ i, (aa + ar) i ^ 2) + (∑ j, (ra + rr) j ^ 2) ≤
      (8 * scale) ^ 2 * ((∑ i, a i ^ 2) + ∑ j, b j ^ 2) := by
  have hleft : l2 (aa + ar) ≤ scale * (7 * l2 a + l2 b / 2) := by
    have ht := l2_add_le aa ar
    linarith
  have hright : l2 (ra + rr) ≤ scale * (l2 a / 2 + 15 * l2 b / 2) := by
    have ht := l2_add_le ra rr
    linarith
  have ha := l2_nonneg a
  have hb := l2_nonneg b
  have hl2 := (sq_le_sq₀ (l2_nonneg (aa + ar)) (by positivity)).mpr hleft
  have hr2 := (sq_le_sq₀ (l2_nonneg (ra + rr)) (by positivity)).mpr hright
  rw [l2_sq] at hl2 hr2
  have hc := mul_le_mul_of_nonneg_left (two_block_energy (l2 a) (l2 b)) (sq_nonneg scale)
  rw [l2_sq, l2_sq] at hc
  nlinarith

end AESMixing
