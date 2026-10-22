import AESConcrete.WordFourierVariants

/-!
# Exact activity correction for one-sided word Fourier entries

The generic centering theorem retains its explicit raw mixed-entry premise.
It supplies the zero-axis cancellations and exact numerical correction;
it is not a proof of the missing raw 1456/2^32 bound.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordMixedCentering
open AESMixing
open AESConcrete.WordFourierCore
set_option maxRecDepth 100000

theorem activity_right_fourier (a b : AES.Word) (ha : a ≠ 0) (hb : b ≠ 0) :
    kernelCompose (activityMatrix (0 : AES.Word)) wordFourier b a =
      -(1/(65536*4294967295) : ℝ) := by
  have hs : (∑ x, wordFourier x a) = 0 := by
    simp_rw [wordFourier_symmetric _ a]
    rw [wordFourier_row_sum, if_neg ha]
  change action (activityMatrix (0 : AES.Word)) (fun x => wordFourier x a) b = _
  rw [activityMatrix_action]
  simp only [wordAverage, if_neg hb, nonzeroMean]
  rw [hs]
  simp only [wordFourier_coefficient,
    AESConcrete.WordFourierCore.wordPairing.zero_left, word_card]
  norm_num

theorem residual_row_zero (K : AES.Word → AES.Word → ℝ)
    (hK : PointedBistochastic K 0) (a : AES.Word) : residualMatrix K 0 0 a = 0 := by
  simp only [residualMatrix, hK.zero_row, activityMatrix, if_true, sub_self]

theorem residual_row_sum (K : AES.Word → AES.Word → ℝ)
    (hK : PointedBistochastic K 0) (b : AES.Word) : (∑ x, residualMatrix K 0 b x) = 0 := by
  have hP := activityMatrix_pointed (0 : AES.Word) (by rw [word_card]; norm_num)
  simp only [residualMatrix, Finset.sum_sub_distrib, hK.row_sum, hP.row_sum, sub_self]

theorem residual_fourier_zero_row (K : AES.Word → AES.Word → ℝ)
    (hK : PointedBistochastic K 0) (a : AES.Word) :
    kernelCompose (residualMatrix K 0) wordFourier 0 a = 0 := by
  simp only [kernelCompose, residual_row_zero K hK, zero_mul, Finset.sum_const_zero]

theorem residual_fourier_zero_column (K : AES.Word → AES.Word → ℝ)
    (hK : PointedBistochastic K 0) (b : AES.Word) :
    kernelCompose (residualMatrix K 0) wordFourier b 0 = 0 := by
  simp only [kernelCompose, wordFourier_coefficient,
    AESConcrete.WordFourierCore.wordPairing.zero_right,
    mul_one_div, ← Finset.sum_div, residual_row_sum K hK, zero_div]

theorem residual_right_fourier (K : AES.Word → AES.Word → ℝ) (a b : AES.Word) :
    kernelCompose (residualMatrix K 0) wordFourier b a =
      kernelCompose K wordFourier b a -
        kernelCompose (activityMatrix (0 : AES.Word)) wordFourier b a := by
  simp only [kernelCompose, residualMatrix, sub_mul, Finset.sum_sub_distrib]

theorem centered_entry_lt_of_raw_le (K : AES.Word → AES.Word → ℝ)
    (hK : PointedBistochastic K 0)
    (hraw : ∀ a b : AES.Word, a ≠ 0 → b ≠ 0 →
      |kernelCompose K wordFourier b a| ≤ (1456/4294967296 : ℝ))
    (a b : AES.Word) :
    |kernelCompose (residualMatrix K 0) wordFourier b a| < (1457/4294967296 : ℝ) := by
  by_cases ha : a = 0
  · subst a
    rw [residual_fourier_zero_column K hK, abs_zero]
    norm_num
  by_cases hb : b = 0
  · subst b
    rw [residual_fourier_zero_row K hK, abs_zero]
    norm_num
  rw [residual_right_fourier, activity_right_fourier a b ha hb]
  calc
    _ ≤ |kernelCompose K wordFourier b a| + |-(1/(65536*4294967295) : ℝ)| :=
      abs_sub _ _
    _ ≤ (1456/4294967296 : ℝ) + |-(1/(65536*4294967295) : ℝ)| :=
      add_le_add (hraw a b ha hb) le_rfl
    _ < _ := by norm_num

end AESConcrete.WordMixedCentering
