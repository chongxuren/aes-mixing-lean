import AESPaper.Assembly
import AESPaper.WordResidualOneOne
import AESPaper.WordResidualOneTwo
import AESPaper.WordResidualFour
import AESPaper.WordResidualFiveSix

/-!
# Exact scalar rounding after residual-position aggregation
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace AESPaper.ResidualRounding

/-- Position aggregation contributes the square root of the two mask counts. -/
def coefficient (i j : ℕ) (raw : ℝ) : ℝ :=
  Real.sqrt ((Nat.choose 4 i : ℝ) * (Nat.choose 4 j : ℝ)) *
    ((WordActivityFrame.conditioningFactor (4 - i) *
      WordActivityFrame.conditioningFactor (4 - j)) * raw)

theorem coefficient_nonnegative (i j : ℕ) (raw : ℝ) (hr : 0 ≤ raw) :
    0 ≤ coefficient i j raw := by
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (WordActivityFrame.conditioningFactor_nonneg _)
      (WordActivityFrame.conditioningFactor_nonneg _)) hr)

theorem coefficient_mono (i j : ℕ) {raw raw' : ℝ} (h : raw ≤ raw') :
    coefficient i j raw ≤ coefficient i j raw' := by
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h
      (mul_nonneg (WordActivityFrame.conditioningFactor_nonneg _)
        (WordActivityFrame.conditioningFactor_nonneg _)))
    (Real.sqrt_nonneg _)

/-- Squaring removes the frame radicals without any real-power estimates. -/
theorem coefficient_sq (i j : ℕ) (raw : ℝ) :
    coefficient i j raw ^ 2 =
      ((Nat.choose 4 i : ℝ) * (Nat.choose 4 j : ℝ)) *
        (((65536 / 65535 : ℝ) ^ (4 - i) *
          (65536 / 65535 : ℝ) ^ (4 - j)) * raw ^ 2) := by
  have hN : (0 : ℝ) ≤ (Nat.choose 4 i : ℝ) * (Nat.choose 4 j : ℝ) := by
    positivity
  simp only [coefficient, mul_pow, Real.sq_sqrt hN,
    WordActivityFrame.conditioningFactor_sq]

theorem coefficient_le_of_sq (i j : ℕ) (raw cap : ℝ)
    (hr : 0 ≤ raw) (hcap : 0 ≤ cap)
    (h : ((Nat.choose 4 i : ℝ) * (Nat.choose 4 j : ℝ)) *
      (((65536 / 65535 : ℝ) ^ (4 - i) *
        (65536 / 65535 : ℝ) ^ (4 - j)) * raw ^ 2) ≤ cap ^ 2) :
    coefficient i j raw ≤ cap := by
  apply (sq_le_sq₀ (coefficient_nonnegative i j raw hr) hcap).mp
  rw [coefficient_sq]
  exact h

-- Stable raw interfaces: these are the accepted fixed-position coefficients,
-- before position aggregation and before the q^2 scaling in Assembly.S.
def raw11 : ℝ := 3 * WordResidualOneOne.coefficient
def raw12 : ℝ := WordResidualOneTwo.coefficient * HardActivityArrays.coefficient32
def raw13 : ℝ := WordResidualFour.coefficient13
def raw22 : ℝ := WordResidualFour.coefficient22
def raw14 : ℝ := Real.sqrt
  (2 * WordResidualFiveSix.fiveA ^ 2 + 6 * WordResidualFiveSix.fiveB ^ 2)
def raw23 : ℝ := Real.sqrt
  (WordResidualFiveSix.fiveA ^ 2 +
    2 * WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB +
    5 * WordResidualFiveSix.fiveB ^ 2)
def raw24 : ℝ := Real.sqrt
  (2 * WordResidualFiveSix.sixPlaneA ^ 2 + 2 * WordResidualFiveSix.sixB ^ 2)
def raw33 : ℝ := WordResidualFiveSix.sixMomentA + WordResidualFiveSix.sixB

theorem raw11_nonnegative : 0 ≤ raw11 := by
  exact mul_nonneg (by norm_num) WordResidualOneOne.coefficient_nonnegative

theorem raw12_nonnegative : 0 ≤ raw12 :=
  mul_nonneg WordResidualOneTwo.coefficient_nonnegative
    HardActivityArrays.coefficient32_positive.le

theorem raw13_nonnegative : 0 ≤ raw13 := WordResidualFour.coefficient13_nonnegative
theorem raw22_nonnegative : 0 ≤ raw22 := WordResidualFour.coefficient22_nonnegative
theorem raw14_nonnegative : 0 ≤ raw14 := Real.sqrt_nonneg _
theorem raw23_nonnegative : 0 ≤ raw23 := Real.sqrt_nonneg _
theorem raw24_nonnegative : 0 ≤ raw24 := Real.sqrt_nonneg _
theorem raw33_nonnegative : 0 ≤ raw33 :=
  add_nonneg WordResidualFiveSix.sixMomentA_nonnegative
    WordResidualFiveSix.sixB_nonnegative

theorem sqrt13_le : Real.sqrt (13 : ℝ) ≤ 361 / 100 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 361 / 100)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
  norm_num

theorem raw12_sq : raw12 ^ 2 =
    (WeightedEncoding.nu ^ 2) ^ 2 * WeightedEncoding.delta /
      ((65536 : ℝ) ^ 2) ^ 2 * (8 + 2 * Real.sqrt 13) := by
  simp only [raw12, WordResidualOneTwo.coefficient, mul_pow, div_pow,
    Real.sq_sqrt WeightedEncoding.delta_nonnegative,
    HardActivityArrays.coefficient32_sq, HardActivityArrays.rho32]

theorem raw13_sq : raw13 ^ 2 =
    4 * WordResidualFour.lineCoefficient ^ 2 +
      6 * WordResidualFour.lineCoefficient * WordResidualFour.momentMiddle +
      3 * WordResidualFour.momentMiddle ^ 2 := by
  have hA := WordResidualFour.lineCoefficient_nonnegative
  have hB := WordResidualFour.momentMiddle_nonnegative
  exact Real.sq_sqrt (by positivity)

theorem fiveA_sq : WordResidualFiveSix.fiveA ^ 2 =
    WeightedEncoding.nu ^ 4 * WordMarkedMoment.delta ^ 3 := by
  rw [WordResidualFiveSix.fiveA, mul_pow,
    Real.sq_sqrt (pow_nonneg WordMomentCoefficients.delta_nonnegative 3)]
  ring

theorem fiveB_sq : WordResidualFiveSix.fiveB ^ 2 =
    WordMarkedMoment.tau ^ 4 * (WordMarkedMoment.delta / WordMarkedMoment.q) := by
  rw [WordResidualFiveSix.fiveB, mul_pow,
    Real.sq_sqrt (div_nonneg WordMomentCoefficients.delta_nonnegative
      WordMomentCoefficients.q_positive.le)]
  ring

/-- The two five-position radicals have an exact rational product. -/
theorem five_product :
    WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB =
      WeightedEncoding.nu ^ 2 * WordMarkedMoment.tau ^ 2 *
        WordMarkedMoment.delta ^ 2 / 65536 := by
  apply (sq_eq_sq₀
    (mul_nonneg WordResidualFiveSix.fiveA_nonnegative
      WordResidualFiveSix.fiveB_nonnegative) (by positivity)).mp
  rw [mul_pow, fiveA_sq, fiveB_sq]
  norm_num [WeightedEncoding.nu, WordMarkedMoment.tau,
    WordMarkedMoment.delta, WordMarkedMoment.q]

theorem raw14_sq : raw14 ^ 2 =
    2 * WordResidualFiveSix.fiveA ^ 2 + 6 * WordResidualFiveSix.fiveB ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem raw23_sq : raw23 ^ 2 =
    WordResidualFiveSix.fiveA ^ 2 +
      2 * (WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB) +
      5 * WordResidualFiveSix.fiveB ^ 2 := by
  have hA := WordResidualFiveSix.fiveA_nonnegative
  have hB := WordResidualFiveSix.fiveB_nonnegative
  have hs : raw23 ^ 2 = WordResidualFiveSix.fiveA ^ 2 +
      2 * WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB +
      5 * WordResidualFiveSix.fiveB ^ 2 := Real.sq_sqrt (by positivity)
  rw [hs]
  ring

theorem raw24_sq : raw24 ^ 2 =
    2 * WordResidualFiveSix.sixPlaneA ^ 2 + 2 * WordResidualFiveSix.sixB ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- A rational certificate for the inner root of the (2,2) array norm. -/
theorem lambda22_inner_le :
    Real.sqrt (WordResidualFour.planeMiddle ^ 2 +
      16 * WordResidualFour.lineCoefficient ^ 2) ≤
      (8973 / 10000000 : ℝ) / Assembly.q ^ 2 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (by norm_num [Assembly.q] :
      (0 : ℝ) ≤ (8973 / 10000000 : ℝ) / Assembly.q ^ 2)).mp
  rw [Real.sq_sqrt (by positivity)]
  norm_num [WordResidualFour.planeMiddle, WordResidualFour.lineCoefficient,
    WeightedEncoding.nu, WeightedEncoding.delta, WordMarkedMoment.q, Assembly.q]

theorem round11 : coefficient 1 1 raw11 ≤ Assembly.S 0 0 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 1 1 raw11 _ raw11_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [raw11, WordResidualOneOne.coefficient, WeightedEncoding.nu,
    Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round12 : coefficient 1 2 raw12 ≤ Assembly.S 0 1 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 1 2 raw12 _ raw12_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw12_sq]
  have hs := sqrt13_le
  norm_num [WeightedEncoding.nu, WeightedEncoding.delta, Nat.choose,
    Assembly.S, Assembly.q, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  nlinarith only [hs]

theorem round13 : coefficient 1 3 raw13 ≤ Assembly.S 0 2 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 1 3 raw13 _ raw13_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw13_sq]
  norm_num [WordResidualFour.lineCoefficient, WordResidualFour.momentMiddle,
    WeightedEncoding.nu, WeightedEncoding.delta, WordMarkedMoment.tau,
    WordMarkedMoment.q, Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round22 : coefficient 2 2 raw22 ≤ Assembly.S 1 1 / Assembly.q ^ 2 := by
  let upper : ℝ := (3 * WordResidualFour.planeMiddle +
    (8973 / 10000000 : ℝ) / Assembly.q ^ 2) / 2
  have hraw : raw22 ≤ upper := by
    change (3 * WordResidualFour.planeMiddle +
      Real.sqrt (WordResidualFour.planeMiddle ^ 2 +
        16 * WordResidualFour.lineCoefficient ^ 2)) / 2 ≤ upper
    dsimp only [upper]
    linarith only [lambda22_inner_le]
  apply (coefficient_mono 2 2 hraw).trans
  apply coefficient_le_of_sq 2 2 upper _
    (by norm_num [upper, WordResidualFour.planeMiddle, WeightedEncoding.nu,
      WordMarkedMoment.q, Assembly.q])
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [upper, WordResidualFour.planeMiddle, WeightedEncoding.nu,
    WordMarkedMoment.q, Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round14 : coefficient 1 4 raw14 ≤ Assembly.S 0 3 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 1 4 raw14 _ raw14_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw14_sq, fiveA_sq, fiveB_sq]
  norm_num [WeightedEncoding.nu, WordMarkedMoment.tau, WordMarkedMoment.delta,
    WordMarkedMoment.q, Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round23 : coefficient 2 3 raw23 ≤ Assembly.S 1 2 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 2 3 raw23 _ raw23_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw23_sq, fiveA_sq, fiveB_sq, five_product]
  norm_num [WeightedEncoding.nu, WordMarkedMoment.tau, WordMarkedMoment.delta,
    WordMarkedMoment.q, Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round24 : coefficient 2 4 raw24 ≤ Assembly.S 1 3 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 2 4 raw24 _ raw24_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw24_sq]
  norm_num [WordResidualFiveSix.sixPlaneA, WordResidualFiveSix.sixB,
    WeightedEncoding.nu, WordMarkedMoment.tau, WordMarkedMoment.delta,
    WordMarkedMoment.q, Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round33 : coefficient 3 3 raw33 ≤ Assembly.S 2 2 / Assembly.q ^ 2 := by
  apply coefficient_le_of_sq 3 3 raw33 _ raw33_nonnegative
    (by norm_num [Assembly.S, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [raw33, WordResidualFiveSix.sixMomentA, WordResidualFiveSix.sixB,
    WordMarkedMoment.tau, WordMarkedMoment.delta, WordMarkedMoment.q,
    Nat.choose, Assembly.S, Assembly.q, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

end AESPaper.ResidualRounding
