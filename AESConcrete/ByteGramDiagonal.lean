import AESMixing.ChannelProjection
import AESMixing.CenteredGram
import AESMixing.Gram
import AESConcrete.ByteOrientations

/-!
# Concrete AES byte residual Gram diagonal

This file derives exact diagonal, support, and zero-sum identities from the
proved concrete byte-channel resources.  No byte or word norm estimate is
assumed.  The four concrete channels are ordinary DDT, its transpose, the
squared-Walsh channel, and its transpose.

These facts are a bounded prerequisite for the direct damped degree-three
word argument.  Signed off-diagonal profiles, absolute-cube row bounds, and
mixed Fourier Gram entries are not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteGramDiagonal
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)

abbrev Byte := BinaryWord 8

def residualGram (D : Byte → Byte → ℝ) : Byte → Byte → ℝ :=
  gram (residualMatrix D 0)

theorem residual_zero_row {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    residualMatrix D 0 0 a = 0 := by
  simp [residualMatrix, activityMatrix, hD.zero_row]

theorem residual_zero_column {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    residualMatrix D 0 a 0 = 0 := by
  by_cases ha : a = 0 <;>
    simp [residualMatrix, activityMatrix, hD.zero_column, ha]

/-- The averaged actual channel column is the corresponding activity column.
This uses only its zero-row and column-sum identities. -/
theorem column_average {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    wordAverage 0 (fun y => D y a) = fun y => activityMatrix 0 y a := by
  funext y
  simp only [wordAverage, nonzeroMean, hD.column_sum, hD.zero_row]
  by_cases hy : y = 0 <;> by_cases ha : a = 0 <;>
    simp [activityMatrix, hy, ha, BinaryWord.card]

theorem residual_column {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    (fun y => residualMatrix D 0 y a) = wordResidual 0 (fun y => D y a) := by
  funext y
  change D y a - activityMatrix 0 y a = D y a - wordAverage 0 (fun x => D x a) y
  rw [column_average hD a]

theorem residual_column_sum {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    (∑ y, residualMatrix D 0 y a) = 0 := by
  change (∑ y, (fun x => residualMatrix D 0 x a) y) = 0
  rw [residual_column hD a]
  exact wordResidual_sum 0 (fun y => D y a) (by norm_num [BinaryWord.card])

theorem activity_symmetric (a b : Byte) : activityMatrix 0 a b = activityMatrix 0 b a := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [activityMatrix, ha, hb]

theorem residual_transpose (D : Byte → Byte → ℝ) (a b : Byte) :
    residualMatrix (fun y x => D x y) 0 a b = residualMatrix D 0 b a := by
  unfold residualMatrix
  rw [activity_symmetric a b]

theorem residual_row_sum {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    (∑ y, residualMatrix D 0 a y) = 0 := by
  have h := residual_column_sum hD.transpose a
  simpa only [residual_transpose] using h

/-- The residual Gram is the channel Gram minus the actual activity
projection.  The centering subtraction is retained exactly. -/
theorem residual_gram_formula {D : Byte → Byte → ℝ} (hD : ByteResources D)
    (a b : Byte) :
    residualGram D a b = gram D a b - activityMatrix 0 a b := by
  have hn : 1 < Fintype.card Byte := by norm_num [BinaryWord.card]
  calc
    residualGram D a b =
        ∑ y, wordResidual 0 (fun x => D x a) y *
          wordResidual 0 (fun x => D x b) y := by
      change (∑ y, (fun x => residualMatrix D 0 x a) y *
        (fun x => residualMatrix D 0 x b) y) = _
      rw [residual_column hD a, residual_column hD b]
    _ = gram D a b -
        (D 0 a * D 0 b +
          ((∑ y, D y a) - D 0 a) * ((∑ y, D y b) - D 0 b) /
            (Fintype.card Byte - 1 : ℝ)) := by
      rw [wordResidual_inner 0 hn, wordAverage_inner 0 hn]
      rfl
    _ = gram D a b - activityMatrix 0 a b := by
      simp only [hD.column_sum, hD.zero_row]
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
        simp [activityMatrix, ha, hb, BinaryWord.card]

theorem residual_gram_zero_row {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    residualGram D 0 a = 0 := by
  simp [residualGram, gram, residual_zero_column hD]

theorem residual_gram_zero_column {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    residualGram D a 0 = 0 := by
  simp [residualGram, gram, residual_zero_column hD]

theorem residual_gram_diagonal_nonzero {D : Byte → Byte → ℝ} (hD : ByteResources D)
    (a : Byte) (ha : a ≠ 0) :
    residualGram D a a = (8383 : ℝ) / 2088960 := by
  rw [residual_gram_formula hD, gram_diagonal, hD.collision_column a ha]
  norm_num [activityMatrix, ha, BinaryWord.card]

theorem residual_gram_diagonal {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    residualGram D a a = if a = 0 then 0 else (8383 : ℝ) / 2088960 := by
  by_cases ha : a = 0
  · subst a
    simp [residual_gram_zero_row hD]
  · rw [if_neg ha]
    exact residual_gram_diagonal_nonzero hD a ha

theorem residual_gram_row_sum {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    (∑ b, residualGram D a b) = 0 := by
  unfold residualGram gram
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, residual_row_sum hD, mul_zero]
  simp

theorem residual_gram_column_sum {D : Byte → Byte → ℝ} (hD : ByteResources D) (a : Byte) :
    (∑ b, residualGram D b a) = 0 := by
  unfold residualGram gram
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, residual_row_sum hD, zero_mul]
  simp

theorem actual_gram_diagonal (orientation : Orientation) (a : Byte) :
    residualGram (channel orientation) a a =
      if a = 0 then 0 else (8383 : ℝ) / 2088960 :=
  residual_gram_diagonal (channel_resources orientation) a

theorem actual_gram_zero_row (orientation : Orientation) (a : Byte) :
    residualGram (channel orientation) 0 a = 0 :=
  residual_gram_zero_row (channel_resources orientation) a

theorem actual_gram_zero_column (orientation : Orientation) (a : Byte) :
    residualGram (channel orientation) a 0 = 0 :=
  residual_gram_zero_column (channel_resources orientation) a

theorem actual_gram_row_sum (orientation : Orientation) (a : Byte) :
    (∑ b, residualGram (channel orientation) a b) = 0 :=
  residual_gram_row_sum (channel_resources orientation) a

theorem actual_gram_column_sum (orientation : Orientation) (a : Byte) :
    (∑ b, residualGram (channel orientation) b a) = 0 :=
  residual_gram_column_sum (channel_resources orientation) a

end AESConcrete.ByteGramDiagonal
