import AES8.Math.PaperSlopeOutputFrame
import AES8.Math.PaperSlopeLineGram

/-! The exact class-count Gram and its positive constant remainder.
This layer proves the upper comparison from the literal normalized line
formula, without yet identifying the graph contraction of an arbitrary map.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeClassGram
open PaperSlopeCoincidences PaperSymbolicSlopeTable PaperSlopeCoincidenceMatrix
open PaperSlopeOutputFrame
set_option autoImplicit false

/-- Scaled line-Gram contraction after changing the input coefficient signs. -/
def scaledGram (u : Interior → ℝ) : ℝ :=
  ∑ p : Fin 6, ∑ k : Fin 20, ∑ l : Fin 20,
    u (inputIndex p k)*u (inputIndex p l) *
      (256/255 : ℝ)^2 * (1/16 : ℝ)^outputDistance p k l *
      ((255/256 : ℝ)*(if slopeClass (pairType p) k = slopeClass (pairType p) l
        then 1 else 0) - 1/256)

def constantRemainder (u : Interior → ℝ) : ℝ :=
  ∑ p : Fin 6, ∑ k : Fin 20, ∑ l : Fin 20,
    u (inputIndex p k)*u (inputIndex p l)*(1/16 : ℝ)^outputDistance p k l

theorem matrix_quadratic (u : Interior → ℝ) :
    (∑ A : Interior, ∑ B : Interior, u A*u B*matrix (1/16) A B) =
      ∑ p : Fin 6, ∑ k : Fin 20, ∑ l : Fin 20,
        if slopeClass (pairType p) k = slopeClass (pairType p) l then
          u (inputIndex p k)*u (inputIndex p l)*(1/16 : ℝ)^outputDistance p k l else 0 := by
  have he (A : Interior) :
      (∑ B : Interior, u A*u B*matrix (1/16) A B) =
      u A * PaperGroupedMatrix.action (matrix (1/16)) u A := by
    unfold PaperGroupedMatrix.action
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  simp_rw [he, matrix_action, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have heq (A : Interior) : inputSet p k = A.val ↔ A = inputIndex p k := by
    simp [Subtype.ext_iff, inputIndex, eq_comm]
  simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem constant_nonneg (u : Interior → ℝ) : 0 ≤ constantRemainder u :=
  Finset.sum_nonneg (fun p _ => distance_quadratic_nonneg p (fun k => u (inputIndex p k)))

theorem scaledGram_identity (u : Interior → ℝ) :
    scaledGram u = (256/255 : ℝ) *
      (∑ A : Interior, ∑ B : Interior, u A*u B*matrix (1/16) A B) -
        ((256/255 : ℝ)^2 / 256) * constantRemainder u := by
  rw [matrix_quadratic]
  unfold scaledGram constantRemainder
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem scaledGram_le (u : Interior → ℝ) :
    scaledGram u ≤ (256/255 : ℝ) *
      (∑ A : Interior, ∑ B : Interior, u A*u B*matrix (1/16) A B) := by
  rw [scaledGram_identity]
  exact sub_le_self _ (mul_nonneg (by norm_num) (constant_nonneg u))

end AES8.PaperSlopeClassGram
