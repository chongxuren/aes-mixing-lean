import AESMixing.PointedProducts

/-! The zero state and the uniform nonzero law are preserved under
composition and under a permutation fixing zero. These closure lemmas
apply to the concrete word channel without a mixing assumption. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem PointedBistochastic.compose {D E : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) (hE : PointedBistochastic E z) :
    PointedBistochastic (kernelCompose D E) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y x
    exact Finset.sum_nonneg (fun a _ =>
      mul_nonneg (hD.nonnegative y a) (hE.nonnegative a x))
  · intro x
    simp only [kernelCompose, hD.zero_row, ite_mul, one_mul, zero_mul]
    simpa using hE.zero_row x
  · intro y
    simp only [kernelCompose, hE.zero_column, mul_ite, mul_one, mul_zero]
    simpa using hD.zero_column y
  · intro x
    unfold kernelCompose
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hD.column_sum, one_mul]
    exact hE.column_sum x
  · intro y
    unfold kernelCompose
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hE.row_sum, mul_one]
    exact hD.row_sum y

theorem PointedBistochastic.relabel_output {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (e : Equiv.Perm V) (hz : e z = z) :
    PointedBistochastic (fun y x => D (e.symm y) x) z := by
  have hi : e.symm z = z := e.symm_apply_eq.mpr hz.symm
  have he (y : V) : e.symm y = z ↔ y = z := by
    rw [e.symm_apply_eq, hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y x
    exact h.nonnegative _ _
  · intro x
    rw [hi]
    exact h.zero_row x
  · intro y
    simp only [h.zero_column, he]
  · intro x
    exact (Equiv.sum_comp e.symm (fun y => D y x)).trans (h.column_sum x)
  · intro y
    exact h.row_sum _

end AESMixing
