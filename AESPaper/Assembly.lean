import AESPaper.Comparison

/-!
Exact 25-entry assembly of v9's repeated comparison matrix from the
printed transfer bounds S, b, C, t and a (Appendix D.3--D.4).
These are arithmetic checks; the operator inequalities supplying those
inputs remain separate mathematical obligations.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AESPaper.Assembly
noncomputable section

def q : ℝ := 2^32
def nu : ℝ := 21 / 131072
def a : ℝ := 601 / 100
def b : Fin 4 → ℝ := ![0, 389 / 10000, 67 / 5000, 216 / 125000]
def t : Fin 4 → ℝ := ![0, (4243 / 500) / q, (8001 / 1000) / 65536, 1]
def S : Fin 4 → Fin 4 → ℝ :=
  ![![101/5000, 59/5000, 193/100000, 47/200000],
    ![59/5000, 17/6250, 223/500000, 27/20000000],
    ![193/100000, 223/500000, 29/2500000, 1/20000000],
    ![47/200000, 27/20000000, 1/20000000, 81/10000000000000]]
def C : Fin 4 → Fin 4 → ℝ :=
  ![![(6001/500)/(q*65536), (1911/100)/q, (1803/125)/65536, 1],
    ![(1911/100)/q, (6001/500)/65536, 1, 1],
    ![(1803/125)/65536, 1, 1, 1],
    ![1, 1, 1, 1]]

def roundedEntry (i j : Fin 5) : ℝ :=
  weights i * comparisonMatrix i j / (weights j * 1000000)

theorem activity_activity : a^2/q^2 + (∑ l, b l * t l) < roundedEntry 0 0 := by
  norm_num [a, q, b, t, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem residual_activity (i : Fin 4) :
    a * b i / q^2 + nu^(i.val+1) * (∑ l, C i l * b l) < roundedEntry i.succ 0 := by
  fin_cases i <;>
    norm_num [a, q, nu, b, C, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem activity_residual (j : Fin 3) :
    a * t j.castSucc + (∑ l, b l * C l j.castSucc) < roundedEntry 0 j.castSucc.succ := by
  fin_cases j <;>
    norm_num [a, q, t, b, C, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem residual_residual (i : Fin 4) (j : Fin 3) :
    b i * t j.castSucc + (∑ l, S i l * C l j.castSucc) <
      roundedEntry i.succ j.castSucc.succ := by
  fin_cases i <;> fin_cases j <;>
    norm_num [q, b, t, S, C, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem activity_last : Real.sqrt (a^2 + ∑ l, b l ^ 2) < roundedEntry 0 4 := by
  apply (Real.sqrt_lt' (by norm_num [roundedEntry, weights, comparisonMatrix, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])).2
  norm_num [a, b, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem residual_last (i : Fin 4) :
    Real.sqrt (b i ^ 2 + ∑ l, S i l ^ 2) < roundedEntry i.succ 4 := by
  apply (Real.sqrt_lt' (by fin_cases i <;> norm_num [roundedEntry, weights, comparisonMatrix, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])).2
  fin_cases i <;>
    norm_num [b, S, roundedEntry, weights, comparisonMatrix, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

end
end AESPaper.Assembly
