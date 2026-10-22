import AESConcrete.WordMomentNumbers

/-! The printed word comparison table and its exact scalar normalization.
This numerical leaf has no physical word-bound consumer dependencies. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperWordDegreeComparison
set_option autoImplicit false

def comparison : Fin 5 → Fin 5 → ℝ :=
  ![![63/10,0,4601/1000,33/10,161/100],
    ![0,116/100,2,161/100,113/1000],
    ![4601/1000,2,145/100,113/1000,8/1000],
    ![33/10,161/100,113/1000,8/1000,56/100000],
    ![161/100,113/1000,8/1000,56/100000,4/100000]]

theorem comparison_nonneg (i j : Fin 5) : 0 ≤ comparison i j := by
  fin_cases i <;> fin_cases j <;> norm_num [comparison]

theorem inherited_le (i j : Fin 5) : AESConcrete.WordMomentNumbers.op i j ≤ comparison i j := by
  fin_cases i <;> fin_cases j <;> norm_num [AESConcrete.WordMomentNumbers.op, comparison]

theorem comparison_symmetric (i j : Fin 5) : comparison i j = comparison j i := by
  fin_cases i <;> fin_cases j <;> norm_num [comparison]

/-- Counting-measure word normalization: sqrt(q) = 65536. -/
def normalizedComparison (i j : Fin 5) : ℝ := comparison i j / 65536

theorem normalizedComparison_nonneg (i j : Fin 5) : 0 ≤ normalizedComparison i j :=
  div_nonneg (comparison_nonneg i j) (by norm_num)

theorem normalizedComparison_symmetric (i j : Fin 5) :
    normalizedComparison i j = normalizedComparison j i := by
  simp only [normalizedComparison, comparison_symmetric i j]

end AES8.PaperWordDegreeComparison
