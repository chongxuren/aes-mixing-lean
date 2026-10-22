import AES8.Recurrence.PaperComparisonMaps

/-!
# Positivity of the fixed rational paper maps

These exhaustive kernel checks cover every entry of the two graph-defined
fourteen-dimensional matrices. They are separate from the image tests.
-/
namespace AES8.PaperComparison
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

 theorem qp_pos (n : ℤ) : 0 < qp n := by
  exact zpow_pos (by norm_num [sqrtQ]) n
 theorem eta_pos : 0 < eta := by norm_num [eta, q]
 theorem xi_pos : 0 < xi := by norm_num [xi, sqrtQ]
 theorem rootUpper_nonneg (n : ℕ) : 0 ≤ rootUpper n := by
  unfold rootUpper
  split <;> norm_num

 theorem stepMatrix_nonneg (i j : Fin 14) : 0 ≤ stepMatrix i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

 theorem returnMatrix_nonneg (i j : Fin 14) : 0 ≤ returnMatrix i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

 theorem mv_nonneg {m : QMatrix} {x : QProfile}
    (hm : ∀ i j, 0 ≤ m i j) (hx : ∀ i, 0 ≤ x i) (i : Fin 14) : 0 ≤ mv m x i := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hm i j) (hx j))

 theorem mv_mono {m : QMatrix} (hm : ∀ i j, 0 ≤ m i j)
    {x y : QProfile} (hxy : x ≤ y) : mv m x ≤ mv m y := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hm i j))

end AES8.PaperComparison
