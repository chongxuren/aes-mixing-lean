/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.Data

/-! Kernel-checkable inequalities for the finite prefix and invariant box. -/
noncomputable section
open scoped BigOperators
namespace AES8

theorem L_mono : Monotone L := by
  intro x y hxy i
  have hs : lowSum x ≤ lowSum y := Finset.sum_le_sum (fun j _ => hxy _)
  fin_cases i <;> simp only [L, L0, vec14_apply]
  all_goals
    linarith [hxy 0, hxy 1, hxy 2, hxy 3, hxy 4, hxy 5, hxy 6,
      hxy 7, hxy 8, hxy 9, hxy 10, hxy 11, hxy 12, hxy 13]

theorem M_mono : Monotone M := by
  intro x y hxy i
  have hs : allSum x ≤ allSum y := Finset.sum_le_sum (fun j _ => hxy j)
  fin_cases i <;> simp only [M, M0, vec14_apply]
  all_goals
    linarith [hxy 0, hxy 1, hxy 2, hxy 3, hxy 4, hxy 5, hxy 6,
      hxy 7, hxy 8, hxy 9, hxy 10, hxy 11, hxy 12, hxy 13]

theorem L_scale (a : ℝ) (x : Profile) : L (scale a x) = scale a (L x) := by
  have hs : lowSum (scale a x) = a * lowSum x := by
    simp only [lowSum, scale, Finset.mul_sum]
  funext i
  fin_cases i <;> simp [L, L0, hs, scale] <;> ring

theorem M_scale (a : ℝ) (x : Profile) : M (scale a x) = scale a (M x) := by
  have hs : allSum (scale a x) = a * allSum x := by
    simp only [allSum, scale, Finset.mul_sum]
  funext i
  fin_cases i <;> simp [M, M0, hs, scale] <;> ring

theorem prefix01 : (fun i => L u0 i + g i) ≤ u1 := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u0,g,u1]

theorem prefix12 : (fun i => L u1 i + M u0 i) ≤ u2 := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u0,u1,u2]

theorem prefix23 : (fun i => L u2 i + M u1 i) ≤ u3 := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u1,u2,u3]

theorem prefix34 : (fun i => L u3 i + M u2 i) ≤ u4 := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u2,u3,u4]

theorem u3_box : u3 ≤ scale 10 h := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u3,h,scale]

theorem u4_box : u4 ≤ scale 10 h := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, u4,h,scale]

theorem invariant : (fun i => L h i + M h i) ≤ h := by
  intro i
  fin_cases i <;> norm_num [L, M, L0, M0, lowSum, allSum, Fin.sum_univ_succ, vec14_apply, Fin.castAdd, h]

end AES8
