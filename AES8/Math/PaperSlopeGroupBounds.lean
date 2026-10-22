import AES8.Math.PaperGroupedMatrix

/-! Literal two-group bounds and weights in the paper's slope criterion.
These scalar consequences do not assume or assert the geometric row bounds;
`slope_group_comparison` exposes those remaining hypotheses explicitly. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeGroupBounds
open PaperGroupedMatrix
set_option autoImplicit false

def distanceGroups : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1+6*(1/16)^2+(1/16)^4, 3*(1/16)+3*(1/16)^3;
     4*(1/16)+4*(1/16)^3, 1+4*(1/16)^2+(1/16)^4]
def coincidenceGroups : Matrix (Fin 2) (Fin 2) ℝ :=
  !![6, 4*(1/16); 4*(1/16), 12+4*(1/16)^2]
def weights : Fin 2 → ℝ := ![3,8]

theorem coincidence_action : action coincidenceGroups weights = ![20,775/8] := by
  funext i
  fin_cases i <;> norm_num [action, coincidenceGroups, weights, Fin.sum_univ_succ]

theorem composed_action : action (distanceGroups * coincidenceGroups) weights =
    ![1268255/32768,54216455/524288] := by
  funext i
  rw [action_mul, coincidence_action]
  fin_cases i <;> norm_num [action, distanceGroups, Fin.sum_univ_succ]

theorem inverse_factor_lt : (256/255 : ℝ)^5 < 51/50 := by norm_num

theorem weighted_comparison (g : Fin 2) :
    (256/255 : ℝ)^5 * action (distanceGroups * coincidenceGroups) weights g <
      (66/5 : ℝ) * weights g := by
  rw [composed_action]
  fin_cases g <;> norm_num [weights]

theorem squared_norm_comparison : (66/(5*256^2) : ℝ) < (71/5000)^2 := by norm_num

theorem slope_group_comparison {I : Type*} [Fintype I]
    (H J : Matrix I I ℝ) (group : I → Fin 2)
    (hH : ∀ i j, 0 ≤ H i j)
    (hHgroup : GroupBound H group group distanceGroups)
    (hJgroup : GroupBound J group group coincidenceGroups) (i : I) :
    (256/255 : ℝ)^5 * action (H * J) (fun j => weights (group j)) i <
      (66/5 : ℝ) * weights (group i) := by
  apply scaled_product_action_lt H J group group distanceGroups coincidenceGroups
    hH _ hHgroup hJgroup weights _ _ _ (by positivity) weighted_comparison i
  · intro h g
    fin_cases h <;> fin_cases g <;> norm_num [coincidenceGroups]
  · intro g
    fin_cases g <;> norm_num [weights]

end AES8.PaperSlopeGroupBounds
