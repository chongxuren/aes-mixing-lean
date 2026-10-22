import AES8.Math.PaperSlopeCoincidenceMatrix

/-! The distance kernel on the fourteen retained activity coordinates.
Only finite subset-distance multiplicities are evaluated; the real row
polynomial is derived from those counts with an arbitrary parameter. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeDistanceMatrix
open PaperSlopeCoincidenceMatrix PaperSlopeCoincidences PaperSlopeGroupBounds
open PaperGroupedMatrix
set_option autoImplicit false
set_option maxRecDepth 100000

def distance (A B : Finset (Fin 4)) : ℕ := ((A \ B) ∪ (B \ A)).card

def distanceCount (A : Interior) (g : Fin 2) (d : Fin 5) : ℕ :=
  ∑ B : Interior, if group B.val = g ∧ distance A.val B.val = d.val then 1 else 0

def printedDistanceCount (a g : Fin 2) (d : Fin 5) : ℕ :=
  if a = g then
    if d.val = 0 ∨ d.val = 4 then 1 else
      if d.val = 2 then (if a = 0 then 6 else 4) else 0
  else if d.val = 1 ∨ d.val = 3 then (if a = 0 then 3 else 4) else 0

theorem distance_le (A B : Finset (Fin 4)) : distance A B ≤ 4 := by
  revert A B
  decide

theorem distance_counts (A : Interior) (g : Fin 2) (d : Fin 5) :
    distanceCount A g d = printedDistanceCount (group A.val) g d := by
  revert A g d
  decide

theorem power_sum (x : ℝ) (A B : Interior) :
    (∑ d : Fin 5, if distance A.val B.val = d.val then x^d.val else 0) =
      x^distance A.val B.val := by
  let e : Fin 5 := ⟨distance A.val B.val, Nat.lt_succ_of_le (distance_le _ _)⟩
  have he (d : Fin 5) : distance A.val B.val = d.val ↔ d = e := by
    simp [Fin.ext_iff, e, eq_comm]
  simp only [he]
  simp [e]

theorem row_polynomial (x : ℝ) (A : Interior) (g : Fin 2) :
    (∑ B : Interior, if group B.val = g then x^distance A.val B.val else 0) =
      ∑ d : Fin 5, (distanceCount A g d : ℝ)*x^d.val := by
  unfold distanceCount
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hg : group B.val = g
  · simp only [hg, true_and, if_true]
    exact (power_sum x A B).symm
  · simp [hg]

def distanceKernel : Matrix Interior Interior ℝ :=
  fun A B => (1/16 : ℝ)^distance A.val B.val

theorem distanceKernel_eq (A B : Interior) :
    distanceKernel A B = (1/16 : ℝ)^distance A.val B.val := rfl

theorem distance_group_rows (A : Interior) (g : Fin 2) :
    (∑ B : Interior, if group B.val = g then distanceKernel A B else 0) =
      distanceGroups (group A.val) g := by
  change (∑ B : Interior, if group B.val = g then
    (1/16 : ℝ)^distance A.val B.val else 0) = _
  rw [row_polynomial]
  simp_rw [distance_counts]
  generalize group A.val = a
  fin_cases a <;> fin_cases g <;>
    norm_num [printedDistanceCount, distanceGroups, Fin.sum_univ_succ]

theorem distance_nonneg (A B : Interior) : 0 ≤ distanceKernel A B := by
  rw [distanceKernel_eq]
  positivity

/-- The weighted comparison for the actual distance and class-count matrices;
all group bounds are derived from the literal table and subset distances. -/
theorem weighted_rows (A : Interior) :
    (256/255 : ℝ)^5 * action (distanceKernel * matrix (1/16))
      (fun B => weights (group B.val)) A < (66/5 : ℝ)*weights (group A.val) := by
  exact slope_group_comparison distanceKernel (matrix (1/16)) (fun B => group B.val)
    distance_nonneg (fun B g => (distance_group_rows B g).le) coincidence_group_bound A

end AES8.PaperSlopeDistanceMatrix
