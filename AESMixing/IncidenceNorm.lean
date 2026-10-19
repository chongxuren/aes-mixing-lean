import AESMixing.ProjectedIncidence
import AESMixing.L2Sums

/-! The exact surviving-dimension cutoff and the incidence norm are now
combined for actual residual projections. The only input condition is a
nonempty set of marked input coordinates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES

def incidenceNormCoefficient (m : ℝ) (n i j : ℕ) : ℝ :=
  if 4 ≤ n ∨ n+i+j ≤ 4 then 0
  else Real.sqrt (m^(4-(n+i)) * m^(4-(n+j)))

theorem incidenceNormCoefficient_nonnegative (m : ℝ) (n i j : ℕ) :
    0 ≤ incidenceNormCoefficient m n i j := by
  unfold incidenceNormCoefficient
  split_ifs <;> positivity

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem markedResidual_zero_function (s : Fin 16) :
    markedResidual s (0 : (MaskCoordinates s → V) → ℝ) = 0 := by
  funext x
  simp [markedResidual, action]

theorem projected_incidence_l2
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (k : MaskCoordinates inp) (f : (MaskCoordinates inp → V) → ℝ) :
    l2 (markedResidual out (action
      (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp))
      (markedResidual inp f))) ≤
      incidenceNormCoefficient (Fintype.card V) (maskSize r+maskSize z)
        (maskSize out) (maskSize inp) * l2 f := by
  by_cases hzero : 4 ≤ maskSize r+maskSize z
  · rw [projected_incidence_zero_dimension L hL r z out inp hzero k f,
      markedResidual_zero_function]
    simp [l2, incidenceNormCoefficient, hzero]
  by_cases hhigh : maskSize r+maskSize z+maskSize out+maskSize inp ≤ 4
  · rw [projected_incidence_high_dimension L hL hn r z out inp hr hz hhigh k f,
      markedResidual_zero_function]
    simp [l2, incidenceNormCoefficient, hhigh]
  rw [incidenceNormCoefficient, if_neg (not_or.mpr ⟨hzero,hhigh⟩)]
  apply l2_le_of_energy _ f _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  exact projected_incidence_energy L hL hn r z out inp hr hz f

end AESMixing
