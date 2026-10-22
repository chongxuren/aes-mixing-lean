import AESMixing.ResidualCoordinates
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact Gram of projected nonzero-slope lines over an arbitrary finite field.
The line response is formed with the actual zero/uniform-complement projector;
the counting normalization is explicit. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeLineGram
open AESMixing
set_option autoImplicit false
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev R : K → K → ℝ := residualProjection (0 : K)

omit [DecidableEq K] in
theorem card_gt_one : 1 < Fintype.card K := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

theorem symmetric (x y : K) : R x y = R y x := by
  exact degreePiece_symmetric (0 : K) true x y

theorem scaling (a : K) (ha : a ≠ 0) (x y : K) : R (a*x) (a*y) = R x y := by
  simp [R, residualProjection, identityKernel, activityMatrix, mul_eq_zero, ha,
    mul_left_cancel₀ ha]

theorem gram (x y : K) : (∑ z : K, R z x * R z y) = R x y := by
  have h := congrFun (congrFun (degreePiece_compose (0 : K) card_gt_one true true) x) y
  change (∑ z : K, R x z * R z y) = R x y at h
  simpa only [symmetric x] using h

def rawResponse (a : K) (y : K × K) : ℝ := ∑ t : K, R y.1 t * R y.2 (a*t)

theorem rawResponse_eq (a : K) (ha : a ≠ 0) (y : K × K) :
    rawResponse a y = R y.2 (a*y.1) := by
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
    (fun z : K => R z y.2 * R z (a*y.1))
  calc
    rawResponse a y = ∑ t : K, R (a*t) y.2 * R (a*t) (a*y.1) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [scaling a ha, symmetric (a*t) y.2, symmetric t y.1]
      ring
    _ = ∑ z : K, R z y.2 * R z (a*y.1) := he
    _ = R y.2 (a*y.1) := gram _ _

theorem nonzero_pair (a b t : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    R (a*t) (b*t) = if t = 0 then 0 else
      (if a = b then 1 else 0) - 1/(Fintype.card K-1 : ℝ) := by
  by_cases ht : t = 0
  · subst t
    simp [R, residualProjection_zero_row]
  · have he : a*t = b*t ↔ a = b := ⟨mul_right_cancel₀ ht, fun h => congrArg (· * t) h⟩
    simp [R, residualProjection, identityKernel, activityMatrix, ht, ha, hb,
      mul_eq_zero, he]

theorem raw_inner (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ y : K × K, rawResponse a y * rawResponse b y) =
      (Fintype.card K-1 : ℝ)*(if a = b then 1 else 0)-1 := by
  simp_rw [rawResponse_eq a ha, rawResponse_eq b hb]
  rw [Fintype.sum_prod_type]
  simp_rw [gram, nonzero_pair a b _ ha hb]
  let c : ℝ := (if a = b then 1 else 0) - 1/(Fintype.card K-1 : ℝ)
  have he (t : K) : (if t = 0 then 0 else c) = c - if t = 0 then c else 0 := by
    by_cases ht : t = 0 <;> simp [ht]
  change (∑ t : K, if t = 0 then 0 else c) = _
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast card_gt_one (K := K)
  dsimp [c]
  field_simp [ne_of_gt (sub_pos.mpr hq)]
  <;> ring

def response (a : K) (y : K × K) : ℝ :=
  rawResponse a y / ((Fintype.card K : ℝ)*Real.sqrt (Fintype.card K))

/-- The literal paper line-Gram formula, valid at every finite-field size. -/
theorem scaled_inner (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Fintype.card K : ℝ)^4 * (∑ y : K × K, response a y * response b y) =
      (Fintype.card K : ℝ)*(Fintype.card K-1)*(if a = b then 1 else 0)-Fintype.card K := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hs := Real.sq_sqrt hq.le
  have hd : ((Fintype.card K : ℝ)*Real.sqrt (Fintype.card K)) *
      ((Fintype.card K : ℝ)*Real.sqrt (Fintype.card K)) = (Fintype.card K : ℝ)^3 := by
    calc
      _ = (Fintype.card K : ℝ)^2 * (Real.sqrt (Fintype.card K))^2 := by ring
      _ = _ := by rw [hs]; ring
  unfold response
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div, raw_inner a b ha hb, hd]
  field_simp [ne_of_gt hq]
  <;> ring

end AES8.PaperSlopeLineGram
