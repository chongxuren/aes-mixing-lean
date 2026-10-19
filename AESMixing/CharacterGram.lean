import AESMixing.InversionBound
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Data.Fintype.BigOperators

/-! A real-character proof of the sign Gram identity for inversion.
The additive character and the difference-count identity are supplied separately. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def invPermutation : Equiv.Perm F where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv

def nonzeroInvPermutation : Equiv.Perm {x : F // x ≠ 0} where
  toFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  invFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  left_inv x := Subtype.ext (inv_inv x.val)
  right_inv x := Subtype.ext (inv_inv x.val)

omit [DecidableEq F] in
theorem real_character_sum_zero (ψ : F → ℝ)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (w : F) (hw : ψ w = -1) : (∑ x, ψ x) = 0 := by
  have h := Equiv.sum_comp (Equiv.addLeft w) ψ
  change (∑ x, ψ (w + x)) = ∑ x, ψ x at h
  simp_rw [hadd, hw, ← Finset.mul_sum] at h
  linarith

theorem real_character_scaled_sum (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hsum : (∑ x, ψ x) = 0) (c : F) :
    (∑ x, ψ (x * c)) = if c = 0 then (Fintype.card F : ℝ) else 0 := by
  by_cases hc : c = 0
  · simp [hc, hzero]
  · rw [if_neg hc, ← hsum]
    exact Equiv.sum_comp (Equiv.mulRight₀ c hc) ψ

theorem real_character_nonzero_sum (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hsum : (∑ x, ψ x) = 0) (c : F) :
    (∑ x : {x : F // x ≠ 0}, ψ (x.val * c)) =
      (if c = 0 then (Fintype.card F : ℝ) else 0) - 1 := by
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun x => ψ (x * c)) (0 : F)
  rw [real_character_scaled_sum ψ hzero hsum, zero_mul, hzero] at h
  linarith

def inversionSignMatrix (ψ : F → ℝ) (y i : {x : F // x ≠ 0}) : ℝ :=
  ψ (y.val⁻¹ * i.val⁻¹)

theorem inversion_sign_gram (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hsum : (∑ x, ψ x) = 0) (hchar : ∀ x : F, x + x = 0)
    (i j : {x : F // x ≠ 0}) :
    gram (inversionSignMatrix ψ) i j =
      (if i = j then (Fintype.card F : ℝ) else 0) - 1 := by
  have hz : i.val⁻¹ + j.val⁻¹ = 0 ↔ i = j := by
    constructor
    · intro h
      apply Subtype.ext
      apply inv_injective
      calc
        i.val⁻¹ = i.val⁻¹ + (j.val⁻¹ + j.val⁻¹) := by rw [hchar, add_zero]
        _ = j.val⁻¹ := by rw [← add_assoc, h, zero_add]
    · rintro rfl; exact hchar _
  unfold gram inversionSignMatrix
  simp_rw [← hadd, ← mul_add]
  have he := Equiv.sum_comp (nonzeroInvPermutation (F := F))
    (fun y : {x : F // x ≠ 0} => ψ (y.val * (i.val⁻¹ + j.val⁻¹)))
  change (∑ y : {x : F // x ≠ 0}, ψ (y.val⁻¹ * (i.val⁻¹ + j.val⁻¹))) = _ at he
  rw [he, real_character_nonzero_sum ψ hzero hsum]
  simp only [hz]

end AESMixing
