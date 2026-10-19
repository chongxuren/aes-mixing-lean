import AESMixing.CharacterGram
import AESMixing.Markov

/-! Fourier coefficients of inversion reduce to one row by field rescaling. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def fieldWalsh (ψ : F → ℝ) (s : F → F) (u v : F) : ℝ :=
  ∑ x, ψ (u * x + v * s x)

omit [DecidableEq F] in
theorem inversion_walsh_scale (ψ : F → ℝ) (u v : F) (hu : u ≠ 0) :
    fieldWalsh ψ (fun x => x⁻¹) u v = fieldWalsh ψ (fun x => x⁻¹) 1 (u * v) := by
  unfold fieldWalsh
  have he := Equiv.sum_comp (Equiv.mulLeft₀ u⁻¹ (inv_ne_zero hu))
    (fun x => ψ (u * x + v * x⁻¹))
  change (∑ t, ψ (u * (u⁻¹ * t) + v * (u⁻¹ * t)⁻¹)) = _ at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  simp only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  ring

omit [DecidableEq F] in
theorem inversion_walsh_symmetric (ψ : F → ℝ) (u v : F) :
    fieldWalsh ψ (fun x => x⁻¹) u v = fieldWalsh ψ (fun x => x⁻¹) v u := by
  unfold fieldWalsh
  have he := Equiv.sum_comp (invPermutation (F := F))
    (fun x => ψ (u * x + v * x⁻¹))
  change (∑ x, ψ (u * x⁻¹ + v * x⁻¹⁻¹)) = _ at he
  rw [← he]
  simp only [inv_inv, add_comm]

theorem field_walsh_zero_first (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hsum : (∑ x, ψ x) = 0) (s : Equiv.Perm F) (v : F) :
    fieldWalsh ψ s 0 v = if v = 0 then (Fintype.card F : ℝ) else 0 := by
  unfold fieldWalsh
  simp only [zero_mul, zero_add]
  have he := Equiv.sum_comp s (fun x => ψ (v * x))
  rw [he]
  simp_rw [mul_comm v]
  exact real_character_scaled_sum ψ hzero hsum v

end AESMixing
