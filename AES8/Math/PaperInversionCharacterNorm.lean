import AES8.Math.PaperMultiplicativeCharacters
import AES8.Math.PaperInversionGauss
import AESMixing.ChannelProjection
import AESMixing.L2Sums

/-! The printed multiplicative-character route to the actual inversion
residual norm. Gauss-sum algebra is imported from its separate leaf.
The argument also applies when card F = 2: the nonconstant mode set is
empty and every mean-zero vector on Fˣ is zero. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionCharacterNorm
open AESMixing
set_option autoImplicit false
set_option maxHeartbeats 200000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

def bound (F : Type*) [Fintype F] : ℝ :=
  (Real.sqrt (Fintype.card F) + 2) / (Fintype.card F : ℝ)

theorem bound_nonneg : 0 ≤ bound F := by unfold bound; positivity

/-- The constant character is the uniform nonzero direction and has
multiplier one, as follows from the actual stochastic channel column. -/
theorem multiplier_one : PaperInversionGauss.multiplier (1 : MulChar F ℂ) = 1 := by
  rw [PaperInversionGauss.multiplier_eq_units]
  simp only [MulChar.one_apply_coe, mul_one]
  rw [PaperInversionGauss.sum_units_eq
    (fun c : F => (differenceChannel invPermutation c 1 : ℂ))
    (by simp [differenceChannel_zero_row, zero_ne_one])]
  exact_mod_cast differenceChannel_column (invPermutation (F := F)) (1 : F)

theorem units_energy (f : Fˣ → ℝ) (hf : ∑ a, f a = 0) :
    (∑ b : Fˣ, (∑ a : Fˣ,
      differenceChannel invPermutation (b : F) (a : F) * f a) ^ 2) ≤
      bound F ^ 2 * ∑ a, f a ^ 2 := by
  have hk (b a : Fˣ) :
      differenceChannel invPermutation ((b * a : Fˣ) : F) 1 =
        differenceChannel invPermutation (b : F) (a : F) := by
    rw [inversion_channel_scale (a : F) (b : F) (Units.ne_zero a)]
    simp only [Units.val_mul, mul_comm]
  have hμ (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
      ‖∑ u : Fˣ, (differenceChannel invPermutation (u : F) 1 : ℂ) * χ (u : F)‖ ≤
        bound F := by
    rw [← PaperInversionGauss.multiplier_eq_units]
    exact PaperInversionGauss.multiplier_norm_le hχ
  simpa only [hk] using PaperMultiplicativeCharacters.real_energy_le
    (fun c : Fˣ => differenceChannel invPermutation (c : F) 1)
    (bound F) bound_nonneg hμ f hf

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem sum_units_real (f : F → ℝ) (hf : f 0 = 0) :
    (∑ u : Fˣ, f (u : F)) = ∑ x : F, f x := by
  have he := Equiv.sum_comp (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
    (fun x : {x : F // x ≠ 0} => f x.val)
  change (∑ u : Fˣ, f (u : F)) = ∑ x : {x : F // x ≠ 0}, f x.val at he
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]
  exact he

theorem full_energy (f : F → ℝ) (hf0 : f 0 = 0) (hf : ∑ a, f a = 0) :
    (∑ b, action (differenceChannel invPermutation) f b ^ 2) ≤
      bound F ^ 2 * ∑ a, f a ^ 2 := by
  have hu : (∑ u : Fˣ, f (u : F)) = 0 := by rw [sum_units_real f hf0, hf]
  have ha (b : F) : action (differenceChannel invPermutation) f b =
      ∑ a : Fˣ, differenceChannel invPermutation b (a : F) * f (a : F) := by
    symm
    exact sum_units_real (fun a : F => differenceChannel invPermutation b a * f a)
      (by rw [hf0, mul_zero])
  have hz : action (differenceChannel invPermutation) f 0 = 0 := by
    simp only [action, differenceChannel_zero_row, ite_mul, one_mul, zero_mul]
    simpa using hf0
  have hout :
      (∑ b : Fˣ, action (differenceChannel invPermutation) f (b : F) ^ 2) =
        ∑ b : F, action (differenceChannel invPermutation) f b ^ 2 :=
    sum_units_real (fun b => action (differenceChannel invPermutation) f b ^ 2)
      (by rw [hz]; norm_num)
  have hin : (∑ a : Fˣ, f (a : F) ^ 2) = ∑ a : F, f a ^ 2 :=
    sum_units_real (fun a => f a ^ 2) (by rw [hf0]; norm_num)
  have h := units_energy (fun a : Fˣ => f (a : F)) hu
  rw [← hout, ← hin]
  simpa only [ha] using h

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem pointed : PointedBistochastic (differenceChannel (invPermutation (F := F))) 0 :=
  ⟨differenceChannel_nonneg _, differenceChannel_zero_row _,
    differenceChannel_zero_column _, differenceChannel_column _, differenceChannel_row _⟩

/-- Literal matrix norm statement for channel minus the zero/uniform projection. -/
theorem residual_l2 (f : F → ℝ) :
    l2 (action (residualMatrix (differenceChannel invPermutation) 0) f) ≤
      bound F * l2 f := by
  apply l2_le_of_energy _ _ _ (bound_nonneg (F := F))
  exact residualMatrix_energy pointed Fintype.one_lt_card (bound F) full_energy f

end AES8.PaperInversionCharacterNorm
