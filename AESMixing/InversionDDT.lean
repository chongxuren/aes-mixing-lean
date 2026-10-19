import AESMixing.CharacterGram
import AESMixing.Difference

/-! Inversion differences at arbitrary nonzero input differences reduce to
the single input difference one. The finite AES row certificate is separate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem inversion_difference_scale (a t : F) :
    difference invPermutation a (a * t) =
      a⁻¹ * difference invPermutation 1 t := by
  change (a * t + a)⁻¹ - (a * t)⁻¹ = a⁻¹ * ((t + 1)⁻¹ - t⁻¹)
  rw [show a * t + a = a * (t + 1) by ring]
  simp only [mul_inv_rev, mul_sub]
  ring

omit [Fintype F] [DecidableEq F] in
theorem inversion_difference_eq (a b t : F) (ha : a ≠ 0) :
    difference invPermutation a (a * t) = b ↔
      difference invPermutation 1 t = a * b := by
  rw [inversion_difference_scale]
  constructor
  · intro h
    have he := congrArg (fun x => a * x) h
    simpa only [← mul_assoc, mul_inv_cancel₀ ha, one_mul] using he
  · intro h
    rw [h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem inversion_channel_scale (a b : F) (ha : a ≠ 0) :
    differenceChannel invPermutation b a = differenceChannel invPermutation (a * b) 1 := by
  unfold differenceChannel
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
    (fun x => if difference invPermutation a x = b then (1 : ℝ) else 0)
  change (∑ t, if difference invPermutation a (a * t) = b then (1 : ℝ) else 0) = _ at he
  rw [← he]
  simp_rw [inversion_difference_eq a b _ ha]

end AESMixing
