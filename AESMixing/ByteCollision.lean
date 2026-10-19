import AESMixing.AESByteNorm
import AESMixing.ByteProfile

/-! Exact collision and largest-entry bounds for actual AES DDT rows/columns. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem inversion_row_one_profile (b : BinaryWord 8) :
    differenceChannel invPermutation b 1 = (AES.inversionProfile b.bits : ℝ) / 256 := by
  rw [inversion_row_one_count, AES.inversion_profile_correct]

theorem inversion_row_one_collision :
    (∑ b : BinaryWord 8, differenceChannel invPermutation b 1 ^ 2) = 65 / 8192 := by
  have he := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun b : BinaryWord 8 => (AES.inversionProfile b.bits : ℝ)^2)
  have hp : (∑ b : BinaryWord 8, (AES.inversionProfile b.bits : ℝ)^2) = 520 := by
    rw [← he]
    exact_mod_cast AES.inversion_profile_square_sum
  simp_rw [inversion_row_one_profile, div_pow]
  rw [← Finset.sum_div, hp]
  norm_num

theorem inversion_collision (a : BinaryWord 8) (ha : a ≠ 0) :
    (∑ b : BinaryWord 8, differenceChannel invPermutation b a ^ 2) = 65 / 8192 := by
  simp_rw [inversion_channel_scale a _ ha]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
    (fun b => differenceChannel invPermutation b 1 ^ 2)
  change (∑ b, differenceChannel invPermutation (a * b) 1 ^ 2) = _ at he
  rw [he, inversion_row_one_collision]

theorem inversion_atom_bound (a b : BinaryWord 8) (ha : a ≠ 0) :
    differenceChannel invPermutation b a ≤ 1 / 64 := by
  rw [inversion_channel_scale a b ha, inversion_row_one_profile]
  have h : (AES.inversionProfile (a * b).bits : ℝ) ≤ 4 := by
    exact_mod_cast AES.inversion_profile_bound (a * b).bits
  linarith

theorem inversion_channel_symmetric (a b : BinaryWord 8) :
    differenceChannel invPermutation b a = differenceChannel invPermutation a b :=
  differenceChannel_transpose invPermutation b a

theorem aes_byte_collision_column (a : BinaryWord 8) (ha : a ≠ 0) :
    (∑ b, aesByteChannel b a ^ 2) = 65 / 8192 := by
  simp_rw [aesByteChannel_affine]
  have he := Equiv.sum_comp AES.affineLinearEquiv.symm.toEquiv
    (fun b => differenceChannel invPermutation b a ^ 2)
  change (∑ b, differenceChannel invPermutation (AES.affineLinearEquiv.symm b) a ^ 2) = _ at he
  rw [he, inversion_collision a ha]

theorem aes_byte_collision_row (b : BinaryWord 8) (hb : b ≠ 0) :
    (∑ a, aesByteChannel b a ^ 2) = 65 / 8192 := by
  have hne : AES.affineLinearEquiv.symm b ≠ 0 := by
    intro h
    apply hb
    have he := congrArg AES.affineLinearEquiv h
    simpa only [AES.affineLinearEquiv.apply_symm_apply, map_zero] using he
  simp_rw [aesByteChannel_affine, inversion_channel_symmetric]
  exact inversion_collision _ hne

theorem aes_byte_atom_bound (a b : BinaryWord 8) (ha : a ≠ 0) :
    aesByteChannel b a ≤ 1 / 64 := by
  rw [aesByteChannel_affine]
  exact inversion_atom_bound a _ ha

end AESMixing
