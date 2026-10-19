import AESMixing.ByteCharacter
import AESMixing.AffineByte
import AESMixing.AffineChannel
import AESMixing.Averaging

/-! The 9/128 residual contraction for the actual AES S-box difference channel.
No AES-specific spectral estimate is a hypothesis of these theorems. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem aes_sbox_as_affine_output : BinaryWord.sboxPerm =
    affineOutput invPermutation AES.affineLinearEquiv (⟨0x63⟩ : BinaryWord 8) := by
  apply Equiv.ext
  intro x
  exact AES.sbox_affine x

theorem aesByteChannel_affine (a b : BinaryWord 8) :
    aesByteChannel b a = differenceChannel invPermutation (AES.affineLinearEquiv.symm b) a := by
  unfold aesByteChannel
  rw [aes_sbox_as_affine_output, affineOutput_channel]

theorem aes_byte_residual_nonzero (x : {x : BinaryWord 8 // x ≠ 0} → ℝ)
    (hx : ∑ i, x i = 0) :
    (∑ b : {x : BinaryWord 8 // x ≠ 0},
      (∑ a : {x : BinaryWord 8 // x ≠ 0}, aesByteChannel b.val a.val * x a)^2) ≤
        (9 / 128 : ℝ)^2 * ∑ i, x i^2 := by
  simp_rw [aesByteChannel_affine]
  have he := Equiv.sum_comp (nonzeroAddEquiv AES.affineLinearEquiv).symm
    (fun b : {x : BinaryWord 8 // x ≠ 0} =>
      (∑ a : {x : BinaryWord 8 // x ≠ 0},
        differenceChannel invPermutation b.val a.val * x a)^2)
  change (∑ b : {x : BinaryWord 8 // x ≠ 0},
      (∑ a : {x : BinaryWord 8 // x ≠ 0},
        differenceChannel invPermutation (AES.affineLinearEquiv.symm b.val) a.val * x a)^2) = _ at he
  rw [he]
  exact concrete_inversion_residual x hx

theorem aes_byte_residual (x : BinaryWord 8 → ℝ)
    (hx0 : x 0 = 0) (hx : ∑ i, x i = 0) :
    (∑ b, (∑ a, aesByteChannel b a * x a)^2) ≤
      (9 / 128 : ℝ)^2 * ∑ i, x i^2 := by
  have hsum : (∑ i : {x : BinaryWord 8 // x ≠ 0}, x i.val) = 0 := by
    have h := Fintype.sum_eq_add_sum_subtype_ne x 0
    rw [hx0, hx, zero_add] at h
    exact h.symm
  have he (b : BinaryWord 8) : (∑ a, aesByteChannel b a * x a) =
      ∑ a : {x : BinaryWord 8 // x ≠ 0}, aesByteChannel b a.val * x a.val := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => aesByteChannel b a * x a) 0, hx0,
      mul_zero, zero_add]
  have hz : (∑ a, aesByteChannel 0 a * x a) = 0 := by
    simp only [aesByteChannel, differenceChannel_zero_row, ite_mul, one_mul, zero_mul]
    simpa using hx0
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun b => (∑ a, aesByteChannel b a * x a)^2) 0,
    hz, zero_pow (by decide), zero_add,
    Fintype.sum_eq_add_sum_subtype_ne (fun a => x a^2) 0,
    hx0, zero_pow (by decide), zero_add]
  simp_rw [he]
  exact aes_byte_residual_nonzero (fun i => x i.val) hsum

theorem aes_byte_projected_residual (f : BinaryWord 8 → ℝ) :
    (∑ b, action aesByteChannel (wordResidual 0 f) b ^ 2) ≤
      (9 / 128 : ℝ)^2 * ∑ i, wordResidual 0 f i ^ 2 := by
  apply aes_byte_residual
  · exact wordResidual_at_zero 0 f
  · exact wordResidual_sum 0 f (by norm_num [BinaryWord.card])

end AESMixing
