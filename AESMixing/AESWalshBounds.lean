import AESMixing.ByteFourierDual
import AESMixing.ByteWalshMoments

/-! Actual AES Walsh moments, in both orientations, and the resulting
squared-Walsh probability bounds. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem aes_walsh_square (u v : BinaryWord 8) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 =
      fieldWalsh byteCharacter (fun x => x⁻¹) u (byteDualEquiv AES.affineLinearEquiv v) ^ 2 := by
  rw [aes_walsh_affine, mul_pow, byteCharacter_sq, one_mul]

theorem aes_walsh_fourth (u v : BinaryWord 8) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 4 =
      fieldWalsh byteCharacter (fun x => x⁻¹) u (byteDualEquiv AES.affineLinearEquiv v) ^ 4 := by
  calc
    _ = (fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2)^2 := by ring
    _ = _ := by rw [aes_walsh_square]; ring

theorem aes_walsh_bound (u v : BinaryWord 8) (hu : u ≠ 0) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 ≤ 1024 := by
  rw [aes_walsh_square]
  exact byte_inversion_walsh_bound _ _ hu

theorem aes_walsh_second_column (u : BinaryWord 8) (hu : u ≠ 0) :
    (∑ v, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2) = 65536 := by
  simp_rw [aes_walsh_square]
  rw [Equiv.sum_comp (byteDualEquiv AES.affineLinearEquiv)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 2)]
  exact byte_inversion_walsh_second u hu

theorem aes_walsh_fourth_column (u : BinaryWord 8) (hu : u ≠ 0) :
    (∑ v, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 4) = 65 * 2^19 := by
  simp_rw [aes_walsh_fourth]
  rw [Equiv.sum_comp (byteDualEquiv AES.affineLinearEquiv)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 4)]
  exact byte_inversion_walsh_fourth u hu

theorem aes_walsh_second_row (v : BinaryWord 8) (hv : v ≠ 0) :
    (∑ u, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2) = 65536 := by
  calc
    _ = ∑ u, fieldWalsh byteCharacter (fun x => x⁻¹)
        (byteDualEquiv AES.affineLinearEquiv v) u ^ 2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [aes_walsh_square, inversion_walsh_symmetric byteCharacter u
        (byteDualEquiv AES.affineLinearEquiv v)]
    _ = _ := byte_inversion_walsh_second _ (byteDualEquiv_ne_zero _ v hv)

theorem aes_walsh_fourth_row (v : BinaryWord 8) (hv : v ≠ 0) :
    (∑ u, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 4) = 65 * 2^19 := by
  calc
    _ = ∑ u, fieldWalsh byteCharacter (fun x => x⁻¹)
        (byteDualEquiv AES.affineLinearEquiv v) u ^ 4 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [aes_walsh_fourth, inversion_walsh_symmetric byteCharacter u
        (byteDualEquiv AES.affineLinearEquiv v)]
    _ = _ := byte_inversion_walsh_fourth _ (byteDualEquiv_ne_zero _ v hv)

def aesSquaredWalshChannel (v u : BinaryWord 8) : ℝ :=
  fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 / 65536

theorem aes_squared_walsh_nonnegative (v u : BinaryWord 8) :
    0 ≤ aesSquaredWalshChannel v u := by unfold aesSquaredWalshChannel; positivity

theorem aes_squared_walsh_atom (u v : BinaryWord 8) (hu : u ≠ 0) :
    aesSquaredWalshChannel v u ≤ 1 / 64 := by
  have h := aes_walsh_bound u v hu
  unfold aesSquaredWalshChannel
  linarith

theorem aes_squared_walsh_collision_column (u : BinaryWord 8) (hu : u ≠ 0) :
    (∑ v, aesSquaredWalshChannel v u ^ 2) = 65 / 8192 := by
  have hp (v : BinaryWord 8) : aesSquaredWalshChannel v u ^ 2 =
      fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 4 / 65536^2 := by
    unfold aesSquaredWalshChannel
    ring
  simp_rw [hp]
  rw [← Finset.sum_div, aes_walsh_fourth_column u hu]
  norm_num

theorem aes_squared_walsh_collision_row (v : BinaryWord 8) (hv : v ≠ 0) :
    (∑ u, aesSquaredWalshChannel v u ^ 2) = 65 / 8192 := by
  have hp (u : BinaryWord 8) : aesSquaredWalshChannel v u ^ 2 =
      fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 4 / 65536^2 := by
    unfold aesSquaredWalshChannel
    ring
  simp_rw [hp]
  rw [← Finset.sum_div, aes_walsh_fourth_row v hv]
  norm_num

end AESMixing
