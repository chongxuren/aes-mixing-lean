import AESMixing.ByteWalshCertificate
import AESMixing.ByteCharacter
import AESMixing.InversionWalsh

/-! Connect the checked integer row to all nonzero-mask inversion Walsh rows. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem byte_walsh_one_lookup (v : BinaryWord 8) :
    fieldWalsh byteCharacter (fun x => x⁻¹) 1 v = (AES.inversionWalshLookup v.bits : ℝ) := by
  rw [AES.inversionWalshLookup_correct]
  unfold fieldWalsh
  have he := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun x : BinaryWord 8 => byteCharacter (1 * x + v * x⁻¹))
  rw [← he]
  simp only [AES.inversionWalshOne, Int.cast_sum, Int.cast_ite, Int.cast_neg, Int.cast_one]
  apply Finset.sum_congr rfl
  intro x _
  rw [AES.invLookup_correct, one_mul]
  rfl

theorem byte_walsh_one_bound (v : BinaryWord 8) :
    fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 2 ≤ 1024 := by
  rw [byte_walsh_one_lookup]
  exact_mod_cast AES.inversion_walsh_bound_certificate v.bits.toFin

theorem byte_walsh_one_second :
    (∑ v : BinaryWord 8, fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 2) = 65536 := by
  simp_rw [byte_walsh_one_lookup]
  rw [← Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun v : BinaryWord 8 => (AES.inversionWalshLookup v.bits : ℝ)^2)]
  exact_mod_cast AES.inversion_walsh_second_certificate

theorem byte_walsh_one_fourth :
    (∑ v : BinaryWord 8, fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 4) = 65 * 2^19 := by
  simp_rw [byte_walsh_one_lookup]
  rw [← Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun v : BinaryWord 8 => (AES.inversionWalshLookup v.bits : ℝ)^4)]
  exact_mod_cast AES.inversion_walsh_fourth_certificate

theorem byte_inversion_walsh_bound (u v : BinaryWord 8) (hu : u ≠ 0) :
    fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 2 ≤ 1024 := by
  rw [inversion_walsh_scale byteCharacter u v hu]
  exact byte_walsh_one_bound _

theorem byte_inversion_walsh_second (u : BinaryWord 8) (hu : u ≠ 0) :
    (∑ v, fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 2) = 65536 := by
  simp_rw [inversion_walsh_scale byteCharacter u _ hu]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ u hu)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 2)
  change (∑ v, fieldWalsh byteCharacter (fun x => x⁻¹) 1 (u * v) ^ 2) = _ at he
  rw [he, byte_walsh_one_second]

theorem byte_inversion_walsh_fourth (u : BinaryWord 8) (hu : u ≠ 0) :
    (∑ v, fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 4) = 65 * 2^19 := by
  simp_rw [inversion_walsh_scale byteCharacter u _ hu]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ u hu)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 4)
  change (∑ v, fieldWalsh byteCharacter (fun x => x⁻¹) 1 (u * v) ^ 4) = _ at he
  rw [he, byte_walsh_one_fourth]

end AESMixing
