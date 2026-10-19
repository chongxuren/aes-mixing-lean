import AESMixing.ByteField
import AESMixing.ByteCertificate
import AESMixing.InversionDDT
import AESMixing.Walsh

/-! Specialize the real character argument to actual AES polynomial bytes.
The two-bit character is defined directly; the differential identity is
established by the separate kernel-checked one-row certificate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def byteCharacter (x : BinaryWord 8) : ℝ := if AES.traceBit x.bits then -1 else 1

theorem byteCharacter_zero : byteCharacter 0 = 1 := by
  have h : AES.traceBit (0#8) = false := by decide
  change (if AES.traceBit (0#8) then (-1 : ℝ) else 1) = 1
  rw [h]
  rfl

theorem byteCharacter_add (x y : BinaryWord 8) :
    byteCharacter (x + y) = byteCharacter x * byteCharacter y := by
  unfold byteCharacter AES.traceBit
  rw [BinaryWord.add_bits]
  simp only [BitVec.getLsbD_xor]
  cases hx5 : x.bits.getLsbD 5 <;> cases hx7 : x.bits.getLsbD 7 <;>
    cases hy5 : y.bits.getLsbD 5 <;> cases hy7 : y.bits.getLsbD 7 <;> norm_num

theorem byteCharacter_witness : byteCharacter (⟨32⟩ : BinaryWord 8) = -1 := by
  have h : AES.traceBit (32#8) = true := by decide
  change (if AES.traceBit (32#8) then (-1 : ℝ) else 1) = -1
  rw [h]
  rfl

theorem byteCharacter_sum : (∑ x, byteCharacter x) = 0 :=
  real_character_sum_zero byteCharacter byteCharacter_add ⟨32⟩ byteCharacter_witness

theorem byte_inversion_sign_gram (i j : {x : BinaryWord 8 // x ≠ 0}) :
    gram (inversionSignMatrix byteCharacter) i j =
      (if i = j then 256 else 0) - 1 := by
  have h := inversion_sign_gram byteCharacter byteCharacter_zero byteCharacter_add
    byteCharacter_sum BinaryWord.add_self i j
  norm_num only [BinaryWord.card] at h
  exact h

theorem inversion_row_one_count (b : BinaryWord 8) :
    differenceChannel invPermutation b 1 = (AES.inversionRowOneCount b.bits : ℝ) / 256 := by
  have he := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun x => if difference invPermutation 1 x = b then (1 : ℝ) else 0)
  have hp (x : Fin 256) :
      (difference invPermutation 1 ((BinaryWord.equivFin 8).symm x) = b) ↔
        AES.invLookup (BitVec.ofFin x ^^^ 1) ^^^ AES.invLookup (BitVec.ofFin x) = b.bits := by
    rw [AES.invLookup_correct, AES.invLookup_correct]
    constructor
    · intro h; exact congrArg (fun w : BinaryWord 8 => w.bits) h
    · intro h; exact BinaryWord.ext h
  simp_rw [hp] at he
  unfold differenceChannel
  rw [← he, BinaryWord.card]
  norm_num only [show 2^8 = 256 by decide]
  congr 1
  simp only [AES.inversionRowOneCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rfl

theorem inversion_row_one_formula (b : BinaryWord 8) (hb : b ≠ 0) :
    differenceChannel invPermutation b 1 =
      (1 + byteCharacter b⁻¹ + 2 * (if b = 1 then (1 : ℝ) else 0)) / 256 := by
  have hfin0 : b.bits.toFin ≠ 0 := by
    intro h
    apply hb
    apply BinaryWord.ext
    exact congrArg BitVec.ofFin h
  have hfin1 : b.bits.toFin = 1 ↔ b = 1 := by
    constructor
    · intro h; apply BinaryWord.ext; exact congrArg BitVec.ofFin h
    · rintro rfl; rfl
  have h := congrArg (fun n : ℕ => (n : ℝ))
    (AES.inversion_row_one_certificate b.bits.toFin hfin0)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero] at h
  rw [inversion_row_one_count, h]
  simp only [byteCharacter, BinaryWord.inv_bits, ← AES.invLookup_correct, hfin1]
  split_ifs <;> norm_num

theorem byte_inversion_formula (a b : {x : BinaryWord 8 // x ≠ 0}) :
    differenceChannel invPermutation b.val a.val =
      (1 + inversionSignMatrix byteCharacter b a +
        2 * (if nonzeroInvPermutation b = a then (1 : ℝ) else 0)) / 256 := by
  rw [inversion_channel_scale _ _ a.property,
    inversion_row_one_formula _ (mul_ne_zero a.property b.property)]
  have he : a.val * b.val = 1 ↔ nonzeroInvPermutation b = a := by
    constructor
    · intro h
      apply Subtype.ext
      change b.val⁻¹ = a.val
      calc
        b.val⁻¹ = (a.val * b.val) * b.val⁻¹ := by rw [h, one_mul]
        _ = a.val := by rw [mul_assoc, mul_inv_cancel₀ b.property, mul_one]
    · intro h
      have hv := congrArg Subtype.val h
      change b.val⁻¹ = a.val at hv
      rw [← hv, inv_mul_cancel₀ b.property]
  simp only [inversionSignMatrix, mul_inv_rev, he]

/-- The actual AES polynomial inversion DDT contracts the zero-sum subspace
of nonzero bytes by at most 9/128. There are no analytic premises. -/
theorem concrete_inversion_residual (x : {x : BinaryWord 8 // x ≠ 0} → ℝ)
    (hx : ∑ i, x i = 0) :
    (∑ b : {x : BinaryWord 8 // x ≠ 0},
      (∑ a : {x : BinaryWord 8 // x ≠ 0},
        differenceChannel invPermutation b.val a.val * x a)^2) ≤
          (9 / 128 : ℝ)^2 * ∑ i, x i^2 :=
  byte_residual_from_sign_gram _ _ nonzeroInvPermutation byte_inversion_sign_gram
    (fun b a => byte_inversion_formula a b) x hx

end AESMixing
