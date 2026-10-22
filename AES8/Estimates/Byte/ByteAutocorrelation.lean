import AESMixing.ByteWalshMoments
import AESConcrete.ByteGramFourier
import AES8.Estimates.Byte.ByteAutocorrelationCertificate
import AES8.Estimates.Byte.PaperCitedByteBounds

/-!
# Byte autocorrelation from the existing checked inversion Walsh row

No new table is generated. A signed interval for the existing Walsh lookup
is imported from a separate ordinary-kernel range certificate. The exact DDT
row formula then gives correlation = Walsh - 2 + 2 character. Inversion
scaling reduces every nonzero input difference to one. The affine AES output
and its transpose are transported with their literal byte labels/dual masks.

The existing proof supplies `concrete_cited_inputs`. The normalization and
affine transport endpoints are factored through the exact autocorrelation
input in PaperCitedByteBounds; their public statements remain unchanged.

This is a local channel resource; it does not assert a mixing theorem.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ByteAutocorrelation
open AESMixing
open AESConcrete.ByteGramCore (inversionChannel)
open AESConcrete.ByteGramFourier (dual_spec)
abbrev Byte := BinaryWord 8
abbrev NonzeroByte := {x : Byte // x ≠ 0}

/-- The isolated certificate only checks the stored 256-entry row, whose
sum identity is already kernel-certified in ByteWalshCertificate. -/
theorem signed_lookup_fin (v : Fin 256) :
    (-28 : ℤ) ≤ AES.inversionWalshLookup (BitVec.ofFin v) ∧
      AES.inversionWalshLookup (BitVec.ofFin v) ≤ 32 := by
  exact ByteAutocorrelationCertificate.signed_lookup_all v

theorem walsh_one_signed (v : Byte) :
    (-28 : ℝ) ≤ fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ∧
      fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ≤ 32 := by
  rw [byte_walsh_one_lookup]
  -- Cast the abstract integer first, so norm_cast never inspects the lookup.
  have cast_bounds (z : ℤ) (hz : (-28 : ℤ) ≤ z ∧ z ≤ 32) :
      (-28 : ℝ) ≤ (z : ℝ) ∧ (z : ℝ) ≤ 32 := by
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2
  have hz : (-28 : ℤ) ≤ AES.inversionWalshLookup v.bits ∧
      AES.inversionWalshLookup v.bits ≤ 32 := signed_lookup_fin v.bits.toFin
  exact cast_bounds _ hz

/-- The unnormalized character coefficient of the actual inversion DDT column. -/
def correlation (a v : Byte) : ℝ :=
  256 * ∑ b : Byte, differenceChannel invPermutation b a * byteCharacter (b * v)

theorem character_cases (v : Byte) : byteCharacter v = 1 ∨ byteCharacter v = -1 := by
  unfold byteCharacter
  split_ifs <;> simp

/-- The zero-output difference contributes zero for input difference one. -/
theorem correlation_one_formula (v : Byte) (hv : v ≠ 0) :
    correlation 1 v = fieldWalsh byteCharacter (fun x => x⁻¹) 1 v - 2 +
      2 * byteCharacter v := by
  have hterm (b : NonzeroByte) :
      256 * (differenceChannel invPermutation b.val 1 * byteCharacter (b.val * v)) =
      byteCharacter (b.val * v) + byteCharacter (b.val⁻¹ + b.val * v) +
        2 * (if b.val = 1 then byteCharacter v else 0) := by
    rw [inversion_row_one_formula b.val b.property, byteCharacter_add]
    by_cases hb : b.val = 1
    · simp only [hb, if_true, one_mul]
      ring
    · simp only [if_neg hb]
      ring
  have hchar : (∑ b : NonzeroByte, byteCharacter (b.val * v)) = -1 := by
    rw [real_character_nonzero_sum byteCharacter byteCharacter_zero byteCharacter_sum,
      if_neg hv]
    norm_num
  have hwalsh : (∑ b : NonzeroByte, byteCharacter (b.val⁻¹ + b.val * v)) =
      fieldWalsh byteCharacter (fun x => x⁻¹) 1 v - 1 := by
    have he := Fintype.sum_eq_add_sum_subtype_ne
      (fun b : Byte => byteCharacter (b⁻¹ + b * v)) 0
    have hw : (∑ b : Byte, byteCharacter (b⁻¹ + b * v)) =
        fieldWalsh byteCharacter (fun x => x⁻¹) v 1 := by
      unfold fieldWalsh
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ring
    rw [hw, inversion_walsh_symmetric byteCharacter v 1] at he
    simp only [inv_zero, zero_mul, zero_add, byteCharacter_zero] at he
    linarith only [he]
  have hdelta : (∑ b : NonzeroByte, if b.val = 1 then byteCharacter v else 0) =
      byteCharacter v := by
    have he (b : NonzeroByte) : b.val = 1 ↔ b = ⟨1, one_ne_zero⟩ := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold correlation
  rw [Finset.mul_sum,
    Fintype.sum_eq_add_sum_subtype_ne
      (fun b : Byte => 256 * (differenceChannel invPermutation b 1 * byteCharacter (b * v))) 0]
  simp only [differenceChannel_zero_row, if_neg (one_ne_zero : (1 : Byte) ≠ 0),
    zero_mul, mul_zero, zero_add]
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hchar, hwalsh, hdelta]
  ring

/-- Rescaling the input difference rescales the output character mask inversely. -/
theorem correlation_scale (a v : Byte) (ha : a ≠ 0) :
    correlation a v = correlation 1 (a⁻¹ * v) := by
  -- Prove reindexing over an abstract field. In the concrete byte instance,
  -- congr/ring normalization may expose the field's finite implementation.
  have generic {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (ψ : F → ℝ) (a v : F) (ha : a ≠ 0) :
      (∑ b : F, differenceChannel invPermutation b a * ψ (b * v)) =
        ∑ b : F, differenceChannel invPermutation b 1 * ψ (b * (a⁻¹ * v)) := by
    have he := Equiv.sum_comp (Equiv.mulLeft₀ a⁻¹ (inv_ne_zero ha))
      (fun b : F => differenceChannel invPermutation b a * ψ (b * v))
    calc
      _ = ∑ b : F, differenceChannel invPermutation (a⁻¹ * b) a *
          ψ ((a⁻¹ * b) * v) := he.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        have hcancel : a * (a⁻¹ * b) = b := by
          rw [← _root_.mul_assoc, mul_inv_cancel₀ ha, one_mul]
        have hmask : (a⁻¹ * b) * v = b * (a⁻¹ * v) := by
          rw [_root_.mul_assoc, _root_.mul_left_comm]
        rw [inversion_channel_scale a (a⁻¹ * b) ha, hcancel, hmask]
  exact congrArg (fun z : ℝ => 256 * z) (generic byteCharacter a v ha)

/-- The asymmetric signed Walsh interval is essential when the character is -1. -/
theorem correlation_one_abs_le (v : Byte) (hv : v ≠ 0) : |correlation 1 v| ≤ 32 := by
  rw [correlation_one_formula v hv]
  have hw := walsh_one_signed v
  rcases character_cases v with hc | hc
  all_goals rw [hc]
  all_goals apply abs_le.mpr
  all_goals constructor <;> linarith

theorem correlation_abs_le (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |correlation a v| ≤ 32 := by
  rw [correlation_scale a v ha]
  exact correlation_one_abs_le _ (mul_ne_zero (inv_ne_zero ha) hv)

/-- The existing concrete proof discharges the exact cited-input interface.
The downstream affine/Fourier deductions below may instead be applied to
any proof of that same mathematical statement. No external axiom is used. -/
theorem concrete_autocorrelation_bound : PaperCitedByteBounds.InversionAutocorrelationBound :=
  correlation_abs_le

def concrete_cited_inputs : PaperCitedByteBounds.Inputs where
  walsh := PaperCitedByteBounds.concreteWalshBound
  autocorrelation := concrete_autocorrelation_bound

/-- Matrix normalization: 256 for the DDT and 16 for the byte Fourier map. -/
theorem inversion_mixed_eq_correlation (a v : Byte) :
    kernelCompose inversionChannel byteFourierMatrix a v = correlation a v / 4096 := by
  unfold kernelCompose inversionChannel byteFourierMatrix correlation
  have he (b : Byte) : differenceChannel invPermutation a b *
      (byteCharacter (b * v) / 16) =
      (differenceChannel invPermutation b a * byteCharacter (b * v)) / 16 := by
    rw [inversion_channel_symmetric a b]
    ring
  simp_rw [he]
  rw [← Finset.sum_div]
  ring

theorem inversion_mixed_abs_le_of_bound
    (h : PaperCitedByteBounds.InversionAutocorrelationBound)
    (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose inversionChannel byteFourierMatrix a v| ≤ 1 / 128 := by
  rw [inversion_mixed_eq_correlation, abs_div]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4096)]
  exact (div_le_div_of_nonneg_right (h a v ha hv) (by norm_num)).trans
    (by norm_num)

theorem inversion_mixed_abs_le (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose inversionChannel byteFourierMatrix a v| ≤ 1 / 128 :=
  inversion_mixed_abs_le_of_bound concrete_cited_inputs.autocorrelation a v ha hv

theorem aes_mixed_eq_inversion (a v : Byte) :
    kernelCompose aesByteChannel byteFourierMatrix a v =
      kernelCompose inversionChannel byteFourierMatrix (AES.affineLinearEquiv.symm a) v := by
  unfold kernelCompose inversionChannel
  simp_rw [aesByteChannel_affine]

theorem aes_mixed_abs_le_of_bound
    (h : PaperCitedByteBounds.InversionAutocorrelationBound)
    (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose aesByteChannel byteFourierMatrix a v| ≤ 1 / 128 := by
  rw [aes_mixed_eq_inversion]
  apply inversion_mixed_abs_le_of_bound h _ v ?_ hv
  intro hz
  exact ha (AES.affineLinearEquiv.symm.injective (hz.trans (map_zero _).symm))

theorem aes_mixed_abs_le (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose aesByteChannel byteFourierMatrix a v| ≤ 1 / 128 :=
  aes_mixed_abs_le_of_bound concrete_cited_inputs.autocorrelation a v ha hv

/-- The adjoint channel uses the dual affine output mask, preserving nonzero masks. -/
theorem aes_transpose_mixed_eq_inversion (a v : Byte) :
    kernelCompose (fun y x => aesByteChannel x y) byteFourierMatrix a v =
      kernelCompose inversionChannel byteFourierMatrix a (byteDualEquiv AES.affineLinearEquiv v) := by
  have he := AES.affineLinearEquiv.toEquiv.sum_comp
    (fun b : Byte => aesByteChannel b a * byteFourierMatrix b v)
  change (∑ b : Byte, aesByteChannel (AES.affineLinearEquiv b) a *
    byteFourierMatrix (AES.affineLinearEquiv b) v) = _ at he
  unfold kernelCompose
  rw [← he]
  apply Finset.sum_congr rfl
  intro b _
  rw [aesByteChannel_affine, AES.affineLinearEquiv.symm_apply_apply,
    inversion_channel_symmetric a b]
  change differenceChannel invPermutation a b * byteFourierMatrix (AES.affineLinearEquiv b) v =
    differenceChannel invPermutation a b * byteFourierMatrix b (byteDualEquiv AES.affineLinearEquiv v)
  congr 1
  unfold byteFourierMatrix
  rw [mul_comm (AES.affineLinearEquiv b) v, dual_spec,
    mul_comm (byteDualEquiv AES.affineLinearEquiv v) b]

theorem aes_transpose_mixed_abs_le_of_bound
    (h : PaperCitedByteBounds.InversionAutocorrelationBound)
    (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose (fun y x => aesByteChannel x y) byteFourierMatrix a v| ≤ 1 / 128 := by
  rw [aes_transpose_mixed_eq_inversion]
  exact inversion_mixed_abs_le_of_bound h a _ ha (byteDualEquiv_ne_zero AES.affineLinearEquiv v hv)

theorem aes_transpose_mixed_abs_le (a v : Byte) (ha : a ≠ 0) (hv : v ≠ 0) :
    |kernelCompose (fun y x => aesByteChannel x y) byteFourierMatrix a v| ≤ 1 / 128 :=
  aes_transpose_mixed_abs_le_of_bound concrete_cited_inputs.autocorrelation a v ha hv

end AES8.ByteAutocorrelation
