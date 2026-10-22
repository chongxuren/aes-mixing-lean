import AES8.Estimates.Word.PaperSharpEntriesFWHT

/-!
# Integer convolution certificate soundness

Draft only. The certificate uses scaled integer inequalities throughout: no
division, machine overflow claim, or approximate inverse transform is trusted.
Actual fixed inventory certificates remain a separate finite obligation.
-/

open scoped BigOperators

namespace AES8.PaperSharpEntriesConvolution
open AESMixing
open AES8.PaperSharpEntriesFinite (Byte)
open AES8.PaperSharpEntriesFWHT (Index Vector byteOf transform traceIndex sign)

set_option autoImplicit false

theorem sign_real (k x : Byte) : (sign k x : ℝ) = byteCharacter (k * x) := by
  simp only [sign, byteCharacter, BinaryWord.mul_bits, Int.cast_ite, Int.cast_neg,
    Int.cast_one]

theorem sign_add (k x y : Byte) : sign k (x+y) = sign k x * sign k y := by
  have he : (sign k (x+y) : ℝ) = (sign k x : ℝ) * (sign k y : ℝ) := by
    simp_rw [sign_real]
    rw [mul_add, byteCharacter_add]
  exact_mod_cast he

theorem sum_sign (x : Byte) :
    (∑ k : Byte, sign k x) = if x = 0 then (256 : ℤ) else 0 := by
  have he : (∑ k : Byte, (sign k x : ℝ)) = if x = 0 then (256 : ℝ) else 0 := by
    simp_rw [sign_real]
    simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using
      real_character_scaled_sum byteCharacter byteCharacter_zero byteCharacter_sum x
  exact_mod_cast he

def hat (f : Byte → ℤ) (k : Byte) : ℤ := ∑ x : Byte, sign k x * f x

theorem hat_fast (hcoeff : PaperSharpEntriesFWHT.CoefficientSpec)
    (f : Byte → ℤ) (k : Byte) :
    hat f k = transform (fun i : Index => f (byteOf i)) (traceIndex k) := by
  rw [PaperSharpEntriesFWHT.transform_trace_formula hcoeff]
  exact (Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun x : Byte => sign k x * f x)).symm

def correlation (f g : Byte → ℤ) (L : Byte →+ Byte) (gamma : Byte) : ℤ :=
  ∑ u : Byte, f u * g (L u + gamma)

/-- A semantic transform equality sufficient for a certificate. It is a proof
of an exact equality, never a claim that an external FWHT execution succeeded. -/
theorem correlation_transform (f g : Byte → ℤ) (L : Byte →+ Byte)
    (Lt : Byte → Byte) (hLt : ∀ k u, sign k (L u) = sign (Lt k) u)
    (gamma : Byte) :
    256 * correlation f g L gamma =
      ∑ k : Byte, sign k gamma * (hat f (Lt k) * hat g k) := by
  symm
  unfold correlation hat
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← hLt]
  rw [Finset.sum_comm]
  calc
    _ = ∑ u : Byte, ∑ v : Byte,
        f u * g v * ∑ k : Byte, sign k (gamma + L u + v) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [sign_add, sign_add]
      ring
    _ = _ := by
      simp_rw [sum_sign]
      have he (u v : Byte) : gamma + L u + v = 0 ↔ v = L u + gamma := by
        constructor
        · intro hh
          calc
            v = (gamma + L u) + ((gamma + L u) + v) := by
              rw [← add_assoc, BinaryWord.add_self, zero_add]
            _ = L u + gamma := by rw [hh, add_zero, add_comm]
        · rintro rfl
          simpa only [add_comm gamma (L u)] using BinaryWord.add_self (L u + gamma)
      simp_rw [he, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- Pointwise scaled caps on the transform output imply the direct correlation
cap. This is the checker soundness boundary used by generated certificates. -/
theorem correlation_le_of_transform_le (f g : Byte → ℤ) (L : Byte →+ Byte)
    (Lt : Byte → Byte) (hLt : ∀ k u, sign k (L u) = sign (Lt k) u)
    (cap : ℤ) (hc : ∀ gamma : Byte,
      (∑ k : Byte, sign k gamma * (hat f (Lt k) * hat g k)) ≤ 256 * cap)
    (gamma : Byte) : correlation f g L gamma ≤ cap := by
  have he := correlation_transform f g L Lt hLt gamma
  have hb := hc gamma
  rw [← he] at hb
  omega

end AES8.PaperSharpEntriesConvolution
