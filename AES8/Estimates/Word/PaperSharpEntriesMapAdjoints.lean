import AES8.Estimates.Word.PaperSharpEntriesByteMaps
import AES8.Estimates.Word.PaperSharpEntriesTransformChecker

/-!
# Adjoint interfaces for the actual mixed maps

Fourier profiles use B=A*, whose adjoint is A. Ordinary profiles use B=A^-1;
their certificate separately supplies a computable inverse of A*. Proving that
inverse identity is a finite model-binding obligation, never an assumed table.
-/

namespace AES8.PaperSharpEntriesMapAdjoints
open AESMixing
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesFWHT (sign)
open AES8.PaperSharpEntriesConvolution (sign_real)
open AES8.PaperSharpEntriesTransformChecker (mixedMap)

set_option autoImplicit false

theorem fourier_adjoint_sign (k u : Byte) :
    sign k (fourierMapHom u) = sign (AES.affineLinear k) u := by
  have he : (sign k (fourierMapHom u) : ℝ) =
      (sign (AES.affineLinear k) u : ℝ) := by
    rw [sign_real, sign_real, mul_comm k, ← fourierMapHom_character]
    rw [mul_comm]
    rfl
  exact_mod_cast he

theorem ordinary_adjoint_sign (C : Byte → Byte)
    (hC : ∀ k, fourierMapHom (C k) = k) (k u : Byte) :
    sign k (ordinaryMapHom u) = sign (C k) u := by
  have he : (sign k (ordinaryMapHom u) : ℝ) = (sign (C k) u : ℝ) := by
    rw [sign_real, sign_real]
    have hi : AES.affineLinearEquiv (ordinaryMapHom u) = u := by
      rw [← ordinaryMap_apply]
      exact AES.affineLinearEquiv.apply_symm_apply u
    calc
      _ = byteCharacter (fourierMapHom (C k) * ordinaryMapHom u) := by rw [hC k]
      _ = byteCharacter (C k * AES.affineLinearEquiv (ordinaryMapHom u)) :=
        (fourierMapHom_character (C k) (ordinaryMapHom u)).symm
      _ = _ := by rw [hi]
  exact_mod_cast he

theorem sign_mul_index (k a x : Byte) : sign k (a*x) = sign (a*k) x := by
  have he : (sign k (a*x) : ℝ) = (sign (a*k) x : ℝ) := by
    rw [sign_real, sign_real]
    congr 1
    ring
  exact_mod_cast he

def mixedAdjoint (C : Byte → Byte) (alpha beta : Byte) : Byte → Byte :=
  fun k => beta * C (alpha * k)

theorem mixed_adjoint_sign (B : Byte →+ Byte) (C : Byte → Byte)
    (hC : ∀ k u, sign k (B u) = sign (C k) u)
    (alpha beta k u : Byte) :
    sign k (mixedMap B alpha beta u) = sign (mixedAdjoint C alpha beta k) u := by
  change sign k (alpha * B (beta * u)) = sign (beta * C (alpha * k)) u
  rw [sign_mul_index, hC, sign_mul_index]

end AES8.PaperSharpEntriesMapAdjoints
