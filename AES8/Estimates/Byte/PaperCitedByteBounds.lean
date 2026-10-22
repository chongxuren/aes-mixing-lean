import AESMixing.ByteWalshMoments
import AESConcrete.ByteGramFourier

/-!
Exact cited-input boundary for the paper's eight-bit inversion estimates.

The two scalar statements below are deliberately specialized to the existing
byte field, absolute-trace character, inversion permutation, mask convention,
and counting normalization. They do not assert any all-dimension external
theorem. Concrete providers remain proved theorems: Walsh is supplied here
from the existing finite certificate, and autocorrelation is supplied by the
staged ByteAutocorrelation module after its existing proof. No axiom is added.

Affine mask transport, Fourier/squared-channel normalization, and zero-mask
identities are our deductions from this interface. Constructive proof only;
no attacks, local Lean/tests, remote work, or vendor edits are in scope.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperCitedByteBounds

open AESMixing
open AESConcrete.ByteGramFourier (squared_walsh_conjugate byteConjugate)

set_option autoImplicit false
set_option maxRecDepth 100000

abbrev Byte := BinaryWord 8

/-- The n=8 specialization of the unnormalized inversion Walsh estimate.
The second mask may be zero; the all-zero pair is excluded by `u ≠ 0`. -/
def InversionWalshSqBound : Prop :=
  ∀ (u v : Byte), u ≠ 0 →
    fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 2 ≤ 1024

/-- The exact n=8 inversion-DDT autocorrelation specialization. The DDT
channel is normalized by 256; this displayed scalar restores its count. -/
def InversionAutocorrelationBound : Prop :=
  ∀ (a v : Byte), a ≠ 0 → v ≠ 0 →
    |(256 : ℝ) * ∑ b : Byte,
      differenceChannel invPermutation b a * byteCharacter (b * v)| ≤ 32

/-- Independent cited inputs. Neither property is inferred from the other. -/
structure Inputs : Prop where
  walsh : InversionWalshSqBound
  autocorrelation : InversionAutocorrelationBound

/-- Existing concrete finite proof supplies the exact Walsh input. This is
a proved specialization/provider, not an external axiom declaration. -/
theorem concreteWalshBound : InversionWalshSqBound :=
  byte_inversion_walsh_bound

/-- The exceptional zero first mask is computed exactly, including (0,0). -/
theorem inversion_walsh_zero_first (v : Byte) :
    fieldWalsh byteCharacter (fun x => x⁻¹) 0 v = if v = 0 then 256 else 0 := by
  simpa [BinaryWord.card, invPermutation] using
    field_walsh_zero_first byteCharacter byteCharacter_zero byteCharacter_sum invPermutation v

theorem inversion_walsh_zero_second (u : Byte) :
    fieldWalsh byteCharacter (fun x => x⁻¹) u 0 = if u = 0 then 256 else 0 := by
  rw [inversion_walsh_symmetric byteCharacter u 0, inversion_walsh_zero_first]

theorem aes_walsh_zero_first (v : Byte) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm 0 v = if v = 0 then 256 else 0 := by
  simpa [BinaryWord.card] using
    field_walsh_zero_first byteCharacter byteCharacter_zero byteCharacter_sum BinaryWord.sboxPerm v

/-- The affine constant contributes a character of square one; the linear
part contributes the literal dual output mask. No scalar bound is used. -/
theorem aes_walsh_square_transport (u v : Byte) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 =
      fieldWalsh byteCharacter (fun x => x⁻¹) u
        (byteDualEquiv AES.affineLinearEquiv v) ^ 2 := by
  rw [aes_walsh_affine, mul_pow, byteCharacter_sq, one_mul]

theorem aes_walsh_sq_le_of_walsh (h : InversionWalshSqBound)
    (u v : Byte) (hu : u ≠ 0) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 ≤ 1024 := by
  rw [aes_walsh_square_transport]
  exact h u _ hu

/-- The transposed squared channel uses a nonzero output mask. Inversion
symmetry moves its dual mask to the first Walsh coordinate. -/
theorem aes_walsh_sq_le_of_output_mask (h : InversionWalshSqBound)
    (u v : Byte) (hv : v ≠ 0) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 ≤ 1024 := by
  rw [aes_walsh_square_transport, inversion_walsh_symmetric byteCharacter u]
  exact h _ u (byteDualEquiv_ne_zero AES.affineLinearEquiv v hv)

/-- The complete nontrivial-mask statement is explicit about the exceptional
all-zero Walsh coefficient, which equals 256 rather than satisfying this bound. -/
theorem aes_walsh_sq_le_of_nonzero_pair (h : InversionWalshSqBound)
    (u v : Byte) (hm : u ≠ 0 ∨ v ≠ 0) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2 ≤ 1024 := by
  rcases hm with hu | hv
  · exact aes_walsh_sq_le_of_walsh h u v hu
  · exact aes_walsh_sq_le_of_output_mask h u v hv

/-- The squared-channel denominator is exactly 256², with the affine mask
transport already applied. -/
theorem aes_squared_channel_formula (u v : Byte) :
    aesSquaredWalshChannel v u =
      fieldWalsh byteCharacter (fun x => x⁻¹) u
        (byteDualEquiv AES.affineLinearEquiv v) ^ 2 / (256 : ℝ)^2 := by
  unfold aesSquaredWalshChannel
  rw [aes_walsh_square_transport]
  norm_num

theorem aes_squared_walsh_atom_of_walsh (h : InversionWalshSqBound)
    (u v : Byte) (hu : u ≠ 0) : aesSquaredWalshChannel v u ≤ (1/64 : ℝ) := by
  have hw := aes_walsh_sq_le_of_walsh h u v hu
  unfold aesSquaredWalshChannel
  linarith

theorem aes_squared_walsh_transpose_atom_of_walsh (h : InversionWalshSqBound)
    (u v : Byte) (hu : u ≠ 0) :
    (fun y x => aesSquaredWalshChannel x y) v u ≤ (1/64 : ℝ) := by
  have hw := aes_walsh_sq_le_of_output_mask h v u hu
  change aesSquaredWalshChannel u v ≤ _
  unfold aesSquaredWalshChannel
  linarith

/-- The already proved exact Fourier-conjugacy identity supplies the channel
identification; the atom bound is deduced from the explicit Walsh input. -/
theorem aes_fourier_atom_of_walsh (h : InversionWalshSqBound)
    (u v : Byte) (hu : u ≠ 0) :
    byteConjugate aesByteChannel v u ≤ (1/64 : ℝ) := by
  rw [← squared_walsh_conjugate]
  exact aes_squared_walsh_atom_of_walsh h u v hu

theorem aes_fourier_transpose_atom_of_walsh (h : InversionWalshSqBound)
    (u v : Byte) (hu : u ≠ 0) :
    (fun y x => byteConjugate aesByteChannel x y) v u ≤ (1/64 : ℝ) := by
  rw [← squared_walsh_conjugate]
  exact aes_squared_walsh_transpose_atom_of_walsh h u v hu

end AES8.PaperCitedByteBounds
