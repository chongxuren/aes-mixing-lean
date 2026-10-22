import AES8.Estimates.Byte.ByteAutocorrelation
import AESConcrete.FourierLineOverlap

/-!
# Actual mixed-byte coefficients as probability mixtures of characters

The normalized coefficient G(x,v)=16(D F)(x,v) is one at x=0 and
has magnitude at most 1/8 at nonzero x,v. Its Fourier expansion has
nonnegative weights of total mass one, supported on nonzero character
labels when v is nonzero. All four existing AES byte orientations are
covered, using exact conjugation rather than a commutation assumption.

This is a byte resource for the later word/MDS argument. It does not
assert its nonexceptional word-entry or exceptional-block instantiations.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ByteMixedCharacterMixture
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteGramFourier
open AESConcrete.FourierLineOverlap (fourierMate channel_fourierMate)
open AES8.ByteAutocorrelation

/-- Conjugation followed by F cancels its right F. Transposing the remaining
left F expression uses symmetry of F, with both physical labels retained. -/
theorem conjugate_right_eq_transpose_right (D : Byte → Byte → ℝ) (x v : Byte) :
    kernelCompose (byteConjugate D) byteFourierMatrix x v =
      kernelCompose (fun y z => D z y) byteFourierMatrix v x := by
  have he : kernelCompose (byteConjugate D) byteFourierMatrix =
      kernelCompose byteFourierMatrix D := by
    apply kernel_action_ext
    intro f
    simp only [byteConjugate, kernelCompose_action, byteFourier_twice]
  rw [he]
  unfold kernelCompose
  apply Finset.sum_congr rfl
  intro z _
  rw [byteFourier_symmetric x z]
  exact mul_comm _ _

/-- Autocorrelation transports to all four byte orientations. -/
theorem orientation_mixed_abs_le (o : Orientation) (x v : Byte)
    (hx : x ≠ 0) (hv : v ≠ 0) :
    |kernelCompose (channel o) byteFourierMatrix x v| ≤ (1 / 128 : ℝ) := by
  cases o
  · exact aes_mixed_abs_le x v hx hv
  · exact aes_transpose_mixed_abs_le x v hx hv
  · change |kernelCompose (channel (fourierMate .ordinary)) byteFourierMatrix x v| ≤ _
    rw [channel_fourierMate, conjugate_right_eq_transpose_right]
    exact aes_transpose_mixed_abs_le v x hv hx
  · change |kernelCompose (channel (fourierMate .transposed)) byteFourierMatrix x v| ≤ _
    rw [channel_fourierMate, conjugate_right_eq_transpose_right]
    exact aes_mixed_abs_le v x hv hx

def G (o : Orientation) (v x : Byte) : ℝ :=
  16 * kernelCompose (channel o) byteFourierMatrix x v

theorem G_zero (o : Orientation) (v : Byte) : G o v 0 = 1 := by
  unfold G kernelCompose
  simp only [(channel_resources o).zero_row, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [byteFourierMatrix, zero_mul, byteCharacter_zero]
  norm_num

theorem G_zero_mask (o : Orientation) (x : Byte) : G o 0 x = 1 := by
  unfold G kernelCompose
  simp only [byteFourierMatrix, mul_zero, byteCharacter_zero]
  rw [← Finset.sum_mul, (channel_resources o).row_sum]
  norm_num

theorem G_abs_le_eighth (o : Orientation) (v x : Byte) (hv : v ≠ 0) (hx : x ≠ 0) :
    |G o v x| ≤ (1 / 8 : ℝ) := by
  unfold G
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
  exact (mul_le_mul_of_nonneg_left (orientation_mixed_abs_le o x v hx hv)
    (by norm_num)).trans (by norm_num)

/-- Exact Fourier inversion uses the nonnegative conjugate channel as weights. -/
theorem G_character_mixture (o : Orientation) (v x : Byte) :
    G o v x = ∑ t : Byte, channel (fourierMate o) t v * byteCharacter (x * t) := by
  have he := congrFun (byteFourier_twice
    (fun z => kernelCompose (channel o) byteFourierMatrix z v)) x
  change action byteFourierMatrix (fun t => byteConjugate (channel o) t v) x =
    kernelCompose (channel o) byteFourierMatrix x v at he
  unfold G
  rw [← he, action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [← channel_fourierMate]
  unfold byteFourierMatrix
  ring

theorem mixture_nonnegative (o : Orientation) (t v : Byte) :
    0 ≤ channel (fourierMate o) t v := (channel_resources _).nonnegative t v

theorem mixture_mass (o : Orientation) (v : Byte) :
    (∑ t : Byte, channel (fourierMate o) t v) = 1 :=
  (channel_resources _).column_sum v

theorem mixture_zero (o : Orientation) (v : Byte) (hv : v ≠ 0) :
    channel (fourierMate o) 0 v = 0 := by
  rw [(channel_resources _).zero_row, if_neg hv]

end AES8.ByteMixedCharacterMixture
