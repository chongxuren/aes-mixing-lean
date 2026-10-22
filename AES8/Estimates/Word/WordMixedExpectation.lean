import AES8.Estimates.Byte.ByteMixedCharacterMixture
import AESConcrete.WordFourierCore
import AESConcrete.ReverseDegreeThree
import AESConcrete.WordColumnGram

/-!
# Exact one-sided full-word Fourier expectation

The middle variable is the original independent row source after the left
substitution. Diffusion is retained literally inside the four G factors.
All four input mask factors are included; a zero mask factor is exactly one.
No output-coordinate independence or nonexceptional entry cap is asserted.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixedExpectation
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierCore (wordFourier wordFourier_tensor)
open AESConcrete.WordColumnGram (Byte Word inputColumn)
open AESConcrete.ReverseDegreeThree (transposeOrientation channel_transpose)
open AES8.ByteMixedCharacterMixture

/-- The source is an actual original product law, expressed by its transpose
orientation so existing input-column mass and zero-event resources apply. -/
def rowSource (o : Orientation) (b y : Word) : ℝ := inputColumn (transposeOrientation o) b y

theorem rowSource_eq (o : Orientation) (b y : Word) :
    rowSource o b y = substitutionKernel (channel o) b y := by
  unfold rowSource inputColumn substitutionKernel coordinateKernel
  rw [channel_transpose]

theorem rowSource_nonnegative (o : Orientation) (b y : Word) : 0 ≤ rowSource o b y :=
  AESConcrete.WordColumnGram.inputColumn_nonneg _ b y

theorem rowSource_mass (o : Orientation) (b : Word) : (∑ y, rowSource o b y) = 1 :=
  AESConcrete.WordColumnGram.inputColumn_mass _ b

/-- Tensor Fourier multiplication is exact before diffusion and before any
absolute values or source estimates are introduced. -/
theorem substitution_right_fourier (o : Orientation) :
    kernelCompose (substitutionKernel (channel o)) wordFourier =
      coordinateKernel (fun _ : Fin 4 => kernelCompose (channel o) byteFourierMatrix) := by
  rw [wordFourier_tensor]
  exact coordinateKernel_compose _ _

theorem full_mixed_expansion (left right : Orientation) (inverse : Bool) (a b : Word) :
    kernelCompose (wordKernel left right inverse) wordFourier b a =
      ∑ y : Word, rowSource left b y *
        ∏ i : Fin 4, kernelCompose (channel right) byteFourierMatrix
          ((byteDiffusionOrientation inverse).symm y i) (a i) := by
  change (∑ x : Word,
    (∑ y : Word, substitutionKernel (channel left) b y *
      substitutionKernel (channel right) ((byteDiffusionOrientation inverse).symm y) x) *
        wordFourier x a) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [rowSource_eq]
  calc
    _ = substitutionKernel (channel left) b y *
        kernelCompose (substitutionKernel (channel right)) wordFourier
          ((byteDiffusionOrientation inverse).symm y) a := by
      unfold kernelCompose
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [substitution_right_fourier]; rfl

/-- This is the manuscript's full-word expectation with all physical labels
and the exact q^(1/2)=65536 normalization retained. -/
theorem full_mixed_expectation (left right : Orientation) (inverse : Bool) (a b : Word) :
    (65536 : ℝ) * kernelCompose (wordKernel left right inverse) wordFourier b a =
      ∑ y : Word, rowSource left b y *
        ∏ i : Fin 4, G right (a i) ((byteDiffusionOrientation inverse).symm y i) := by
  rw [full_mixed_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [G, Fin.prod_univ_four]
  ring

theorem G_abs_le_one (o : Orientation) (v x : Byte) : |G o v x| ≤ (1 : ℝ) := by
  by_cases hv : v = 0
  · subst v
    rw [G_zero_mask, abs_one]
  by_cases hx : x = 0
  · subst x
    rw [G_zero, abs_one]
  · exact (G_abs_le_eighth o v x hv hx).trans (by norm_num)

end AES8.WordMixedExpectation
