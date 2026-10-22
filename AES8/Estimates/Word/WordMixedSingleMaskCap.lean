import AES8.Estimates.Word.WordMixedPairCap
import AESConcrete.SingleByteCoordinates
import AESConcrete.WordFourierDiffusion

/-!
# Single-mask mixed-word entries with two active original source bytes

Fourier inversion of G is a probability mixture of nontrivial characters.
Every actual diffusion coefficient is nonzero, so each such character has
at least two nontrivial original byte biases. Independence belongs only to
that original row source. This gives raw q-scaled entry cap 1024 for the
single-mask/multiple-source branch; the exceptional single/single block is
still separate.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixedSingleMaskCap
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word singleByteWord)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierCore (wordFourier)
open AESConcrete.WordFourierDiffusion (byteCharacter_finset_sum)
open AES8.ByteMixedCharacterMixture
open AES8.WordMixedExpectation
open AES8.WordMixedPairCap (abs_prod_le_pair)

theorem G_eq_row_character (o : Orientation) (v x : Byte) :
    G o v x = ∑ t : Byte, channel o x t * byteCharacter (t * v) := by
  unfold G kernelCompose byteFourierMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- No coefficient certificate is needed: a single physical input byte
parametrizes each output coordinate bijectively by the existing MDS theorem. -/
theorem mixing_coefficient_ne_zero (inverse : Bool) (k i : Fin 4) :
    gramMixing inverse k i ≠ 0 := by
  have he : byteDiffusionOrientation inverse (singleByteWord i (1 : Byte)) k =
      gramMixing inverse k i := by
    rw [byteDiffusionOrientation_apply]
    change (∑ j : Fin 4, gramMixing inverse k j * singleByteWord i 1 j) = _
    simp only [singleByteWord, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← he]
  exact AESConcrete.SingleByteCoordinates.coordinatePerm_ne_zero inverse i k 1 one_ne_zero

/-- Exact factorization of an actual diffused-coordinate character under the
original product row law. No independence of diffused coordinates is used. -/
theorem row_character_product (o : Orientation) (inverse : Bool) (b : Word)
    (k : Fin 4) (t : Byte) :
    (∑ y : Word, rowSource o b y * byteCharacter (byteDiffusionOrientation inverse y k * t)) =
      ∏ i : Fin 4, G o (t * gramMixing inverse k i) (b i) := by
  have hchar (y : Word) : byteCharacter (byteDiffusionOrientation inverse y k * t) =
      ∏ i : Fin 4, byteCharacter (y i * (t * gramMixing inverse k i)) := by
    rw [byteDiffusionOrientation_apply]
    change byteCharacter ((∑ i : Fin 4, gramMixing inverse k i * y i) * t) = _
    rw [Finset.sum_mul, byteCharacter_finset_sum]
    apply Finset.prod_congr rfl
    intro i _
    -- Reassociate the three byte factors explicitly; concrete-field ring
    -- normalization caused a timeout in the preceding autocorrelation proof.
    apply congrArg byteCharacter
    calc
      _ = y i * (gramMixing inverse k i * t) :=
        (_root_.mul_assoc (gramMixing inverse k i) (y i) t).trans
          (_root_.mul_left_comm (gramMixing inverse k i) (y i) t)
      _ = _ := congrArg (fun z : Byte => y i * z)
        (_root_.mul_comm (gramMixing inverse k i) t)
  simp_rw [rowSource_eq, hchar]
  change (∑ y : Word, (∏ i : Fin 4, channel o (b i) (y i)) *
    ∏ i : Fin 4, byteCharacter (y i * (t * gramMixing inverse k i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : Fin 4, ∑ v : Byte,
        channel o (b i) v * byteCharacter (v * (t * gramMixing inverse k i)) :=
      (Fintype.prod_sum (fun (i : Fin 4) (v : Byte) =>
        channel o (b i) v * byteCharacter (v * (t * gramMixing inverse k i)))).symm
    _ = _ := by simp_rw [← G_eq_row_character]

theorem row_character_abs_le (o : Orientation) (inverse : Bool) (b : Word)
    (k : Fin 4) (t : Byte) (ht : t ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (hi : b i ≠ 0) (hj : b j ≠ 0) :
    |∑ y : Word, rowSource o b y * byteCharacter (byteDiffusionOrientation inverse y k * t)| ≤
      (1 / 64 : ℝ) := by
  rw [row_character_product]
  calc
    _ ≤ |G o (t * gramMixing inverse k i) (b i)| *
        |G o (t * gramMixing inverse k j) (b j)| :=
      abs_prod_le_pair _ i j hij (fun _ => G_abs_le_one _ _ _)
    _ ≤ (1 / 8 : ℝ) * (1 / 8) :=
      mul_le_mul
        (G_abs_le_eighth o _ _ (mul_ne_zero ht (mixing_coefficient_ne_zero inverse k i)) hi)
        (G_abs_le_eighth o _ _ (mul_ne_zero ht (mixing_coefficient_ne_zero inverse k j)) hj)
        (abs_nonneg _) (by norm_num)
    _ = _ := by norm_num

/-- Mixture weights vanish at the zero character and sum to one, so the
two-original-byte bias bound is retained without a factor 255. -/
theorem mixed_G_expectation_abs_le (left right : Orientation) (inverse : Bool)
    (b : Word) (k : Fin 4) (v : Byte) (hv : v ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (hi : b i ≠ 0) (hj : b j ≠ 0) :
    |∑ y : Word, rowSource left b y * G right v (byteDiffusionOrientation inverse y k)| ≤
      (1 / 64 : ℝ) := by
  have he : (∑ y : Word, rowSource left b y * G right v (byteDiffusionOrientation inverse y k)) =
      ∑ t : Byte, channel (AESConcrete.FourierLineOverlap.fourierMate right) t v *
        ∑ y : Word, rowSource left b y * byteCharacter (byteDiffusionOrientation inverse y k * t) := by
    simp_rw [G_character_mixture, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  calc
    _ ≤ ∑ t : Byte, |channel (AESConcrete.FourierLineOverlap.fourierMate right) t v *
        ∑ y : Word, rowSource left b y * byteCharacter (byteDiffusionOrientation inverse y k * t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Byte, channel (AESConcrete.FourierLineOverlap.fourierMate right) t v * (1 / 64 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t = 0
      · subst t
        rw [mixture_zero right v hv]
        norm_num
      · rw [abs_mul, abs_of_nonneg (mixture_nonnegative right t v)]
        exact mul_le_mul_of_nonneg_left
          (row_character_abs_le left inverse b k t ht i j hij hi hj)
          (mixture_nonnegative right t v)
    _ = _ := by rw [← Finset.sum_mul, mixture_mass, one_mul]

theorem G_product_single_mask (right : Orientation) (a x : Word) (k : Fin 4)
    (ha : ∀ i, i ≠ k → a i = 0) :
    (∏ i : Fin 4, G right (a i) (x i)) = G right (a k) (x k) := by
  apply Finset.prod_eq_single k
  · intro i _ hik
    rw [ha i hik, G_zero_mask]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem full_mixed_single_mask_le (left right : Orientation) (inverse : Bool)
    (a b : Word) (k : Fin 4) (ha : ∀ l, l ≠ k → a l = 0) (hak : a k ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (hi : b i ≠ 0) (hj : b j ≠ 0) :
    |kernelCompose (wordKernel left right inverse) wordFourier b a| ≤
      (1024 / 4294967296 : ℝ) := by
  have he := full_mixed_expectation left right inverse a b
  simp_rw [G_product_single_mask right a _ k ha] at he
  have hL : (byteDiffusionOrientation inverse).symm = byteDiffusionOrientation (!inverse) := by
    simpa only [Bool.not_not] using byteDiffusionOrientation_symm (!inverse)
  rw [hL] at he
  have hb := mixed_G_expectation_abs_le left right (!inverse) b k (a k) hak i j hij hi hj
  rw [← he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 65536)] at hb
  linarith only [hb]

end AES8.WordMixedSingleMaskCap
