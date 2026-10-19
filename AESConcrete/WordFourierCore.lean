import AESConcrete.FourierLineOverlap
import AESMixing.ProductFourier

/-!
# Exact Fourier algebra on one AES word

The word pairing is the product of the four actual byte trace pairings.
Its Fourier coefficient has counting normalization 1/65536. Conjugation
acts on arbitrary word kernels and on the actual substitution channels.
The activity correction is the global rank-two zero/nonzero-word
projection, not the tensor product of byte activity projections. Its
Fourier invariance is proved from its actual action and Fourier sums.
Diffusion duality, entry bounds and round assembly remain separate.
Constructive mathematics only; no attacks, manuscript or frozen edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WordFourierCore
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.FourierLineOverlap (fourierMate)

abbrev Byte := BinaryWord 8
abbrev Word := Fin 4 → Byte

def wordPairing : CharacterPairing Word := bytePairing.product (Fin 4)
def wordFourier : Word → Word → ℝ := pairingFourier wordPairing
def wordConjugate (T : Word → Word → ℝ) : Word → Word → ℝ :=
  fourierConjugate wordPairing T

theorem word_card : Fintype.card Word = 4294967296 := by
  norm_num [Word,Fintype.card_fun,BinaryWord.card]

private theorem word_sqrt_card : Real.sqrt (Fintype.card Word : ℝ) = 65536 := by
  rw [word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536^2 by norm_num,Real.sqrt_sq_eq_abs]
  norm_num

theorem wordFourier_coefficient (y x : Word) :
    wordFourier y x = wordPairing.value y x / 65536 := by
  unfold wordFourier pairingFourier
  rw [word_sqrt_card]

theorem wordFourier_tensor :
    wordFourier = coordinateKernel (fun _ : Fin 4 => byteFourierMatrix) := by
  unfold wordFourier wordPairing
  rw [productPairing_fourier,← ByteGramFourier.byteFourier_pairing]

theorem wordFourier_symmetric (x y : Word) : wordFourier x y = wordFourier y x :=
  pairingFourier_symmetric wordPairing x y

theorem wordFourier_twice (f : Word → ℝ) :
    action wordFourier (action wordFourier f) = f :=
  pairingFourier_twice wordPairing word_add_self f

theorem wordFourier_comp_self : kernelCompose wordFourier wordFourier = identityKernel := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action,wordFourier_twice,identityKernel_action]

theorem wordFourier_energy (f : Word → ℝ) :
    (∑ y, action wordFourier f y^2) = ∑ x, f x^2 :=
  pairingFourier_energy wordPairing word_add_self f

theorem wordConjugate_action (T : Word → Word → ℝ) (f : Word → ℝ) :
    action (wordConjugate T) f = action wordFourier (action T (action wordFourier f)) := by
  simp only [wordConjugate,fourierConjugate,kernelCompose_action,wordFourier]

/-- Insert Fourier twice between the factors; no commutation with either
arbitrary kernel is assumed. -/
theorem wordConjugate_compose (T U : Word → Word → ℝ) :
    wordConjugate (kernelCompose T U) = kernelCompose (wordConjugate T) (wordConjugate U) := by
  apply kernel_action_ext
  intro f
  simp only [wordConjugate_action,kernelCompose_action,wordFourier_twice]

theorem wordConjugate_sub (T U : Word → Word → ℝ) :
    wordConjugate (T-U) = wordConjugate T-wordConjugate U := by
  apply kernel_action_ext
  intro f
  simp only [wordConjugate_action,kernel_action_sub,action_sub]

theorem wordConjugate_twice (T : Word → Word → ℝ) :
    wordConjugate (wordConjugate T) = T := by
  apply kernel_action_ext
  intro f
  simp only [wordConjugate_action,wordFourier_twice]

theorem wordConjugate_coordinate (T : Byte → Byte → ℝ) :
    wordConjugate (coordinateKernel (fun _ : Fin 4 => T)) =
      coordinateKernel (fun _ : Fin 4 => ByteGramFourier.byteConjugate T) := by
  simpa only [wordConjugate,wordPairing,ByteGramFourier.byteConjugate_pairing] using
    (coordinate_fourierConjugate (I := Fin 4) bytePairing T)

theorem wordConjugate_substitution (o : Orientation) :
    wordConjugate (substitutionKernel (channel o)) =
      substitutionKernel (channel (fourierMate o)) := by
  simpa only [substitutionKernel,FourierLineOverlap.channel_fourierMate o] using
    (wordConjugate_coordinate (channel o))

theorem wordFourier_at_zero (f : Word → ℝ) :
    action wordFourier f 0 = (∑ x, f x) / 65536 := by
  unfold action
  simp only [wordFourier_coefficient,CharacterPairing.zero_left,div_mul_eq_mul_div,
    one_mul,← Finset.sum_div]

theorem wordFourier_row_sum (y : Word) :
    (∑ x, wordFourier y x) = if y=0 then 65536 else 0 := by
  have hs : (∑ x, wordPairing.value y x) =
      if y=0 then (Fintype.card Word : ℝ) else 0 := by
    rw [Finset.sum_congr rfl (fun x _ => wordPairing.symmetric y x)]
    by_cases hy : y=0
    · simpa only [if_pos hy] using wordPairing.full_sum y
    · simpa only [if_neg hy] using wordPairing.full_sum y
  simp only [wordFourier_coefficient]
  rw [← Finset.sum_div,hs,word_card]
  by_cases hy : y=0 <;> norm_num [hy]

theorem wordFourier_sum (f : Word → ℝ) :
    (∑ y, action wordFourier f y) = 65536*f 0 := by
  have hc (x : Word) : (∑ y, wordFourier y x) = if x=0 then 65536 else 0 := by
    calc
      _ = ∑ y, wordFourier x y :=
        Finset.sum_congr rfl (fun y _ => wordFourier_symmetric y x)
      _ = _ := wordFourier_row_sum x
  unfold action
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hc]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- This is the Fourier action on the actual global word average. Its
two scalars are the zero value and the total mass of the whole word law. -/
theorem wordFourier_average_formula (f : Word → ℝ) (y : Word) :
    action wordFourier (wordAverage (0 : Word) f) y =
      (if y=0 then 65536 else 0)*nonzeroMean 0 f +
        (f 0-nonzeroMean 0 f)/65536 := by
  have hp (x : Word) : wordAverage (0 : Word) f x =
      nonzeroMean 0 f + (if x=0 then f 0-nonzeroMean 0 f else 0) := by
    by_cases hx : x=0 <;> simp [wordAverage,hx]
  unfold action
  simp_rw [hp,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,wordFourier_row_sum]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [wordFourier_coefficient,wordPairing.zero_right]
  ring

theorem word_activity_fourier_commutes :
    kernelCompose wordFourier (activityMatrix (0 : Word)) =
      kernelCompose (activityMatrix (0 : Word)) wordFourier := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action,activityMatrix_action]
  funext y
  rw [wordFourier_average_formula]
  have hn : (Fintype.card Word-1 : ℝ) = 4294967295 := by
    rw [word_card]
    norm_num
  by_cases hy : y=0
  · subst y
    rw [if_pos rfl,wordAverage_at_zero,wordFourier_at_zero]
    have hscalar (a b : ℝ) :
        65536*((b-a)/4294967295)+(a-(b-a)/4294967295)/65536 = b/65536 := by
      ring
    simpa only [nonzeroMean,hn] using hscalar (f 0) (∑ x, f x)
  · rw [if_neg hy,zero_mul,wordAverage,if_neg hy]
    unfold nonzeroMean
    rw [wordFourier_sum,wordFourier_at_zero]
    have hscalar (a b : ℝ) :
        (a-(b-a)/4294967295)/65536 = (65536*a-b/65536)/4294967295 := by
      ring
    simpa only [hn,zero_add] using hscalar (f 0) (∑ x, f x)

/-- Global rank-two zero/nonzero-word activity is Fourier-fixed. It is
not replaced by the tensor of four byte activity projections. -/
theorem word_activity_fourier_fixed :
    wordConjugate (activityMatrix (0 : Word)) = activityMatrix 0 := by
  apply kernel_action_ext
  intro f
  rw [wordConjugate_action,← kernelCompose_action,word_activity_fourier_commutes,
    kernelCompose_action,wordFourier_twice]

end AESConcrete.WordFourierCore
