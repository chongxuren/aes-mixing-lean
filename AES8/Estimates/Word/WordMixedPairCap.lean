import AES8.Estimates.Word.WordMixedExpectation
import AES8.Estimates.Word.WordMixedZeroEvents

/-!
# Actual raw mixed-word cap with two active mask bytes

Only two G factors are retained. Their zero events are evaluated on the
original product source through inverse diffusion, using the already proved
MDS one/two-zero bounds. The other factors have magnitude at most one.
This establishes one nonexceptional branch; the single-mask/multiple-source
branch and the exceptional single/single block remain separate obligations.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixedPairCap
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierCore (wordFourier)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.ReverseDegreeThree (transposeOrientation)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.RestrictedSourcePushforward (outputZeros)
open AES8.ByteMixedCharacterMixture
open AES8.WordMixedExpectation
open AES8.WordMixedZeroEvents

section Generic
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem abs_prod_le_pair (g : I → ℝ) (i j : I) (hij : i ≠ j)
    (hcap : ∀ k, |g k| ≤ 1) : |∏ k, g k| ≤ |g i| * |g j| := by
  rw [Finset.abs_prod]
  have hi : i ∈ (Finset.univ : Finset I) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset I).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hrest : (∏ k ∈ ((Finset.univ : Finset I).erase i).erase j, |g k|) ≤ 1 := by
    calc
      _ ≤ ∏ _k ∈ ((Finset.univ : Finset I).erase i).erase j, (1 : ℝ) :=
        Finset.prod_le_prod (fun k _ => abs_nonneg (g k)) (fun k _ => hcap k)
      _ = 1 := by simp
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hj]
  have hm := mul_le_mul_of_nonneg_left hrest
    (mul_nonneg (abs_nonneg (g i)) (abs_nonneg (g j)))
  simpa only [mul_one, mul_assoc] using hm

end Generic

theorem singleton_output_zero (inverse : Bool) (i : Fin 4) (y : Word) :
    outputZeros inverse (singletonMask i) y ↔ byteDiffusionOrientation inverse y i = 0 := by
  constructor
  · intro h
    exact h i ((singletonMask_bit i i).mpr rfl)
  · intro h k hk
    have hki := (singletonMask_bit i k).mp hk
    simpa only [hki] using h

theorem pair_mask_size (i j : Fin 4) (hij : i ≠ j) :
    maskSize (maskUnion (singletonMask i) (singletonMask j)) = 2 := by
  have hd : MaskDisjoint (singletonMask i) (singletonMask j) := by
    intro k hki hkj
    have hki' : k = i := (singletonMask_bit i k).mp hki
    have hkj' : k = j := (singletonMask_bit j k).mp hkj
    exact hij (hki'.symm.trans hkj')
  rw [maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]

theorem pair_output_zero (inverse : Bool) (i j : Fin 4) (y : Word) :
    outputZeros inverse (maskUnion (singletonMask i) (singletonMask j)) y ↔
      byteDiffusionOrientation inverse y i = 0 ∧ byteDiffusionOrientation inverse y j = 0 := by
  constructor
  · intro h
    constructor
    · apply h i
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inl ((singletonMask_bit i i).mpr rfl)
    · apply h j
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inr ((singletonMask_bit j j).mpr rfl)
  · rintro ⟨hi, hj⟩ k hk
    rw [maskUnion_bit, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · simpa only [(singletonMask_bit i k).mp hk] using hi
    · simpa only [(singletonMask_bit j k).mp hk] using hj

def zeroFlag (x : Byte) : ℝ := if x = 0 then 1 else 0

theorem G_abs_le_flag (o : Orientation) (v x : Byte) (hv : v ≠ 0) :
    |G o v x| ≤ 1 / 8 + (7 / 8 : ℝ) * zeroFlag x := by
  by_cases hx : x = 0
  · subst x
    rw [G_zero, abs_one]
    norm_num [zeroFlag]
  · simpa only [zeroFlag, if_neg hx, mul_zero, add_zero] using G_abs_le_eighth o v x hv hx

theorem flag_product (x z : Byte) :
    zeroFlag x * zeroFlag z = if x = 0 ∧ z = 0 then (1 : ℝ) else 0 := by
  by_cases hx : x = 0 <;> by_cases hz : z = 0 <;> simp [zeroFlag, hx, hz]

/-- All coordinates other than the two selected nonzero mask bytes are paid
by one. The resulting joint event is still on the original source. -/
theorem full_mixed_le_pair (left right : Orientation) (inverse : Bool) (a b : Word)
    (hb : b ≠ 0) (i j : Fin 4) (hij : i ≠ j) (hi : a i ≠ 0) (hj : a j ≠ 0) :
    |kernelCompose (wordKernel left right inverse) wordFourier b a| ≤
      (585713 / (512 * 4294967296) : ℝ) := by
  let L := byteDiffusionOrientation (!inverse)
  have hL : (byteDiffusionOrientation inverse).symm = L := by
    simpa only [Bool.not_not] using byteDiffusionOrientation_symm (!inverse)
  have hsource : rowSource left b = AESConcrete.WordColumnGram.inputColumn
      (transposeOrientation left) b := rfl
  have hone (k : Fin 4) :
      (∑ y : Word, rowSource left b y * zeroFlag (L y k)) ≤ (65 / 8192 : ℝ) := by
    have he : (∑ y : Word, rowSource left b y * zeroFlag (L y k)) =
        fullZeroMass (transposeOrientation left) (!inverse) b (singletonMask k) := by
      unfold fullZeroMass
      apply Finset.sum_congr rfl
      intro y _
      have ho : outputZeros (!inverse) (singletonMask k) y ↔ L y k = 0 :=
        singleton_output_zero (!inverse) k y
      by_cases hz : L y k = 0
      · rw [if_pos (ho.mpr hz)]
        simp only [zeroFlag, if_pos hz, mul_one]
        rfl
      · rw [if_neg (fun h => hz (ho.mp h))]
        simp only [zeroFlag, if_neg hz, mul_zero]
    rw [he]
    exact one_zero_le _ _ b hb _ (singletonMask_size k)
  have htwo : (∑ y : Word, rowSource left b y * (zeroFlag (L y i) * zeroFlag (L y j))) ≤
      (1 / 64 : ℝ) * (65 / 8192) := by
    have he : (∑ y : Word, rowSource left b y * (zeroFlag (L y i) * zeroFlag (L y j))) =
        fullZeroMass (transposeOrientation left) (!inverse) b
          (maskUnion (singletonMask i) (singletonMask j)) := by
      unfold fullZeroMass
      apply Finset.sum_congr rfl
      intro y _
      have ho : outputZeros (!inverse) (maskUnion (singletonMask i) (singletonMask j)) y ↔
          L y i = 0 ∧ L y j = 0 := pair_output_zero (!inverse) i j y
      by_cases hz : L y i = 0 ∧ L y j = 0
      · rw [if_pos (ho.mpr hz)]
        simp only [flag_product, if_pos hz, mul_one]
        rfl
      · rw [if_neg (fun h => hz (ho.mp h))]
        simp only [flag_product, if_neg hz, mul_zero]
    rw [he]
    exact two_zero_le _ _ b hb _ (pair_mask_size i j hij)
  have hnorm : (65536 : ℝ) *
      |kernelCompose (wordKernel left right inverse) wordFourier b a| ≤
      1 / 64 + 7 / 64 * (65 / 8192) + 7 / 64 * (65 / 8192) +
        (49 / 64 : ℝ) * ((1 / 64) * (65 / 8192)) := by
    calc
      _ = |(65536 : ℝ) * kernelCompose (wordKernel left right inverse) wordFourier b a| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 65536)]
      _ = |∑ y : Word, rowSource left b y * ∏ k : Fin 4, G right (a k) (L y k)| := by
        rw [full_mixed_expectation, hL]
      _ ≤ ∑ y : Word, rowSource left b y * |∏ k : Fin 4, G right (a k) (L y k)| := by
        calc
          _ ≤ ∑ y : Word, |rowSource left b y * ∏ k : Fin 4, G right (a k) (L y k)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul, abs_of_nonneg (rowSource_nonnegative left b _)]
      _ ≤ ∑ y : Word, rowSource left b y *
          ((1 / 8 + (7 / 8 : ℝ) * zeroFlag (L y i)) *
            (1 / 8 + (7 / 8 : ℝ) * zeroFlag (L y j))) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (rowSource_nonnegative left b y)
        exact (abs_prod_le_pair _ i j hij (fun k => G_abs_le_one right _ _)).trans
          (mul_le_mul (G_abs_le_flag right _ _ hi) (G_abs_le_flag right _ _ hj)
            (abs_nonneg _) (by unfold zeroFlag; split_ifs <;> norm_num))
      _ = 1 / 64 + 7 / 64 * (∑ y, rowSource left b y * zeroFlag (L y i)) +
          7 / 64 * (∑ y, rowSource left b y * zeroFlag (L y j)) +
          (49 / 64 : ℝ) * (∑ y, rowSource left b y * (zeroFlag (L y i) * zeroFlag (L y j))) := by
        have ht (y : Word) : rowSource left b y *
            ((1 / 8 + (7 / 8 : ℝ) * zeroFlag (L y i)) *
              (1 / 8 + (7 / 8 : ℝ) * zeroFlag (L y j))) =
            rowSource left b y / 64 +
              7 / 64 * (rowSource left b y * zeroFlag (L y i)) +
              7 / 64 * (rowSource left b y * zeroFlag (L y j)) +
              (49 / 64 : ℝ) * (rowSource left b y * (zeroFlag (L y i) * zeroFlag (L y j))) := by ring
        simp only [ht, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, rowSource_mass]
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left (hone i) (by norm_num : (0 : ℝ) ≤ 7 / 64)
        have h2 := mul_le_mul_of_nonneg_left (hone j) (by norm_num : (0 : ℝ) ≤ 7 / 64)
        have h3 := mul_le_mul_of_nonneg_left htwo (by norm_num : (0 : ℝ) ≤ 49 / 64)
        linarith only [h1, h2, h3]
  linarith only [hnorm]

end AES8.WordMixedPairCap
