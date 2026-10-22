import AES8.Estimates.Byte.ByteExceptionalBlockResources
import AES8.Estimates.Word.OneSidedWordEnergy
import AESConcrete.SingleByteCoordinates

/-!
# Literal one-active-byte entries of the one-sided word residual

The output row of the first substitution is restricted to its physical byte
position. The right Fourier map then factors across all four coordinates.
Only the selected input coordinate survives as a nonconstant byte factor.
The global word activity correction is kept separate from byte centering.
Constructive only; no attacks, manuscript changes or proof bypasses.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperExceptionalWordEntries
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteGramCore (NonzeroByte)
open AESConcrete.ByteGramFourier (byteFourier_symmetric)
open AESConcrete.ByteGramDiagonal (residual_zero_row residual_column_sum)
open AESConcrete.WordColumnGram (singleByteWord)
open AESConcrete.SingleByteCoordinates (coordinatePerm coordinatePerm_zero)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierCore
open AESConcrete.WordFourierVariants (baseOrientation baseResidual_eq)
open AES8.ByteExceptionalBlockResources (byteResidual H u)
open AES8.OneSidedWordEnergy (rightMixed)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Byte := BinaryWord 8
abbrev Word := AES.Word

def fullByteMixed (o : Orientation) : Byte → Byte → ℝ :=
  kernelCompose (channel o) byteFourierMatrix

theorem fullByteMixed_zero_column (o : Orientation) (b : Byte) :
    fullByteMixed o b 0 = 1 / 16 := by
  unfold fullByteMixed kernelCompose byteFourierMatrix
  simp only [mul_zero, byteCharacter_zero, ← Finset.sum_mul]
  rw [(channel_resources o).row_sum]
  norm_num

theorem byteFourier_column_sum (a : Byte) :
    (∑ z : Byte, byteFourierMatrix z a) = if a = 0 then 16 else 0 := by
  unfold byteFourierMatrix
  rw [← Finset.sum_div,
    real_character_scaled_sum byteCharacter byteCharacter_zero byteCharacter_sum]
  by_cases ha : a = 0 <;> norm_num [ha, BinaryWord.card]

theorem byteActivityFourier_nonzero (b a : Byte) (hb : b ≠ 0) (ha : a ≠ 0) :
    kernelCompose (activityMatrix (0 : Byte)) byteFourierMatrix b a =
      -(1 / 4080 : ℝ) := by
  change action (activityMatrix (0 : Byte)) (fun z => byteFourierMatrix z a) b = _
  rw [activityMatrix_action]
  simp only [wordAverage, if_neg hb, nonzeroMean]
  rw [byteFourier_column_sum, if_neg ha]
  simp only [byteFourierMatrix, zero_mul, byteCharacter_zero, BinaryWord.card]
  norm_num

theorem fullByteMixed_eq (o : Orientation) (b a : Byte) :
    fullByteMixed o b a = AESConcrete.ByteLineBounds.leg o true b a +
      kernelCompose (activityMatrix (0 : Byte)) byteFourierMatrix b a := by
  change (∑ z, channel o b z * byteFourierMatrix z a) =
    (∑ z, (channel o b z - activityMatrix 0 b z) * byteFourierMatrix z a) +
      ∑ z, activityMatrix 0 b z * byteFourierMatrix z a
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem mixedByte_column_sum (o : Orientation) (a : Byte) :
    (∑ b : Byte, AESConcrete.ByteLineBounds.leg o true b a) = 0 := by
  change (∑ b : Byte, ∑ z : Byte,
    residualMatrix (channel o) 0 b z * byteFourierMatrix z a) = 0
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, residual_column_sum (channel_resources o),
    zero_mul, Finset.sum_const_zero]

theorem mixedByte_zero_row (o : Orientation) (a : Byte) :
    AESConcrete.ByteLineBounds.leg o true 0 a = 0 := by
  change (∑ z : Byte, residualMatrix (channel o) 0 0 z * byteFourierMatrix z a) = 0
  simp only [residual_zero_row (channel_resources o), zero_mul, Finset.sum_const_zero]

/-- Exact removal of both byte activity terms, for the actual intermediate
zero-preserving coordinate permutation. No additive invariance is assumed. -/
theorem fullByteComposition_eq (left right : Orientation) (e : Equiv.Perm Byte)
    (he : e 0 = 0) (b a : Byte) (hb : b ≠ 0) (ha : a ≠ 0) :
    (∑ z : Byte, channel left b z * fullByteMixed right (e z) a) =
      H left right e b a - 1 / 4080 := by
  have hez (z : Byte) (hz : z ≠ 0) : e z ≠ 0 := by
    intro h
    exact hz (e.injective (h.trans he.symm))
  have hterm (z : Byte) :
      channel left b z * fullByteMixed right (e z) a =
        channel left b z * AESConcrete.ByteLineBounds.leg right true (e z) a -
          channel left b z / 4080 := by
    by_cases hz : z = 0
    · subst z
      simp [(channel_resources left).zero_column, hb]
    · rw [fullByteMixed_eq,
        byteActivityFourier_nonzero (e z) a (hez z hz) ha]
      ring
  have hcenter (z : Byte) :
      channel left b z * AESConcrete.ByteLineBounds.leg right true (e z) a =
        byteResidual left b z * AESConcrete.ByteLineBounds.leg right true (e z) a +
          (1 / 255 : ℝ) * AESConcrete.ByteLineBounds.leg right true (e z) a := by
    by_cases hz : z = 0
    · subst z
      rw [he, mixedByte_zero_row]
      ring
    · change channel left b z * _ =
        (channel left b z - activityMatrix (0 : Byte) b z) * _ + _
      norm_num [activityMatrix, hb, hz, BinaryWord.card]
      ring
  simp_rw [hterm, hcenter]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, (channel_resources left).row_sum,
    Equiv.sum_comp e (fun z => AESConcrete.ByteLineBounds.leg right true z a),
    mixedByte_column_sum]
  change H left right e b a + (1 / 255 : ℝ) * 0 - 1 / 4080 = _
  ring

theorem singleByteWord_zero (k : Fin 4) : singleByteWord k (0 : Byte) = 0 := by
  funext i
  simp [singleByteWord]

theorem singleByteWord_ne_zero (k : Fin 4) (b : Byte) (hb : b ≠ 0) :
    singleByteWord k b ≠ 0 := by
  intro h
  have he := congrFun h k
  exact hb (by simpa [singleByteWord] using he)

theorem substitution_row_single (o : Orientation) (j : Fin 4) (b t : Byte) :
    substitutionKernel (channel o) (singleByteWord j b) (singleByteWord j t) =
      channel o b t := by
  change (∏ i : Fin 4, channel o (singleByteWord j b i) (singleByteWord j t i)) = _
  calc
    _ = ∏ i : Fin 4, if i = j then channel o b t else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = j
      · subst i
        simp [singleByteWord]
      · simp [singleByteWord, hi, (channel_resources o).zero_row]
    _ = _ := by simp

theorem substitution_row_zero_outside_single (o : Orientation) (j : Fin 4)
    (b : Byte) (z : Word) (hz : z ∉ Finset.univ.image (singleByteWord j)) :
    substitutionKernel (channel o) (singleByteWord j b) z = 0 := by
  have hex : ∃ i : Fin 4, i ≠ j ∧ z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    refine Finset.mem_image.mpr ⟨z j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : i = j
    · subst i
      simp [singleByteWord]
    · simp [singleByteWord, hi, h i hi]
  obtain ⟨i, hij, hi⟩ := hex
  change (∏ k : Fin 4, channel o (singleByteWord j b k) (z k)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [singleByteWord, hij, (channel_resources o).zero_row, hi]

theorem substitution_single_row_sum (o : Orientation) (j : Fin 4) (b : Byte)
    (f : Word → ℝ) :
    (∑ z : Word, substitutionKernel (channel o) (singleByteWord j b) z * f z) =
      ∑ t : Byte, channel o b t * f (singleByteWord j t) := by
  calc
    _ = ∑ z ∈ Finset.univ.image (singleByteWord j),
        substitutionKernel (channel o) (singleByteWord j b) z * f z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      rw [substitution_row_zero_outside_single o j b z hz, zero_mul]
    _ = ∑ t : Byte,
        substitutionKernel (channel o) (singleByteWord j b) (singleByteWord j t) *
          f (singleByteWord j t) :=
      Finset.sum_image (fun t _ s _ h =>
        AESConcrete.WordColumnGram.singleByteWord_injective j h)
    _ = _ := by simp only [substitution_row_single]

theorem substitution_right_fourier (o : Orientation) :
    kernelCompose (substitutionKernel (channel o)) wordFourier =
      coordinateKernel (fun _ : Fin 4 => fullByteMixed o) := by
  rw [wordFourier_tensor]
  exact coordinateKernel_compose _ _

theorem single_input_tensor (o : Orientation) (v : Word) (k : Fin 4) (a : Byte) :
    coordinateKernel (fun _ : Fin 4 => fullByteMixed o) v (singleByteWord k a) =
      fullByteMixed o (v k) a / 4096 := by
  fin_cases k <;>
    simp [coordinateKernel, singleByteWord, Fin.prod_univ_four,
      fullByteMixed_zero_column] <;> ring

theorem fullWordMixed_single (left right : Orientation) (inverse : Bool)
    (j k : Fin 4) (b a : Byte) :
    kernelCompose (wordKernel left right inverse) wordFourier
        (singleByteWord j b) (singleByteWord k a) =
      (∑ t : Byte, channel left b t *
        fullByteMixed right (coordinatePerm (!inverse) j k t) a) / 4096 := by
  have hex (y x : Word) :
      kernelCompose (wordKernel left right inverse) wordFourier y x =
        ∑ z : Word, substitutionKernel (channel left) y z *
          kernelCompose (substitutionKernel (channel right)) wordFourier
            ((byteDiffusionOrientation inverse).symm z) x := by
    unfold wordKernel twoSubstitutionKernel kernelCompose
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [hex, substitution_single_row_sum]
  simp only [substitution_right_fourier, single_input_tensor]
  have hdiff : (byteDiffusionOrientation inverse).symm =
      byteDiffusionOrientation (!inverse) := by cases inverse <;> rfl
  simp only [hdiff, ← AESConcrete.SingleByteCoordinates.coordinatePerm_apply]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]

theorem wordActivityFourier_nonzero (y x : Word) (hy : y ≠ 0) (hx : x ≠ 0) :
    kernelCompose (activityMatrix (0 : Word)) wordFourier y x =
      -(1 / (65536 * 4294967295) : ℝ) := by
  have hs : (∑ z : Word, wordFourier z x) = 0 := by
    simp_rw [wordFourier_symmetric _ x]
    rw [wordFourier_row_sum, if_neg hx]
  change action (activityMatrix (0 : Word)) (fun z => wordFourier z x) y = _
  rw [activityMatrix_action]
  simp only [wordAverage, if_neg hy, nonzeroMean]
  rw [hs, word_card]
  norm_num [wordFourier_coefficient, CharacterPairing.zero_left]

def translation : ℝ := 512 * (1 / 255 - 1 / 4294967295)

theorem translation_nonneg : 0 ≤ translation := by norm_num [translation]
theorem translation_le : translation ≤ 33 / 16 := by norm_num [translation]

/-- The actual ordinary and adjoint one-sided word entries, with all physical
byte positions and the intermediate diffusion relabeling retained. -/
theorem rightMixed_single_entry (adjoint : Bool) (j k : Fin 4)
    (b a : NonzeroByte) :
    (4294967296 : ℝ) * rightMixed adjoint
        (singleByteWord j b.val) (singleByteWord k a.val) =
      128 * (u (baseOrientation adjoint) (baseOrientation adjoint)
        (coordinatePerm (!adjoint) j k) b.val a.val - translation) := by
  have hy := singleByteWord_ne_zero j b.val b.property
  have hx := singleByteWord_ne_zero k a.val a.property
  have he := fullByteComposition_eq (baseOrientation adjoint) (baseOrientation adjoint)
    (coordinatePerm (!adjoint) j k) (coordinatePerm_zero (!adjoint) j k)
    b.val a.val b.property a.property
  unfold rightMixed
  rw [baseResidual_eq]
  have hr (y x : Word) :
      kernelCompose (residualMatrix
          (wordKernel (baseOrientation adjoint) (baseOrientation adjoint) adjoint) 0)
          wordFourier y x =
        kernelCompose (wordKernel (baseOrientation adjoint) (baseOrientation adjoint) adjoint)
          wordFourier y x - kernelCompose (activityMatrix (0 : Word)) wordFourier y x := by
    simp only [kernelCompose, residualMatrix, sub_mul, Finset.sum_sub_distrib]
  rw [hr, fullWordMixed_single, he, wordActivityFourier_nonzero _ _ hy hx]
  unfold u translation
  ring

end AES8.PaperExceptionalWordEntries
