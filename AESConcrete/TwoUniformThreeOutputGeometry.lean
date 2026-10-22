import AESConcrete.WeightedThreeOutputGeometry
import AESConcrete.InvariantSubspaceFourier

/-!
# Actual output-zero code with a joint residual pair and two input uniforms

Geometry for (11,10). The Code, Retained and Residual types are exactly the
existing generic WeightedThreeOutputGeometry types at output (3,3) and input
(2,4). The input inactive mask has size zero, so this is the actual output-
zero subgroup. One original uniform input label completes the residual pair to
an input information set. Its unrestricted counting multiplicity is exactly q.

The residual-zero translation line is a separate actual ShortenedCode: the
output zero is preserved and both original residual inputs are zero. Every
retained output singleton parametrizes that line. No response bound, source
normalization, event expansion, physical cap or certificate is asserted.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and the ordered-distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoUniformThreeOutputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 3 3) :=
  WeightedThreeOutputGeometry.Retained pOut

abbrev Residual (pIn : SelectedSupport 2 4) :=
  WeightedThreeOutputGeometry.Residual pIn

abbrev SourceUniformPositions (pIn : SelectedSupport 2 4) :=
  WeightedThreeOutputGeometry.SourceUniformPositions pIn

abbrev Code (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :=
  WeightedThreeOutputGeometry.Code pOut pIn

def curve (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  WeightedThreeOutputGeometry.curve pOut pIn c

def residualTuple (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : Residual pIn → AES.Word :=
  WeightedThreeOutputGeometry.residualTuple pOut pIn c

theorem retainedCoordinates_card (pOut : SelectedSupport 3 3) :
    Fintype.card (Retained pOut) = 3 :=
  WeightedThreeOutputGeometry.retainedCoordinates_card pOut

theorem residualCoordinates_card (pIn : SelectedSupport 2 4) :
    Fintype.card (Residual pIn) = 2 := by
  rw [maskCoordinates_card, WeightedThreeOutputGeometry.residualMask_size]
  norm_num

theorem sourceUniformPositions_card (pIn : SelectedSupport 2 4) :
    Fintype.card (SourceUniformPositions pIn) = 2 := by
  simpa using WeightedThreeOutputGeometry.sourceUniformPositions_card pIn

theorem inputInactiveMask_size (pIn : SelectedSupport 2 4) :
    maskSize pIn.val.val.2 = 0 := by
  simpa using WeightedThreeOutputGeometry.inputInactiveMask_size pIn

theorem input_inactive_not (pIn : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pIn.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inputInactiveMask_size] at hc
  omega

/-- The retained image is the actual additive output restriction. -/
def retainedHom (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :
    Code pOut pIn →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 pIn.val.val.2 pOut.val.val.1

@[simp]
theorem retainedHom_apply (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) (i : Retained pOut) :
    retainedHom pOut pIn c i = curve pOut pIn c i := rfl

/-- Three retained outputs together with the one output zero determine the code. -/
theorem retainedHom_bijective (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :
    Function.Bijective (retainedHom pOut pIn) := by
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size, inputInactiveMask_size,
      WeightedThreeOutputGeometry.retainedMask_size]
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pOut.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem retainedHom_injective (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :
    Function.Injective (retainedHom pOut pIn) := (retainedHom_bijective pOut pIn).1

/-- The translation parameter is the actual output-zero/residual-input-zero line. -/
abbrev ResidualZero (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.1

/-- Include that line into the original output-zero code without changing states. -/
def translation (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) :
    ResidualZero pOut pIn →+ Code pOut pIn where
  toFun t := ⟨t.val, t.property.1, by
    intro i hi
    exact (input_inactive_not pIn i hi).elim⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

@[simp]
theorem translation_residual_zero (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (t : ResidualZero pOut pIn) (i : Residual pIn) :
    (translation pOut pIn t).val i.val = 0 := t.property.2 i.val i.property

/-- One arbitrary signed joint h is unchanged by every residual-zero translation. -/
theorem amplitude_translation (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn)
    (t : ResidualZero pOut pIn) :
    h (residualTuple pOut pIn (c + translation pOut pIn t)) =
      h (residualTuple pOut pIn c) := by
  apply congrArg h
  funext i
  change c.val i.val + t.val i.val = c.val i.val
  rw [t.property.2 i.val i.property, add_zero]

/-- One output zero, two original residual zeros and one output label total four. -/
theorem translation_coordinate_bijective
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) (s : Retained pOut) :
    Function.Bijective (fun t : ResidualZero pOut pIn =>
      retainedHom pOut pIn (translation pOut pIn t) s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he : i = s.val := (singletonMask_bit s.val i).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.1 +
      maskSize (singletonMask s.val) = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size,
      WeightedThreeOutputGeometry.residualMask_size, singletonMask_size]
    norm_num
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
      pOut.val.val.2 pIn.val.val.1 (singletonMask s.val) hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem translation_dependent_surjective
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4) (s : Retained pOut) :
    Function.Surjective (fun t : ResidualZero pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        retainedHom pOut pIn (translation pOut pIn t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t : ResidualZero pOut pIn => retainedHom pOut pIn (translation pOut pIn t))
    (translation_coordinate_bijective pOut pIn s).2

/-- Two residual labels and any one original uniform label parametrize the code. -/
def residualUniformEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) :
    Code pOut pIn ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hsu : MaskDisjoint pIn.val.val.1 (singletonMask s.val.val) := by
    intro i hi hs
    have he : i = s.val.val := (singletonMask_bit _ _).mp hs
    subst i
    exact s.val.property hi
  have hzu : MaskDisjoint pIn.val.val.2
      (maskUnion pIn.val.val.1 (singletonMask s.val.val)) := by
    intro i hi _
    exact (input_inactive_not pIn i hi).elim
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 + maskSize (singletonMask s.val.val) = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size, inputInactiveMask_size,
      WeightedThreeOutputGeometry.residualMask_size, singletonMask_size]
    norm_num
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hsu hzu hsize)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv s.val.val))

@[simp]
theorem residualUniformEquiv_fst (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).1 = residualTuple pOut pIn c := rfl

@[simp]
theorem residualUniformEquiv_snd (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).2 = c.val s.val.val := rfl

/-- Exactly one unrestricted original uniform coordinate accompanies each joint residual pair. -/
theorem full_amplitude_energy_at (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ u, h u ^ 2 := by
  have he := (residualUniformEquiv pOut pIn s).sum_comp
    (fun uv : (Residual pIn → AES.Word) × AES.Word => h uv.1 ^ 2)
  change (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
    ∑ uv : (Residual pIn → AES.Word) × AES.Word, h uv.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem full_amplitude_energy (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  exact full_amplitude_energy_at pOut pIn (Classical.choice inferInstance) h

theorem freeCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 2 := by
  change Fintype.card {i : Retained pOut // i ≠ s} = 2
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
  IndexedFourierSupport.dependentCoordinates_card s

end AESConcrete.TwoUniformThreeOutputGeometry
