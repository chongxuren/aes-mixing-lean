import AESConcrete.OmittedUniformTwoInputPushforward
import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.WordCrossZero
import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.MultiUniformExpansion
import AESConcrete.InvariantSubspaceFourier

/-!
# Actual raw-source geometry for output (2,3), input (2,4)

The support indices are (9,10). The code uses the actual output-zero mask AND
actual input-zero mask. Two original residual input labels and one original
uniform input label parametrize its joint amplitude. One original residual
singleton and the retained output pair instead parametrize its retained
fibers.

The retained map is NOT declared injective. Each of its fibers has q points.
The separate residual-zero line sets BOTH original residual inputs to zero;
its inclusion preserves the original code and amplitude, and either retained
physical singleton is a bijective coordinate on that line.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

No physical cap is supplied here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoInputRawGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 2 3) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 2 4) := MaskCoordinates pIn.val.val.1
abbrev SourceUniformPositions (pIn : SelectedSupport 2 4) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

/-- First zero mask: output. Second zero mask: original input. -/
abbrev Code (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

def curve (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : Residual pIn → AES.Word := fun i => c.val i.val

def retainedHom (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :
    Code pOut pIn →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 pIn.val.val.2 pOut.val.val.1

@[simp]
theorem retainedHom_apply (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : retainedHom pOut pIn c = curve pOut pIn c := rfl

theorem retainedMask_size (pOut : SelectedSupport 2 3) :
    maskSize pOut.val.val.1 = 2 := by
  have hd := pOut.val.property.2
  norm_num at hd
  exact hd

theorem residualMask_size (pIn : SelectedSupport 2 4) :
    maskSize pIn.val.val.1 = 2 := by
  have hd := pIn.val.property.2
  norm_num at hd
  exact hd

theorem outputInactiveMask_size (pOut : SelectedSupport 2 3) :
    maskSize pOut.val.val.2 = 1 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 3 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport 2 4) :
    maskSize pIn.val.val.2 = 0 := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + 4 = 4 at hp
  omega

theorem input_inactive_not (pIn : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pIn.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inputInactiveMask_size] at hc
  omega

theorem retainedCoordinates_card (pOut : SelectedSupport 2 3) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem residualCoordinates_card (pIn : SelectedSupport 2 4) :
    Fintype.card (Residual pIn) = 2 := by
  rw [maskCoordinates_card, residualMask_size]

theorem sourceUniformPositions_card (pIn : SelectedSupport 2 4) :
    Fintype.card (SourceUniformPositions pIn) = 2 := by
  rw [MultiUniformExpansion.uniformPositions_card _ _ pIn.val.property.1,
    inputInactiveMask_size, residualMask_size]

/-- The joint residual pair and one actual original uniform input give the
entire code. The first component is the unchanged original residual tuple. -/
def residualUniformEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
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
    rw [outputInactiveMask_size, inputInactiveMask_size,
      residualMask_size, singletonMask_size]
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hsu hzu hsize)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv s.val.val))

@[simp]
theorem residualUniformEquiv_fst (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).1 = residualTuple pOut pIn c := rfl

@[simp]
theorem residualUniformEquiv_snd (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).2 = c.val s.val.val := rfl

/-- Exactly q copies of the SAME arbitrary signed joint residual pair. -/
theorem full_amplitude_energy_at (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
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

theorem full_amplitude_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  exact full_amplitude_energy_at pOut pIn (Classical.choice inferInstance) h

/-- One ORIGINAL residual singleton and the retained output pair are a mixed
information set. Its second component is exactly the noninjective retained map. -/
def retainedFiberParam (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) : Code pOut pIn ≃ AES.Word × (Retained pOut → AES.Word) := by
  have hz : MaskDisjoint pIn.val.val.2 (singletonMask j.val) := by
    intro i hi _
    exact (input_inactive_not pIn i hi).elim
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 + maskSize (singletonMask j.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size,
      retainedMask_size, singletonMask_size]
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ pOut.val.property.1 hz hsize)).trans
        (Equiv.prodCongr (singletonTupleEquiv j.val) (Equiv.refl _))

@[simp]
theorem retainedFiberParam_fst (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (c : Code pOut pIn) :
    (retainedFiberParam pOut pIn j c).1 = c.val j.val := rfl

@[simp]
theorem retainedFiberParam_snd (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (c : Code pOut pIn) :
    (retainedFiberParam pOut pIn j c).2 = retainedHom pOut pIn c := rfl

/-- A physical retained fiber is parametrized by exactly one original input word. -/
def retainedFiberEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (z : Retained pOut → AES.Word) :
    {c : Code pOut pIn // retainedHom pOut pIn c = z} ≃ AES.Word :=
  OmittedUniformTwoInputPushforward.fiberEquiv (retainedHom pOut pIn)
    (retainedFiberParam pOut pIn j) (retainedFiberParam_snd pOut pIn j) z

theorem retained_fiber_card (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (z : Retained pOut → AES.Word) :
    Fintype.card {c : Code pOut pIn // retainedHom pOut pIn c = z} =
      Fintype.card AES.Word := Fintype.card_congr (retainedFiberEquiv pOut pIn j z)

/-- This line keeps the original output zero and sets BOTH residual inputs zero. -/
abbrev ResidualZero (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.1

/-- Include the residual-zero line into the original code, preserving physical states. -/
def translation (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :
    ResidualZero pOut pIn →+ Code pOut pIn where
  toFun t := ⟨t.val, t.property.1, by
    intro i hi
    exact (input_inactive_not pIn i hi).elim⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

@[simp]
theorem translation_residual_zero (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (t : ResidualZero pOut pIn) (i : Residual pIn) :
    (translation pOut pIn t).val i.val = 0 := t.property.2 i.val i.property

theorem amplitude_translation (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn)
    (t : ResidualZero pOut pIn) :
    h (residualTuple pOut pIn (c + translation pOut pIn t)) =
      h (residualTuple pOut pIn c) := by
  apply congrArg h
  funext i
  change c.val i.val + t.val i.val = c.val i.val
  rw [t.property.2 i.val i.property, add_zero]

/-- One output zero plus the two original residual input zeros leaves one
free word; either actual retained output singleton parametrizes it. -/
theorem translation_coordinate_bijective
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) (s : Retained pOut) :
    Function.Bijective (fun t : ResidualZero pOut pIn =>
      retainedHom pOut pIn (translation pOut pIn t) s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he : i = s.val := (singletonMask_bit s.val i).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.1 +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, residualMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
      pOut.val.val.2 pIn.val.val.1 (singletonMask s.val) hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem translation_dependent_surjective
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) (s : Retained pOut) :
    Function.Surjective (fun t : ResidualZero pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        retainedHom pOut pIn (translation pOut pIn t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t : ResidualZero pOut pIn => retainedHom pOut pIn (translation pOut pIn t))
    (translation_coordinate_bijective pOut pIn s).2

theorem freeCoordinates_card (pOut : SelectedSupport 2 3) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  change Fintype.card {i : Retained pOut // i ≠ s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 3) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
  IndexedFourierSupport.dependentCoordinates_card s

end AESConcrete.OmittedUniformTwoInputRawGeometry
