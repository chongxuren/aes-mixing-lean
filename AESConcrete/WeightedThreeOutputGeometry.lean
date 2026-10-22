import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.IndexedTripleEnergy
import AESConcrete.DoubleUniformGeometry
import AESConcrete.MultiUniformExpansion

/-!
# Actual shortened input information sets for three retained outputs

The support indices are (11,5), (11,6), (11,9). The line/plane consumers are
source-layout references, never premises. Output type (3,3) supplies one
actual output zero. Input type (1,2) gives a line; (1,3) and (2,3) give
planes. Output information sets and INPUT information sets have separate
proofs. In particular, for (1,3) the original residual tuple and one actual
uniform input label form an exact bijection. This is not coordinate
independence.

Fixed independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference and constructive AES10/14/16.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedThreeOutputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000
variable {e b : Fin 5}

abbrev Retained (pOut : SelectedSupport 3 3) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport e b) := MaskCoordinates pIn.val.val.1
abbrev SourceUniformPositions (pIn : SelectedSupport e b) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

/-- The first zero mask is on outputs; the second is on inputs. -/
abbrev Code (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

instance codeFintype (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b) :
    Fintype (Code pOut pIn) := by classical exact inferInstance

theorem retainedMask_size (pOut : SelectedSupport 3 3) :
    maskSize pOut.val.val.1 = 3 := by
  have hd := pOut.val.property.2
  norm_num at hd
  exact hd

theorem residualMask_size (pIn : SelectedSupport e b) :
    maskSize pIn.val.val.1 = e.val := pIn.val.property.2

theorem outputInactiveMask_size (pOut : SelectedSupport 3 3) :
    maskSize pOut.val.val.2 = 1 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 3 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport e b) :
    maskSize pIn.val.val.2 = 4 - b.val := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + b.val = 4 at hp
  omega

theorem retainedCoordinates_card (pOut : SelectedSupport 3 3) :
    Fintype.card (Retained pOut) = 3 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem sourceUniformPositions_card (pIn : SelectedSupport e b) :
    Fintype.card (SourceUniformPositions pIn) = b.val - e.val := by
  rw [MultiUniformExpansion.uniformPositions_card _ _ pIn.val.property.1,
    inputInactiveMask_size, residualMask_size]
  have hp := pIn.property
  have hd := pIn.val.property.2
  omega

theorem output_nonretained_inactive : ∀ (pOut : SelectedSupport 3 3) (i : Fin 4),
    maskBit pOut.val.val.1 i ≠ true → maskBit pOut.val.val.2 i = true := by decide

theorem output_inactive_iff_not_retained (pOut : SelectedSupport 3 3) (i : Fin 4) :
    maskBit pOut.val.val.2 i = true ↔ maskBit pOut.val.val.1 i ≠ true := by
  constructor
  · exact pOut.val.property.1 i
  · exact output_nonretained_inactive pOut i

attribute [local instance] Classical.propDecidable

def curve (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (c : Code pOut pIn) : Residual pIn → AES.Word := fun i => c.val i.val

/-- One output zero, two input zeros, and this retained singleton total four. -/
theorem line_retained_coordinate_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (s : Retained pOut) :
    Function.Bijective (fun c : Code pOut pIn => curve pOut pIn c s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he : i = s.val := (singletonMask_bit s.val i).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, singletonMask_size]
    norm_num
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
      pOut.val.val.2 pIn.val.val.2 (singletonMask s.val) hr hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

def lineCoordinateEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 2)
    (s : Retained pOut) : Code pOut pIn ≃ AES.Word :=
  Equiv.ofBijective _ (line_retained_coordinate_bijective pOut pIn s)

def freeTupleEquiv (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) ≃ AES.Word where
  toFun w := w ⟨s, rfl⟩
  invFun v := fun _ => v
  left_inv w := by
    funext i
    have hi : i = ⟨s, rfl⟩ := Subtype.ext i.property
    rw [hi]
  right_inv _ := rfl

def lineRetainedFreeEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 2)
    (s : Retained pOut) :
    Code pOut pIn ≃ (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (lineCoordinateEquiv pOut pIn s).trans (freeTupleEquiv pOut s).symm

theorem lineRetainedFreeEquiv_apply (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (s : Retained pOut) (c : Code pOut pIn)
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    lineRetainedFreeEquiv pOut pIn s c i = curve pOut pIn c i.val := by
  change curve pOut pIn c s = curve pOut pIn c i.val
  rw [i.property]

theorem line_freeCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  simp only [FreeCoordinates, Fintype.card_subtype_eq]

theorem line_dependentCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i = s)) = 2 := by
  change Fintype.card {i : Retained pOut // ¬ i = s} = 2
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

/-- Every physical retained output pair parametrizes the actual plane. -/
theorem plane_retained_pair_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport e 3) (s : Retained pOut) :
    Function.Bijective (fun c : Code pOut pIn =>
      fun i : {i : Retained pOut // i ≠ s} => curve pOut pIn c i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 s
  have hp : maskSize pair = 2 :=
    DoubleUniformGeometry.retainedPairMask_size _ (retainedMask_size pOut) s
  have hr : MaskDisjoint pOut.val.val.2 pair := by
    intro i hi hpair
    exact pOut.val.property.1 i hi
      ((DoubleUniformGeometry.retainedPairMask_bit _ s i).mp hpair).1
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 + maskSize pair = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, hp]
    norm_num
  have hb : Function.Bijective (fun c : Code pOut pIn =>
      fun i : MaskCoordinates pair => wordMixAddEquiv.toAddMonoidHom c.val i.val) :=
    (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS pOut.val.val.2 pIn.val.val.2 pair hr hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  exact (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := AES.Word)
    pOut.val.val.1 s).bijective.comp hb

/-- The original residual singleton itself is the line's INPUT information set. -/
theorem line_residualTuple_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) : Function.Bijective (residualTuple pOut pIn) := by
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, residualMask_size]
    norm_num
  exact (RestrictedMDSCoordinates.input_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
      pIn.val.property.1 hsize).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem plane_residualTuple_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 3) : Function.Bijective (residualTuple pOut pIn) := by
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, residualMask_size]
    norm_num
  exact (RestrictedMDSCoordinates.input_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
      pIn.val.property.1 hsize).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

/-- Keep a real prescribed uniform leg with the original joint residual tuple.
The two disjoint labelled input masks, plus the two original zeros, total four. -/
def residualUniformEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 3)
    (s : SourceUniformPositions pIn) :
    Code pOut pIn ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hsu : MaskDisjoint pIn.val.val.1 (singletonMask s.val.val) := by
    intro i hi hs
    have he : i = s.val.val := (singletonMask_bit _ _).mp hs
    subst i
    exact s.val.property hi
  have hzu : MaskDisjoint pIn.val.val.2
      (maskUnion pIn.val.val.1 (singletonMask s.val.val)) := by
    intro i hi hu
    rw [maskUnion_bit, Bool.or_eq_true] at hu
    rcases hu with hu | hu
    · exact pIn.val.property.1 i hi hu
    · have he : i = s.val.val := (singletonMask_bit _ _).mp hu
      subst i
      exact s.property hi
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 + maskSize (singletonMask s.val.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, residualMask_size, singletonMask_size]
    norm_num
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hsu hzu hsize)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv s.val.val))

@[simp]
theorem residualUniformEquiv_fst (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 3) (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).1 = residualTuple pOut pIn c := rfl

@[simp]
theorem residualUniformEquiv_snd (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 3) (s : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn s c).2 = c.val s.val.val := rfl

end AESConcrete.WeightedThreeOutputGeometry
