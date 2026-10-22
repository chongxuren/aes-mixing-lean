import AESConcrete.WeightedThreeOutputGeometry
import AESConcrete.InvariantSubspaceFourier

/-!
# Actual output-zero code with one residual and three input uniforms

Geometry for (11,7). The Code, Retained, Residual and SourceUniformPositions
types are the existing WeightedThreeOutputGeometry types at output (3,3) and
input (1,4). The input inactive mask has size zero. The original residual and
two distinct original uniform input labels form an information set, with
multiplicity exactly q^2.

The residual-zero translation space is an actual ShortenedCode plane. Its
projection onto the entire retained output pair is bijective by the mixed MDS
information-set equality 1+1+2=4. Surjectivity of a singleton is not used to
infer joint surjectivity. No event, normalized response or physical cap is
here.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and the ordered-distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeUniformThreeOutputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 3 3) :=
  WeightedThreeOutputGeometry.Retained pOut

abbrev Residual (pIn : SelectedSupport 1 4) :=
  WeightedThreeOutputGeometry.Residual pIn

abbrev SourceUniformPositions (pIn : SelectedSupport 1 4) :=
  WeightedThreeOutputGeometry.SourceUniformPositions pIn

abbrev Code (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :=
  WeightedThreeOutputGeometry.Code pOut pIn

def curve (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  WeightedThreeOutputGeometry.curve pOut pIn c

def residualTuple (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) : Residual pIn → AES.Word :=
  WeightedThreeOutputGeometry.residualTuple pOut pIn c

theorem retainedCoordinates_card (pOut : SelectedSupport 3 3) :
    Fintype.card (Retained pOut) = 3 :=
  WeightedThreeOutputGeometry.retainedCoordinates_card pOut

theorem residualCoordinates_card (pIn : SelectedSupport 1 4) :
    Fintype.card (Residual pIn) = 1 := by
  rw [maskCoordinates_card, WeightedThreeOutputGeometry.residualMask_size]
  norm_num

theorem sourceUniformPositions_card (pIn : SelectedSupport 1 4) :
    Fintype.card (SourceUniformPositions pIn) = 3 := by
  simpa using WeightedThreeOutputGeometry.sourceUniformPositions_card pIn

theorem inputInactiveMask_size (pIn : SelectedSupport 1 4) :
    maskSize pIn.val.val.2 = 0 := by
  simpa using WeightedThreeOutputGeometry.inputInactiveMask_size pIn

theorem input_inactive_not (pIn : SelectedSupport 1 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pIn.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inputInactiveMask_size] at hc
  omega

/-- Actual additive restriction to the three retained physical output labels. -/
def retainedHom (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :
    Code pOut pIn →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 pIn.val.val.2 pOut.val.val.1

@[simp]
theorem retainedHom_apply (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) (i : Retained pOut) :
    retainedHom pOut pIn c i = curve pOut pIn c i := rfl

theorem retainedHom_bijective (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :
    Function.Bijective (retainedHom pOut pIn) := by
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size, inputInactiveMask_size,
      WeightedThreeOutputGeometry.retainedMask_size]
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pOut.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem retainedHom_injective (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :
    Function.Injective (retainedHom pOut pIn) := (retainedHom_bijective pOut pIn).1

/-- Actual output-zero and original-residual-input-zero translation plane. -/
abbrev ResidualZero (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.1

/-- Include the plane without changing its physical source state. -/
def translation (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) :
    ResidualZero pOut pIn →+ Code pOut pIn where
  toFun t := ⟨t.val, t.property.1, by
    intro i hi
    exact (input_inactive_not pIn i hi).elim⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

@[simp]
theorem translation_residual_zero (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (t : ResidualZero pOut pIn) (i : Residual pIn) :
    (translation pOut pIn t).val i.val = 0 := t.property.2 i.val i.property

theorem amplitude_translation (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn)
    (t : ResidualZero pOut pIn) :
    h (residualTuple pOut pIn (c + translation pOut pIn t)) =
      h (residualTuple pOut pIn c) := by
  apply congrArg h
  funext i
  change c.val i.val + t.val i.val = c.val i.val
  rw [t.property.2 i.val i.property, add_zero]

/-- Joint projection of the translation plane onto both dependent output labels. -/
theorem translation_pair_bijective
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) (s : Retained pOut) :
    Function.Bijective (fun t : ResidualZero pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i = s) =>
        retainedHom pOut pIn (translation pOut pIn t) i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 s
  have hp : maskSize pair = 2 :=
    DoubleUniformGeometry.retainedPairMask_size _
      (WeightedThreeOutputGeometry.retainedMask_size pOut) s
  have hr : MaskDisjoint pOut.val.val.2 pair := by
    intro i hi hj
    exact pOut.val.property.1 i hi
      ((DoubleUniformGeometry.retainedPairMask_bit _ s i).mp hj).1
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.1 + maskSize pair = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size,
      WeightedThreeOutputGeometry.residualMask_size, hp]
    norm_num
  have hb : Function.Bijective (fun t : ResidualZero pOut pIn =>
      fun i : MaskCoordinates pair => wordMixAddEquiv.toAddMonoidHom t.val i.val) :=
    (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS pOut.val.val.2 pIn.val.val.1 pair hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  exact (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := AES.Word)
    pOut.val.val.1 s).bijective.comp hb

theorem translation_dependent_surjective
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4) (s : Retained pOut) :
    Function.Surjective (fun t : ResidualZero pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i = s) =>
        retainedHom pOut pIn (translation pOut pIn t) i.val) :=
  (translation_pair_bijective pOut pIn s).2

section UniformPair
variable {pIn : SelectedSupport 1 4}

theorem uniform_labels_ne (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    u.val.val ≠ v.val.val := by
  intro he
  apply huv
  exact Subtype.ext (Subtype.ext he)

/-- Two distinct original uniform input labels, with no coordinate substitution. -/
def uniformPairMask (u v : SourceUniformPositions pIn) : Fin 16 :=
  maskUnion (singletonMask u.val.val) (singletonMask v.val.val)

theorem uniformPairMask_size (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    maskSize (uniformPairMask u v) = 2 := by
  have hd : MaskDisjoint (singletonMask u.val.val) (singletonMask v.val.val) := by
    intro i hi hj
    apply uniform_labels_ne u v huv
    exact ((singletonMask_bit u.val.val i).mp hi).symm.trans
      ((singletonMask_bit v.val.val i).mp hj)
  rw [uniformPairMask, maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]

theorem uniformPairMask_residual_disjoint (u v : SourceUniformPositions pIn) :
    MaskDisjoint pIn.val.val.1 (uniformPairMask u v) := by
  intro i hi hu
  rw [uniformPairMask, maskUnion_bit, Bool.or_eq_true] at hu
  rcases hu with hu | hu
  · have he : i = u.val.val := (singletonMask_bit u.val.val i).mp hu
    subst i
    exact u.val.property hi
  · have he : i = v.val.val := (singletonMask_bit v.val.val i).mp hu
    subst i
    exact v.val.property hi

end UniformPair

/-- The original residual and two original uniforms form the input information set. -/
def residualUniformEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    Code pOut pIn ≃
      (Residual pIn → AES.Word) × (MaskCoordinates (uniformPairMask u v) → AES.Word) := by
  have hzu : MaskDisjoint pIn.val.val.2
      (maskUnion pIn.val.val.1 (uniformPairMask u v)) := by
    intro i hi _
    exact (input_inactive_not pIn i hi).elim
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 + maskSize (uniformPairMask u v) = 4 := by
    rw [WeightedThreeOutputGeometry.outputInactiveMask_size, inputInactiveMask_size,
      WeightedThreeOutputGeometry.residualMask_size, uniformPairMask_size u v huv]
    norm_num
  exact (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ (uniformPairMask_residual_disjoint u v) hzu hsize)

@[simp]
theorem residualUniformEquiv_fst (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn u v huv c).1 = residualTuple pOut pIn c := rfl

@[simp]
theorem residualUniformEquiv_snd (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (c : Code pOut pIn)
    (i : MaskCoordinates (uniformPairMask u v)) :
    (residualUniformEquiv pOut pIn u v huv c).2 i = c.val i.val := rfl

/-- Each original residual has exactly q^2 unweighted code states. -/
theorem full_amplitude_energy_at (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) ^ 2 * ∑ w, h w ^ 2 := by
  have he := (residualUniformEquiv pOut pIn u v huv).sum_comp
    (fun uw : (Residual pIn → AES.Word) ×
      (MaskCoordinates (uniformPairMask u v) → AES.Word) => h uw.1 ^ 2)
  change (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
    ∑ uw : (Residual pIn → AES.Word) ×
      (MaskCoordinates (uniformPairMask u v) → AES.Word), h uw.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_fun, maskCoordinates_card, uniformPairMask_size u v huv, Nat.cast_pow]
  exact (Finset.mul_sum _ _ _).symm

theorem full_amplitude_energy (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) ^ 2 * ∑ w, h w ^ 2 := by
  let e : SourceUniformPositions pIn ≃ Fin 3 :=
    Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)
  have huv : e.symm 0 ≠ e.symm 1 := by
    intro hh
    have hf : (0 : Fin 3) = 1 := by
      simpa only [Equiv.apply_symm_apply] using congrArg e hh
    exact (by decide : (0 : Fin 3) ≠ 1) hf
  exact full_amplitude_energy_at pOut pIn (e.symm 0) (e.symm 1) huv h

theorem freeCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 :=
  WeightedThreeOutputGeometry.line_freeCoordinates_card pOut s

theorem dependentCoordinates_card (pOut : SelectedSupport 3 3) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i = s)) = 2 :=
  WeightedThreeOutputGeometry.line_dependentCoordinates_card pOut s

end AESConcrete.ThreeUniformThreeOutputGeometry
