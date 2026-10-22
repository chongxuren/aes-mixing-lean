import AESConcrete.OmittedUniformTwoOutputEventGeometry
import AESConcrete.WeightedResidualLineGeometry

/-!
# Actual (1,3) input as a single event of the completed (1,4) input

The residual mask and every physical label are preserved. The completed input
has no inactive mask; the original inactive singleton becomes one of its three
uniform labels. Physical input states, rather than finite instances, are
transported explicitly. No energy or desired-bound premise occurs here.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

abbrev Retained (pOut : SelectedSupport 2 3) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 1 3) := MaskCoordinates pIn.val.val.1
abbrev SourceUniformPositions (pIn : SelectedSupport 1 3) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1
abbrev Code (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

set_option maxRecDepth 100000

-- Finite mask facts precede the classical predicate instance.
theorem completion_mask_facts : ∀ r : Fin 16,
    MaskDisjoint 0 r ∧ maskSize (0 : Fin 16) + 4 = 4 := by decide

theorem inactive_mask_singleton : ∀ (pIn : SelectedSupport 1 3) (i : Fin 4),
    maskBit pIn.val.val.2 i = true → pIn.val.val.2 = singletonMask i := by decide

attribute [local instance] Classical.propDecidable

/-- Only the input inactive mask changes; the original residual mask is literal. -/
def completeInput (pIn : SelectedSupport 1 3) : SelectedSupport 1 4 :=
  ⟨⟨(pIn.val.val.1, 0),
    ⟨(completion_mask_facts pIn.val.val.1).1, pIn.val.property.2⟩⟩,
    (completion_mask_facts pIn.val.val.1).2⟩

theorem completeInput_residual (pIn : SelectedSupport 1 3) :
    (completeInput pIn).val.val.1 = pIn.val.val.1 := rfl

theorem completeInput_inactive (pIn : SelectedSupport 1 3) :
    (completeInput pIn).val.val.2 = 0 := rfl

theorem residualMask_size (pIn : SelectedSupport 1 3) : maskSize pIn.val.val.1 = 1 := by
  exact pIn.val.property.2

theorem inactiveMask_size (pIn : SelectedSupport 1 3) : maskSize pIn.val.val.2 = 1 :=
  WeightedResidualLineGeometry.inputInactiveMask_size pIn

theorem inactivePositions_card (pIn : SelectedSupport 1 3) :
    Fintype.card (MaskCoordinates pIn.val.val.2) = 1 := by
  rw [maskCoordinates_card, inactiveMask_size]

theorem sourceUniformPositions_card (pIn : SelectedSupport 1 3) :
    Fintype.card (SourceUniformPositions pIn) = 2 := by
  rw [MultiUniformExpansion.uniformPositions_card _ _ pIn.val.property.1,
    inactiveMask_size, residualMask_size]

def inactiveIndexEquiv (pIn : SelectedSupport 1 3) :
    MaskCoordinates pIn.val.val.2 ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [inactivePositions_card, Fintype.card_fin])

def inactivePosition (pIn : SelectedSupport 1 3) : MaskCoordinates pIn.val.val.2 :=
  (inactiveIndexEquiv pIn).symm 0

def inactiveLabel (pIn : SelectedSupport 1 3) : Fin 4 := (inactivePosition pIn).val

theorem inactiveLabel_mem (pIn : SelectedSupport 1 3) :
    maskBit pIn.val.val.2 (inactiveLabel pIn) = true := (inactivePosition pIn).property

def completedInactive (pIn : SelectedSupport 1 3) :
    OmittedUniformTwoOutputGeometry.SourceUniformPositions (completeInput pIn) :=
  ⟨⟨inactiveLabel pIn, pIn.val.property.1 _ (inactiveLabel_mem pIn)⟩,
    OmittedUniformTwoOutputGeometry.input_inactive_not _ _⟩

def completedUniform (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn) :
    OmittedUniformTwoOutputGeometry.SourceUniformPositions (completeInput pIn) :=
  ⟨u.val, OmittedUniformTwoOutputGeometry.input_inactive_not _ _⟩

theorem completedUniform_injective (pIn : SelectedSupport 1 3) :
    Function.Injective (completedUniform pIn) := by
  intro u v huv
  exact Subtype.ext (Subtype.ext (congrArg (fun w :
    OmittedUniformTwoOutputGeometry.SourceUniformPositions (completeInput pIn) => w.val.val) huv))

theorem completedInactive_ne_uniform (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) : completedInactive pIn ≠ completedUniform pIn u := by
  intro he
  have hl := congrArg (fun w : OmittedUniformTwoOutputGeometry.SourceUniformPositions
    (completeInput pIn) => w.val.val) he
  change inactiveLabel pIn = u.val.val at hl
  apply u.property
  rw [← hl]
  exact inactiveLabel_mem pIn

theorem completed_singleMask (pIn : SelectedSupport 1 3) :
    OmittedUniformTwoOutputEventGeometry.singleMask (completedInactive pIn) = pIn.val.val.2 :=
  (inactive_mask_singleton pIn _ (inactiveLabel_mem pIn)).symm

/-- No signed-amplitude map is needed: the residual tuple type is unchanged. -/
theorem residual_tuple_type (pIn : SelectedSupport 1 3) :
    OmittedUniformTwoOutputGeometry.Residual (completeInput pIn) = Residual pIn := rfl

def baseCode (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (c : Code pOut pIn) : OmittedUniformTwoOutputGeometry.Code pOut (completeInput pIn) :=
  ⟨c.val, ⟨c.property.1, fun i hi =>
    (OmittedUniformTwoOutputGeometry.input_inactive_not (completeInput pIn) i hi).elim⟩⟩

def residualTuple (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (c : Code pOut pIn) : Residual pIn → AES.Word := fun i => c.val i.val

def bareKernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  OmittedUniformTwoOutputBareResponse.bareKernel pOut (completeInput pIn) y (baseCode pOut pIn c)

/-- The original physical code is the single original-inactive-label event. -/
def planeEventEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3) :
    Code pOut pIn ≃ OmittedUniformTwoOutputEventGeometry.EventCode pOut (completeInput pIn)
      (OmittedUniformTwoOutputEventGeometry.singleMask (completedInactive pIn)) where
  toFun c := ⟨c.val, by
    constructor
    · exact c.property.1
    · intro i hi
      rw [OmittedUniformTwoOutputEventGeometry.eventInputMask_eq, completed_singleMask] at hi
      exact c.property.2 i hi⟩
  invFun c := ⟨c.val, by
    constructor
    · exact c.property.1
    · intro i hi
      apply c.property.2 i
      rw [OmittedUniformTwoOutputEventGeometry.eventInputMask_eq, completed_singleMask]
      exact hi⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Additional zero restrictions preserve the exact original physical states. -/
def conditionedEventEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (t : Fin 16) :
    {c : Code pOut pIn // OmittedUniformTwoOutputEventGeometry.inputConditions t c.val} ≃
      OmittedUniformTwoOutputEventGeometry.EventCode pOut (completeInput pIn)
        (maskUnion pIn.val.val.2 t) where
  toFun c := ⟨c.val.val, by
    constructor
    · exact c.val.property.1
    · intro i hi
      rw [OmittedUniformTwoOutputEventGeometry.eventInputMask_eq, maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact c.val.property.2 i hi
      · exact c.property i hi⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · exact c.property.1
    · intro i hi
      apply c.property.2 i
      rw [OmittedUniformTwoOutputEventGeometry.eventInputMask_eq, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi⟩, by
    intro i hi
    apply c.property.2 i
    rw [OmittedUniformTwoOutputEventGeometry.eventInputMask_eq, maskUnion_bit, Bool.or_eq_true]
    exact Or.inr hi⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

def uniformIndexEquiv (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card, Fintype.card_fin])

def uniformFirst (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

theorem uniformFirst_ne_second (pIn : SelectedSupport 1 3) :
    uniformFirst pIn ≠ uniformSecond pIn := by
  intro he
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [uniformFirst, uniformSecond, Equiv.apply_symm_apply] using
      congrArg (uniformIndexEquiv pIn) he
  exact (by decide : (0 : Fin 2) ≠ 1) h01

end AESConcrete.OmittedUniformTwoInputGeometry
