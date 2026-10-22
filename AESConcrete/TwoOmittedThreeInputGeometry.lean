--
--
import AESConcrete.TwoOmittedOutputRawInputEventEnergy
import AESConcrete.OmittedUniformTwoOutputResponseEnergy

/-!
# Original physical geometry for cell (10,7)

The four included TwoOmittedOutputRaw modules supply their own proofs. The
(9,7) family is used at its literal interfaces. Both original inactive masks
are empty. Every response keeps the original retained mask E, residual mask J,
and arbitrary signed tuple h including h(0). The full cancellation uses J plus
ONE extra uniform input, giving 0+0+2+2=4. No false bijection using only J and
E is asserted.

Constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedThreeInputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 2 4) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 1 4) := MaskCoordinates pIn.val.val.1
abbrev SourceUniformPositions (pIn : SelectedSupport 1 4) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

theorem retainedMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.1 = 2 := pOut.val.property.2

theorem residualMask_size (pIn : SelectedSupport 1 4) :
    maskSize pIn.val.val.1 = 1 := pIn.val.property.2

theorem retainedCoordinates_card (pOut : SelectedSupport 2 4) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem residualCoordinates_card (pIn : SelectedSupport 1 4) :
    Fintype.card (Residual pIn) = 1 := by
  rw [maskCoordinates_card, residualMask_size]

theorem outputInactiveMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.2 = 0 := TwoOmittedOutputRawGeometry.outputInactiveMask_size pOut

theorem output_inactive_not (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pOut.val.val.2 i ≠ true := by
  intro hi
  have hc := Fintype.card_pos_iff.mpr (show Nonempty (MaskCoordinates pOut.val.val.2)
    from ⟨⟨i, hi⟩⟩)
  rw [maskCoordinates_card, outputInactiveMask_size] at hc
  omega

theorem input_inactive_not (pIn : SelectedSupport 1 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := TripleUniformSource.inactiveLabel_not pIn i

theorem sourceUniformPositions_card (pIn : SelectedSupport 1 4) :
    Fintype.card (SourceUniformPositions pIn) = 3 :=
  OmittedUniformTwoOutputGeometry.sourceUniformPositions_card pIn

def residualTuple (pIn : SelectedSupport 1 4) (x : AES.WordState) :
    Residual pIn → AES.Word := fun i => x i.val

def stateKernel (pOut : SelectedSupport 2 4) (y : Retained pOut → AES.Word)
    (x : AES.WordState) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)

abbrev normalizedSource := OmittedUniformTwoOutputSplit.normalizedSource

theorem normalizedSource_energy (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 :=
  OmittedUniformTwoOutputSplit.normalizedSource_energy pIn h

theorem uniform_labels_ne {pIn : SelectedSupport 1 4}
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) : u.val.val ≠ v.val.val := by
  intro he
  exact huv (Subtype.ext (Subtype.ext he))

/-- Add one original input-zero event, retaining J literally. -/
def inputZero (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn) :
    SelectedSupport 1 3 :=
  ⟨⟨(pIn.val.val.1, singletonMask u.val.val), ⟨by
    intro i hi hJ
    have he := (singletonMask_bit u.val.val i).mp hi
    subst i
    exact u.val.property hJ, pIn.val.property.2⟩⟩, by rw [singletonMask_size]; norm_num⟩

def remainingUniform (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn)
    (huv : u ≠ v) : TwoOmittedOutputRawGeometry.SourceUniformPositions (inputZero pIn u) :=
  ⟨v.val, by
    intro hi
    exact uniform_labels_ne u v huv ((singletonMask_bit _ _).mp hi).symm⟩

theorem remainingUniform_ne (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    remainingUniform pIn u v huv ≠ remainingUniform pIn u w huw := by
  intro he
  apply hvw
  apply Subtype.ext
  exact congrArg
    (fun z : TwoOmittedOutputRawGeometry.SourceUniformPositions (inputZero pIn u) => z.val) he

def extendedResidualMask (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn) :
    Fin 16 := maskUnion pIn.val.val.1 (singletonMask u.val.val)

theorem extendedResidualMask_size (pIn : SelectedSupport 1 4)
    (u : SourceUniformPositions pIn) : maskSize (extendedResidualMask pIn u) = 2 := by
  have hd : MaskDisjoint pIn.val.val.1 (singletonMask u.val.val) := by
    intro i hJ hu
    have he := (singletonMask_bit u.val.val i).mp hu
    subst i
    exact u.val.property hJ
  rw [extendedResidualMask, maskUnion_size _ _ hd, residualMask_size, singletonMask_size]

def residualInExtended (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (i : Residual pIn) : MaskCoordinates (extendedResidualMask pIn u) :=
  ⟨i.val, by rw [extendedResidualMask, maskUnion_bit, Bool.or_eq_true]; exact Or.inl i.property⟩

/-- Both original zero masks are empty: physical states and original Code agree. -/
def fullCodeEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4) :
    AES.WordState ≃ ShortenedCode wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 where
  toFun x := ⟨x, by
    constructor
    · intro i hi
      exact (output_inactive_not pOut i hi).elim
    · intro i hi
      exact (input_inactive_not pIn i hi).elim⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def fullMixedEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u : SourceUniformPositions pIn) :
    AES.WordState ≃ (MaskCoordinates (extendedResidualMask pIn u) → AES.Word) ×
      (Retained pOut → AES.Word) :=
  (fullCodeEquiv pOut pIn).trans
    ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
      (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
        wordMixAddEquiv_zeroMDS pOut.val.val.2 pIn.val.val.2 pOut.val.val.1
        (extendedResidualMask pIn u) pOut.val.property.1
        (by intro i hi _; exact input_inactive_not pIn i hi)
        (by rw [outputInactiveMask_size, TripleUniformSource.inactiveMask_size,
                retainedMask_size, extendedResidualMask_size])))

theorem fullMixedEquiv_fst (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u : SourceUniformPositions pIn) (x : AES.WordState) :
    (fullMixedEquiv pOut pIn u x).1 = fun i => x i.val := rfl

theorem fullMixedEquiv_snd (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u : SourceUniformPositions pIn) (x : AES.WordState) :
    (fullMixedEquiv pOut pIn u x).2 = fun i => wordMixAddEquiv x i.val := rfl

def extendedAmplitude (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ)
    (z : MaskCoordinates (extendedResidualMask pIn u) → AES.Word) : ℝ :=
  h (fun i => z (residualInExtended pIn u i))

theorem fullMixedEquiv_symm_amplitude (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ)
    (z : MaskCoordinates (extendedResidualMask pIn u) → AES.Word)
    (t : Retained pOut → AES.Word) :
    h (residualTuple pIn ((fullMixedEquiv pOut pIn u).symm (z,t))) =
      extendedAmplitude pIn u h z := by
  apply congrArg h
  funext i
  exact congrFun (congrArg Prod.fst
    ((fullMixedEquiv pOut pIn u).apply_symm_apply (z,t))) (residualInExtended pIn u i)

theorem fullMixedEquiv_symm_kernel (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (z : MaskCoordinates (extendedResidualMask pIn u) → AES.Word)
    (t y : Retained pOut → AES.Word) :
    stateKernel pOut y ((fullMixedEquiv pOut pIn u).symm (z,t)) =
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (t i) := by
  have he := congrArg Prod.snd ((fullMixedEquiv pOut pIn u).apply_symm_apply (z,t))
  unfold stateKernel
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun v => residualMatrix AES.wordSuperboxKernel 0 (y i) v) (congrFun he i)

def bareResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (fun x => h (residualTuple pIn x)) (stateKernel pOut)

theorem bareResponse_factorization (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    bareResponse pOut pIn h y = (∑ z, extendedAmplitude pIn u h z) *
      ∑ t : Retained pOut → AES.Word,
        ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (t i) := by
  unfold bareResponse WeightedResponse.rawResponse
  rw [← (fullMixedEquiv pOut pIn u).symm.sum_comp
    (fun x => h (residualTuple pIn x) * stateKernel pOut y x), Fintype.sum_prod_type]
  simp_rw [fullMixedEquiv_symm_amplitude, fullMixedEquiv_symm_kernel]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  exact (Finset.mul_sum _ _ _).symm

theorem bareResponse_eq_zero (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    bareResponse pOut pIn h = 0 := by
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  let u : SourceUniformPositions pIn := Classical.choice inferInstance
  funext y
  change bareResponse pOut pIn h y = (0 : ℝ)
  rw [bareResponse_factorization pOut pIn u h y,
    TwoOmittedOutputRawResponse.retainedResidual_sum_zero, mul_zero]

end AESConcrete.TwoOmittedThreeInputGeometry
