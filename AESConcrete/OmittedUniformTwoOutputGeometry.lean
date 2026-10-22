import AESConcrete.RestrictedMDSCoordinates
import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.WordCrossZero
import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.MultiUniformExpansion

/-!
# Mixed information set for two retained outputs and one original residual

Output support is (2,3), input support is (1,4). Code is the actual
ShortenedCode with the original output-zero mask and original input-zero mask.
The input-zero mask has size zero; the output-zero mask has size one.

The original residual singleton and the two retained physical outputs form a
mixed information set: 1+0+2+1=4. Its equivalence preserves both restrictions.
No input or omitted-output uniform weight, selected minor, response estimate,
physical cap or certificate is supplied by this geometry module.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoOutputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 2 3) := MaskCoordinates pOut.val.val.1

abbrev Residual (pIn : SelectedSupport 1 4) := MaskCoordinates pIn.val.val.1

abbrev SourceUniformPositions (pIn : SelectedSupport 1 4) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

/-- The first mask is on outputs, the second on inputs. -/
abbrev Code (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

def curve (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) : Residual pIn → AES.Word :=
  fun i => c.val i.val

theorem retainedMask_size (pOut : SelectedSupport 2 3) :
    maskSize pOut.val.val.1 = 2 := by
  have hd := pOut.val.property.2
  norm_num at hd
  exact hd

theorem retainedCoordinates_card (pOut : SelectedSupport 2 3) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem residualMask_size (pIn : SelectedSupport 1 4) :
    maskSize pIn.val.val.1 = 1 := by
  have hd := pIn.val.property.2
  norm_num at hd
  exact hd

theorem residualCoordinates_card (pIn : SelectedSupport 1 4) :
    Fintype.card (Residual pIn) = 1 := by
  rw [maskCoordinates_card, residualMask_size]

theorem outputInactiveMask_size (pOut : SelectedSupport 2 3) :
    maskSize pOut.val.val.2 = 1 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 3 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport 1 4) :
    maskSize pIn.val.val.2 = 0 := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + 4 = 4 at hp
  omega

theorem input_inactive_not (pIn : SelectedSupport 1 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pIn.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inputInactiveMask_size] at hc
  omega

theorem sourceUniformPositions_card (pIn : SelectedSupport 1 4) :
    Fintype.card (SourceUniformPositions pIn) = 3 := by
  rw [MultiUniformExpansion.uniformPositions_card _ _ pIn.val.property.1,
    inputInactiveMask_size, residualMask_size]

theorem mixed_information_size (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4) :
    maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 + maskSize pIn.val.val.1 = 4 := by
  rw [outputInactiveMask_size, inputInactiveMask_size, retainedMask_size, residualMask_size]

/-- Original residual input and original retained outputs jointly parametrize Code. -/
def residualRetainedEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4) :
    Code pOut pIn ≃ (Residual pIn → AES.Word) × (Retained pOut → AES.Word) :=
  (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS pOut.val.val.2 pIn.val.val.2 pOut.val.val.1 pIn.val.val.1
      pOut.val.property.1 pIn.val.property.1 (mixed_information_size pOut pIn))

@[simp]
theorem residualRetainedEquiv_fst (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) :
    (residualRetainedEquiv pOut pIn c).1 = residualTuple pOut pIn c := rfl

@[simp]
theorem residualRetainedEquiv_snd (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) :
    (residualRetainedEquiv pOut pIn c).2 = curve pOut pIn c := rfl

theorem residualRetainedEquiv_symm_residual
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (u : Residual pIn → AES.Word) (x : Retained pOut → AES.Word) :
    residualTuple pOut pIn ((residualRetainedEquiv pOut pIn).symm (u, x)) = u :=
  congrArg Prod.fst ((residualRetainedEquiv pOut pIn).apply_symm_apply (u, x))

theorem residualRetainedEquiv_symm_curve
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (u : Residual pIn → AES.Word) (x : Retained pOut → AES.Word) :
    curve pOut pIn ((residualRetainedEquiv pOut pIn).symm (u, x)) = x :=
  congrArg Prod.snd ((residualRetainedEquiv pOut pIn).apply_symm_apply (u, x))

end AESConcrete.OmittedUniformTwoOutputGeometry
