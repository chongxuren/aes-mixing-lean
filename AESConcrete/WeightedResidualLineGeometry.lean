import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.IndexedTripleEnergy
import AESConcrete.ResidualIncidenceCoefficient

/-!
# Actual three-zero line with one or two residual input coordinates

Lemmas for (8,9) and (8,6). TwoResidualLine was a source layout template, not
an imported premise. Output type (2,2) has two output zeros; input
type (e,3) has one input zero. A retained output coordinate parametrizes the
actual line. Separately, an active input coordinate is an information set; a
nonempty residual tuple is injective. The two projection arguments must remain
separate when these types change.

Constructive AES10/14/16 with independent uniform retained round keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedResidualLineGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000

variable {e : Fin 5}

abbrev Retained (pOut : SelectedSupport 2 2) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport e 3) := MaskCoordinates pIn.val.val.1

/-- The first zero mask constrains outputs; the second constrains inputs. -/
abbrev LineCode (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

instance lineFintype (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3) :
    Fintype (LineCode pOut pIn) := by
  classical
  exact inferInstance

theorem retainedMask_size (pOut : SelectedSupport 2 2) :
    maskSize pOut.val.val.1 = 2 := by
  have hd := pOut.val.property.2
  norm_num at hd
  exact hd

theorem outputInactiveMask_size (pOut : SelectedSupport 2 2) :
    maskSize pOut.val.val.2 = 2 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 2 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport e 3) :
    maskSize pIn.val.val.2 = 1 := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + 3 = 4 at hp
  omega

theorem retainedCoordinates_card (pOut : SelectedSupport 2 2) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

--
theorem output_nonretained_inactive : ∀ (pOut : SelectedSupport 2 2) (i : Fin 4),
    maskBit pOut.val.val.1 i ≠ true → maskBit pOut.val.val.2 i = true := by decide

theorem output_inactive_iff_not_retained (pOut : SelectedSupport 2 2) (i : Fin 4) :
    maskBit pOut.val.val.2 i = true ↔ maskBit pOut.val.val.1 i ≠ true := by
  constructor
  · intro hi
    exact pOut.val.property.1 i hi
  · exact output_nonretained_inactive pOut i

-- Keep classical decidability after the finite support proofs above.
attribute [local instance] Classical.propDecidable

def curve (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (c : LineCode pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (c : LineCode pOut pIn) : Residual pIn → AES.Word := fun i => c.val i.val

/-- Two output zeros, one input zero and this one retained label total four. -/
theorem retained_coordinate_bijective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport e 3) (s : Retained pOut) :
    Function.Bijective (fun c : LineCode pOut pIn => curve pOut pIn c s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he : i = s.val := (singletonMask_bit s.val i).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
      pOut.val.val.2 pIn.val.val.2 (singletonMask s.val) hr hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom
          pOut.val.val.2 pIn.val.val.2).bijective)

def coordinateEquiv (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (s : Retained pOut) : LineCode pOut pIn ≃ AES.Word :=
  Equiv.ofBijective (fun c => curve pOut pIn c s)
    (retained_coordinate_bijective pOut pIn s)

theorem line_code_card (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (s : Retained pOut) : Fintype.card (LineCode pOut pIn) = Fintype.card AES.Word :=
  Fintype.card_congr (coordinateEquiv pOut pIn s)

/-- Only a singleton label tuple is reindexed; its physical label stays s. -/
def freeTupleEquiv (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) ≃ AES.Word where
  toFun w := w ⟨s, rfl⟩
  invFun v := fun _ => v
  left_inv w := by
    funext i
    have hi : i = ⟨s, rfl⟩ := Subtype.ext i.property
    rw [hi]
  right_inv v := rfl

def retainedFreeEquiv (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (s : Retained pOut) :
    LineCode pOut pIn ≃ (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (coordinateEquiv pOut pIn s).trans (freeTupleEquiv pOut s).symm

theorem retainedFreeEquiv_apply (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport e 3) (s : Retained pOut) (c : LineCode pOut pIn)
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    retainedFreeEquiv pOut pIn s c i = curve pOut pIn c i.val := by
  change curve pOut pIn c s = curve pOut pIn c i.val
  rw [i.property]

theorem freeCoordinates_card (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  simp only [FreeCoordinates, Fintype.card_subtype_eq]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  change Fintype.card {i : Retained pOut // ¬ i = s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

/-- Restriction of one arbitrary signed state amplitude introduces no q loss. -/
theorem line_subenergy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (G : AES.WordState → ℝ) :
    (∑ c : LineCode pOut pIn, G c.val ^ 2) ≤ ∑ x, G x ^ 2 :=
  IndexedTripleEnergy.restriction_energy_le (fun c : LineCode pOut pIn => c.val)
    (fun _ _ he => Subtype.ext he) G

/-- Input projection is proved independently of the retained-output projection.
The active label need only be disjoint from the original inactive input mask. -/
theorem active_input_coordinate_bijective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport e 3) (s : Fin 4)
    (hs : maskBit pIn.val.val.2 s ≠ true) :
    Function.Bijective (fun c : LineCode pOut pIn => c.val s) := by
  have hz : MaskDisjoint pIn.val.val.2 (singletonMask s) := by
    intro i hi hsingle
    have hi' : i = s := (singletonMask_bit s i).mp hsingle
    subst i
    exact hs hi
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize (singletonMask s) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s).bijective.comp
    ((RestrictedMDSCoordinates.input_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
      pOut.val.val.2 pIn.val.val.2 (singletonMask s) hz hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom
          pOut.val.val.2 pIn.val.val.2).bijective)

theorem residualCoordinates_card (pIn : SelectedSupport e 3) :
    Fintype.card (Residual pIn) = e.val := by
  simpa only [Residual, ← Nat.card_eq_fintype_card] using
    (maskCoordinates_card pIn.val.val.1).trans pIn.val.property.2

-- Editorial dependency: the uniform weights below will use this INPUT tuple
-- injection. Retained-output bijectivity does not supply it.
theorem residualTuple_injective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport e 3) (he : 1 ≤ e.val) :
    Function.Injective (residualTuple pOut pIn) := by
  haveI : Nonempty (Residual pIn) :=
    Fintype.card_pos_iff.mp (by rw [residualCoordinates_card]; omega)
  let s : Residual pIn := Classical.choice inferInstance
  have hs : maskBit pIn.val.val.2 s.val ≠ true := by
    intro hz
    exact pIn.val.property.1 s.val hz s.property
  intro c d hcd
  apply (active_input_coordinate_bijective pOut pIn s.val hs).1
  exact congrFun hcd s

/-- An arbitrary signed joint residual tuple has only subenergy on the line. -/
theorem residual_subenergy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (he : 1 ≤ e.val) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : LineCode pOut pIn, h (residualTuple pOut pIn c) ^ 2) ≤ ∑ u, h u ^ 2 :=
  IndexedTripleEnergy.restriction_energy_le (residualTuple pOut pIn)
    (residualTuple_injective pOut pIn he) h

end AESConcrete.WeightedResidualLineGeometry
