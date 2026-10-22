-- Source-only successor for job 15958825; signatures and physical model retained.
--
import AESConcrete.OmittedUniformTwoInputPushforward
import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.WordCrossZero
import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.MultiUniformExpansion
import AESConcrete.InvariantSubspaceFourier

/-!
# Original full physical geometry for (10,12)

Original output(2,4), input(3,4), empty inactive masks and literal J,E labels.
The full retained map has q^2-point fibers; it is NOT injective. Its full raw
source has q copies of the same signed joint three-word h, including h(0). The
residual-zero line supplies whole singleton-dependent Fourier surjectivity.
Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000
-- Bounded finite mask fact.
theorem complement_partition : ∀ E : Fin 16, maskSize E = 2 →
    ∀ a b : Fin 4, maskBit E a ≠ true → maskBit E b ≠ true → a ≠ b →
      ∀ i : Fin 4, maskBit (maskComplement E) i = true ↔ i = a ∨ i = b := by
  -- Use the complement's cardinality and the two distinct omitted labels;
  -- no whole-proposition Decidable instance or word-state computation is needed.
  intro E hE a b ha hb hab i
  let t : Finset (Fin 4) :=
    Finset.univ.filter (fun j => maskBit (maskComplement E) j)
  have ht : t.card = 2 := by
    change maskSize (maskComplement E) = 2
    rw [maskComplement_size, hE]
  have ha' : a ∈ t := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    rw [maskComplement_bit, Bool.eq_false_of_not_eq_true ha]
    rfl
  have hb' : b ∈ t := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ b, ?_⟩
    rw [maskComplement_bit, Bool.eq_false_of_not_eq_true hb]
    rfl
  have hsub : ({a, b} : Finset (Fin 4)) ⊆ t := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ha'
    · exact hb'
  have hpair : ({a, b} : Finset (Fin 4)) = t :=
    Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (ht.trans (Finset.card_pair hab).symm))
  have hi : i ∈ t ↔ i = a ∨ i = b := by
    rw [← hpair]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hi


attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 2 4) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 3 4) := MaskCoordinates pIn.val.val.1
abbrev InputOther (pIn : SelectedSupport 3 4) := OtherCoordinates pIn.val.val.1
abbrev Omitted (pOut : SelectedSupport 2 4) := OtherCoordinates pOut.val.val.1

theorem retainedMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.1 = 2 := pOut.val.property.2

theorem residualMask_size (pIn : SelectedSupport 3 4) :
    maskSize pIn.val.val.1 = 3 := pIn.val.property.2

theorem outputInactiveMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.2 = 0 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 4 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport 3 4) :
    maskSize pIn.val.val.2 = 0 := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + 4 = 4 at hp
  omega

theorem output_inactive_not (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pOut.val.val.2 i ≠ true := by
  intro hi
  have hc := Fintype.card_pos_iff.mpr
    (show Nonempty (MaskCoordinates pOut.val.val.2) from ⟨⟨i,hi⟩⟩)
  rw [maskCoordinates_card, outputInactiveMask_size] at hc
  omega

theorem input_inactive_not (pIn : SelectedSupport 3 4) (i : Fin 4) :
    maskBit pIn.val.val.2 i ≠ true := by
  intro hi
  have hc := Fintype.card_pos_iff.mpr
    (show Nonempty (MaskCoordinates pIn.val.val.2) from ⟨⟨i,hi⟩⟩)
  rw [maskCoordinates_card, inputInactiveMask_size] at hc
  omega

theorem retained_card (pOut : SelectedSupport 2 4) : Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem residual_card (pIn : SelectedSupport 3 4) : Fintype.card (Residual pIn) = 3 := by
  rw [maskCoordinates_card, residualMask_size]

theorem inputOther_card (pIn : SelectedSupport 3 4) : Fintype.card (InputOther pIn) = 1 := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, residualMask_size]

theorem omitted_card (pOut : SelectedSupport 2 4) : Fintype.card (Omitted pOut) = 2 := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, retainedMask_size]

def inputOtherEquiv (pIn : SelectedSupport 3 4) : InputOther pIn ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [inputOther_card]; simp)

def inputUniform (pIn : SelectedSupport 3 4) : InputOther pIn :=
  (inputOtherEquiv pIn).symm 0

theorem inputOther_eq (pIn : SelectedSupport 3 4) (i : InputOther pIn) :
    i = inputUniform pIn := by
  apply (inputOtherEquiv pIn).injective
  exact Subsingleton.elim _ _

def residualEquiv (pIn : SelectedSupport 3 4) : Residual pIn ≃ Fin 3 :=
  Fintype.equivOfCardEq (by rw [residual_card]; simp)

def residualFirst (pIn : SelectedSupport 3 4) : Residual pIn := (residualEquiv pIn).symm 0
def residualSecond (pIn : SelectedSupport 3 4) : Residual pIn := (residualEquiv pIn).symm 1

theorem residual_labels_ne (pIn : SelectedSupport 3 4) :
    (residualFirst pIn).val ≠ (residualSecond pIn).val := by
  intro he
  have hf : residualFirst pIn = residualSecond pIn := Subtype.ext he
  have h01 : (0 : Fin 3) = 1 := by
    simpa only [residualFirst, residualSecond, Equiv.apply_symm_apply] using
      congrArg (residualEquiv pIn) hf
  exact (by decide : (0 : Fin 3) ≠ 1) h01

def residualPairMask (pIn : SelectedSupport 3 4) : Fin 16 :=
  maskUnion (singletonMask (residualFirst pIn).val) (singletonMask (residualSecond pIn).val)

theorem residualPairMask_bit (pIn : SelectedSupport 3 4) (i : Fin 4) :
    maskBit (residualPairMask pIn) i = true ↔
      i = (residualFirst pIn).val ∨ i = (residualSecond pIn).val := by
  rw [residualPairMask, maskUnion_bit, Bool.or_eq_true,
    singletonMask_bit, singletonMask_bit]

theorem residualPairMask_size (pIn : SelectedSupport 3 4) :
    maskSize (residualPairMask pIn) = 2 := by
  have hd : MaskDisjoint (singletonMask (residualFirst pIn).val)
      (singletonMask (residualSecond pIn).val) := by
    intro i hi hj
    exact residual_labels_ne pIn
      (((singletonMask_bit _ _).mp hi).symm.trans ((singletonMask_bit _ _).mp hj))
  rw [residualPairMask, maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]

theorem residualPairMask_subset (pIn : SelectedSupport 3 4) (i : Fin 4)
    (hi : maskBit (residualPairMask pIn) i = true) : maskBit pIn.val.val.1 i = true := by
  rcases (residualPairMask_bit pIn i).mp hi with hi | hi
  · rw [hi]; exact (residualFirst pIn).property
  · rw [hi]; exact (residualSecond pIn).property

def omittedIndexEquiv (pOut : SelectedSupport 2 4) : Omitted pOut ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [omitted_card]; simp)

def omittedFirst (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 0

def omittedSecond (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 1

theorem omitted_labels_ne (pOut : SelectedSupport 2 4) :
    (omittedFirst pOut).val ≠ (omittedSecond pOut).val := by
  intro he
  have hf := congrArg (omittedIndexEquiv pOut) (Subtype.ext he)
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [omittedFirst, omittedSecond, Equiv.apply_symm_apply] using hf
  exact (by decide : (0 : Fin 2) ≠ 1) h01


theorem omitted_partition (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit (maskComplement pOut.val.val.1) i = true ↔
      i = (omittedFirst pOut).val ∨ i = (omittedSecond pOut).val :=
  complement_partition _ (retainedMask_size pOut) _ _
    (omittedFirst pOut).property (omittedSecond pOut).property (omitted_labels_ne pOut) i

theorem empty_disjoint (r : Fin 16) : MaskDisjoint 0 r := by
  intro i hi _
  exact (empty_mask_coordinate ⟨i,hi⟩).elim

def residualTuple (pIn : SelectedSupport 3 4) (x : AES.WordState) : Residual pIn → AES.Word :=
  fun i => x i.val

def retainedHom (pOut : SelectedSupport 2 4) : AES.WordState →+ (Retained pOut → AES.Word) where
  toFun x := fun i => wordMixAddEquiv x i.val
  map_zero' := by funext i; simp
  map_add' x y := by funext i; exact congrFun (wordMixAddEquiv.map_add x y) i.val

def stateKernel (pOut : SelectedSupport 2 4) (y : Retained pOut → AES.Word)
    (x : AES.WordState) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedHom pOut x i)

def fullCodeEquiv : AES.WordState ≃ ShortenedCode wordMixAddEquiv.toAddMonoidHom 0 0 where
  toFun x := ⟨x, by constructor <;> intro i hi <;>
    exact (empty_mask_coordinate ⟨i,hi⟩).elim⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- Exact two-word fibers of the full retained map; no injectivity claim. -/
def fullRetainedFiberParam (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4) :
    AES.WordState ≃ (MaskCoordinates (residualPairMask pIn) → AES.Word) ×
      (Retained pOut → AES.Word) :=
  fullCodeEquiv.trans ((graphEquiv wordMixAddEquiv.toAddMonoidHom 0 0).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS 0 0 pOut.val.val.1 (residualPairMask pIn)
      (empty_disjoint _) (empty_disjoint _)
      (by simp only [show maskSize (0 : Fin 16) = 0 by decide,
        retainedMask_size, residualPairMask_size])))

theorem fullRetainedFiberParam_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (x : AES.WordState) :
    (fullRetainedFiberParam pOut pIn x).2 = retainedHom pOut x := rfl

/-- J and the sole original input-uniform word parametrize the full source. -/
def residualUniformEquiv (pIn : SelectedSupport 3 4) :
    AES.WordState ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hd : MaskDisjoint pIn.val.val.1 (singletonMask (inputUniform pIn).val) := by
    intro i hi hu
    have he := (singletonMask_bit _ _).mp hu
    subst i
    exact (inputUniform pIn).property hi
  exact (fullCodeEquiv.trans ((graphEquiv wordMixAddEquiv.toAddMonoidHom 0 0).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS 0 0 pIn.val.val.1 (singletonMask (inputUniform pIn).val)
      hd (empty_disjoint _) (by simp only [show maskSize (0 : Fin 16) = 0 by decide,
        residualMask_size, singletonMask_size])))).trans
      (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv (inputUniform pIn).val))

theorem residualUniformEquiv_fst (pIn : SelectedSupport 3 4) (x : AES.WordState) :
    (residualUniformEquiv pIn x).1 = residualTuple pIn x := rfl

theorem residualUniformEquiv_snd (pIn : SelectedSupport 3 4) (x : AES.WordState) :
    (residualUniformEquiv pIn x).2 = x (inputUniform pIn).val := rfl

abbrev ResidualZero (pIn : SelectedSupport 3 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom 0 pIn.val.val.1

def translation (pIn : SelectedSupport 3 4) : ResidualZero pIn →+ AES.WordState :=
  (ShortenedWeightedGeometry.shortenedSubgroup wordMixAddEquiv.toAddMonoidHom 0 pIn.val.val.1).subtype

theorem amplitude_translation (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) (t : ResidualZero pIn) :
    h (residualTuple pIn (x + translation pIn t)) = h (residualTuple pIn x) := by
  apply congrArg h
  funext i
  change x i.val + t.val i.val = x i.val
  rw [t.property.2 i.val i.property, add_zero]

/-- Three original residual input zeros plus one physical output is an information set. -/
theorem translation_coordinate_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (s : Retained pOut) :
    Function.Bijective (fun t : ResidualZero pIn => retainedHom pOut (translation pIn t) s) := by
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS 0 pIn.val.val.1 (singletonMask s.val) (empty_disjoint _)
      (by rw [show maskSize (0 : Fin 16) = 0 by decide, residualMask_size,
        singletonMask_size])).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem translation_dependent_surjective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (s : Retained pOut) :
    Function.Surjective (fun t : ResidualZero pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        retainedHom pOut (translation pIn t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t : ResidualZero pIn => retainedHom pOut (translation pIn t))
    (translation_coordinate_bijective pOut pIn s).2

theorem freeCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  change Fintype.card {i : Retained pOut // i ≠ s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retained_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
  IndexedFourierSupport.dependentCoordinates_card s

end AESConcrete.TwoOmittedOneInputGeometry
