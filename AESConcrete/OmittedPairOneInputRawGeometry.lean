import AESConcrete.OmittedPairOneInputPushforward
import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.WordCrossZero
import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.MultiUniformExpansion
import AESConcrete.InvariantSubspaceFourier

/-!
Lemmas for (10,9). The original one-input-zero domain has dimension three. Its
unchanged joint residual pair has q-fold multiplicity. Its retained output
pair has q-point fibers, explicitly parametrized by the original uniform input
word. Constructive fixed AES10/14/16 only; independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct reference.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedPairOneInputRawGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Retained (pOut : SelectedSupport 2 4) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 2 3) := MaskCoordinates pIn.val.val.1
abbrev SourceUniformPositions (pIn : SelectedSupport 2 3) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1
abbrev Code (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

def curve (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (c : Code pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (c : Code pOut pIn) : Residual pIn → AES.Word := fun i => c.val i.val

def retainedHom (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3) :
    Code pOut pIn →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 pIn.val.val.2 pOut.val.val.1

@[simp] theorem retainedHom_apply (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (c : Code pOut pIn) :
    retainedHom pOut pIn c = curve pOut pIn c := rfl

theorem retainedMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.1 = 2 := by
  have hd := pOut.val.property.2
  norm_num at hd
  exact hd

theorem residualMask_size (pIn : SelectedSupport 2 3) :
    maskSize pIn.val.val.1 = 2 := by
  have hd := pIn.val.property.2
  norm_num at hd
  exact hd

theorem outputInactiveMask_size (pOut : SelectedSupport 2 4) :
    maskSize pOut.val.val.2 = 0 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 4 = 4 at hp
  omega

theorem inputInactiveMask_size (pIn : SelectedSupport 2 3) :
    maskSize pIn.val.val.2 = 1 := by
  have hp := pIn.property
  change maskSize pIn.val.val.2 + 3 = 4 at hp
  omega

theorem output_inactive_not (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pOut.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pOut.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, outputInactiveMask_size] at hc
  omega

theorem retainedCoordinates_card (pOut : SelectedSupport 2 4) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem residualCoordinates_card (pIn : SelectedSupport 2 3) :
    Fintype.card (Residual pIn) = 2 := by
  rw [maskCoordinates_card, residualMask_size]

theorem sourceUniformPositions_card (pIn : SelectedSupport 2 3) :
    Fintype.card (SourceUniformPositions pIn) = 1 := by
  rw [MultiUniformExpansion.uniformPositions_card _ _ pIn.val.property.1,
    inputInactiveMask_size, residualMask_size]

/-- Input pair first, original uniform singleton second. -/
def residualUniformEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (u : SourceUniformPositions pIn) :
    Code pOut pIn ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hju : MaskDisjoint pIn.val.val.1 (singletonMask u.val.val) := by
    intro i hi hu
    have he : i = u.val.val := (singletonMask_bit _ _).mp hu
    subst i
    exact u.val.property hi
  have hzu : MaskDisjoint pIn.val.val.2
      (maskUnion pIn.val.val.1 (singletonMask u.val.val)) := by
    intro i hz hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hj | hu
    · exact pIn.val.property.1 i hz hj
    · have he := (singletonMask_bit _ _).mp hu
      subst i
      exact u.property hz
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 + maskSize (singletonMask u.val.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size,
      residualMask_size, singletonMask_size]
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hju hzu hs)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv u.val.val))

@[simp] theorem residualUniformEquiv_fst (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn u c).1 = residualTuple pOut pIn c := rfl

@[simp] theorem residualUniformEquiv_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (residualUniformEquiv pOut pIn u c).2 = c.val u.val.val := rfl

theorem full_amplitude_energy_at (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ r, h r ^ 2 := by
  have he := (residualUniformEquiv pOut pIn u).sum_comp
    (fun ru : (Residual pIn → AES.Word) × AES.Word => h ru.1 ^ 2)
  change (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
    ∑ ru : (Residual pIn → AES.Word) × AES.Word, h ru.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem full_amplitude_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ r, h r ^ 2 := by
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  exact full_amplitude_energy_at pOut pIn (Classical.choice inferInstance) h

/-- The exact original source dimension is three word coordinates. -/
theorem code_card_at (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (u : SourceUniformPositions pIn) :
    Fintype.card (Code pOut pIn) = Fintype.card AES.Word ^ 3 := by
  calc
    _ = Fintype.card ((Residual pIn → AES.Word) × AES.Word) :=
      Fintype.card_congr (residualUniformEquiv pOut pIn u)
    _ = _ := by
      rw [Fintype.card_prod, Fintype.card_fun, residualCoordinates_card]
      -- Jobs 15958825/15958974 exhausted concrete-card memory/recursion.
      -- Prove the identity with a variable before instantiating the word card.
      have hpow (q : ℕ) : q ^ 2 * q = q ^ 3 := by
        exact (pow_succ q 2).symm
      exact hpow (Fintype.card AES.Word)

/-- mixedSplitEquiv returns INPUT first and OUTPUT second. No injection is used. -/
def retainedFiberParam (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (u : SourceUniformPositions pIn) : Code pOut pIn ≃ AES.Word × (Retained pOut → AES.Word) := by
  have hz : MaskDisjoint pIn.val.val.2 (singletonMask u.val.val) := by
    intro i hi hu
    have he := (singletonMask_bit _ _).mp hu
    subst i
    exact u.property hi
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 + maskSize (singletonMask u.val.val) = 4 := by
    rw [outputInactiveMask_size, inputInactiveMask_size,
      retainedMask_size, singletonMask_size]
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ pOut.val.property.1 hz hs)).trans
        (Equiv.prodCongr (singletonTupleEquiv u.val.val) (Equiv.refl _))

@[simp] theorem retainedFiberParam_fst (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (retainedFiberParam pOut pIn u c).1 = c.val u.val.val := rfl

@[simp] theorem retainedFiberParam_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn) (c : Code pOut pIn) :
    (retainedFiberParam pOut pIn u c).2 = retainedHom pOut pIn c := rfl

def retainedFiberEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (u : SourceUniformPositions pIn) (z : Retained pOut → AES.Word) :
    {c : Code pOut pIn // retainedHom pOut pIn c = z} ≃ AES.Word :=
  OmittedPairOneInputPushforward.fiberEquiv (retainedHom pOut pIn)
    (retainedFiberParam pOut pIn u) (retainedFiberParam_snd pOut pIn u) z

theorem retained_fiber_card (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (u : SourceUniformPositions pIn) (z : Retained pOut → AES.Word) :
    Fintype.card {c : Code pOut pIn // retainedHom pOut pIn c = z} =
      Fintype.card AES.Word := Fintype.card_congr (retainedFiberEquiv pOut pIn u z)

/-- The original input zero AND BOTH original residual zeros; free original u. -/
abbrev ResidualZero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2
    (maskUnion pIn.val.val.2 pIn.val.val.1)

def translation (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3) :
    ResidualZero pOut pIn →+ Code pOut pIn where
  toFun t := ⟨t.val, t.property.1, by
    intro i hi
    apply t.property.2 i
    rw [maskUnion_bit, Bool.or_eq_true]
    exact Or.inl hi⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

@[simp] theorem translation_residual_zero (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (t : ResidualZero pOut pIn) (i : Residual pIn) :
    (translation pOut pIn t).val i.val = 0 := by
  apply t.property.2 i.val
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inr i.property

theorem amplitude_translation (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) (t : ResidualZero pOut pIn) :
    h (residualTuple pOut pIn (c + translation pOut pIn t)) =
      h (residualTuple pOut pIn c) := by
  apply congrArg h
  funext i
  change c.val i.val + (translation pOut pIn t).val i.val = c.val i.val
  rw [translation_residual_zero, add_zero]

theorem translation_coordinate_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (s : Retained pOut) :
    Function.Bijective (fun t : ResidualZero pOut pIn =>
      retainedHom pOut pIn (translation pOut pIn t) s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi _
    exact (output_inactive_not pOut i hi).elim
  have hs : maskSize pOut.val.val.2 + maskSize (maskUnion pIn.val.val.2 pIn.val.val.1) +
      maskSize (singletonMask s.val) = 4 := by
    rw [maskUnion_size _ _ pIn.val.property.1, outputInactiveMask_size,
      inputInactiveMask_size, residualMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _ hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem translation_dependent_surjective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (s : Retained pOut) :
    Function.Surjective (fun t : ResidualZero pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        retainedHom pOut pIn (translation pOut pIn t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t : ResidualZero pOut pIn => retainedHom pOut pIn (translation pOut pIn t))
    (translation_coordinate_bijective pOut pIn s).2

theorem freeCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  change Fintype.card {i : Retained pOut // i ≠ s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
  IndexedFourierSupport.dependentCoordinates_card s
end AESConcrete.OmittedPairOneInputRawGeometry
