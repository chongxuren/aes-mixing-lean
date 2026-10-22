import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.InvariantSubspaceFourier
import AESConcrete.TripleUniformSource

/-!
# Actual plane, input-zero lines and residual-zero translations for (8,7)

The output has two original residual labels and two zero labels; the input has
one original residual label and three prescribed uniform labels. The full
code, its input-zero lines, its retained additive embedding and its residual-
zero translation inclusion are separate objects and interfaces.

Fixed constructive AES10/14/16 with independent uniform retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoOutputThreeUniformGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry
  (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.TripleUniformSource
  (SourceUniformPositions residualLabel residualLabel_mem)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000

abbrev Retained (pOut : SelectedSupport 2 2) := MaskCoordinates pOut.val.val.1

theorem retainedMask_size (pOut : SelectedSupport 2 2) : maskSize pOut.val.val.1 = 2 :=
  pOut.val.property.2

theorem outputInactiveMask_size (pOut : SelectedSupport 2 2) :
    maskSize pOut.val.val.2 = 2 := by
  have hp := pOut.property
  change maskSize pOut.val.val.2 + 2 = 4 at hp
  omega

theorem retainedCoordinates_card (pOut : SelectedSupport 2 2) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

-- Keep finite decidability before the local classical instance.
theorem empty_mask_no_label : ∀ i : Fin 4, maskBit (0 : Fin 16) i ≠ true := by decide

theorem output_nonretained_inactive : ∀ (pOut : SelectedSupport 2 2) (i : Fin 4),
    maskBit pOut.val.val.1 i ≠ true → maskBit pOut.val.val.2 i = true := by decide

theorem output_inactive_iff_not_retained (pOut : SelectedSupport 2 2) (i : Fin 4) :
    maskBit pOut.val.val.2 i = true ↔ maskBit pOut.val.val.1 i ≠ true :=
  ⟨pOut.val.property.1 i, output_nonretained_inactive pOut i⟩

attribute [local instance] Classical.propDecidable

theorem empty_mask_disjoint (m : Fin 16) : MaskDisjoint 0 m := by
  intro i hi _
  exact empty_mask_no_label i hi

def uniformIndexEquiv (pIn : SelectedSupport 1 4) : Fin 3 ≃ SourceUniformPositions pIn :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, TripleUniformSource.sourceUniformPositions_card])

theorem uniform_labels_ne (pIn : SelectedSupport 1 4)
    (j k : SourceUniformPositions pIn) (hjk : j ≠ k) : j.val.val ≠ k.val.val := by
  intro he
  exact hjk (Subtype.ext (Subtype.ext he))

theorem uniform_ne_residual (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) :
    j.val.val ≠ residualLabel pIn := by
  intro he
  apply j.val.property
  rw [he]
  exact residualLabel_mem pIn

/-- Actual two-output-zero additive plane; there are no inactive input labels. -/
abbrev Plane (pOut : SelectedSupport 2 2) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 0

/-- One further original prescribed uniform input is zero. -/
abbrev Line (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (singletonMask j.val.val)

def retainedEmbedding (pOut : SelectedSupport 2 2) : Plane pOut →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 0 pOut.val.val.1

theorem retainedEmbedding_bijective (pOut : SelectedSupport 2 2) :
    Function.Bijective (retainedEmbedding pOut) := by
  have hs : maskSize pOut.val.val.2 + maskSize (0 : Fin 16) + maskSize pOut.val.val.1 = 4 := by
    rw [outputInactiveMask_size, retainedMask_size]
    rfl
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pOut.val.property.1 hs).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem retainedEmbedding_injective (pOut : SelectedSupport 2 2) :
    Function.Injective (retainedEmbedding pOut) := (retainedEmbedding_bijective pOut).1

def lineCurve (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) (c : Line pOut pIn j) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def lineRestrictionEquiv (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) :
    {c : Plane pOut // c.val j.val.val = 0} ≃ Line pOut pIn j where
  toFun c := ⟨c.val.val, c.val.property.1, by
    intro i hi
    rw [(singletonMask_bit _ _).mp hi]
    exact c.property⟩
  invFun c := ⟨⟨c.val, c.property.1, fun i hi => (empty_mask_no_label i hi).elim⟩,
    c.property.2 _ ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem line_retained_coordinate_bijective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) (s : Retained pOut) :
    Function.Bijective (fun c : Line pOut pIn j => lineCurve pOut pIn j c s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he := (singletonMask_bit _ _).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize (singletonMask j.val.val) +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, singletonMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem line_residual_bijective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) :
    Function.Bijective (fun c : Line pOut pIn j => c.val (residualLabel pIn)) := by
  have hz : MaskDisjoint (singletonMask j.val.val) (singletonMask (residualLabel pIn)) := by
    intro i hi hr
    exact uniform_ne_residual pIn j
      (((singletonMask_bit _ _).mp hi).symm.trans ((singletonMask_bit _ _).mp hr))
  have hs : maskSize pOut.val.val.2 + maskSize (singletonMask j.val.val) +
      maskSize (singletonMask (residualLabel pIn)) = 4 := by
    rw [outputInactiveMask_size, singletonMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) (residualLabel pIn)).bijective.comp
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

def equalityTupleEquiv (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) ≃ AES.Word where
  toFun w := w ⟨s, rfl⟩
  invFun v := fun _ => v
  left_inv w := by
    funext i
    have hi : i = ⟨s, rfl⟩ := Subtype.ext i.property
    rw [hi]
  right_inv _ := rfl

def lineRetainedFreeEquiv (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) (s : Retained pOut) :
    Line pOut pIn j ≃ (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (Equiv.ofBijective _ (line_retained_coordinate_bijective pOut pIn j s)).trans
    (equalityTupleEquiv pOut s).symm

theorem lineRetainedFreeEquiv_apply (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) (s : Retained pOut)
    (c : Line pOut pIn j) (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    lineRetainedFreeEquiv pOut pIn j s c i = lineCurve pOut pIn j c i.val := by
  change lineCurve pOut pIn j c s = lineCurve pOut pIn j c i.val
  rw [i.property]

/-- A genuine pair of original input labels gives exactly q points per residual. -/
def residualUniformEquiv (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) : Plane pOut ≃ AES.Word × AES.Word := by
  have hd : MaskDisjoint (singletonMask (residualLabel pIn)) (singletonMask j.val.val) := by
    intro i hr hj
    exact uniform_ne_residual pIn j
      (((singletonMask_bit _ _).mp hj).symm.trans ((singletonMask_bit _ _).mp hr))
  have hs : maskSize pOut.val.val.2 + maskSize (0 : Fin 16) +
      maskSize (singletonMask (residualLabel pIn)) + maskSize (singletonMask j.val.val) = 4 := by
    rw [outputInactiveMask_size, singletonMask_size, singletonMask_size]
    rfl
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hd (empty_mask_disjoint _) hs)).trans
        (Equiv.prodCongr (singletonTupleEquiv _) (singletonTupleEquiv _))

@[simp] theorem residualUniformEquiv_fst (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) (c : Plane pOut) :
    (residualUniformEquiv pOut pIn j c).1 = c.val (residualLabel pIn) := rfl

@[simp] theorem residualUniformEquiv_snd (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (j : SourceUniformPositions pIn) (c : Plane pOut) :
    (residualUniformEquiv pOut pIn j c).2 = c.val j.val.val := rfl

abbrev Translation (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4) :=
  ShortenedWeightedGeometry.Translation wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 0 (residualLabel pIn)

/-- Actual additive inclusion of the residual-zero line in the output-zero plane. -/
def translation (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4) :
    Translation pOut pIn →+ Plane pOut :=
  ShortenedWeightedGeometry.translation wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 0 (residualLabel pIn)

theorem amplitude_translation (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (c : Plane pOut) (t : Translation pOut pIn) :
    h ((c + translation pOut pIn t).val (residualLabel pIn)) = h (c.val (residualLabel pIn)) :=
  ShortenedWeightedGeometry.amplitude_translation _ _ _ _ h c t

theorem translation_coordinate_bijective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (s : Retained pOut) :
    Function.Bijective (fun t : Translation pOut pIn =>
      retainedEmbedding pOut (translation pOut pIn t) s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he := (singletonMask_bit _ _).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize (0 : Fin 16) + 1 +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, singletonMask_size]
    rfl
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    (ShortenedWeightedGeometry.translation_output_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hr (empty_mask_no_label _) hs)

theorem translation_dependent_surjective (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport 1 4) (s : Retained pOut) :
    Function.Surjective (fun t : Translation pOut pIn =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        retainedEmbedding pOut (translation pOut pIn t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t => retainedEmbedding pOut (translation pOut pIn t))
    (translation_coordinate_bijective pOut pIn s).2

theorem freeCoordinates_card (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 2) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  simp only [DependentCoordinates, ne_eq, not_not, Fintype.card_subtype_eq]

/-- The two output zeros plus two distinct actual input zeros force the zero state. -/
theorem pair_input_zeros (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j k : SourceUniformPositions pIn) (hjk : j ≠ k) (c : Plane pOut)
    (hj : c.val j.val.val = 0) (hk : c.val k.val.val = 0) : c.val = 0 := by
  have hd : MaskDisjoint (singletonMask j.val.val) (singletonMask k.val.val) := by
    intro i hi hi'
    exact uniform_labels_ne pIn j k hjk
      (((singletonMask_bit _ _).mp hi).symm.trans ((singletonMask_bit _ _).mp hi'))
  apply mds_graph_zero_high wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
    pOut.val.val.2 (maskUnion (singletonMask j.val.val) (singletonMask k.val.val))
  · rw [outputInactiveMask_size, maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]
  · constructor
    · exact c.property.1
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · rw [(singletonMask_bit _ _).mp hi]
        exact hj
      · rw [(singletonMask_bit _ _).mp hi]
        exact hk

end AESConcrete.TwoOutputThreeUniformGeometry
