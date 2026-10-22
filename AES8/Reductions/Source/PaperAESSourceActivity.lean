import AES8.Reductions.Source.PaperAESSourceZeroEvents
import AES8.Reductions.Source.PaperActivityMajorization

/-!
# The current MDS source route on the actual activity energy

This final adapter reindexes the generic proper zero sets by the actual AES
masks, then applies the checked activity-energy identity. The source cap uses
the current generic MDS theorem; no scalar cap-table comparison is a premise.
The all-caps expression remains unevaluated. Residual aggregation and the
complete mixing theorem remain separate obligations. Constructive proofs only.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Word)
open AESConcrete.ActualZeroEventProbabilities (SmallMask)

attribute [local instance] Classical.propDecidable

/-- Nonempty proper masks enumerate exactly the generic proper zero sets. -/
def properMaskEquiv : SmallMask 4 ≃ PaperSourceZeroEvents.ProperZeros (Fin 4) :=
  maskSetEquiv.subtypeEquiv (by
    intro r
    change (0 < maskSize r ∧ maskSize r < 4) ↔
      maskSet r ≠ ∅ ∧ maskSet r ≠ Finset.univ
    rw [← maskSet_card]
    constructor
    · rintro ⟨hpos, hlt⟩
      refine ⟨Finset.card_pos.mp hpos |>.ne_empty, ?_⟩
      intro he
      simpa [he] using hlt
    · rintro ⟨hne, hproper⟩
      exact ⟨Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne),
        by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)⟩)

/-- The symbolic generic majorant is exactly the paper's 4/6/4 expression. -/
theorem generic_majorant_eq_allCaps (p rho : ℝ) :
    PaperSourceMajorization.quadratic
      (fun z : PaperSourceZeroEvents.ProperZeros (Fin 4) => (255 : ℝ) ^ z.val.card)
      (fun z : PaperSourceZeroEvents.ProperZeros (Fin 4) => p ^ (z.val.card - 1) * rho) =
      PaperActivityMajorization.allCaps p rho := by
  rw [← PaperActivityMajorization.quadratic_eq_allCaps]
  unfold PaperSourceMajorization.quadratic
  rw [← properMaskEquiv.sum_comp, ← properMaskEquiv.sum_comp]
  rfl

/-- The actual source collision bound with all local resource premises discharged. -/
theorem probability_collision_le_allCaps (right : Orientation) (inverse : Bool)
    (a : Word) (ha : a ≠ 0) :
    (∑ r : Fin 16, (255 : ℝ) ^ maskSize r *
      AESConcrete.ActualZeroEventProbabilities.exactMass right inverse a r ^ 2) ≤
      PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) := by
  rw [← generic_majorant_eq_allCaps]
  exact probability_collision_le_generic_majorant right inverse a ha

/-- Actual degree-zero energy obtained through the current paper's source route. -/
theorem activity_energy_le_allCaps (left right : Orientation) (inverse : Bool)
    (a : Word) (ha : a ≠ 0) :
    (∑ y : Word, degreeComponent (0 : AESConcrete.WordColumnGram.Byte) 0
      (fun v => AESConcrete.WordOrientationClosure.wordKernel left right inverse v a) y ^ 2) ≤
      PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) / 255 ^ 4 := by
  rw [AESConcrete.ActualColumnActivity.column_activity_energy]
  exact div_le_div_of_nonneg_right (probability_collision_le_allCaps right inverse a ha)
    (by norm_num)

end AES8.PaperAESSource
