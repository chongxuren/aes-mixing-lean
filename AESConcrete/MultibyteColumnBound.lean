import AESConcrete.ActualColumnActivity
import AESConcrete.ActualPositiveColumnDegrees
import AESConcrete.WordColumnBounds

/-!
# Actual two-, three-, and four-active-byte column bounds

The physical column is decomposed into orthogonal support components.
Actual restricted-response bounds control positive residual degrees; exact
support probabilities control degree zero. Exact rational comparisons and
the pointed-channel centering identity give the claimed residual bound.
No numerical word-column resource is an assumption of this theorem.

Constructive mathematics only; no attacks, manuscript edits or complete
experiment-security claim.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MultibyteColumnBound
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)

theorem full_column_energy_le (left right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    (∑ y : Word, wordKernel left right inverse y a^2) ≤
      MultibyteColumnNumbers.fullColumnCap t := by
  have ha0 := ActualZeroEventProbabilities.input_nonzero_of_active_count a z ha (by omega)
  apply ColumnSupportAggregation.full_energy_le t ht
  · exact ActualColumnActivity.actual_column_activity_energy_le left right inverse a z t ht hcount ha
  · intro j _ p
    have h := ActualPositiveColumnDegrees.support_component_energy_le left right inverse a ha0 z t hcount ha
      p.val.2 p.val.1 p.property.1
    simpa only [supportIndexComponent,p.property.2] using h

theorem full_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    (∑ y : Word, wordKernel left right inverse y a^2) <
      (17/(15*4294967296) : ℝ) := by
  have h := (full_column_energy_le left right inverse a z t ht hcount ha).trans_lt
    (MultibyteColumnNumbers.fullColumnCap_lt t ht)
  norm_num only [MultibyteColumnNumbers.q] at h ⊢
  exact h

theorem residual_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a^2) <
      (2/(15*4294967296) : ℝ) := by
  have ha0 := ActualZeroEventProbabilities.input_nonzero_of_active_count a z ha (by omega)
  rw [pointed_residual_column_energy_exact (word_kernel_pointed left right inverse)
    AES.word_card_gt_one a ha0, AES.word_card_exact]
  have h := full_column_energy_lt left right inverse a z t ht hcount ha
  norm_num at h ⊢
  linarith

end AESConcrete.MultibyteColumnBound
