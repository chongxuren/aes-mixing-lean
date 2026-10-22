import AES8.Estimates.Word.PaperActivityPairBounds
import AESConcrete.ActualDegreeThreeGram
import AESConcrete.ActivityGramDominance
import AESConcrete.DegreeThreeFrameEnergy

/-!
# Printed activity-pair resources for the actual degree-three Gram

The Gram kernel definitions and exact triple-compression/four-triple identities
stay unchanged. Their interval provider is the owned printed-byte activity-pair
route. Endpoint-row vanishing and interior restriction are rederived here as
well, so parity consumers do not inherit the old quantitative interval proof
through an algebraic-looking interior wrapper. All constants are retained.
Constructive source candidate only; no attacks or canonical/vendor/paper edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeGramPrinted
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ActualDegreeThreeGram
open AESConcrete.TripleOutputCoordinates
open AESConcrete.DegreeThreeAssembly
open AESConcrete.ActivityPairIntervals
open AESConcrete.ActivityGramDominance (EntryBounds)
open AESConcrete.ActivityEffectiveMetric (Interior qForm)
set_option autoImplicit false
set_option maxRecDepth 100000

theorem actual_tripleGram_mem_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (A B : Fin 16) :
    inInterval (scaleInterval frameFactor
      (compressedInterval concreteResources (maskSize A) (maskSize B)
        (maskSize (maskIntersection A B)))) (tripleGram left right inverse out A B) := by
  rw [tripleGram_eq_compressed left right inverse out hout e r hr A B]
  exact concrete_compressedPair_mem _
    (PaperActivityPairBounds.actual_pair_bounds_of_walsh hWalsh
      inverse out hout e r hr (fun _ => left)) A B

theorem actual_degreeThreeGram_mem_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (left right : Orientation) (inverse : Bool) (A B : Fin 16) :
    inInterval (scaleInterval (4 * frameFactor)
      (compressedInterval concreteResources (maskSize A) (maskSize B)
        (maskSize (maskIntersection A B)))) (degreeThreeGram left right inverse A B) := by
  have h (r : Fin 4) := actual_tripleGram_mem_of_walsh hWalsh left right inverse (tripleMask r)
    (tripleMask_size r) (tripleCoordinates r) r (tripleMask_unmarked r) A B
  rw [degreeThreeGram_eq_sum]
  constructor
  · have hl := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) => (h r).1)
    simpa only [scaleInterval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using hl
  · have hu := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) => (h r).2)
    simpa only [scaleInterval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using hu

theorem actual_entry_bounds_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (left right : Orientation) (inverse : Bool) :
    EntryBounds (degreeThreeGram left right inverse) := by
  intro A B
  exact actual_degreeThreeGram_mem_of_walsh hWalsh left right inverse A.val B.val

theorem degreeThreeGram_endpoint_row_zero_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (left right : Orientation) (inverse : Bool)
    (A B : Fin 16) (hA : maskSize A = 0 ∨ maskSize A = 4) :
    degreeThreeGram left right inverse A B = 0 := by
  have h := actual_degreeThreeGram_mem_of_walsh hWalsh left right inverse A B
  rcases hA with hA | hA <;>
    simp only [inInterval, scaleInterval, hA, compressedInterval, mul_zero] at h <;>
    exact le_antisymm h.2 h.1

/-- Restricting the Gram quadratic uses the owned endpoint-row resource. -/
theorem degreeThreeGram_interior_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    qForm u (degreeThreeGram left right inverse) =
      qForm (fun A : Interior => u A.val)
        (fun A B => degreeThreeGram left right inverse A.val B.val) := by
  have hz0 (B : Fin 16) : degreeThreeGram left right inverse 0 B = 0 :=
    degreeThreeGram_endpoint_row_zero_of_walsh hWalsh left right inverse 0 B (Or.inl (by decide))
  have hz15 (B : Fin 16) : degreeThreeGram left right inverse 15 B = 0 :=
    degreeThreeGram_endpoint_row_zero_of_walsh hWalsh left right inverse 15 B (Or.inr (by decide))
  have hz0r (A : Fin 16) : degreeThreeGram left right inverse A 0 = 0 := by
    rw [degreeThreeGram_symmetric, hz0]
  have hz15r (A : Fin 16) : degreeThreeGram left right inverse A 15 = 0 := by
    rw [degreeThreeGram_symmetric, hz15]
  unfold qForm
  rw [ActivityEffectiveMetric.sum_split]
  simp only [hz0, hz15, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [ActivityEffectiveMetric.sum_split]
  simp only [hz0r, hz15r, mul_zero, zero_add]

theorem actual_entry_bounds (left right : Orientation) (inverse : Bool) :
    EntryBounds (degreeThreeGram left right inverse) :=
  actual_entry_bounds_of_walsh PaperCitedByteBounds.concreteWalshBound left right inverse

theorem degreeThreeGram_interior (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    qForm u (degreeThreeGram left right inverse) =
      qForm (fun A : Interior => u A.val)
        (fun A B => degreeThreeGram left right inverse A.val B.val) :=
  degreeThreeGram_interior_of_walsh PaperCitedByteBounds.concreteWalshBound left right inverse u

#print axioms actual_tripleGram_mem_of_walsh
#print axioms actual_degreeThreeGram_mem_of_walsh
#print axioms actual_entry_bounds_of_walsh
#print axioms degreeThreeGram_endpoint_row_zero_of_walsh
#print axioms degreeThreeGram_interior_of_walsh
#print axioms actual_entry_bounds
#print axioms degreeThreeGram_interior
end AES8.PaperDegreeThreeGramPrinted
