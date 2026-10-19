import AESConcrete.DegreeThreeAssembly
import AESConcrete.ActualActivityPairBounds

/-!
# Actual centered degree-three word Gram intervals

The local AES activity-pair bounds are compressed with the inverse output
metric and summed over four orthogonal physical output triples. Every
quantity here is defined from the centered concrete word kernel. No word
operator bound or pair-table premise is assumed. The input metric and its
spectral comparison are separate remaining obligations.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualDegreeThreeGram
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ActivityFrame
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.TripleOutputCoordinates
open AESConcrete.DegreeThreeAssembly
open AESConcrete.ActivityPairIntervals
open AESConcrete.ActualActivityPairBounds

set_option maxRecDepth 100000

def wordVector (left right : Orientation) (inverse : Bool) (A : Fin 16) :
    (Fin 4 → Byte) → ℝ :=
  action (residualMatrix (wordKernel left right inverse) 0) (frameColumn (maskBit A))

def tripleGram (left right : Orientation) (inverse : Bool) (out A B : Fin 16) : ℝ :=
  (4294967296 : ℝ) * ∑ y : Fin 4 → Byte,
    action (productProjection 0 (maskBit out)) (wordVector left right inverse A) y *
    action (productProjection 0 (maskBit out)) (wordVector left right inverse B) y

def degreeThreeGram (left right : Orientation) (inverse : Bool) (A B : Fin 16) : ℝ :=
  (4294967296 : ℝ) * ∑ y : Fin 4 → Byte,
    degreeComponent 0 3 (wordVector left right inverse A) y *
    degreeComponent 0 3 (wordVector left right inverse B) y

def tripleCoordinates (r : Fin 4) : Fin 3 ≃ MaskCoordinates (tripleMask r) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, maskCoordinates_card, tripleMask_size])

theorem tripleGram_eq_compressed (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (A B : Fin 16) :
    tripleGram left right inverse out A B =
      compressedPair (actualPair inverse e r (fun _ => left)) A B := by
  unfold tripleGram wordVector
  rw [actual_centered_word_triple_inner left right inverse out hout e r hr A B]
  simp only [compressedPair, inverseCompression, actualPair, actualResponse,
    Finset.mul_sum, mul_assoc, mul_left_comm]

theorem actual_tripleGram_mem (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (A B : Fin 16) :
    inInterval (scaleInterval frameFactor
      (compressedInterval concreteResources (maskSize A) (maskSize B)
        (maskSize (maskIntersection A B)))) (tripleGram left right inverse out A B) := by
  rw [tripleGram_eq_compressed left right inverse out hout e r hr A B]
  exact concrete_compressedPair_mem _
    (actual_pair_bounds inverse out hout e r hr (fun _ => left)) A B

theorem degreeThreeGram_eq_sum (left right : Orientation) (inverse : Bool) (A B : Fin 16) :
    degreeThreeGram left right inverse A B =
      ∑ r : Fin 4, tripleGram left right inverse (tripleMask r) A B := by
  unfold degreeThreeGram tripleGram
  rw [degree_three_inner (0 : Byte) (by norm_num [BinaryWord.card]), Finset.mul_sum]

theorem actual_degreeThreeGram_mem (left right : Orientation) (inverse : Bool) (A B : Fin 16) :
    inInterval (scaleInterval (4 * frameFactor)
      (compressedInterval concreteResources (maskSize A) (maskSize B)
        (maskSize (maskIntersection A B)))) (degreeThreeGram left right inverse A B) := by
  have h (r : Fin 4) := actual_tripleGram_mem left right inverse (tripleMask r)
    (tripleMask_size r) (tripleCoordinates r) r (tripleMask_unmarked r) A B
  rw [degreeThreeGram_eq_sum]
  constructor
  · have hl := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) => (h r).1)
    simpa only [scaleInterval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using hl
  · have hu := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) => (h r).2)
    simpa only [scaleInterval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using hu

theorem degreeThreeGram_symmetric (left right : Orientation) (inverse : Bool) (A B : Fin 16) :
    degreeThreeGram left right inverse A B = degreeThreeGram left right inverse B A := by
  unfold degreeThreeGram
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem degreeThreeGram_endpoint_row_zero (left right : Orientation) (inverse : Bool)
    (A B : Fin 16) (hA : maskSize A = 0 ∨ maskSize A = 4) :
    degreeThreeGram left right inverse A B = 0 := by
  have h := actual_degreeThreeGram_mem left right inverse A B
  rcases hA with hA | hA <;>
    simp only [inInterval, scaleInterval, hA, compressedInterval, mul_zero] at h <;>
    exact le_antisymm h.2 h.1

theorem degreeThree_endpoint_zero (left right : Orientation) (inverse : Bool)
    (A : Fin 16) (hA : maskSize A = 0 ∨ maskSize A = 4) (y : Fin 4 → Byte) :
    degreeComponent 0 3 (wordVector left right inverse A) y = 0 := by
  have h := degreeThreeGram_endpoint_row_zero left right inverse A A hA
  unfold degreeThreeGram at h
  simp_rw [← pow_two] at h
  have hy := Finset.single_le_sum
    (fun x (_ : x ∈ (Finset.univ : Finset (Fin 4 → Byte))) =>
      sq_nonneg (degreeComponent 0 3 (wordVector left right inverse A) x))
    (Finset.mem_univ y)
  nlinarith [sq_nonneg (degreeComponent 0 3 (wordVector left right inverse A) y)]

end AESConcrete.ActualDegreeThreeGram
