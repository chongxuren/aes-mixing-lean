import AESPaper.WordPhysicalEncoding

/-!
# Actual two-dimensional physical operator bounds

Finite cardinalities construct physical core/extra splits. The information-set
property itself is supplied by WordPhysicalEncoding's actual primal and dual
projection theorems. In the four-coordinate side, only two coordinates are
selected as a core; the other two remain functions of the same source.
-/

set_option autoImplicit false
noncomputable section

namespace AESPaper.WordPlaneOperator
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.WordPhysicalEncoding (sideCoefficient)
open AESPaper.WeightedEncoding (nu delta delta_nonnegative)
attribute [local instance] Classical.propDecidable

/-- A physical split with two core coordinates and the stated number of extras.
This equivalence alone asserts no information-set property. -/
def twoCoreSplit {K : Type*} [Fintype K] (j : ℕ)
    (h : Fintype.card K = 2+j) : Fin 2 ⊕ Fin j ≃ K :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_fin] using h.symm)

theorem sideCoefficient_two : sideCoefficient (Fin 2) (Fin 0) = nu^2 := by
  simp [sideCoefficient]

theorem sideCoefficient_four_two : sideCoefficient (Fin 2) (Fin 2) = nu^2*delta := by
  simp only [sideCoefficient, Fintype.card_fin, Real.sqrt_sq delta_nonnegative]

/-- Two marked coordinates on each side and actual source dimension two. -/
theorem boundary_two_two (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ho : Fintype.card (OutputMarked m) = 2)
    (hi : Fintype.card (InputMarked m) = 2)
    (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      (nu^4 / (2 : ℝ)^32) := by
  have hm : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, ho, hi]
  have ht : uniformCount s = 2 := by
    have hb := MarkedBlockScale.count_balance m s
    omega
  have h := WordPhysicalEncoding.boundary_primal_bound m s
    (twoCoreSplit 0 (by simpa using ho)) (twoCoreSplit 0 (by simpa using hi))
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hd)
  rw [sideCoefficient_two, ht] at h
  convert h using 1 <;> ring_nf

/-- Two output positions and four input positions, with a two-dimensional
primal source. The input information set consists of two selected positions. -/
theorem boundary_two_four_primal (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ho : Fintype.card (OutputMarked m) = 2)
    (hi : Fintype.card (InputMarked m) = 4)
    (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      (nu^4 * delta) := by
  have hm : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, ho, hi]
  have ht : uniformCount s = 0 := by
    have hb := MarkedBlockScale.count_balance m s
    omega
  have h := WordPhysicalEncoding.boundary_primal_bound m s
    (twoCoreSplit 0 (by simpa using ho)) (twoCoreSplit 2 (by simpa using hi))
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hd)
  rw [sideCoefficient_two, sideCoefficient_four_two, ht] at h
  convert h using 1 <;> ring_nf

/-- The same physical shape with primal dimension four and annihilator
dimension two. Fourier transport preserves the input-adjoint flags. -/
theorem boundary_two_four_dual (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ho : Fintype.card (OutputMarked m) = 2)
    (hi : Fintype.card (InputMarked m) = 4)
    (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 4 = 4) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      (nu^4 * delta) := by
  have hm : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, ho, hi]
  have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 0 := by
    omega
  have h := WordPhysicalEncoding.boundary_dual_bound m s 4 hd (by omega)
    (twoCoreSplit 0 (by simpa using ho)) (twoCoreSplit 2 (by simpa using hi))
    (by simpa only [Fintype.card_fin, hm, hz])
    (by simpa only [Fintype.card_fin, hm, hz])
  rw [sideCoefficient_two, sideCoefficient_four_two, hz] at h
  convert h using 1 <;> ring_nf

end AESPaper.WordPlaneOperator
