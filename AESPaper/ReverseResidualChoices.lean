import AESPaper.WordResidualOneTwo
import AESPaper.WordResidualFour
import AESPaper.WordResidualFiveSix

/-!
# Direct reverse-orientation residual choice bounds

These are actual per-choice bounds for marked shapes (2,1), (3,1), and
(4,2). The line and moment estimates use the physical counts directly.
For (4,2), the output side has two selected core coordinates and two
extras, while the input side has two cores and no extras. Both primal
and dual information-set theorems retain the actual input-adjoint flags.
No symmetry of the physical sandwich is assumed. Activity-frame assembly,
residual-position aggregation and q^2 scaling are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ReverseResidualChoices
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (interiorEntry endpointEntry)
attribute [local instance] Classical.propDecidable

/-- The two surviving weights are supplied by the actual primal and dual
line theorems; every other activity choice vanishes exactly. -/
theorem boundary_choice_bound21 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (HardActivityArrays.entry32 WordResidualOneTwo.coefficient (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 3 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hcount := MarkedBlockScale.count_balance m s
  have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  by_cases ht2 : uniformCount s = 2
  · rw [HardActivityArrays.entry32, if_pos (Or.inl ht2)]
    have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa [hlen, ht2, WordResidualOneTwo.coefficient] using
      WordLineOperator.boundary_primal_line_bound m s hline ho hi
  · by_cases ht3 : uniformCount s = 3
    · rw [HardActivityArrays.entry32, if_pos (Or.inr ht3)]
      have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 2 := by
        omega
      have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
          (Fintype.card (Marked m) - 1) = 4 := by omega
      simpa [hlen, hz, WordResidualOneTwo.coefficient] using
        WordLineOperator.boundary_dual_line_bound m s hline ho hi
    · rw [HardActivityArrays.entry32, if_neg (by tauto)]
      obtain ⟨o⟩ := ho
      have hm : ∃ p, m p = true := ⟨Sum.inl o.val, o.property⟩
      apply WordPhysicalEnergy.boundary_contracted_operator_zero m s hm
      rw [WordActivityCounts.surviving_iff]
      omega

/-- Total marked count four gives the same line endpoints and physical
middle moment without exchanging the input and output operators. -/
theorem boundary_choice_bound31 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (interiorEntry WordResidualFour.lineCoefficient WordResidualFour.momentMiddle
        (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hcount := MarkedBlockScale.count_balance m s
  unfold interiorEntry
  split_ifs with ht ht2
  · exact WordResidualFour.boundary_line_bound m s hlen ho hi ht
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa only [WordMomentCoefficients.moment_4_2, WordResidualFour.momentMiddle] using
      WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 4 hlen hdim (by omega)
  · exact WordResidualFour.boundary_zero_outside m s hlen (by omega)

/-- In the actual (4,2) primal plane, the output has two core positions and
two extras; the input has two cores and no extras. -/
theorem boundary_four_two_primal (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 2)
    (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (WeightedEncoding.nu ^ 4 * WeightedEncoding.delta) := by
  have hm : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have ht : uniformCount s = 0 := by
    have hb := MarkedBlockScale.count_balance m s
    omega
  have h := WordPhysicalEncoding.boundary_primal_bound m s
    (WordPlaneOperator.twoCoreSplit 2 (by simpa using hO))
    (WordPlaneOperator.twoCoreSplit 0 (by simpa using hI))
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hd)
  rw [WordPlaneOperator.sideCoefficient_four_two, WordPlaneOperator.sideCoefficient_two, ht] at h
  convert h using 1 <;> ring_nf

/-- The actual annihilator has dimension two. Fourier transport keeps the
input-adjoint flags and its exact zero-count denominator. -/
theorem boundary_four_two_dual (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 2)
    (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 4 = 4) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (WeightedEncoding.nu ^ 4 * WeightedEncoding.delta) := by
  have hm : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 0 := by
    omega
  have h := WordPhysicalEncoding.boundary_dual_bound m s 4 hd (by omega)
    (WordPlaneOperator.twoCoreSplit 2 (by simpa using hO))
    (WordPlaneOperator.twoCoreSplit 0 (by simpa using hI))
    (by simpa only [Fintype.card_fin, hm, hz])
    (by simpa only [Fintype.card_fin, hm, hz])
  rw [WordPlaneOperator.sideCoefficient_four_two, WordPlaneOperator.sideCoefficient_two, hz] at h
  convert h using 1 <;> ring_nf

/-- The two endpoint choices use actual reverse planes, while the middle
uses the physical six-coordinate, dimension-three moment. -/
theorem boundary_choice_bound42 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (endpointEntry 2 WordResidualFiveSix.sixPlaneA WordResidualFiveSix.sixB
        (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hcount := MarkedBlockScale.count_balance m s
  have ht : uniformCount s ≤ 2 := by omega
  by_cases ht0 : uniformCount s = 0
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa [endpointEntry, ht0, WordResidualFiveSix.sixPlaneA,
      WordMomentCoefficients.delta_eq_weighted] using
      boundary_four_two_primal m s hO hI hdim
  · by_cases ht1 : uniformCount s = 1
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 3 = 4 := by
        omega
      have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 3 6 hlen hdim
        (by omega)
      rw [WordMomentCoefficients.moment_6_3] at h
      simpa [endpointEntry, ht1, WordResidualFiveSix.sixB] using h
    · have ht2 : uniformCount s = 2 := by omega
      have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 4 = 4 := by
        omega
      simpa [endpointEntry, ht2, WordResidualFiveSix.sixPlaneA,
        WordMomentCoefficients.delta_eq_weighted] using
        boundary_four_two_dual m s hO hI hdim

end AESPaper.ReverseResidualChoices
