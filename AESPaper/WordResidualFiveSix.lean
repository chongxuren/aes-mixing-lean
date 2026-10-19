import AESPaper.WordActivityCounts
import AESPaper.WordPhysicalActivity
import AESPaper.WordLineOperator
import AESPaper.WordPlaneOperator
import AESPaper.WordMomentCoefficients
import AESPaper.SimpleActivityArrays

/-!
# Actual fixed-position residual blocks with five or six marked positions

The physical count balance selects actual primal/dual lines, two-four
planes, or the accepted shortened-code moment operator. The Fourier routes
retain the physical input transpose. The checked scalar arrays then apply
to arbitrary joint signed inputs, with both frame factors explicit.
Residual-position aggregation, q^2 scaling and the full mixing theorem are
separate obligations; none is included in these raw fixed-position bounds.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordResidualFiveSix
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (endpointEntry)
open AESPaper.WordMarkedMoment (q tau delta)
attribute [local instance] Classical.propDecidable

/-- Total marked count five: actual primal/dual line coefficient. -/
def fiveA : ℝ := WeightedEncoding.nu ^ 2 * Real.sqrt (delta ^ 3)

/-- Total marked count five: the two middle shortened-code moments. -/
def fiveB : ℝ := tau ^ 2 * Real.sqrt (delta / q)

/-- The stronger two-four plane coefficient at total marked count six. -/
def sixPlaneA : ℝ := WeightedEncoding.nu ^ 4 * delta

/-- The generic endpoint moment coefficient for the three-three case. -/
def sixMomentA : ℝ := tau ^ 2 * delta

/-- The middle six-coordinate moment, with the literal sqrt(q)=65536. -/
def sixB : ℝ := tau ^ 3 / (65536 : ℝ)

theorem fiveA_nonnegative : 0 ≤ fiveA := by
  unfold fiveA
  positivity

theorem fiveB_nonnegative : 0 ≤ fiveB := by
  unfold fiveB
  positivity

theorem sixPlaneA_nonnegative : 0 ≤ sixPlaneA := by
  exact mul_nonneg (pow_nonneg WeightedEncoding.nu_nonnegative 4)
    WordMomentCoefficients.delta_nonnegative

theorem sixMomentA_nonnegative : 0 ≤ sixMomentA := by
  exact mul_nonneg (sq_nonneg tau) WordMomentCoefficients.delta_nonnegative

theorem sixB_nonnegative : 0 ≤ sixB := by
  exact div_nonneg (pow_nonneg WordMomentCoefficients.tau_nonnegative 3) (by norm_num)

/-- Five marked physical coordinates leave exactly four possible uniform
counts. The endpoints use actual primal/dual lines; the middle counts use
the actual moment operator, without an assumed physical operator estimate. -/
theorem boundary_five_choice_bound (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 5)
    (hO : Nonempty (OutputMarked m)) (hI : Nonempty (InputMarked m))
    (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (endpointEntry 3 fiveA fiveB (uniformCount s)) := by
  have hcount := MarkedBlockScale.count_balance m s
  have ht : uniformCount s ≤ 3 := by omega
  by_cases ht0 : uniformCount s = 0
  · have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa [endpointEntry, ht0, hlen, fiveA, WordMomentCoefficients.delta_eq_weighted] using
      WordLineOperator.boundary_primal_line_bound m s hline hO hI
  · by_cases ht1 : uniformCount s = 1
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
        omega
      have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 5 hlen hdim
        (by omega)
      rw [WordMomentCoefficients.moment_5_2] at h
      simpa [endpointEntry, ht1, fiveB] using h
    · by_cases ht2 : uniformCount s = 2
      · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 3 = 4 := by
          omega
        have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 3 5 hlen hdim
          (by omega)
        rw [WordMomentCoefficients.moment_5_3] at h
        simpa [endpointEntry, ht2, fiveB] using h
      · have ht3 : uniformCount s = 3 := by omega
        have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 0 := by
          omega
        have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
            (Fintype.card (Marked m) - 1) = 4 := by omega
        simpa [endpointEntry, ht3, hlen, hz, fiveA,
          WordMomentCoefficients.delta_eq_weighted] using
          WordLineOperator.boundary_dual_line_bound m s hline hO hI

/-- Two output and four input marked coordinates use actual primal/dual
planes at the endpoints, preserving the stronger nu^4 coefficient. -/
theorem boundary_two_four_choice_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 4) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (endpointEntry 2 sixPlaneA sixB (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hcount := MarkedBlockScale.count_balance m s
  have ht : uniformCount s ≤ 2 := by omega
  by_cases ht0 : uniformCount s = 0
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa [endpointEntry, ht0, sixPlaneA, WordMomentCoefficients.delta_eq_weighted] using
      WordPlaneOperator.boundary_two_four_primal m s hO hI hdim
  · by_cases ht1 : uniformCount s = 1
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 3 = 4 := by
        omega
      have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 3 6 hlen hdim
        (by omega)
      rw [WordMomentCoefficients.moment_6_3] at h
      simpa [endpointEntry, ht1, sixB] using h
    · have ht2 : uniformCount s = 2 := by omega
      have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 4 = 4 := by
        omega
      simpa [endpointEntry, ht2, sixPlaneA, WordMomentCoefficients.delta_eq_weighted] using
        WordPlaneOperator.boundary_two_four_dual m s hO hI hdim

/-- The three-three residual uses moment dimensions two, three and four.
The exact count balance establishes each dimension before applying a moment. -/
theorem boundary_six_moment_choice_bound (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 6) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (endpointEntry 2 sixMomentA sixB (uniformCount s)) := by
  have hcount := MarkedBlockScale.count_balance m s
  have ht : uniformCount s ≤ 2 := by omega
  by_cases ht0 : uniformCount s = 0
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 6 hlen hdim
      (by omega)
    rw [WordMomentCoefficients.moment_6_2] at h
    simpa [endpointEntry, ht0, sixMomentA] using h
  · by_cases ht1 : uniformCount s = 1
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 3 = 4 := by
        omega
      have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 3 6 hlen hdim
        (by omega)
      rw [WordMomentCoefficients.moment_6_3] at h
      simpa [endpointEntry, ht1, sixB] using h
    · have ht2 : uniformCount s = 2 := by omega
      have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 4 = 4 := by
        omega
      have h := WordPhysicalEnergy.boundary_contracted_operator_bound m s 4 6 hlen hdim
        (by omega)
      rw [WordMomentCoefficients.moment_6_4] at h
      simpa [endpointEntry, ht2, sixMomentA] using h

/-- Fixed marked shape (1,4), with the checked (3,0) scalar array.
The empty input activity type still has its unique Boolean choice. -/
theorem markedKernel_one_four_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 4) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 0) *
        Real.sqrt (2 * fiveA ^ 2 + 6 * fiveB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 3 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 0 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 5 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hOn : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hIn : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  let entry := endpointEntry 3 fiveA fiveB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (2 * fiveA ^ 2 + 6 * fiveB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 3 0 ho hi entry _
    exact SimpleActivityArrays.energyBound_array30 fiveA fiveB fiveA_nonnegative fiveB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 3 fiveA fiveB
      fiveA_nonnegative fiveB_nonnegative _)
    (fun so si => boundary_five_choice_bound m hlen hOn hIn (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Fixed marked shape (2,3), with the checked (2,1) scalar array. -/
theorem markedKernel_two_three_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 1) *
        Real.sqrt (fiveA ^ 2 + 2 * fiveA * fiveB + 5 * fiveB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 2 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 1 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 5 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hOn : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hIn : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  let entry := endpointEntry 3 fiveA fiveB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (fiveA ^ 2 + 2 * fiveA * fiveB + 5 * fiveB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 2 1 ho hi entry _
    exact SimpleActivityArrays.energyBound_array21 fiveA fiveB fiveA_nonnegative fiveB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 3 fiveA fiveB
      fiveA_nonnegative fiveB_nonnegative _)
    (fun so si => boundary_five_choice_bound m hlen hOn hIn (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Fixed marked shape (2,4), retaining the stronger physical plane endpoints. -/
theorem markedKernel_two_four_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 4) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 0) *
        Real.sqrt (2 * sixPlaneA ^ 2 + 2 * sixB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 2 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 0 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry := endpointEntry 2 sixPlaneA sixB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (2 * sixPlaneA ^ 2 + 2 * sixB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 2 0 ho hi entry _
    exact SimpleActivityArrays.energyBound_array20 sixPlaneA sixB
      sixPlaneA_nonnegative sixB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 2 sixPlaneA sixB
      sixPlaneA_nonnegative sixB_nonnegative _)
    (fun so si => boundary_two_four_choice_bound m hO hI (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Fixed marked shape (3,3), with the checked (1,1) scalar array. -/
theorem markedKernel_three_three_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 1) *
        (sixMomentA + sixB)) := by
  have ho : Fintype.card (OutputActivity m) = 1 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 1 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 6 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  let entry := endpointEntry 2 sixMomentA sixB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (sixMomentA + sixB) := by
    apply WordActivityCounts.energyBound_join_of_card m 1 1 ho hi entry _
    exact SimpleActivityArrays.energyBound_array11 sixMomentA sixB
      sixMomentA_nonnegative sixB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 2 sixMomentA sixB
      sixMomentA_nonnegative sixB_nonnegative _)
    (fun so si => boundary_six_moment_choice_bound m hlen (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

end AESPaper.WordResidualFiveSix
