import AESPaper.ReverseResidualChoices
import AESPaper.WordActivityCounts
import AESPaper.WordPhysicalActivity
import AESPaper.WordResidualOneTwo
import AESPaper.WordResidualFour
import AESPaper.WordResidualFiveSix
import AESPaper.RectangularBounds

/-!
# Actual reverse fixed-position residual assemblies

Only the scalar weight arrays are transposed. The physical per-choice
operators keep their actual output/input orientation, and no symmetry of
the AES sandwich is asserted. The empty activity types retain their unique
Boolean choice. Each final bound contains both physical frame factors once;
residual-position aggregation and q^2 scaling remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordResidualReverse
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (weightArray interiorEntry endpointEntry)
attribute [local instance] Classical.propDecidable

/-- Transposition exchanges only the two scalar choice index types. -/
theorem weightArray_transpose (a b : ℕ) (entry : ℕ → ℝ) :
    weightArray b a entry = RectangularBounds.transpose (weightArray a b entry) := by
  funext s t
  change entry (ScalarActivityArrays.weight s + ScalarActivityArrays.weight t) =
    entry (ScalarActivityArrays.weight t + ScalarActivityArrays.weight s)
  rw [Nat.add_comm]

theorem energyBound_weightArray_transpose (a b : ℕ) (entry : ℕ → ℝ) (n : ℝ)
    (h : EnergyBound (weightArray a b entry) n) :
    EnergyBound (weightArray b a entry) n := by
  rw [weightArray_transpose a b entry]
  exact RectangularBounds.energyBound_transpose (weightArray a b entry) n h

/-- Reverse of the checked hard (3,2) scalar array. -/
theorem energyBound_array23 (e : ℝ) (he : 0 ≤ e) :
    EnergyBound (weightArray 2 3 (HardActivityArrays.entry32 e))
      (e * HardActivityArrays.coefficient32) := by
  apply energyBound_weightArray_transpose 3 2 (HardActivityArrays.entry32 e)
  exact HardActivityArrays.energyBound_array32 e he

/-- Reverse of the checked interior (3,1) scalar array. -/
theorem energyBound_array13 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (weightArray 1 3 (interiorEntry A B))
      (Real.sqrt (4 * A ^ 2 + 6 * A * B + 3 * B ^ 2)) := by
  apply energyBound_weightArray_transpose 3 1 (interiorEntry A B)
  exact SimpleActivityArrays.energyBound_array31 A B hA hB

/-- Reverse of the checked endpoint (3,0) scalar array, including Choice 0. -/
theorem energyBound_array03 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (weightArray 0 3 (endpointEntry 3 A B))
      (Real.sqrt (2 * A ^ 2 + 6 * B ^ 2)) := by
  apply energyBound_weightArray_transpose 3 0 (endpointEntry 3 A B)
  exact SimpleActivityArrays.energyBound_array30 A B hA hB

/-- Reverse of the checked endpoint (2,1) scalar array. -/
theorem energyBound_array12 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (weightArray 1 2 (endpointEntry 3 A B))
      (Real.sqrt (A ^ 2 + 2 * A * B + 5 * B ^ 2)) := by
  apply energyBound_weightArray_transpose 2 1 (endpointEntry 3 A B)
  exact SimpleActivityArrays.energyBound_array21 A B hA hB

/-- Reverse of the checked endpoint (2,0) scalar array, including Choice 0. -/
theorem energyBound_array02 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (weightArray 0 2 (endpointEntry 2 A B))
      (Real.sqrt (2 * A ^ 2 + 2 * B ^ 2)) := by
  apply energyBound_weightArray_transpose 2 0 (endpointEntry 2 A B)
  exact SimpleActivityArrays.energyBound_array20 A B hA hB

/-- Actual fixed marked shape (2,1), retaining the physical orientation. -/
theorem markedKernel_bound21 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 3) *
        (WordResidualOneTwo.coefficient * HardActivityArrays.coefficient32)) := by
  have ho : Fintype.card (OutputActivity m) = 2 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 3 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry := HardActivityArrays.entry32 WordResidualOneTwo.coefficient
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (WordResidualOneTwo.coefficient * HardActivityArrays.coefficient32) := by
    apply WordActivityCounts.energyBound_join_of_card m 2 3 ho hi entry _
    exact energyBound_array23 WordResidualOneTwo.coefficient
      WordResidualOneTwo.coefficient_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
    (WordResidualOneTwo.coefficient * HardActivityArrays.coefficient32)
    (by
      intro so si
      dsimp only [entry, HardActivityArrays.entry32]
      split_ifs
      · exact WordResidualOneTwo.coefficient_nonnegative
      · exact le_rfl)
    (fun so si => ReverseResidualChoices.boundary_choice_bound21 m hO hI
      (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Actual fixed marked shape (3,1), with the original moment middle entry. -/
theorem markedKernel_bound31 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 3) *
        WordResidualFour.coefficient13) := by
  have ho : Fintype.card (OutputActivity m) = 1 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 3 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry : ℕ → ℝ := interiorEntry WordResidualFour.lineCoefficient
    WordResidualFour.momentMiddle
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      WordResidualFour.coefficient13 := by
    apply WordActivityCounts.energyBound_join_of_card m 1 3 ho hi entry _
    exact energyBound_array13 WordResidualFour.lineCoefficient WordResidualFour.momentMiddle
      WordResidualFour.lineCoefficient_nonnegative WordResidualFour.momentMiddle_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
    WordResidualFour.coefficient13
    (fun so si => ScalarActivityArrays.interiorEntry_nonnegative _ _
      WordResidualFour.lineCoefficient_nonnegative WordResidualFour.momentMiddle_nonnegative _)
    (fun so si => ReverseResidualChoices.boundary_choice_bound31 m hO hI
      (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Actual fixed marked shape (4,1), including its empty output activity type. -/
theorem markedKernel_bound41 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 0 * WordActivityFrame.conditioningFactor 3) *
        Real.sqrt (2 * WordResidualFiveSix.fiveA ^ 2 + 6 * WordResidualFiveSix.fiveB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 0 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 3 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 5 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hOn : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hIn : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  let entry := endpointEntry 3 WordResidualFiveSix.fiveA WordResidualFiveSix.fiveB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (2 * WordResidualFiveSix.fiveA ^ 2 + 6 * WordResidualFiveSix.fiveB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 0 3 ho hi entry _
    exact energyBound_array03 WordResidualFiveSix.fiveA WordResidualFiveSix.fiveB
      WordResidualFiveSix.fiveA_nonnegative WordResidualFiveSix.fiveB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 3 _ _
      WordResidualFiveSix.fiveA_nonnegative WordResidualFiveSix.fiveB_nonnegative _)
    (fun so si => WordResidualFiveSix.boundary_five_choice_bound m hlen hOn hIn
      (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Actual fixed marked shape (3,2), using the orientation-independent five-count choices. -/
theorem markedKernel_bound32 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 2) *
        Real.sqrt (WordResidualFiveSix.fiveA ^ 2 +
          2 * WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB +
          5 * WordResidualFiveSix.fiveB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 1 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 2 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 5 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hOn : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hIn : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  let entry := endpointEntry 3 WordResidualFiveSix.fiveA WordResidualFiveSix.fiveB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (WordResidualFiveSix.fiveA ^ 2 +
        2 * WordResidualFiveSix.fiveA * WordResidualFiveSix.fiveB +
        5 * WordResidualFiveSix.fiveB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 1 2 ho hi entry _
    exact energyBound_array12 WordResidualFiveSix.fiveA WordResidualFiveSix.fiveB
      WordResidualFiveSix.fiveA_nonnegative WordResidualFiveSix.fiveB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 3 _ _
      WordResidualFiveSix.fiveA_nonnegative WordResidualFiveSix.fiveB_nonnegative _)
    (fun so si => WordResidualFiveSix.boundary_five_choice_bound m hlen hOn hIn
      (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Actual fixed marked shape (4,2), retaining its oriented stronger plane endpoints. -/
theorem markedKernel_bound42 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 0 * WordActivityFrame.conditioningFactor 2) *
        Real.sqrt (2 * WordResidualFiveSix.sixPlaneA ^ 2 + 2 * WordResidualFiveSix.sixB ^ 2)) := by
  have ho : Fintype.card (OutputActivity m) = 0 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 2 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry := endpointEntry 2 WordResidualFiveSix.sixPlaneA WordResidualFiveSix.sixB
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (Real.sqrt (2 * WordResidualFiveSix.sixPlaneA ^ 2 + 2 * WordResidualFiveSix.sixB ^ 2)) := by
    apply WordActivityCounts.energyBound_join_of_card m 0 2 ho hi entry _
    exact energyBound_array02 WordResidualFiveSix.sixPlaneA WordResidualFiveSix.sixB
      WordResidualFiveSix.sixPlaneA_nonnegative WordResidualFiveSix.sixB_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) _
    (fun so si => ScalarActivityArrays.endpointEntry_nonnegative 2 _ _
      WordResidualFiveSix.sixPlaneA_nonnegative WordResidualFiveSix.sixB_nonnegative _)
    (fun so si => ReverseResidualChoices.boundary_choice_bound42 m hO hI
      (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

end AESPaper.WordResidualReverse
