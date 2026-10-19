import AESPaper.WordActivityCounts
import AESPaper.WordPhysicalActivity
import AESPaper.WordLineOperator
import AESPaper.WordMarkedEnergy
import AESPaper.SimpleActivityArrays

/-!
# Actual one-output, one-input residual block
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordResidualOneOne
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound rectAction)
attribute [local instance] Classical.propDecidable

/-- The raw line coefficient; sqrt(q)=65536 for the actual word alphabet. -/
def coefficient : ℝ := WeightedEncoding.nu ^ 2 / (65536 : ℝ)^3

theorem coefficient_nonnegative : 0 ≤ coefficient := by
  unfold coefficient
  positivity

/-- The exact surviving choice and actual line estimate, with no unproved
physical matrix or activity-array estimate as a premise. -/
theorem boundary_choice_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (if uniformCount s = 3 then coefficient else 0) := by
  have hlen : Fintype.card (Marked m) = 2 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hcount := MarkedBlockScale.count_balance m s
  by_cases ht : uniformCount s = 3
  · rw [if_pos ht]
    have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
    have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
    have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa [hlen, ht, coefficient] using
      WordLineOperator.boundary_primal_line_bound m s hline ho hi
  · rw [if_neg ht]
    have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨o⟩ := ho
    have hm : ∃ p, m p = true := ⟨Sum.inl o.val, o.property⟩
    have hout : ¬ (0 < WordMarkedEnergy.dimension m s ∧
        WordMarkedEnergy.dimension m s < Fintype.card (Marked m)) := by
      unfold WordMarkedEnergy.dimension
      omega
    have hz := WordMarkedEnergy.boundary_contracted_zero_outside_surviving m s hm hout
    intro f
    simp [rectAction, WordOperatorDuality.reshape, hz]

/-- For a fixed pair of residual positions, the (3,3) scalar array and both
canonical frame losses bound the actual marked H Pi H matrix. -/
theorem markedKernel_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 3) *
        (3 * coefficient)) := by
  have ho : Fintype.card (OutputActivity m) = 3 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 3 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry : ℕ → ℝ := fun t => if t = 3 then coefficient else 0
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (3 * coefficient) := by
    apply WordActivityCounts.energyBound_join_of_card m 3 3 ho hi entry (3 * coefficient)
    exact SimpleActivityArrays.energyBound_array33 coefficient coefficient_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) (3 * coefficient)
    (by
      intro so si
      dsimp only [entry]
      split_ifs
      · exact coefficient_nonnegative
      · exact le_rfl)
    (fun so si => boundary_choice_bound m hO hI (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

end AESPaper.WordResidualOneOne
