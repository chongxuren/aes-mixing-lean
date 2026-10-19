import AESPaper.WordActivityCounts
import AESPaper.WordPhysicalActivity
import AESPaper.WordPhysicalEnergy
import AESPaper.WordLineOperator
import AESPaper.HardActivityArrays

/-!
# Actual one-output, two-input residual block
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordResidualOneTwo
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound)
attribute [local instance] Classical.propDecidable

def coefficient : ℝ :=
  WeightedEncoding.nu ^ 2 * Real.sqrt WeightedEncoding.delta / (65536 : ℝ)^2

theorem coefficient_nonnegative : 0 ≤ coefficient := by
  unfold coefficient
  positivity

/-- Every actual contraction has the checked scalar array's entry rule. -/
theorem boundary_choice_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (HardActivityArrays.entry32 coefficient (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 3 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hcount := MarkedBlockScale.count_balance m s
  have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  by_cases ht2 : uniformCount s = 2
  · rw [HardActivityArrays.entry32, if_pos (Or.inl ht2)]
    have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa [hlen, ht2, coefficient] using
      WordLineOperator.boundary_primal_line_bound m s hline ho hi
  · by_cases ht3 : uniformCount s = 3
    · rw [HardActivityArrays.entry32, if_pos (Or.inr ht3)]
      have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 2 := by
        omega
      have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
          (Fintype.card (Marked m) - 1) = 4 := by omega
      simpa [hlen, hz, coefficient] using
        WordLineOperator.boundary_dual_line_bound m s hline ho hi
    · rw [HardActivityArrays.entry32, if_neg (by tauto)]
      obtain ⟨o⟩ := ho
      have hm : ∃ p, m p = true := ⟨Sum.inl o.val, o.property⟩
      apply WordPhysicalEnergy.boundary_contracted_operator_zero m s hm
      rw [WordActivityCounts.surviving_iff]
      omega

/-- Actual fixed-position H Pi H estimate, before position aggregation. -/
theorem markedKernel_bound (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 2) *
        (coefficient * HardActivityArrays.coefficient32)) := by
  have ho : Fintype.card (OutputActivity m) = 3 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 2 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry := HardActivityArrays.entry32 coefficient
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      (coefficient * HardActivityArrays.coefficient32) := by
    apply WordActivityCounts.energyBound_join_of_card m 3 2 ho hi entry _
    exact HardActivityArrays.energyBound_array32 coefficient coefficient_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
    (coefficient * HardActivityArrays.coefficient32)
    (by
      intro so si
      dsimp only [entry, HardActivityArrays.entry32]
      split_ifs
      · exact coefficient_nonnegative
      · exact le_rfl)
    (fun so si => boundary_choice_bound m hO hI (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

end AESPaper.WordResidualOneTwo
