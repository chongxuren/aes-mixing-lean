import AESPaper.WordActivityCounts
import AESPaper.WordPhysicalActivity
import AESPaper.WordLineOperator
import AESPaper.WordPlaneOperator
import AESPaper.WordMomentCoefficients
import AESPaper.SimpleActivityArrays
import AESPaper.HardActivityArrays

/-!
# Actual four-position residual blocks of shapes (1,3) and (2,2)

The checked (3,1) and (2,2) scalar arrays then give arbitrary-signed-input
fixed-position bounds with both physical frame factors. All coefficients
remain raw: residual-position aggregation and q^2 scaling are separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordResidualFour
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (interiorEntry)
attribute [local instance] Classical.propDecidable

def lineCoefficient : ℝ := WeightedEncoding.nu ^ 2 * WeightedEncoding.delta / 65536

def momentMiddle : ℝ := WordMarkedMoment.tau ^ 2 / WordMarkedMoment.q

def planeMiddle : ℝ := WeightedEncoding.nu ^ 4 / WordMarkedMoment.q

def coefficient13 : ℝ :=
  Real.sqrt (4 * lineCoefficient ^ 2 + 6 * lineCoefficient * momentMiddle +
    3 * momentMiddle ^ 2)

def coefficient22 : ℝ := HardActivityArrays.lambda22 lineCoefficient planeMiddle

theorem lineCoefficient_nonnegative : 0 ≤ lineCoefficient := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) WeightedEncoding.delta_nonnegative)
    (by norm_num)

theorem momentMiddle_nonnegative : 0 ≤ momentMiddle := by
  exact div_nonneg (sq_nonneg _) WordMomentCoefficients.q_positive.le

theorem planeMiddle_nonnegative : 0 ≤ planeMiddle := by
  exact div_nonneg (pow_nonneg WeightedEncoding.nu_nonnegative _)
    WordMomentCoefficients.q_positive.le

theorem coefficient13_nonnegative : 0 ≤ coefficient13 := Real.sqrt_nonneg _

theorem coefficient22_nonnegative : 0 ≤ coefficient22 :=
  HardActivityArrays.lambda22_nonnegative _ _ planeMiddle_nonnegative

/-- The two line endpoints have different physical denominators before the
actual four-position counts are substituted. Input adjoints are unchanged. -/
theorem boundary_line_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 4)
    (hO : Nonempty (OutputMarked m)) (hI : Nonempty (InputMarked m))
    (ht : uniformCount s = 1 ∨ uniformCount s = 3) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s)) lineCoefficient := by
  have hcount := MarkedBlockScale.count_balance m s
  rcases ht with ht | ht
  · have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa [hlen, ht, lineCoefficient, Real.sqrt_sq WeightedEncoding.delta_nonnegative] using
      WordLineOperator.boundary_primal_line_bound m s hline hO hI
  · have hz : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) = 1 := by
      omega
    have hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
        (Fintype.card (Marked m) - 1) = 4 := by omega
    simpa [hlen, hz, lineCoefficient, Real.sqrt_sq WeightedEncoding.delta_nonnegative] using
      WordLineOperator.boundary_dual_line_bound m s hline hO hI

/-- All weights outside one through three vanish as the actual matrix. -/
theorem boundary_zero_outside (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 4)
    (hout : ¬ (1 ≤ uniformCount s ∧ uniformCount s ≤ 3)) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s)) 0 := by
  have hn : Nonempty (Marked m) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hn
  have hm : ∃ p, m p = true := ⟨p.val, p.property⟩
  apply WordPhysicalEnergy.boundary_contracted_operator_zero m s hm
  rw [WordActivityCounts.surviving_iff]
  omega

/-- Actual (1,3) per-choice bound, including exact zero endpoints. -/
theorem boundary_choice_bound13 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 3) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (interiorEntry lineCoefficient momentMiddle (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hcount := MarkedBlockScale.count_balance m s
  unfold interiorEntry
  split_ifs with ht ht2
  · exact boundary_line_bound m s hlen ho hi ht
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa only [WordMomentCoefficients.moment_4_2, momentMiddle] using
      WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 4 hlen hdim (by omega)
  · exact boundary_zero_outside m s hlen (by omega)

/-- Actual (2,2) per-choice bound; its middle uses the stronger plane bound. -/
theorem boundary_choice_bound22 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (interiorEntry lineCoefficient planeMiddle (uniformCount s)) := by
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have ho : Nonempty (OutputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hi : Nonempty (InputMarked m) := Fintype.card_pos_iff.mp (by omega)
  have hcount := MarkedBlockScale.count_balance m s
  unfold interiorEntry
  split_ifs with ht ht2
  · exact boundary_line_bound m s hlen ho hi ht
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa only [planeMiddle, WordMarkedMoment.q] using
      WordPlaneOperator.boundary_two_two m s hO hI hdim
  · exact boundary_zero_outside m s hlen (by omega)

/-- Fixed physical residual positions, checked (3,1) scalar array and both
physical frame factors; no residual-position aggregation is included. -/
theorem markedKernel_bound13 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 1) *
        coefficient13) := by
  have ho : Fintype.card (OutputActivity m) = 3 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 1 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry : ℕ → ℝ := interiorEntry lineCoefficient momentMiddle
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      coefficient13 := by
    apply WordActivityCounts.energyBound_join_of_card m 3 1 ho hi entry coefficient13
    exact SimpleActivityArrays.energyBound_array31 lineCoefficient momentMiddle
      lineCoefficient_nonnegative momentMiddle_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) coefficient13
    (fun so si => ScalarActivityArrays.interiorEntry_nonnegative _ _
      lineCoefficient_nonnegative momentMiddle_nonnegative _)
    (fun so si => boundary_choice_bound13 m hO hI (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Fixed physical residual positions, checked (2,2) scalar array and both
physical frame factors, with the actual plane middle coefficient. -/
theorem markedKernel_bound22 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 2) *
        coefficient22) := by
  have ho : Fintype.card (OutputActivity m) = 2 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 2 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  let entry : ℕ → ℝ := interiorEntry lineCoefficient planeMiddle
  have hs : EnergyBound (fun so si => entry (uniformCount (WordActivitySplit.join m so si)))
      coefficient22 := by
    apply WordActivityCounts.energyBound_join_of_card m 2 2 ho hi entry coefficient22
    exact HardActivityArrays.energyBound_array22 lineCoefficient planeMiddle
      lineCoefficient_nonnegative planeMiddle_nonnegative
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) coefficient22
    (fun so si => ScalarActivityArrays.interiorEntry_nonnegative _ _
      lineCoefficient_nonnegative planeMiddle_nonnegative _)
    (fun so si => boundary_choice_bound22 m hO hI (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

end AESPaper.WordResidualFour
