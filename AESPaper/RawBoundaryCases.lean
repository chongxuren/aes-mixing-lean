import AESPaper.RawBoundaryChoices
import AESPaper.SimpleActivityArrays
import AESPaper.WordResidualReverse
import AESPaper.ActivityInputArrays

/-!
# Physical fixed-position low raw C and t blocks
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryCases
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Activity)
open AESConcrete.MarkedBlockShortening (uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RawBoundaryIncidence (q)
open AESPaper.RawBoundaryKernel (contractedResponse)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (weightArray interiorEntry)
open AESPaper.RawBoundaryChoices (e11 e12 e13 A22 B22 e20 e30)
attribute [local instance] Classical.propDecidable

-- These exact raw constants match the parent's independent rounding interface.
def raw11 : ℝ := 3 / (q * (65536 : ℝ))
def raw12 : ℝ := HardActivityArrays.coefficient32 / q
def raw13 : ℝ := Real.sqrt 13 / (65536 : ℝ)
def raw22 : ℝ := HardActivityArrays.lambda22 (1 / (65536 : ℝ)) (1 / q)
def raw2 : ℝ := Real.sqrt 12 / q
def raw3 : ℝ := 4 / (65536 : ℝ)

theorem raw11_nonnegative : 0 ≤ raw11 := by norm_num [raw11, q]
theorem raw12_nonnegative : 0 ≤ raw12 :=
  div_nonneg HardActivityArrays.coefficient32_positive.le RawBoundaryIncidence.q_positive.le
theorem raw13_nonnegative : 0 ≤ raw13 := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
theorem raw22_nonnegative : 0 ≤ raw22 :=
  HardActivityArrays.lambda22_nonnegative _ _ (by norm_num [q])
theorem raw2_nonnegative : 0 ≤ raw2 :=
  div_nonneg (Real.sqrt_nonneg _) RawBoundaryIncidence.q_positive.le
theorem raw3_nonnegative : 0 ≤ raw3 := by norm_num [raw3]

theorem spike_nonnegative (e : ℝ) (he : 0 ≤ e) (k : ℕ) :
    0 ≤ (if k = 3 then e else 0) := by
  split_ifs
  · exact he
  · exact le_rfl

theorem entry32_nonnegative (e : ℝ) (he : 0 ≤ e) (k : ℕ) :
    0 ≤ HardActivityArrays.entry32 e k := by
  unfold HardActivityArrays.entry32
  split_ifs
  · exact he
  · exact le_rfl

/-- Assemble actual raw per-choice matrices with the scalar norm; the
marked/activity partition derives the two physical frame dimensions. -/
theorem markedKernel_of_entry (m : GraphPosition → Bool) (i j : ℕ)
    (hO : Fintype.card (OutputMarked m) = i)
    (hI : Fintype.card (InputMarked m) = j)
    (entry : ℕ → ℝ) (n : ℝ) (hentry : ∀ k, 0 ≤ entry k)
    (hchoice : ∀ s : Activity m → Bool,
      EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s)) (entry (uniformCount s)))
    (hScalar : EnergyBound (weightArray (4-i) (4-j) entry) n) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor (4-i) *
        WordActivityFrame.conditioningFactor (4-j)) * n) := by
  have ho : Fintype.card (OutputActivity m) = 4-i := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 4-j := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hs := WordActivityCounts.energyBound_join_of_card m (4-i) (4-j) ho hi entry n hScalar
  have hb := RawBoundaryKernel.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) n
    (fun so si => hentry _) (fun so si => hchoice (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

theorem scalar11_bound :
    EnergyBound (weightArray 3 3 (fun k => if k = 3 then e11 else 0)) raw11 := by
  simpa only [SimpleActivityArrays.array33, raw11, e11, div_eq_mul_inv, one_mul] using
    SimpleActivityArrays.energyBound_array33 e11 RawBoundaryChoices.e11_nonnegative

theorem scalar12_bound :
    EnergyBound (weightArray 3 2 (HardActivityArrays.entry32 e12)) raw12 := by
  simpa only [HardActivityArrays.array32, raw12, e12, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
    HardActivityArrays.energyBound_array32 e12 RawBoundaryChoices.e12_nonnegative

/-- The equal endpoint/middle entries simplify the scalar (3,1) coefficient
to sqrt(13)/65536 by exact nonnegative squares. -/
theorem scalar13_bound :
    EnergyBound (weightArray 3 1 (interiorEntry e13 e13)) raw13 := by
  have he13 := RawBoundaryChoices.e13_nonnegative
  have h := SimpleActivityArrays.energyBound_array31 e13 e13
    RawBoundaryChoices.e13_nonnegative RawBoundaryChoices.e13_nonnegative
  have hc : Real.sqrt (4 * e13 ^ 2 + 6 * e13 * e13 + 3 * e13 ^ 2) = raw13 := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) raw13_nonnegative).mp
    rw [Real.sq_sqrt (by positivity)]
    unfold raw13
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
    norm_num [e13]
  rw [hc] at h
  exact h

theorem scalar22_bound :
    EnergyBound (weightArray 2 2 (interiorEntry A22 B22)) raw22 :=
  HardActivityArrays.energyBound_array22 A22 B22
    RawBoundaryChoices.A22_nonnegative RawBoundaryChoices.B22_nonnegative

theorem scalar20_bound :
    EnergyBound (weightArray 2 4 (fun k => if k = 3 then e20 else 0)) raw2 := by
  simpa only [ActivityInputArrays.array24, raw2, e20, div_eq_mul_inv, one_mul] using
    ActivityInputArrays.energyBound_array24 e20 RawBoundaryChoices.e20_nonnegative

theorem scalar30_bound :
    EnergyBound (weightArray 1 4 (HardActivityArrays.entry32 e30)) raw3 := by
  simpa only [ActivityInputArrays.array14, raw3, e30, div_eq_mul_inv, one_mul] using
    ActivityInputArrays.energyBound_array14 e30 RawBoundaryChoices.e30_nonnegative

theorem markedKernel_bound11 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 3) * raw11) := by
  apply markedKernel_of_entry m 1 1 hO hI (fun k => if k = 3 then e11 else 0) raw11
  · exact spike_nonnegative e11 RawBoundaryChoices.e11_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound11 m hO hI
  · exact scalar11_bound

theorem markedKernel_bound12 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 2) * raw12) := by
  apply markedKernel_of_entry m 1 2 hO hI (HardActivityArrays.entry32 e12) raw12
  · exact entry32_nonnegative e12 RawBoundaryChoices.e12_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound12 m hO hI
  · exact scalar12_bound

theorem markedKernel_bound21 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 3) * raw12) := by
  apply markedKernel_of_entry m 2 1 hO hI (HardActivityArrays.entry32 e12) raw12
  · exact entry32_nonnegative e12 RawBoundaryChoices.e12_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound21 m hO hI
  · exact WordResidualReverse.energyBound_weightArray_transpose 3 2 _ _ scalar12_bound

theorem markedKernel_bound13 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 3 * WordActivityFrame.conditioningFactor 1) * raw13) := by
  apply markedKernel_of_entry m 1 3 hO hI (interiorEntry e13 e13) raw13
  · exact ScalarActivityArrays.interiorEntry_nonnegative e13 e13
      RawBoundaryChoices.e13_nonnegative RawBoundaryChoices.e13_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound13 m hO hI
  · exact scalar13_bound

theorem markedKernel_bound31 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 1) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 3) * raw13) := by
  apply markedKernel_of_entry m 3 1 hO hI (interiorEntry e13 e13) raw13
  · exact ScalarActivityArrays.interiorEntry_nonnegative e13 e13
      RawBoundaryChoices.e13_nonnegative RawBoundaryChoices.e13_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound31 m hO hI
  · exact WordResidualReverse.energyBound_weightArray_transpose 3 1 _ _ scalar13_bound

theorem markedKernel_bound22 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 2) * raw22) := by
  apply markedKernel_of_entry m 2 2 hO hI (interiorEntry A22 B22) raw22
  · exact ScalarActivityArrays.interiorEntry_nonnegative A22 B22
      RawBoundaryChoices.A22_nonnegative RawBoundaryChoices.B22_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound22 m hO hI
  · exact scalar22_bound

theorem markedKernel_bound20 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 0) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 4) * raw2) := by
  apply markedKernel_of_entry m 2 0 hO hI (fun k => if k = 3 then e20 else 0) raw2
  · exact spike_nonnegative e20 RawBoundaryChoices.e20_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound20 m hO hI
  · exact scalar20_bound

theorem markedKernel_bound02 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 4 * WordActivityFrame.conditioningFactor 2) * raw2) := by
  apply markedKernel_of_entry m 0 2 hO hI (fun k => if k = 3 then e20 else 0) raw2
  · exact spike_nonnegative e20 RawBoundaryChoices.e20_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound02 m hO hI
  · exact WordResidualReverse.energyBound_weightArray_transpose 2 4 _ _ scalar20_bound

theorem markedKernel_bound30 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 0) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 4) * raw3) := by
  apply markedKernel_of_entry m 3 0 hO hI (HardActivityArrays.entry32 e30) raw3
  · exact entry32_nonnegative e30 RawBoundaryChoices.e30_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound30 m hO hI
  · exact scalar30_bound

theorem markedKernel_bound03 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (RawBoundaryKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 4 * WordActivityFrame.conditioningFactor 1) * raw3) := by
  apply markedKernel_of_entry m 0 3 hO hI (HardActivityArrays.entry32 e30) raw3
  · exact entry32_nonnegative e30 RawBoundaryChoices.e30_nonnegative
  · exact RawBoundaryChoices.boundary_choice_bound03 m hO hI
  · exact WordResidualReverse.energyBound_weightArray_transpose 1 4 _ _ scalar30_bound

end AESPaper.RawBoundaryCases
