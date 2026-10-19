import AESPaper.ActivityCouplingRounding
import AESPaper.ActivityInputArrays
import AESPaper.ResidualMatrix

/-!
# Actual two-sided activity/residual sandwich bounds

Every physical per-choice estimate is specialized in its actual orientation.
Only the scalar activity arrays are transposed for the reverse orientation.
The physical input-adjoint flags are unchanged. Both frame factors and the
position factor occur once, and the printed b entries bound q^2-scaled norms.
The additional final Pi in fourRound remains a separate composition step.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordActivityCoupling
open AESMixing AESConcrete
open AESPaper.ProfileSpace
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (weightArray interiorEntry)
open AESPaper.ActivityCouplingChoices (e2 e3 A4 B4)
open AESPaper.ActivityCouplingRounding (raw2 raw3 raw4)
attribute [local instance] Classical.propDecidable

/-- Assemble an explicit nonnegative scalar entry rule with actual physical
per-choice matrices, keeping the two frame factors separate from n. -/
theorem markedKernel_of_entry (m : GraphPosition → Bool) (a b : ℕ)
    (ho : Fintype.card (OutputActivity m) = a)
    (hi : Fintype.card (InputActivity m) = b)
    (entry : ℕ → ℝ) (n : ℝ) (hentry : ∀ k, 0 ≤ entry k)
    (hchoice : ∀ s : Activity m → Bool,
      EnergyBound (WordOperatorDuality.reshape m
        (WordMarkedResponse.boundaryContractedResponse m s)) (entry (uniformCount s)))
    (hScalar : EnergyBound (weightArray a b entry) n) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor a * WordActivityFrame.conditioningFactor b) * n) := by
  have hs := WordActivityCounts.energyBound_join_of_card m a b ho hi entry n hScalar
  have hb := WordPhysicalActivity.markedKernel_array_bound m
    (fun so si => entry (uniformCount (WordActivitySplit.join m so si))) n
    (fun so si => hentry _) (fun so si => hchoice (WordActivitySplit.join m so si)) hs
  simpa only [ho, hi] using hb

/-- Two output residual positions and an activity input. -/
theorem markedKernel_bound20 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 0) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 2 * WordActivityFrame.conditioningFactor 4) * raw2) := by
  have ho : Fintype.card (OutputActivity m) = 2 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 4 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 2 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 2 4 ho hi (fun k => if k = 3 then e2 else 0) raw2
  · intro k
    split_ifs
    · exact ActivityCouplingChoices.e2_nonnegative
    · exact le_rfl
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound2 m s hlen
  · exact ActivityInputArrays.energyBound_array24 e2 ActivityCouplingChoices.e2_nonnegative

/-- Activity output and two input residual positions. Only its scalar
array is obtained by transposition. -/
theorem markedKernel_bound02 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 2) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 4 * WordActivityFrame.conditioningFactor 2) * raw2) := by
  have ho : Fintype.card (OutputActivity m) = 4 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 2 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 2 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 4 2 ho hi (fun k => if k = 3 then e2 else 0) raw2
  · intro k
    split_ifs
    · exact ActivityCouplingChoices.e2_nonnegative
    · exact le_rfl
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound2 m s hlen
  · apply WordResidualReverse.energyBound_weightArray_transpose 2 4
    exact ActivityInputArrays.energyBound_array24 e2 ActivityCouplingChoices.e2_nonnegative

/-- Three output residual positions and an activity input. -/
theorem markedKernel_bound30 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 0) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 1 * WordActivityFrame.conditioningFactor 4) * raw3) := by
  have ho : Fintype.card (OutputActivity m) = 1 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 4 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 3 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 1 4 ho hi (HardActivityArrays.entry32 e3) raw3
  · intro k
    unfold HardActivityArrays.entry32
    split_ifs
    · exact ActivityCouplingChoices.e3_nonnegative
    · exact le_rfl
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound3 m s hlen
  · exact ActivityInputArrays.energyBound_array14 e3 ActivityCouplingChoices.e3_nonnegative

/-- Activity output and three input residual positions, using its direct
physical moment bounds and the scalar array transpose. -/
theorem markedKernel_bound03 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 3) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 4 * WordActivityFrame.conditioningFactor 1) * raw3) := by
  have ho : Fintype.card (OutputActivity m) = 4 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 1 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 3 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 4 1 ho hi (HardActivityArrays.entry32 e3) raw3
  · intro k
    unfold HardActivityArrays.entry32
    split_ifs
    · exact ActivityCouplingChoices.e3_nonnegative
    · exact le_rfl
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound3 m s hlen
  · apply WordResidualReverse.energyBound_weightArray_transpose 1 4
    exact ActivityInputArrays.energyBound_array14 e3 ActivityCouplingChoices.e3_nonnegative

/-- Four output residual positions, including the unique empty output
activity choice in the one-row scalar array. -/
theorem markedKernel_bound40 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 4)
    (hI : Fintype.card (InputMarked m) = 0) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 0 * WordActivityFrame.conditioningFactor 4) * raw4) := by
  have ho : Fintype.card (OutputActivity m) = 0 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 4 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 0 4 ho hi (interiorEntry A4 B4) raw4
  · exact ScalarActivityArrays.interiorEntry_nonnegative A4 B4
      ActivityCouplingChoices.A4_nonnegative ActivityCouplingChoices.B4_nonnegative
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound4 m s hlen
  · exact ActivityInputArrays.energyBound_array04 A4 B4

/-- Activity output and four input residual positions. The physical
orientation is retained even though the scalar array has one column. -/
theorem markedKernel_bound04 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 4) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
      ((WordActivityFrame.conditioningFactor 4 * WordActivityFrame.conditioningFactor 0) * raw4) := by
  have ho : Fintype.card (OutputActivity m) = 4 := by
    have h := WordActivityCounts.output_marked_activity_card m
    omega
  have hi : Fintype.card (InputActivity m) = 0 := by
    have h := WordActivityCounts.input_marked_activity_card m
    omega
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  apply markedKernel_of_entry m 4 0 ho hi (interiorEntry A4 B4) raw4
  · exact ScalarActivityArrays.interiorEntry_nonnegative A4 B4
      ActivityCouplingChoices.A4_nonnegative ActivityCouplingChoices.B4_nonnegative
  · intro s
    exact ActivityCouplingChoices.boundary_choice_bound4 m s hlen
  · apply WordResidualReverse.energyBound_weightArray_transpose 0 4
    exact ActivityInputArrays.energyBound_array04 A4 B4

theorem sandwich_b20 (f : ProfileSpace.State) :
    ‖component 2 (BoundaryContraction.sandwich (component 0 f))‖ ≤
      (Assembly.b 1 / Assembly.q ^ 2) * ‖component 0 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 2 0 raw2 _
    ActivityCouplingRounding.raw2_nonnegative ActivityCouplingRounding.round20 ?_ f
  intro m hO hI
  simpa using markedKernel_bound20 m hO hI

theorem sandwich_b02 (f : ProfileSpace.State) :
    ‖component 0 (BoundaryContraction.sandwich (component 2 f))‖ ≤
      (Assembly.b 1 / Assembly.q ^ 2) * ‖component 2 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 0 2 raw2 _
    ActivityCouplingRounding.raw2_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 0 2 raw2 ≤ Assembly.b 1 / Assembly.q ^ 2
    rw [ResidualMatrix.coefficient_comm 0 2]
    exact ActivityCouplingRounding.round20
  · intro m hO hI
    simpa using markedKernel_bound02 m hO hI

theorem sandwich_b30 (f : ProfileSpace.State) :
    ‖component 3 (BoundaryContraction.sandwich (component 0 f))‖ ≤
      (Assembly.b 2 / Assembly.q ^ 2) * ‖component 0 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 3 0 raw3 _
    ActivityCouplingRounding.raw3_nonnegative ActivityCouplingRounding.round30 ?_ f
  intro m hO hI
  simpa using markedKernel_bound30 m hO hI

theorem sandwich_b03 (f : ProfileSpace.State) :
    ‖component 0 (BoundaryContraction.sandwich (component 3 f))‖ ≤
      (Assembly.b 2 / Assembly.q ^ 2) * ‖component 3 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 0 3 raw3 _
    ActivityCouplingRounding.raw3_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 0 3 raw3 ≤ Assembly.b 2 / Assembly.q ^ 2
    rw [ResidualMatrix.coefficient_comm 0 3]
    exact ActivityCouplingRounding.round30
  · intro m hO hI
    simpa using markedKernel_bound03 m hO hI

theorem sandwich_b40 (f : ProfileSpace.State) :
    ‖component 4 (BoundaryContraction.sandwich (component 0 f))‖ ≤
      (Assembly.b 3 / Assembly.q ^ 2) * ‖component 0 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 4 0 raw4 _
    ActivityCouplingRounding.raw4_nonnegative ActivityCouplingRounding.round40 ?_ f
  intro m hO hI
  simpa using markedKernel_bound40 m hO hI

theorem sandwich_b04 (f : ProfileSpace.State) :
    ‖component 0 (BoundaryContraction.sandwich (component 4 f))‖ ≤
      (Assembly.b 3 / Assembly.q ^ 2) * ‖component 4 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 0 4 raw4 _
    ActivityCouplingRounding.raw4_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 0 4 raw4 ≤ Assembly.b 3 / Assembly.q ^ 2
    rw [ResidualMatrix.coefficient_comm 0 4]
    exact ActivityCouplingRounding.round40
  · intro m hO hI
    simpa using markedKernel_bound04 m hO hI

/-- A typed bridge to the actual H Pi H function used by BoundaryZeros. -/
theorem sandwich_eq_toLp (f : ProfileSpace.State) :
    BoundaryContraction.sandwich f = WithLp.toLp 2
      (GroupedRecurrence.H (GroupedRecurrence.Pi (GroupedRecurrence.H (fun x => f x)))) := by
  apply PiLp.ext
  intro x
  exact (BoundaryContraction.sandwich_apply f x).trans
    (PiLp.toLp_apply 2 (fun _ : AES.WordState => ℝ)
      (GroupedRecurrence.H (GroupedRecurrence.Pi (GroupedRecurrence.H (fun y => f y)))) x).symm

/-- The degree-one/activity coupling is exactly zero in this orientation. -/
theorem sandwich_b10 (f : ProfileSpace.State) :
    ‖component 1 (BoundaryContraction.sandwich (component 0 f))‖ ≤
      (Assembly.b 0 / Assembly.q ^ 2) * ‖component 0 f‖ := by
  rw [sandwich_eq_toLp, BoundaryZeros.component_H_Pi_H_one_zero]
  norm_num [Assembly.b, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

/-- The reverse degree-one/activity coupling is also exactly zero. -/
theorem sandwich_b01 (f : ProfileSpace.State) :
    ‖component 0 (BoundaryContraction.sandwich (component 1 f))‖ ≤
      (Assembly.b 0 / Assembly.q ^ 2) * ‖component 1 f‖ := by
  rw [sandwich_eq_toLp, BoundaryZeros.component_H_Pi_H_zero_one]
  norm_num [Assembly.b, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

/-- Every printed b entry bounds the actual activity-to-residual sandwich
block on arbitrary signed joint inputs, with its q^2 scale explicit. -/
theorem sandwich_b_from_activity (i : Fin 4) (f : ProfileSpace.State) :
    ‖component i.succ (BoundaryContraction.sandwich (component 0 f))‖ ≤
      (Assembly.b i / Assembly.q ^ 2) * ‖component 0 f‖ := by
  fin_cases i
  · exact sandwich_b10 f
  · exact sandwich_b20 f
  · exact sandwich_b30 f
  · exact sandwich_b40 f

/-- Every printed b entry also bounds the actual reverse block; this uses
direct physical estimates rather than symmetry of the sandwich. -/
theorem sandwich_b_to_activity (i : Fin 4) (f : ProfileSpace.State) :
    ‖component 0 (BoundaryContraction.sandwich (component i.succ f))‖ ≤
      (Assembly.b i / Assembly.q ^ 2) * ‖component i.succ f‖ := by
  fin_cases i
  · exact sandwich_b01 f
  · exact sandwich_b02 f
  · exact sandwich_b03 f
  · exact sandwich_b04 f

end AESPaper.WordActivityCoupling
