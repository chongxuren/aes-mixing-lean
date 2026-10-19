import AESPaper.WordActivitySplit
import AESPaper.WordActivityArray
import AESPaper.WordOperatorDuality

/-!
# Actual physical activity fixedness and two-sided array assembly
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordPhysicalActivity
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESPaper.WordActivitySplit (OutputActivity InputActivity physicalKernel)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordFrameCoordinates (projectActivity tensorActivityKernel)
open AESPaper.RectangularFourier (EnergyBound)
attribute [local instance] Classical.propDecidable

/-- A sum of actual projector columns is fixed, even with arbitrary signed
weights and repeated source-coordinate values. -/
theorem project_sum_columns {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    (g : C → ℝ) (coord : C → I → AES.Word) :
    projectActivity (fun u => ∑ c : C, g c * tensorActivityKernel u (coord c)) =
      (fun u => ∑ c : C, g c * tensorActivityKernel u (coord c)) := by
  funext u
  unfold projectActivity action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = g c * ∑ v : I → AES.Word,
        tensorActivityKernel u v * tensorActivityKernel v (coord c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      have hp := congrFun (congrFun
        (WordMarkedResponse.tensorActivityKernel_idempotent (J := I)) u) (coord c)
      change (∑ v : I → AES.Word,
        tensorActivityKernel u v * tensorActivityKernel v (coord c)) = _ at hp
      rw [hp]

def outputSource (m : GraphPosition → Bool) (w : AES.WordState) :
    OutputActivity m → AES.Word := fun i =>
  graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom w
    (WordActivitySplit.outputPosition m i).val

def inputSource (m : GraphPosition → Bool) (w : AES.WordState) :
    InputActivity m → AES.Word := fun i =>
  graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom w
    (WordActivitySplit.inputPosition m i).val

def markedWeight (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word)
    (w : AES.WordState) : ℝ :=
  ∏ p : Marked m, WordMarkedResponse.wordMarkedLeg m p
    (WordMarkedSplit.join m y x p)
    (graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom w p.val)

/-- Common-source formula with the two actual physical activity projectors. -/
theorem physicalKernel_formula (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word)
    (u : OutputActivity m → AES.Word) (v : InputActivity m → AES.Word) :
    physicalKernel m (y,u) (x,v) = ∑ w : AES.WordState,
      markedWeight m y x w * tensorActivityKernel u (outputSource m w) *
        tensorActivityKernel v (inputSource m w) := by
  rw [WordActivitySplit.physicalKernel_splitResponse]
  unfold MarkedBlockVectorization.splitResponse
  apply Finset.sum_congr rfl
  intro w _
  rw [WordActivitySplit.prod_positions]
  simp only [WordActivitySplit.join_output, WordActivitySplit.join_input]
  change markedWeight m y x w *
    (tensorActivityKernel u (outputSource m w) * tensorActivityKernel v (inputSource m w)) = _
  ring

/-- Every output activity section is in the actual activity space. -/
theorem physicalKernel_output_fixed (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word)
    (xv : (InputMarked m → AES.Word) × (InputActivity m → AES.Word)) :
    projectActivity (fun u => physicalKernel m (y,u) xv) =
      (fun u => physicalKernel m (y,u) xv) := by
  have he : (fun u => physicalKernel m (y,u) xv) =
      (fun u => ∑ w : AES.WordState,
        (markedWeight m y xv.1 w * tensorActivityKernel xv.2 (inputSource m w)) *
          tensorActivityKernel u (outputSource m w)) := by
    funext u
    rw [physicalKernel_formula]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  exact project_sum_columns _ _

/-- Every input activity section is in the actual activity space. -/
theorem physicalKernel_input_fixed (m : GraphPosition → Bool)
    (yu : (OutputMarked m → AES.Word) × (OutputActivity m → AES.Word))
    (x : InputMarked m → AES.Word) :
    projectActivity (fun v => physicalKernel m yu (x,v)) =
      (fun v => physicalKernel m yu (x,v)) := by
  have he : (fun v => physicalKernel m yu (x,v)) =
      (fun v => ∑ w : AES.WordState,
        (markedWeight m yu.1 x w * tensorActivityKernel yu.2 (outputSource m w)) *
          tensorActivityKernel v (inputSource m w)) := by
    funext v
    exact physicalKernel_formula m yu.1 x yu.2 v
  rw [he]
  exact project_sum_columns _ _

/-- Two-sided frame analysis is exactly the existing contracted boundary
matrix, with activity choices joined in physical order. -/
theorem physical_contraction_eq (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool) :
    WordActivityArray.contraction (physicalKernel m) so si =
      WordOperatorDuality.reshape m
        (WordMarkedResponse.boundaryContractedResponse m (WordActivitySplit.join m so si)) := by
  funext y x
  exact WordActivitySplit.physicalKernel_contraction m so si y x

/-- Both frame factors for the actual split marked AES boundary. The
remaining premises are explicit scalar-array and per-choice estimates. -/
theorem physicalKernel_array_bound (m : GraphPosition → Bool)
    (F : (OutputActivity m → Bool) → (InputActivity m → Bool) → ℝ) (n : ℝ)
    (hF : ∀ so si, 0 ≤ F so si)
    (hT : ∀ so si, EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m (WordActivitySplit.join m so si)))
      (F so si))
    (hScalar : EnergyBound F n) :
    EnergyBound (physicalKernel m)
      ((WordActivityFrame.conditioningFactor (Fintype.card (OutputActivity m)) *
        WordActivityFrame.conditioningFactor (Fintype.card (InputActivity m))) * n) := by
  apply WordActivityArray.activity_array_bound_of_sections (physicalKernel m) F n
    (physicalKernel_input_fixed m) (physicalKernel_output_fixed m) hF _ hScalar
  intro so si
  rw [physical_contraction_eq]
  exact hT so si

/-- The operator inequality applies to the actual marked H Pi H matrix on
whole AES word states, via exact physical coordinate equivalences. -/
theorem markedKernel_array_bound (m : GraphPosition → Bool)
    (F : (OutputActivity m → Bool) → (InputActivity m → Bool) → ℝ) (n : ℝ)
    (hF : ∀ so si, 0 ≤ F so si)
    (hT : ∀ so si, EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m (WordActivitySplit.join m so si)))
      (F so si))
    (hScalar : EnergyBound F n) :
    EnergyBound
      (WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor (Fintype.card (OutputActivity m)) *
        WordActivityFrame.conditioningFactor (Fintype.card (InputActivity m))) * n) := by
  have h := RectangularArrays.energyBound_reindex (physicalKernel m) _
    (WordActivitySplit.outputEquiv m).symm (WordActivitySplit.inputEquiv m).symm
    (physicalKernel_array_bound m F n hF hT hScalar)
  simpa only [WordActivitySplit.physicalKernel_matrix, Equiv.apply_symm_apply] using h

end AESPaper.WordPhysicalActivity
