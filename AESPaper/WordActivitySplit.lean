import AESPaper.WordMarkedResponse
import AESPaper.WordMarkedSplit

/-!
# Physical output/input activity split and actual frame contractions
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordActivitySplit
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Activity)
attribute [local instance] Classical.propDecidable

abbrev OutputActivity (m : GraphPosition → Bool) := {i : Fin 4 // m (Sum.inl i) ≠ true}
abbrev InputActivity (m : GraphPosition → Bool) := {i : Fin 4 // m (Sum.inr i) ≠ true}

def outputPosition (m : GraphPosition → Bool) (i : OutputActivity m) : Activity m :=
  ⟨Sum.inl i.val, i.property⟩

def inputPosition (m : GraphPosition → Bool) (i : InputActivity m) : Activity m :=
  ⟨Sum.inr i.val, i.property⟩

/-- The physical sum split, with output and input roles retained. -/
def positionEquiv (m : GraphPosition → Bool) :
    OutputActivity m ⊕ InputActivity m ≃ Activity m where
  toFun := Sum.elim (outputPosition m) (inputPosition m)
  invFun p := match p with
    | ⟨Sum.inl i, h⟩ => Sum.inl ⟨i,h⟩
    | ⟨Sum.inr i, h⟩ => Sum.inr ⟨i,h⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl

@[simp] theorem positionEquiv_inl (m : GraphPosition → Bool) (i : OutputActivity m) :
    positionEquiv m (Sum.inl i) = outputPosition m i := rfl

@[simp] theorem positionEquiv_inr (m : GraphPosition → Bool) (i : InputActivity m) :
    positionEquiv m (Sum.inr i) = inputPosition m i := rfl

theorem activity_card (m : GraphPosition → Bool) :
    Fintype.card (Activity m) = Fintype.card (OutputActivity m) + Fintype.card (InputActivity m) := by
  rw [← Fintype.card_congr (positionEquiv m), Fintype.card_sum]

theorem sum_positions (m : GraphPosition → Bool) (f : Activity m → ℝ) :
    (∑ p : Activity m, f p) =
      (∑ i : OutputActivity m, f (outputPosition m i)) +
        ∑ i : InputActivity m, f (inputPosition m i) := by
  simpa only [Fintype.sum_sum_type, positionEquiv_inl, positionEquiv_inr] using
    ((positionEquiv m).sum_comp f).symm

theorem prod_positions (m : GraphPosition → Bool) (f : Activity m → ℝ) :
    (∏ p : Activity m, f p) =
      (∏ i : OutputActivity m, f (outputPosition m i)) *
        ∏ i : InputActivity m, f (inputPosition m i) := by
  simpa only [Fintype.prod_sum_type, positionEquiv_inl, positionEquiv_inr] using
    ((positionEquiv m).prod_comp f).symm

section Tuples
variable {V : Type*}

/-- Tuples split into their actual physical output and input restrictions. -/
def tupleEquiv (m : GraphPosition → Bool) :
    (Activity m → V) ≃ (OutputActivity m → V) × (InputActivity m → V) where
  toFun v := (fun i => v (outputPosition m i), fun i => v (inputPosition m i))
  invFun v := fun p => Sum.elim v.1 v.2 ((positionEquiv m).symm p)
  left_inv v := by
    funext p
    rcases p with ⟨p,h⟩
    cases p <;> rfl
  right_inv v := by
    apply Prod.ext <;> funext p <;> rfl

def join (m : GraphPosition → Bool) (y : OutputActivity m → V) (x : InputActivity m → V) :
    Activity m → V := (tupleEquiv m).symm (y,x)

@[simp] theorem join_output (m : GraphPosition → Bool)
    (y : OutputActivity m → V) (x : InputActivity m → V) (i : OutputActivity m) :
    join m y x (outputPosition m i) = y i := rfl

@[simp] theorem join_input (m : GraphPosition → Bool)
    (y : OutputActivity m → V) (x : InputActivity m → V) (i : InputActivity m) :
    join m y x (inputPosition m i) = x i := rfl

theorem join_restrictions (m : GraphPosition → Bool) (v : Activity m → V) :
    join m (fun i => v (outputPosition m i)) (fun i => v (inputPosition m i)) = v :=
  (tupleEquiv m).symm_apply_apply v

variable [Fintype V]

theorem sum_tuples (m : GraphPosition → Bool) (f : (Activity m → V) → ℝ) :
    (∑ v : Activity m → V, f v) =
      ∑ y : OutputActivity m → V, ∑ x : InputActivity m → V, f (join m y x) := by
  calc
    _ = ∑ yx : (OutputActivity m → V) × (InputActivity m → V),
        f ((tupleEquiv m).symm yx) := ((tupleEquiv m).symm.sum_comp f).symm
    _ = _ := by simp only [Fintype.sum_prod_type, join]

/-- Coordinate kernels factor in the same physical split as the tuples. -/
theorem coordinateKernel_join (m : GraphPosition → Bool)
    (T : Activity m → V → V → ℝ)
    (y v : OutputActivity m → V) (x w : InputActivity m → V) :
    coordinateKernel T (join m y x) (join m v w) =
      coordinateKernel (fun i => T (outputPosition m i)) y v *
        coordinateKernel (fun i => T (inputPosition m i)) x w := by
  unfold coordinateKernel
  rw [prod_positions]
  simp only [join_output, join_input]

end Tuples


/-- The actual normalized word-frame column factors across physical sides. -/
theorem frameColumn_join (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool)
    (u : OutputActivity m → AES.Word) (v : InputActivity m → AES.Word) :
    WordActivityFrame.frameColumn (join m so si) (join m u v) =
      WordActivityFrame.frameColumn so u * WordActivityFrame.frameColumn si v := by
  unfold WordActivityFrame.frameColumn
  rw [prod_positions]
  simp only [join_output, join_input]

/-- Actual marked sandwich, with residual and activity indices separated on
both physical sides. The same source remains on all eight graph positions. -/
def physicalKernel (m : GraphPosition → Bool) :
    ((WordMarkedSplit.OutputMarked m → AES.Word) × (OutputActivity m → AES.Word)) →
    ((WordMarkedSplit.InputMarked m → AES.Word) × (InputActivity m → AES.Word)) → ℝ :=
  fun yu xv => WordGraphKernel.wordVectorizedResponse m
    (MarkedBlockVectorization.join m (WordMarkedSplit.join m yu.1 xv.1) (join m yu.2 xv.2))

/-- Actual physical output coordinate permutation, including marked and
activity positions exactly once. -/
def outputEquiv (m : GraphPosition → Bool) :
    ((WordMarkedSplit.OutputMarked m → AES.Word) × (OutputActivity m → AES.Word)) ≃
      AES.WordState :=
  (MarkedBlockVectorization.partitionEquiv (V := AES.Word) (fun i => m (Sum.inl i))).symm

def inputEquiv (m : GraphPosition → Bool) :
    ((WordMarkedSplit.InputMarked m → AES.Word) × (InputActivity m → AES.Word)) ≃
      AES.WordState :=
  (MarkedBlockVectorization.partitionEquiv (V := AES.Word) (fun i => m (Sum.inr i))).symm

theorem physical_join (m : GraphPosition → Bool)
    (yu : (WordMarkedSplit.OutputMarked m → AES.Word) × (OutputActivity m → AES.Word))
    (xv : (WordMarkedSplit.InputMarked m → AES.Word) × (InputActivity m → AES.Word)) :
    MarkedBlockVectorization.join m (WordMarkedSplit.join m yu.1 xv.1) (join m yu.2 xv.2) =
      Sum.elim (outputEquiv m yu) (inputEquiv m xv) := by
  funext p
  cases p with
  | inl i =>
      by_cases h : m (Sum.inl i) = true <;>
        simp [MarkedBlockVectorization.join, outputEquiv,
          MarkedBlockVectorization.partitionEquiv, h,
          WordMarkedSplit.join, WordMarkedSplit.tupleEquiv, WordMarkedSplit.positionEquiv,
          join, tupleEquiv, positionEquiv]
  | inr i =>
      by_cases h : m (Sum.inr i) = true <;>
        simp [MarkedBlockVectorization.join, inputEquiv,
          MarkedBlockVectorization.partitionEquiv, h,
          WordMarkedSplit.join, WordMarkedSplit.tupleEquiv, WordMarkedSplit.positionEquiv,
          join, tupleEquiv, positionEquiv]

/-- The split kernel is exactly the actual marked H Pi H matrix in physical
coordinate equivalences, not a merely cardinality-equivalent matrix. -/
theorem physicalKernel_matrix (m : GraphPosition → Bool)
    (yu : (WordMarkedSplit.OutputMarked m → AES.Word) × (OutputActivity m → AES.Word))
    (xv : (WordMarkedSplit.InputMarked m → AES.Word) × (InputActivity m → AES.Word)) :
    physicalKernel m yu xv =
      WordGraphKernel.markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))
        (outputEquiv m yu) (inputEquiv m xv) := by
  unfold physicalKernel
  rw [physical_join, WordGraphKernel.wordVectorizedResponse_matrix]

theorem physicalKernel_splitResponse (m : GraphPosition → Bool)
    (y : WordMarkedSplit.OutputMarked m → AES.Word)
    (x : WordMarkedSplit.InputMarked m → AES.Word)
    (u : OutputActivity m → AES.Word) (v : InputActivity m → AES.Word) :
    physicalKernel m (y,u) (x,v) =
      MarkedBlockVectorization.splitResponse m (WordMarkedResponse.wordMarkedLeg m)
        (graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom)
        (WordMarkedSplit.join m y x) (join m u v) :=
  WordGraphKernel.wordVectorizedResponse_join m _ _

/-- Exact two-sided analysis contractions, with no inverse Gram absorbed into
an entry and no independence assumption on the marked residual tuple. -/
theorem physicalKernel_contraction (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool)
    (y : WordMarkedSplit.OutputMarked m → AES.Word)
    (x : WordMarkedSplit.InputMarked m → AES.Word) :
    (∑ u : OutputActivity m → AES.Word, ∑ v : InputActivity m → AES.Word,
      WordActivityFrame.frameColumn so u * physicalKernel m (y,u) (x,v) *
        WordActivityFrame.frameColumn si v) =
      WordMarkedResponse.boundaryContractedResponse m (join m so si)
        (WordMarkedSplit.join m y x) := by
  rw [WordMarkedResponse.boundaryContractedResponse_analyze]
  unfold WordFrameCoordinates.analyze action
  rw [sum_tuples]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  dsimp only
  rw [frameColumn_join]
  change _ = (WordActivityFrame.frameColumn so u * WordActivityFrame.frameColumn si v) *
    physicalKernel m (y,u) (x,v)
  ring

end AESPaper.WordActivitySplit
