import AESPaper.ChoiceReindex
import AESPaper.WordActivitySplit
import AESPaper.WordMarkedEnergy

/-!
# Actual physical activity-choice and marked-position counts

The physical joins and marked/activity partitions are the accepted ones.
All-eight-position balance is reused from MarkedBlockScale. The surviving
dimension criterion is first stated additively, so natural subtraction
cannot turn a negative signed threshold into an unintended zero threshold.
Actual endpoint cancellation remains in WordMarkedEnergy.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordActivityCounts
open AESMixing AESConcrete AESPaper.RectangularFourier
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.WordActivitySplit (OutputActivity InputActivity join)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)

theorem output_marked_activity_card (m : GraphPosition → Bool) :
    Fintype.card (OutputMarked m) + Fintype.card (OutputActivity m) = 4 := by
  simpa only [Fintype.card_fin] using
    MarkedBlockScale.partition_card (fun i : Fin 4 => m (Sum.inl i))

theorem input_marked_activity_card (m : GraphPosition → Bool) :
    Fintype.card (InputMarked m) + Fintype.card (InputActivity m) = 4 := by
  simpa only [Fintype.card_fin] using
    MarkedBlockScale.partition_card (fun i : Fin 4 => m (Sum.inr i))

/-- True/uniform frame choices split by their actual physical sides. -/
theorem uniformCount_join (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool) :
    uniformCount (join m so si) = uniformCount so + uniformCount si := by
  have hj : join m so si =
      ChoiceReindex.tupleEquiv (WordActivitySplit.positionEquiv m) (Sum.elim so si) := rfl
  rw [hj, ChoiceReindex.uniformCount_tupleEquiv]
  let e : {p : OutputActivity m ⊕ InputActivity m // Sum.elim so si p = true} ≃
      {o : OutputActivity m // so o = true} ⊕ {i : InputActivity m // si i = true} :=
    { toFun := fun p => match p with
        | ⟨Sum.inl o,h⟩ => Sum.inl ⟨o,h⟩
        | ⟨Sum.inr i,h⟩ => Sum.inr ⟨i,h⟩
      invFun := fun p => match p with
        | Sum.inl o => ⟨Sum.inl o.val,o.property⟩
        | Sum.inr i => ⟨Sum.inr i.val,i.property⟩
      left_inv := by intro p; rcases p with ⟨p,h⟩; cases p <;> rfl
      right_inv := by intro p; cases p <;> rfl }
  change Fintype.card {p : OutputActivity m ⊕ InputActivity m // Sum.elim so si p = true} =
    Fintype.card {o : OutputActivity m // so o = true} +
      Fintype.card {i : InputActivity m // si i = true}
  simpa only [Fintype.card_sum] using Fintype.card_congr e

theorem uniformCount_join_weights (m : GraphPosition → Bool) (a b : ℕ)
    (eO : OutputActivity m ≃ Fin a) (eI : InputActivity m ≃ Fin b)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool) :
    uniformCount (join m so si) =
      ScalarActivityArrays.weight (ChoiceReindex.tupleEquiv eO so) +
        ScalarActivityArrays.weight (ChoiceReindex.tupleEquiv eI si) := by
  rw [uniformCount_join, ChoiceReindex.weight_tupleEquiv, ChoiceReindex.weight_tupleEquiv]

/-- Apply any proved canonical weight-array bound to the actual physical
activity choices, with no independence or normalization premise. -/
theorem energyBound_join_of_card (m : GraphPosition → Bool) (a b : ℕ)
    (hO : Fintype.card (OutputActivity m) = a) (hI : Fintype.card (InputActivity m) = b)
    (entry : ℕ → ℝ) (n : ℝ)
    (hScalar : EnergyBound (ScalarActivityArrays.weightArray a b entry) n) :
    EnergyBound (fun so si => entry (uniformCount (join m so si))) n := by
  have he : (fun so si => entry (uniformCount (join m so si))) =
      ChoiceReindex.countArray (A := OutputActivity m) (B := InputActivity m) entry := by
    funext so si
    rw [uniformCount_join]
    rfl
  rw [he]
  exact ChoiceReindex.energyBound_countArray_of_card a b hO hI entry n hScalar

/-- The accepted eight-position balance gives the exact activity budget. -/
theorem uniform_zero_count (m : GraphPosition → Bool) (s : Activity m → Bool) :
    uniformCount s + (maskSize (outputZeros m s) + maskSize (inputZeros m s)) =
      8 - Fintype.card (Marked m) := by
  have h := MarkedBlockScale.count_balance m s
  omega

/-- Additive criterion valid for every marking, including more than four
marked positions and zero uniform choices. -/
theorem surviving_iff (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (0 < WordMarkedEnergy.dimension m s ∧
      WordMarkedEnergy.dimension m s < Fintype.card (Marked m)) ↔
      (4 < Fintype.card (Marked m) + uniformCount s ∧ uniformCount s < 4) := by
  have h := MarkedBlockScale.count_balance m s
  unfold WordMarkedEnergy.dimension
  omega

/-- The familiar lower uniform-count threshold uses natural subtraction
only when at most four positions are marked. -/
theorem surviving_iff_subtraction (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hr : Fintype.card (Marked m) ≤ 4) :
    (0 < WordMarkedEnergy.dimension m s ∧
      WordMarkedEnergy.dimension m s < Fintype.card (Marked m)) ↔
      (4 - Fintype.card (Marked m) < uniformCount s ∧ uniformCount s < 4) := by
  rw [surviving_iff]
  omega

end AESPaper.WordActivityCounts
