import AESPaper.RawBoundaryOperator
import AESPaper.HardActivityArrays

/-!
# Exact per-choice coefficients for low raw C and t blocks
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryChoices
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.RawBoundaryIncidence (q zeroCount)
open AESPaper.RawBoundaryKernel (contractedResponse)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays (interiorEntry)
attribute [local instance] Classical.propDecidable

def e11 : ℝ := 1 / (q * (65536 : ℝ))
def e12 : ℝ := 1 / q
def e13 : ℝ := 1 / (65536 : ℝ)
def A22 : ℝ := 1 / (65536 : ℝ)
def B22 : ℝ := 1 / q
def e20 : ℝ := 1 / q
def e30 : ℝ := 1 / (65536 : ℝ)

theorem e11_nonnegative : 0 ≤ e11 := by norm_num [e11, q]
theorem e12_nonnegative : 0 ≤ e12 := by norm_num [e12, q]
theorem e13_nonnegative : 0 ≤ e13 := by norm_num [e13]
theorem A22_nonnegative : 0 ≤ A22 := by norm_num [A22]
theorem B22_nonnegative : 0 ≤ B22 := by norm_num [B22, q]
theorem e20_nonnegative : 0 ≤ e20 := by norm_num [e20, q]
theorem e30_nonnegative : 0 ≤ e30 := by norm_num [e30]

/-- Eight-position count balance, before any coefficient simplification. -/
theorem zeroCount_eq_of_card (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ell t : ℕ) (hlen : Fintype.card (Marked m) = ell) (ht : uniformCount s = t) :
    zeroCount m s = 8 - (ell + t) := by
  have hcount := MarkedBlockScale.count_balance m s
  dsimp only [zeroCount]
  omega

/-- Nonnegative coefficient identities are established by exact squares. -/
theorem coefficient_eq_of_square (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : ℝ) (hc : 0 ≤ c)
    (hs : RawBoundaryOperator.fiberProduct m s / q ^ uniformCount s = c ^ 2) :
    RawBoundaryOperator.coefficient m s = c := by
  apply (sq_eq_sq₀ (RawBoundaryOperator.coefficient_nonnegative m s) hc).mp
  rw [RawBoundaryOperator.coefficient_sq, hs]

theorem coefficient11_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 1) (ht : uniformCount s = 3) :
    RawBoundaryOperator.coefficient m s = e11 := by
  have hlen : Fintype.card (Marked m) = 2 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hz := zeroCount_eq_of_card m s 2 3 hlen ht
  apply coefficient_eq_of_square m s e11 e11_nonnegative
  norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, e11]

/-- Either physical orientation has this scalar identity at weights two/three. -/
theorem coefficient12_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hshape : (Fintype.card (OutputMarked m) = 1 ∧ Fintype.card (InputMarked m) = 2) ∨
      (Fintype.card (OutputMarked m) = 2 ∧ Fintype.card (InputMarked m) = 1))
    (ht : uniformCount s = 2 ∨ uniformCount s = 3) :
    RawBoundaryOperator.coefficient m s = e12 := by
  rcases hshape with ⟨hO,hI⟩ | ⟨hO,hI⟩
  all_goals
    rcases ht with ht | ht
    all_goals
      have hlen : Fintype.card (Marked m) = 3 := by
        rw [WordMarkedSplit.marked_card, hO, hI]
      have hz := zeroCount_eq_of_card m s 3 _ hlen ht
      apply coefficient_eq_of_square m s e12 e12_nonnegative
      norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, e12]

theorem coefficient13_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hshape : (Fintype.card (OutputMarked m) = 1 ∧ Fintype.card (InputMarked m) = 3) ∨
      (Fintype.card (OutputMarked m) = 3 ∧ Fintype.card (InputMarked m) = 1))
    (ht : uniformCount s = 1 ∨ uniformCount s = 2 ∨ uniformCount s = 3) :
    RawBoundaryOperator.coefficient m s = e13 := by
  rcases hshape with ⟨hO,hI⟩ | ⟨hO,hI⟩
  all_goals
    rcases ht with ht | ht | ht
    all_goals
      have hlen : Fintype.card (Marked m) = 4 := by
        rw [WordMarkedSplit.marked_card, hO, hI]
      have hz := zeroCount_eq_of_card m s 4 _ hlen ht
      apply coefficient_eq_of_square m s e13 e13_nonnegative
      norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, e13]

theorem coefficient22_line_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2)
    (ht : uniformCount s = 1 ∨ uniformCount s = 3) :
    RawBoundaryOperator.coefficient m s = A22 := by
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  rcases ht with ht | ht
  all_goals
    have hz := zeroCount_eq_of_card m s 4 _ hlen ht
    apply coefficient_eq_of_square m s A22 A22_nonnegative
    norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, A22]

theorem coefficient22_middle_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2) (ht : uniformCount s = 2) :
    RawBoundaryOperator.coefficient m s = B22 := by
  have hlen : Fintype.card (Marked m) = 4 := by
    rw [WordMarkedSplit.marked_card, hO, hI]
  have hz := zeroCount_eq_of_card m s 4 2 hlen ht
  apply coefficient_eq_of_square m s B22 B22_nonnegative
  norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, B22]

theorem coefficient20_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hshape : (Fintype.card (OutputMarked m) = 2 ∧ Fintype.card (InputMarked m) = 0) ∨
      (Fintype.card (OutputMarked m) = 0 ∧ Fintype.card (InputMarked m) = 2))
    (ht : uniformCount s = 3) : RawBoundaryOperator.coefficient m s = e20 := by
  rcases hshape with ⟨hO,hI⟩ | ⟨hO,hI⟩
  all_goals
    have hlen : Fintype.card (Marked m) = 2 := by
      rw [WordMarkedSplit.marked_card, hO, hI]
    have hz := zeroCount_eq_of_card m s 2 3 hlen ht
    apply coefficient_eq_of_square m s e20 e20_nonnegative
    norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, e20]

theorem coefficient30_eq (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hshape : (Fintype.card (OutputMarked m) = 3 ∧ Fintype.card (InputMarked m) = 0) ∨
      (Fintype.card (OutputMarked m) = 0 ∧ Fintype.card (InputMarked m) = 3))
    (ht : uniformCount s = 2 ∨ uniformCount s = 3) :
    RawBoundaryOperator.coefficient m s = e30 := by
  rcases hshape with ⟨hO,hI⟩ | ⟨hO,hI⟩
  all_goals
    rcases ht with ht | ht
    all_goals
      have hlen : Fintype.card (Marked m) = 3 := by
        rw [WordMarkedSplit.marked_card, hO, hI]
      have hz := zeroCount_eq_of_card m s 3 _ hlen ht
      apply coefficient_eq_of_square m s e30 e30_nonnegative
      norm_num [RawBoundaryOperator.fiberProduct, hO, hI, hz, ht, q, e30]

/-- Cancellation needs a nonempty total marking, allowing either side empty. -/
theorem boundary_zero_outside (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ell : ℕ) (hlen : Fintype.card (Marked m) = ell) (hell : 0 < ell)
    (hout : ¬ (4 < ell + uniformCount s ∧ uniformCount s < 4)) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s)) 0 := by
  have hn : Nonempty (Marked m) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hn
  apply RawBoundaryOperator.contracted_operator_zero m s ⟨p.val, p.property⟩
  rw [WordActivityCounts.surviving_iff, hlen]
  exact hout

/-- Total-two entry rule from its actual surviving coefficient. -/
theorem boundary_choice_two (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 2) (c : ℝ)
    (he : uniformCount s = 3 → RawBoundaryOperator.coefficient m s = c) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (if uniformCount s = 3 then c else 0) := by
  by_cases ht : uniformCount s = 3
  · rw [if_pos ht]
    simpa only [he ht] using RawBoundaryOperator.contracted_operator_bound m s
  · rw [if_neg ht]
    exact boundary_zero_outside m s 2 hlen (by decide) (by omega)

theorem boundary_choice_three (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 3) (c : ℝ)
    (he : uniformCount s = 2 ∨ uniformCount s = 3 → RawBoundaryOperator.coefficient m s = c) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (HardActivityArrays.entry32 c (uniformCount s)) := by
  unfold HardActivityArrays.entry32
  split_ifs with ht
  · simpa only [he ht] using RawBoundaryOperator.contracted_operator_bound m s
  · exact boundary_zero_outside m s 3 hlen (by decide) (by omega)

theorem boundary_choice_four (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 4) (A B : ℝ)
    (heA : uniformCount s = 1 ∨ uniformCount s = 3 → RawBoundaryOperator.coefficient m s = A)
    (heB : uniformCount s = 2 → RawBoundaryOperator.coefficient m s = B) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (interiorEntry A B (uniformCount s)) := by
  unfold interiorEntry
  split_ifs with ht ht2
  · simpa only [heA ht] using RawBoundaryOperator.contracted_operator_bound m s
  · simpa only [heB ht2] using RawBoundaryOperator.contracted_operator_bound m s
  · exact boundary_zero_outside m s 4 hlen (by decide) (by omega)

theorem boundary_choice_bound11 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (if uniformCount s = 3 then e11 else 0) := by
  apply boundary_choice_two m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e11
  exact coefficient11_eq m s hO hI

theorem boundary_choice_bound12 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (HardActivityArrays.entry32 e12 (uniformCount s)) := by
  apply boundary_choice_three m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e12
  exact coefficient12_eq m s (Or.inl ⟨hO,hI⟩)

theorem boundary_choice_bound21 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (HardActivityArrays.entry32 e12 (uniformCount s)) := by
  apply boundary_choice_three m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e12
  exact coefficient12_eq m s (Or.inr ⟨hO,hI⟩)

theorem boundary_choice_bound13 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 1)
    (hI : Fintype.card (InputMarked m) = 3) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (interiorEntry e13 e13 (uniformCount s)) := by
  apply boundary_choice_four m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e13 e13
  · intro ht
    exact coefficient13_eq m s (Or.inl ⟨hO,hI⟩) (by omega)
  · intro ht
    exact coefficient13_eq m s (Or.inl ⟨hO,hI⟩) (by omega)

theorem boundary_choice_bound31 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 1) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (interiorEntry e13 e13 (uniformCount s)) := by
  apply boundary_choice_four m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e13 e13
  · intro ht
    exact coefficient13_eq m s (Or.inr ⟨hO,hI⟩) (by omega)
  · intro ht
    exact coefficient13_eq m s (Or.inr ⟨hO,hI⟩) (by omega)

theorem boundary_choice_bound22 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (interiorEntry A22 B22 (uniformCount s)) := by
  apply boundary_choice_four m s (by rw [WordMarkedSplit.marked_card, hO, hI]) A22 B22
  · exact coefficient22_line_eq m s hO hI
  · exact coefficient22_middle_eq m s hO hI

theorem boundary_choice_bound20 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 2)
    (hI : Fintype.card (InputMarked m) = 0) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (if uniformCount s = 3 then e20 else 0) := by
  apply boundary_choice_two m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e20
  exact coefficient20_eq m s (Or.inl ⟨hO,hI⟩)

theorem boundary_choice_bound02 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 2) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (if uniformCount s = 3 then e20 else 0) := by
  apply boundary_choice_two m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e20
  exact coefficient20_eq m s (Or.inr ⟨hO,hI⟩)

theorem boundary_choice_bound30 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 3)
    (hI : Fintype.card (InputMarked m) = 0) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (HardActivityArrays.entry32 e30 (uniformCount s)) := by
  apply boundary_choice_three m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e30
  exact coefficient30_eq m s (Or.inl ⟨hO,hI⟩)

theorem boundary_choice_bound03 (m : GraphPosition → Bool)
    (hO : Fintype.card (OutputMarked m) = 0)
    (hI : Fintype.card (InputMarked m) = 3) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (HardActivityArrays.entry32 e30 (uniformCount s)) := by
  apply boundary_choice_three m s (by rw [WordMarkedSplit.marked_card, hO, hI]) e30
  exact coefficient30_eq m s (Or.inr ⟨hO,hI⟩)

end AESPaper.RawBoundaryChoices
