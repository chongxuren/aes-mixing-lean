import AESPaper.OneSourceLaw
import AESPaper.StartingWordDegrees
import AESMixing.Product

/-!
# The exact activity component of the actual one-source law

Degree zero here counts residual 32-bit words in the full state. Its
activity kernel averages independently within each zero/nonzero cell.
Every unit-mass law supported on the all-active cell therefore has the
same activity projection, regardless of correlations among its words.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.OneSourceActivity
open AESMixing AESConcrete
open AESPaper.StartingWord (q)

section GenericCell
variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

/-- The uniform law on the cell with all four coordinates nonzero. -/
def cellLaw : (Fin 4 → V) → ℝ :=
  fun y => ∏ i : Fin 4, uniformExcept (0 : V) (y i)

theorem cellLaw_apply (y : Fin 4 → V) :
    cellLaw y = if (∀ i, y i ≠ 0) then 1/(Fintype.card V-1 : ℝ)^4 else 0 := by
  by_cases hy : ∀ i, y i ≠ 0
  · rw [if_pos hy]
    have hu (i : Fin 4) : uniformExcept (0 : V) (y i) = 1/(Fintype.card V-1 : ℝ) := by
      rw [uniformExcept, if_neg (hy i)]
    unfold cellLaw
    simp only [hu, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div_pow]
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ := not_forall.mp hy
    have hzero : y i = 0 := not_not.mp hi
    unfold cellLaw
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hzero, uniformExcept, if_true]

theorem activityMatrix_nonzero_source (y x : V) (hx : x ≠ 0) :
    activityMatrix (0 : V) y x = uniformExcept (0 : V) y := by
  by_cases hy : y = 0 <;> simp only [activityMatrix, uniformExcept, hy, hx, if_true, if_false]

/-- The whole degree-zero column is constant over all-active input labels. -/
theorem degree_zero_kernel_allActive (y x : Fin 4 → V) (hx : ∀ i, x i ≠ 0) :
    degreeKernel (0 : V) 0 y x = cellLaw y := by
  rw [degreeKernel_zero]
  simp only [productProjection, degreePiece, Bool.false_eq_true, if_false, cellLaw]
  apply Finset.prod_congr rfl
  intro i _
  exact activityMatrix_nonzero_source (y i) (x i) (hx i)

/-- Only actual mass and support are needed; no product-law hypothesis occurs. -/
theorem degree_zero_of_allActive (f : (Fin 4 → V) → ℝ)
    (hmass : (∑ y, f y) = 1)
    (hsupport : ∀ y i, y i = 0 → f y = 0) :
    degreeComponent (0 : V) 0 f = cellLaw := by
  funext y
  rw [← degreeKernel_action]
  change (∑ x, degreeKernel (0 : V) 0 y x * f x) = cellLaw y
  have hterm (x : Fin 4 → V) :
      degreeKernel (0 : V) 0 y x * f x = cellLaw y * f x := by
    by_cases hx : ∀ i, x i ≠ 0
    · rw [degree_zero_kernel_allActive y x hx]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hzero : x i = 0 := not_not.mp hi
      rw [hsupport x i hzero, mul_zero, mul_zero]
  simp only [hterm, ← Finset.mul_sum, hmass, mul_one]

theorem uniformExcept_energy (hn : 1 < Fintype.card V) :
    (∑ x : V, uniformExcept (0 : V) x ^ 2) = 1/(Fintype.card V-1 : ℝ) := by
  have hpoint (x : V) : uniformExcept (0 : V) x ^ 2 =
      (1/(Fintype.card V-1 : ℝ)) * uniformExcept (0 : V) x := by
    by_cases hx : x = 0 <;> simp [uniformExcept, hx, pow_two]
  simp only [hpoint, ← Finset.mul_sum, GroupedLaw.uniform_total (0 : V) hn, mul_one]

theorem cellLaw_mass (hn : 1 < Fintype.card V) :
    (∑ y : Fin 4 → V, cellLaw y) = 1 := by
  unfold cellLaw
  rw [← Fintype.prod_sum]
  simp only [GroupedLaw.uniform_total (0 : V) hn, Finset.prod_const_one]

theorem cellLaw_zero : cellLaw (0 : Fin 4 → V) = 0 := by
  simp [cellLaw, uniformExcept]

theorem cellLaw_energy (hn : 1 < Fintype.card V) :
    (∑ y : Fin 4 → V, cellLaw y ^ 2) = 1/(Fintype.card V-1 : ℝ)^4 := by
  unfold cellLaw
  rw [product_column_energy]
  simp only [uniformExcept_energy hn, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_div_pow]

end GenericCell

/-- The actual one-source activity output is the uniform all-active cell. -/
theorem activity_law (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    degreeComponent (0 : AES.Word) 0 (OneSourceLaw.law k a) = cellLaw :=
  degree_zero_of_allActive (OneSourceLaw.law k a) (OneSourceLaw.law_mass k a)
    (fun y i hy => OneSourceLaw.law_zero_of_coordinate_zero k a ha y i hy)

theorem activity_uniformExcept :
    degreeComponent (0 : AES.Word) 0 (uniformExcept (0 : AES.WordState)) =
      uniformExcept 0 := by
  rw [← degreeKernel_action]
  exact StartingWordDegrees.pointed_uniformExcept
    (degree_zero_pointed (0 : AES.Word) AESConcrete.AES.word_card_gt_one)

theorem centered_activity_law (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    degreeComponent (0 : AES.Word) 0
        (OneSourceLaw.law k a-uniformExcept (0 : AES.WordState)) =
      cellLaw-uniformExcept (0 : AES.WordState) := by
  rw [← degreeKernel_action, action_sub, degreeKernel_action, degreeKernel_action,
    activity_law k a ha, activity_uniformExcept]

/-- The full-state reference is subtracted after the actual activity identity. -/
theorem centered_activity_energy (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y : AES.WordState, degreeComponent (0 : AES.Word) 0
      (OneSourceLaw.law k a-uniformExcept (0 : AES.WordState)) y ^ 2) =
        1/(q-1)^4 - 1/(q^4-1) := by
  rw [centered_activity_law k a ha]
  have hword : (Fintype.card AES.Word : ℝ) = q := StartingWord.q_eq_word_card.symm
  have hstate : (Fintype.card AES.WordState : ℝ) = q^4 := by
    change (Fintype.card (Fin 4 → AES.Word) : ℝ) = q^4
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, hword]
  have hn : 1 < Fintype.card AES.WordState := by
    change 1 < Fintype.card (Fin 4 → AES.Word)
    rw [Fintype.card_fun, Fintype.card_fin, AES.word_card]
    norm_num
  have h := centered_energy (cellLaw : AES.WordState → ℝ) (0 : AES.WordState)
    hn cellLaw_zero (cellLaw_mass AESConcrete.AES.word_card_gt_one)
  rw [cellLaw_energy AESConcrete.AES.word_card_gt_one, hword, hstate] at h
  simpa only [energy, Pi.sub_apply] using h

end AESPaper.OneSourceActivity
