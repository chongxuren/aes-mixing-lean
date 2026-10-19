import AESPaper.SuperboxGrouping
import AESMixing.ParallelSuperboxes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Exact physical/grouped correspondence for the v9 paper. Output coordinates
remove the final ShiftRows and transpose to four column words. The source
ShiftRows is retained explicitly in the superbox formula. No mixing estimate
or independent-current-word assumption enters this identification.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.GroupedLaw
open AESMixing AESMixing.AES

def outputCoordinates : WordState ≃+ State := transposeState.trans shiftRowsEquiv

def groupedLaw (n : ℕ) (a : State) (x : WordState) : ℝ :=
  physicalDifferenceLaw (2*n+2) a (outputCoordinates x)

def error (n : ℕ) (a : State) (x : WordState) : ℝ :=
  groupedLaw n a x - uniformExcept (0 : WordState) x

theorem uniform_total {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) : (∑ x, uniformExcept z x) = 1 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (Fintype.card V - 1 : ℝ) ≠ 0 := by linarith
  have hp (x : V) : uniformExcept z x =
      1/(Fintype.card V - 1 : ℝ) - if x=z then 1/(Fintype.card V - 1 : ℝ) else 0 := by
    by_cases h : x=z <;> simp [uniformExcept, h]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

theorem channel_total (s : Equiv.Perm State) (f : State → ℝ) :
    (∑ y, action (differenceChannel s) f y) = ∑ x, f x := by
  unfold action
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, differenceChannel_column, _root_.one_mul]

theorem channel_at_zero (s : Equiv.Perm State) (f : State → ℝ) :
    action (differenceChannel s) f 0 = f 0 := by
  simp [action, differenceChannel_zero_row, ite_mul]

theorem ordinary_total (n : ℕ) (a : State) : (∑ x, ordinaryDifferenceLaw n a x) = 1 := by
  induction n with
  | zero => simp [ordinaryDifferenceLaw, differencePoint]
  | succ n ih => rw [ordinaryDifferenceLaw, channel_total, ih]

theorem physical_total (r : ℕ) (a : State) : (∑ x, physicalDifferenceLaw r a x) = 1 := by
  cases r with
  | zero => simp [physicalDifferenceLaw, differencePoint]
  | succ n => rw [physicalDifferenceLaw, channel_total, ordinary_total]

theorem ordinary_at_zero (n : ℕ) (a : State) (ha : a ≠ 0) :
    ordinaryDifferenceLaw n a 0 = 0 := by
  induction n with
  | zero => simp [ordinaryDifferenceLaw, differencePoint, ha]
  | succ n ih => rw [ordinaryDifferenceLaw, channel_at_zero, ih]

theorem physical_at_zero (r : ℕ) (a : State) (ha : a ≠ 0) :
    physicalDifferenceLaw r a 0 = 0 := by
  cases r with
  | zero => simp [physicalDifferenceLaw, differencePoint, ha]
  | succ n => rw [physicalDifferenceLaw, channel_at_zero, ordinary_at_zero n a ha]

theorem uniform_output (x : WordState) :
    uniformExcept (0 : State) (outputCoordinates x) = uniformExcept (0 : WordState) x := by
  have he : outputCoordinates x = 0 ↔ x=0 := map_eq_zero_iff outputCoordinates outputCoordinates.injective
  simp only [uniformExcept, he]

theorem grouped_total (n : ℕ) (a : State) : (∑ x, groupedLaw n a x) = 1 := by
  unfold groupedLaw
  exact (Equiv.sum_comp outputCoordinates.toEquiv (physicalDifferenceLaw (2*n+2) a)).trans
    (physical_total _ a)

theorem error_zero (n : ℕ) (a : State) (ha : a ≠ 0) : error n a 0 = 0 := by
  simp only [error, groupedLaw, map_zero, physical_at_zero _ _ ha, uniformExcept,
    if_true, sub_self]

theorem error_sum (n : ℕ) (a : State) : (∑ x, error n a x) = 0 := by
  have hn : 1 < Fintype.card WordState := by rw [state_card]; norm_num
  simp only [error, Finset.sum_sub_distrib, grouped_total, uniform_total 0 hn, sub_self]

theorem grouped_tv (n : ℕ) (a : State) :
    tv (physicalDifferenceLaw (2*n+2) a) (uniformExcept (0 : State)) =
      (∑ x, |error n a x|)/2 := by
  unfold tv
  apply congrArg (fun t : ℝ => t/2)
  calc
    (∑ x, |physicalDifferenceLaw (2*n+2) a x - uniformExcept (0 : State) x|) =
        ∑ x, |physicalDifferenceLaw (2*n+2) a (outputCoordinates x) -
          uniformExcept (0 : State) (outputCoordinates x)| :=
      (Equiv.sum_comp outputCoordinates.toEquiv
        (fun x => |physicalDifferenceLaw (2*n+2) a x - uniformExcept (0 : State) x|)).symm
    _ = ∑ x, |error n a x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [uniform_output]
      rfl

theorem grouped_superbox_formula (n : ℕ) (a : State) (x : WordState) :
    groupedLaw n a x =
      superboxLaw (((interSuperboxLaw ∘ superboxLaw)^[n])
        (differencePoint (shiftRows a))) (transposeState x) := by
  unfold groupedLaw
  rw [physical_superbox_grouping, shift_differencePoint]
  let g := superboxLaw (((interSuperboxLaw ∘ superboxLaw)^[n])
    (differencePoint (shiftRows a)))
  change g (shiftRowsEquiv.symm (shiftRowsEquiv (transposeState x))) = g (transposeState x)
  exact congrArg g (shiftRowsEquiv.symm_apply_apply (transposeState x))

end AESPaper.GroupedLaw
