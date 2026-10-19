import AESPaper.RectangularBounds
import AESPaper.WordActivityFrame
import AESMixing.MatrixEstimate
import AESMixing.WeightedRectangularSchur
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

/-!
# Boolean-choice scalar arrays and generic counting-energy helpers

Weights count true activity choices. Exact Boolean-tuple sums are proved by
an explicit head/tail equivalence, without the unbound selection-counting
module. All energy statements quantify over arbitrary real signed inputs.
Scalar array coefficients are raw; q^2 scaling and physical frame factors
belong to their separate application.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ScalarActivityArrays
open AESMixing AESPaper.RectangularFourier

abbrev Choice (n : ℕ) := Fin n → Bool

def weight {n : ℕ} (s : Choice n) : ℕ := ∑ k : Fin n, if s k then 1 else 0

def weightArray (a b : ℕ) (entry : ℕ → ℝ) : Choice a → Choice b → ℝ :=
  fun s t => entry (weight s + weight t)

def interiorEntry (A B : ℝ) (t : ℕ) : ℝ :=
  if t = 1 ∨ t = 3 then A else if t = 2 then B else 0

def endpointEntry (total : ℕ) (A B : ℝ) (t : ℕ) : ℝ :=
  if t = 0 ∨ t = total then A else B

theorem interiorEntry_nonnegative (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (t : ℕ) :
    0 ≤ interiorEntry A B t := by
  unfold interiorEntry
  split_ifs <;> positivity

theorem endpointEntry_nonnegative (total : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (t : ℕ) : 0 ≤ endpointEntry total A B t := by
  unfold endpointEntry
  split_ifs <;> positivity

theorem weightArray_nonnegative (a b : ℕ) (entry : ℕ → ℝ)
    (he : ∀ k, 0 ≤ entry k) (s : Choice a) (t : Choice b) :
    0 ≤ weightArray a b entry s t := he _

def choiceSuccEquiv (n : ℕ) : Choice (n+1) ≃ Bool × Choice n where
  toFun s := (s 0, fun i => s i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rcases p with ⟨b,s⟩; rfl

theorem sum_choice_succ {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Choice (n+1) → M) :
    (∑ s, f s) = (∑ t : Choice n, f (Fin.cons false t)) +
      ∑ t : Choice n, f (Fin.cons true t) := by
  rw [← (choiceSuccEquiv n).symm.sum_comp f, Fintype.sum_prod_type]
  simp [choiceSuccEquiv, add_comm]

theorem sum_choice_zero {M : Type*} [AddCommMonoid M] (f : Choice 0 → M) :
    (∑ s, f s) = f (fun i => Fin.elim0 i) := by
  rw [Fintype.sum_unique]
  congr 1

theorem weight_cons (n : ℕ) (b : Bool) (s : Choice n) :
    weight (Fin.cons b s) = (if b then 1 else 0) + weight s := by
  simp only [weight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem weight_zero (s : Choice 0) : weight s = 0 := by simp [weight]

theorem weight_one (s : Choice 1) : weight s = if s 0 then 1 else 0 := by
  unfold weight
  rw [Fin.sum_univ_succ]
  simp

theorem weight_le {n : ℕ} (s : Choice n) : weight s ≤ n := by
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      cases s i <;> simp
    _ = n := by simp

theorem weight_eq_card {n : ℕ} (s : Choice n) :
    weight s = Fintype.card {k : Fin n // s k = true} := by
  simp [weight, Fintype.card_subtype]

theorem sum_choice_one (f : Choice 1 → ℝ) :
    (∑ s, f s) = f ![false] + f ![true] := by
  have he : ((fun i : Fin 0 => Fin.elim0 i) : Choice 0) = ![] := by
    funext i
    exact Fin.elim0 i
  simp only [sum_choice_succ 0, sum_choice_zero, he, Matrix.vecCons]

theorem sum_choice_two (f : Choice 2 → ℝ) :
    (∑ s, f s) = f ![false,false] + f ![false,true] +
      f ![true,false] + f ![true,true] := by
  have he : ((fun i : Fin 0 => Fin.elim0 i) : Choice 0) = ![] := by
    funext i
    exact Fin.elim0 i
  simp only [sum_choice_succ 1, sum_choice_succ 0, sum_choice_zero, he, Matrix.vecCons]
  ring

theorem sum_choice_three (f : Choice 3 → ℝ) :
    (∑ s, f s) = f ![false,false,false] + f ![false,false,true] +
      f ![false,true,false] + f ![false,true,true] +
      f ![true,false,false] + f ![true,false,true] +
      f ![true,true,false] + f ![true,true,true] := by
  have he : ((fun i : Fin 0 => Fin.elim0 i) : Choice 0) = ![] := by
    funext i
    exact Fin.elim0 i
  simp only [sum_choice_succ 2, sum_choice_succ 1, sum_choice_succ 0,
    sum_choice_zero, he, Matrix.vecCons]
  ring

theorem sum_weight_one (f : ℕ → ℝ) :
    (∑ s : Choice 1, f (weight s)) = f 0 + f 1 := by
  norm_num [sum_choice_succ 0, sum_choice_zero, weight_cons, weight_zero]

theorem sum_weight_two (f : ℕ → ℝ) :
    (∑ s : Choice 2, f (weight s)) = f 0 + 2 * f 1 + f 2 := by
  norm_num [sum_choice_succ 1, sum_choice_succ 0, sum_choice_zero, weight_cons, weight_zero] <;> ring

theorem sum_weight_three (f : ℕ → ℝ) :
    (∑ s : Choice 3, f (weight s)) = f 0 + 3 * f 1 + 3 * f 2 + f 3 := by
  norm_num [sum_choice_succ 2, sum_choice_succ 1, sum_choice_succ 0,
    sum_choice_zero, weight_cons, weight_zero] <;> ring

theorem weightArray_swap (a b : ℕ) (entry : ℕ → ℝ) (s : Choice a) (t : Choice b) :
    weightArray a b entry s t = weightArray b a entry t s := by
  unfold weightArray
  rw [Nat.add_comm]

section EnergyHelpers
variable {Y X : Type*} [Fintype Y] [Fintype X] [DecidableEq X]

/-- The frozen rectangular Schur theorem in the accepted EnergyBound syntax. -/
theorem energyBound_of_row_col (M : Y → X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ y x, 0 ≤ M y x)
    (hrow : ∀ y, (∑ x, M y x) ≤ c) (hcol : ∀ x, (∑ y, M y x) ≤ c) :
    EnergyBound M c := by
  intro f
  simpa only [rectAction, action, pow_two] using
    rectangular_schur_energy M c c hc hM hrow hcol f

/-- The actual column Gram's absolute row cap bounds energy directly. -/
theorem energyBound_of_gram_rows (M : Y → X → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ x, (∑ z, |gram M x z|) ≤ R) :
    EnergyBound M (Real.sqrt R) := by
  intro f
  rw [Real.sq_sqrt hR]
  have he : (∑ y, rectAction M f y ^ 2) = ∑ x, f x * action (gram M) f x := by
    simpa only [rectAction, action, pow_two] using
      AESPaper.WordActivityFrame.synthesis_bilinear M f f
  rw [he]
  exact AESPaper.WordActivityFrame.symmetric_quadratic_le_row_sum
    (gram M) R (gram_symmetric M) hrow f

end EnergyHelpers
end AESPaper.ScalarActivityArrays
