import AESPaper.WordMarkedEnergy
import AESPaper.WordOperatorDuality

/-!
# Physical per-choice Frobenius and operator bounds

All powers have natural exponents. The coefficient is the square root of the
literal scaled moment expression, rather than a formula with negative natural
exponents. Outside the surviving range the actual matrix is exactly zero.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordPhysicalEnergy
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESPaper.RectangularFourier (rectAction EnergyBound)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordMarkedMoment (q tau delta)
open AESPaper.WordMarkedResponse (boundaryContractedResponse)
open AESPaper.WordMarkedEnergy (dimension)
attribute [local instance] Classical.propDecidable

section Rectangular
variable {Y X : Type*} [Fintype Y] [Fintype X]

/-- Rowwise Cauchy--Schwarz, with arbitrary signed input and matrix entries. -/
theorem rectangular_energy_le_frobenius (M : Y → X → ℝ) (f : X → ℝ) :
    (∑ y : Y, rectAction M f y ^ 2) ≤
      (∑ y : Y, ∑ x : X, M y x ^ 2) * ∑ x : X, f x ^ 2 := by
  calc
    (∑ y : Y, rectAction M f y ^ 2) ≤
        ∑ y : Y, (∑ x : X, M y x ^ 2) * ∑ x : X, f x ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M y) f
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A proved Frobenius estimate supplies the full signed-input predicate. -/
theorem energyBound_of_frobenius (M : Y → X → ℝ) (c : ℝ)
    (h : (∑ y : Y, ∑ x : X, M y x ^ 2) ≤ c ^ 2) : EnergyBound M c := by
  intro f
  calc
    (∑ y : Y, rectAction M f y ^ 2) ≤
        (∑ y : Y, ∑ x : X, M y x ^ 2) * ∑ x : X, f x ^ 2 :=
      rectangular_energy_le_frobenius M f
    _ ≤ c ^ 2 * ∑ x : X, f x ^ 2 :=
      mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun x _ => sq_nonneg (f x))

end Rectangular

/-- Exact reindexing by the physical output/input tuple equivalence. -/
theorem reshape_frobenius (m : GraphPosition → Bool)
    (v : (Marked m → AES.Word) → ℝ) :
    (∑ y : OutputMarked m → AES.Word, ∑ x : InputMarked m → AES.Word,
      WordOperatorDuality.reshape m v y x ^ 2) =
      ∑ z : Marked m → AES.Word, v z ^ 2 := by
  exact (WordMarkedSplit.sum_tuples m (fun z => v z ^ 2)).symm

/-- Literal nonnegative squared coefficient from the complete mixed moment. -/
def momentEnergy (ell d : ℕ) : ℝ :=
  (q ^ ell * ((tau ^ 2 / q) ^ min d (ell-d) *
    delta ^ (ell-2*min d (ell-d)))) / q ^ 4

def momentCoefficient (ell d : ℕ) : ℝ := Real.sqrt (momentEnergy ell d)

theorem q_positive : 0 < q := by norm_num [q]

theorem momentEnergy_nonnegative (ell d : ℕ) : 0 ≤ momentEnergy ell d := by
  have hd : 0 ≤ delta := by norm_num [delta, q]
  unfold momentEnergy
  exact div_nonneg
    (mul_nonneg (pow_nonneg q_positive.le ell)
      (mul_nonneg
        (pow_nonneg (div_nonneg (sq_nonneg tau) q_positive.le) _)
        (pow_nonneg hd _)))
    (pow_nonneg q_positive.le 4)

theorem momentCoefficient_nonnegative (ell d : ℕ) :
    0 ≤ momentCoefficient ell d := Real.sqrt_nonneg _

theorem momentCoefficient_sq (ell d : ℕ) :
    momentCoefficient ell d ^ 2 = momentEnergy ell d :=
  Real.sq_sqrt (momentEnergy_nonnegative ell d)

/-- The proved physical counting-energy bound, with the exact q^4 scale
removed. The information-set partition and input transpose are inherited from
the actual boundary theorem rather than supplied as hypotheses. -/
theorem boundary_contracted_frobenius_le
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    (∑ y : OutputMarked m → AES.Word, ∑ x : InputMarked m → AES.Word,
      WordOperatorDuality.reshape m (boundaryContractedResponse m s) y x ^ 2) ≤
      momentEnergy ell d := by
  rw [reshape_frobenius]
  unfold momentEnergy
  apply (le_div_iff₀ (pow_pos q_positive 4)).mpr
  simpa only [mul_comm] using
    WordMarkedEnergy.boundary_contracted_energy_scaled m s d ell hlen hdim hdle

/-- Actual physical per-choice operator bound for every joint signed input. -/
theorem boundary_contracted_operator_bound
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    EnergyBound (WordOperatorDuality.reshape m (boundaryContractedResponse m s))
      (momentCoefficient ell d) := by
  apply energyBound_of_frobenius
  rw [momentCoefficient_sq]
  exact boundary_contracted_frobenius_le m s d ell hlen hdim hdle

/-- The accepted piecewise physical energy theorem under the exact reshape. -/
theorem boundary_contracted_frobenius_scaled_piecewise
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true) :
    q ^ 4 *
        (∑ y : OutputMarked m → AES.Word, ∑ x : InputMarked m → AES.Word,
          WordOperatorDuality.reshape m (boundaryContractedResponse m s) y x ^ 2) ≤
      if 0 < dimension m s ∧ dimension m s < Fintype.card (Marked m) then
        q ^ Fintype.card (Marked m) *
          ((tau ^ 2 / q) ^ min (dimension m s) (Fintype.card (Marked m)-dimension m s) *
            delta ^ (Fintype.card (Marked m)-
              2*min (dimension m s) (Fintype.card (Marked m)-dimension m s)))
      else 0 := by
  rw [reshape_frobenius]
  exact WordMarkedEnergy.boundary_contracted_energy_piecewise m s hm

/-- Nonsurviving cases vanish as matrices, before any norm estimate. -/
theorem boundary_reshape_zero_outside_surviving
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < dimension m s ∧ dimension m s < Fintype.card (Marked m))) :
    WordOperatorDuality.reshape m (boundaryContractedResponse m s) = fun _ _ => 0 := by
  funext y x
  exact WordMarkedEnergy.boundary_contracted_zero_outside_surviving m s hm hout
    (WordMarkedSplit.join m y x)

theorem boundary_contracted_operator_zero
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < dimension m s ∧ dimension m s < Fintype.card (Marked m))) :
    EnergyBound (WordOperatorDuality.reshape m (boundaryContractedResponse m s)) 0 := by
  rw [boundary_reshape_zero_outside_surviving m s hm hout]
  intro f
  simp [rectAction]

/-- Complete coefficient; literal zero is used outside the surviving range. -/
def piecewiseCoefficient (m : GraphPosition → Bool) (s : Activity m → Bool) : ℝ :=
  if 0 < dimension m s ∧ dimension m s < Fintype.card (Marked m) then
    momentCoefficient (Fintype.card (Marked m)) (dimension m s)
  else 0

theorem piecewiseCoefficient_nonnegative
    (m : GraphPosition → Bool) (s : Activity m → Bool) :
    0 ≤ piecewiseCoefficient m s := by
  unfold piecewiseCoefficient
  split_ifs
  · exact momentCoefficient_nonnegative _ _
  · exact le_rfl

/-- Unconditional actual per-choice bound for every nonempty residual marking.
This is the generic Frobenius bridge, not the sharper line/plane bound. -/
theorem boundary_contracted_operator_piecewise
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true) :
    EnergyBound (WordOperatorDuality.reshape m (boundaryContractedResponse m s))
      (piecewiseCoefficient m s) := by
  unfold piecewiseCoefficient
  split_ifs with hs
  · apply boundary_contracted_operator_bound m s (dimension m s)
      (Fintype.card (Marked m)) rfl _ (by omega)
    dsimp only [dimension] at hs ⊢
    omega
  · exact boundary_contracted_operator_zero m s hm hs

end AESPaper.WordPhysicalEnergy
