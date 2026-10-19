import AESPaper.WordActivityCounts
import AESPaper.WordMomentCoefficients
import AESPaper.HardActivityArrays

/-!
# Physical per-choice bounds for activity/residual couplings

Only the total marked count is assumed. Thus the same actual moment
argument specializes to both (i,0) and (0,i), preserving the physical
input-adjoint flags without any sandwich symmetry premise. Nonsurviving
choices vanish as actual matrices. Scalar activity-array bounds, both
frame factors, position aggregation and q^2 scaling remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActivityCouplingChoices
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.WordMarkedMoment (q tau delta)
open AESPaper.WordPhysicalEnergy (momentEnergy momentCoefficient)
open AESPaper.ScalarActivityArrays (interiorEntry)
attribute [local instance] Classical.propDecidable

/-- Total marked count two, at its unique surviving uniform count. -/
def e2 : ℝ := tau / (q * (65536 : ℝ))

/-- Total marked count three, at either surviving uniform count. -/
def e3 : ℝ := tau * Real.sqrt delta / q

/-- Total marked count four, at uniform counts one and three. -/
def A4 : ℝ := tau * delta / (65536 : ℝ)

/-- Total marked count four, at uniform count two. -/
def B4 : ℝ := tau ^ 2 / q

theorem e2_nonnegative : 0 ≤ e2 := by
  exact div_nonneg WordMomentCoefficients.tau_nonnegative
    (mul_nonneg WordMomentCoefficients.q_positive.le (by norm_num))

theorem e3_nonnegative : 0 ≤ e3 := by
  exact div_nonneg
    (mul_nonneg WordMomentCoefficients.tau_nonnegative (Real.sqrt_nonneg _))
    WordMomentCoefficients.q_positive.le

theorem A4_nonnegative : 0 ≤ A4 := by
  exact div_nonneg
    (mul_nonneg WordMomentCoefficients.tau_nonnegative WordMomentCoefficients.delta_nonnegative)
    (by norm_num)

theorem B4_nonnegative : 0 ≤ B4 := by
  exact div_nonneg (sq_nonneg _) WordMomentCoefficients.q_positive.le

theorem moment_2_1 : momentCoefficient 2 1 = e2 := by
  apply WordMomentCoefficients.moment_eq_of_square 2 1 e2 e2_nonnegative
  norm_num [momentEnergy, q, e2] <;> ring

theorem moment_3_1 : momentCoefficient 3 1 = e3 := by
  apply WordMomentCoefficients.moment_eq_of_square 3 1 e3 e3_nonnegative
  unfold e3
  rw [div_pow, mul_pow, Real.sq_sqrt WordMomentCoefficients.delta_nonnegative]
  norm_num [momentEnergy] <;> field_simp [WordMomentCoefficients.q_nonzero] <;> ring

theorem moment_3_2 : momentCoefficient 3 2 = e3 := by
  have he : momentCoefficient 3 2 = momentCoefficient 3 1 := by
    norm_num [momentCoefficient, momentEnergy]
  rw [he, moment_3_1]

theorem moment_4_1 : momentCoefficient 4 1 = A4 := by
  apply WordMomentCoefficients.moment_eq_of_square 4 1 A4 A4_nonnegative
  norm_num [momentEnergy, q, A4] <;> ring

theorem moment_4_3 : momentCoefficient 4 3 = A4 := by
  have he : momentCoefficient 4 3 = momentCoefficient 4 1 := by
    norm_num [momentCoefficient, momentEnergy]
  rw [he, moment_4_1]

/-- Exact cancellation outside the additive surviving-count criterion.
Only a nonzero total marked count is required, not nonempty marked sides. -/
theorem boundary_zero_outside (m : GraphPosition → Bool) (s : Activity m → Bool)
    (ell : ℕ) (hlen : Fintype.card (Marked m) = ell) (hell : 0 < ell)
    (hout : ¬ (4 < ell + uniformCount s ∧ uniformCount s < 4)) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s)) 0 := by
  have hn : Nonempty (Marked m) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hn
  have hm : ∃ p, m p = true := ⟨p.val, p.property⟩
  apply WordPhysicalEnergy.boundary_contracted_operator_zero m s hm
  rw [WordActivityCounts.surviving_iff, hlen]
  exact hout

/-- Every total-two marking has exactly one possible surviving weight.
This includes both the activity-to-residual and reverse orientations. -/
theorem boundary_choice_bound2 (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 2) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (if uniformCount s = 3 then e2 else 0) := by
  have hcount := MarkedBlockScale.count_balance m s
  by_cases ht3 : uniformCount s = 3
  · rw [if_pos ht3]
    have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
      omega
    simpa only [moment_2_1] using
      WordPhysicalEnergy.boundary_contracted_operator_bound m s 1 2 hlen hdim (by omega)
  · rw [if_neg ht3]
    exact boundary_zero_outside m s 2 hlen (by decide) (by omega)

/-- The total-three choices are exactly the scalar entry32 rule; no
marked-side nonemptiness or operator symmetry assumption occurs. -/
theorem boundary_choice_bound3 (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 3) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (HardActivityArrays.entry32 e3 (uniformCount s)) := by
  have hcount := MarkedBlockScale.count_balance m s
  unfold HardActivityArrays.entry32
  split_ifs with ht
  · rcases ht with ht2 | ht3
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
        omega
      simpa only [moment_3_1] using
        WordPhysicalEnergy.boundary_contracted_operator_bound m s 1 3 hlen hdim (by omega)
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
        omega
      simpa only [moment_3_2] using
        WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 3 hlen hdim (by omega)
  · exact boundary_zero_outside m s 3 hlen (by decide) (by omega)

/-- Total marked count four uses moment dimensions one, two and three,
with actual cancellation outside the interior entry rule. -/
theorem boundary_choice_bound4 (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlen : Fintype.card (Marked m) = 4) :
    EnergyBound (WordOperatorDuality.reshape m
      (WordMarkedResponse.boundaryContractedResponse m s))
      (interiorEntry A4 B4 (uniformCount s)) := by
  have hcount := MarkedBlockScale.count_balance m s
  unfold interiorEntry
  split_ifs with ht ht2
  · rcases ht with ht1 | ht3
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4 := by
        omega
      simpa only [moment_4_1] using
        WordPhysicalEnergy.boundary_contracted_operator_bound m s 1 4 hlen hdim (by omega)
    · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 3 = 4 := by
        omega
      simpa only [moment_4_3] using
        WordPhysicalEnergy.boundary_contracted_operator_bound m s 3 4 hlen hdim (by omega)
  · have hdim : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 2 = 4 := by
      omega
    simpa only [WordMomentCoefficients.moment_4_2, B4] using
      WordPhysicalEnergy.boundary_contracted_operator_bound m s 2 4 hlen hdim (by omega)
  · exact boundary_zero_outside m s 4 hlen (by decide) (by omega)

end AESPaper.ActivityCouplingChoices
