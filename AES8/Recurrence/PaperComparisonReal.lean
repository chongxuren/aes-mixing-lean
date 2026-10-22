import AES8.Recurrence.PaperComparisonOrder
import AES8.Recurrence.PaperOutputEnvelopes

/-!
# Real-coordinate interface of the fixed rational paper maps

The matrices are scalar casts of the graph-defined rational maps. Matching
these maps to the physical AES block norms is a separate obligation.
-/
open scoped BigOperators
namespace AES8.PaperComparison

def realProfile (x : QProfile) : AES8.Profile := fun i => (x i : ℝ)
def realStep (i j : Fin 14) : ℝ := (stepMatrix i j : ℝ)
def realReturn (i j : Fin 14) : ℝ := (returnMatrix i j : ℝ)
def realMv (m : Fin 14 → Fin 14 → ℝ) (x : AES8.Profile) : AES8.Profile :=
  fun i => ∑ j, m i j * x j

 theorem realStep_nonneg (i j : Fin 14) : 0 ≤ realStep i j := by
  unfold realStep
  exact_mod_cast stepMatrix_nonneg i j
 theorem realReturn_nonneg (i j : Fin 14) : 0 ≤ realReturn i j := by
  unfold realReturn
  exact_mod_cast returnMatrix_nonneg i j

 theorem realProfile_mv (m : QMatrix) (x : QProfile) :
    realProfile (mv m x) = realMv (fun i j => (m i j : ℝ)) (realProfile x) := by
  ext i
  simp [realProfile, realMv, mv]

 theorem realProfile_add (x y : QProfile) :
    realProfile (x+y) = realProfile x + realProfile y := by
  ext i
  simp [realProfile]

 theorem real_even_eq : realProfile evenEnvelope = PaperOutputEnvelopes.evenEnvelope := by
  ext i
  fin_cases i <;> norm_num [realProfile, evenEnvelope, PaperOutputEnvelopes.evenEnvelope]
 theorem real_odd_eq : realProfile oddEnvelope = PaperOutputEnvelopes.oddEnvelope := by
  ext i
  fin_cases i <;> norm_num [realProfile, oddEnvelope, PaperOutputEnvelopes.oddEnvelope]
 theorem real_scales_eq : realProfile scales = AES8.d := by
  ext i
  fin_cases i <;> norm_num [realProfile, scales, AES8.d]

end AES8.PaperComparison
