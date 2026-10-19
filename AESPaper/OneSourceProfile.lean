import AESPaper.OneSourceActivity
import AESPaper.OneSourceBounds
import AESPaper.ConcreteProfile
import AESPaper.BoundaryZeros
import AESPaper.SmoothingArithmetic

/-!
# The complete actual one-source initial profile
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.OneSourceProfile
open AESMixing AESConcrete AESPaper.ProfileSpace
open AESPaper.StartingWord (q)

/-- A small coercion bridge prevents expansion of the concrete AES state space. -/
theorem profile_energy_toLp (i : Fin 5) (f : AES.WordState → ℝ) :
    profile (WithLp.toLp 2 f) i ^ 2 =
      ∑ y, degreeComponent (0 : AES.Word) i f y ^ 2 := by
  rw [profile, EuclideanSpace.real_norm_sq_eq]
  simp only [BoundaryZeros.component_toLp_apply]

theorem centeredError_one (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a) :
    ConcreteProfile.centeredError 1 b =
      WithLp.toLp 2 (OneSourceLaw.law k a - uniformExcept (0 : AES.WordState)) := by
  have he : GroupedLaw.error 1 b = OneSourceLaw.law k a - uniformExcept 0 := by
    funext y
    simp only [GroupedLaw.error, OneSourceLaw.groupedLaw_one_eq_law b k a hsource, Pi.sub_apply]
  exact congrArg (WithLp.toLp 2) he

theorem activity_energy (b : AES.State) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a) :
    profile (ConcreteProfile.centeredError 1 b) 0 ^ 2 =
      1/(q-1)^4 - 1/(q^4-1) := by
  rw [centeredError_one b k a hsource, profile_energy_toLp]
  exact OneSourceActivity.centered_activity_energy k a ha

/-- The square-root scaling is exactly q^(5/2)=2^80. -/
theorem scaled_activity_lt (b : AES.State) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a) :
    (2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) 0 < 21/10 := by
  have hs : ((2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) 0)^2 =
      q^5 * (1/(q-1)^4 - 1/(q^4-1)) := by
    rw [mul_pow, activity_energy b k a ha hsource]
    norm_num [q]
  have hnum : q^5 * (1/(q-1)^4 - 1/(q^4-1)) < (21/10:ℝ)^2 :=
    SmoothingArithmetic.reference_activity.trans SmoothingArithmetic.activity_profile
  have hsq := hs.trans_lt hnum
  nlinarith [profile_nonnegative (ConcreteProfile.centeredError 1 b) 0]

/-- The actual activity entry satisfies the paper's normalized initial envelope. -/
theorem physical_activity_initial (b : AES.State) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a) :
    ConcreteProfile.physicalProfile b 0 0 ≤ AESPaper.initialEnvelope 0 := by
  have h := scaled_activity_lt b k a ha hsource
  change (2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) 0 / 4096 ≤ 1/1000
  linarith

/-- The positive-degree energy estimates use the same exact normalization. -/
theorem scaled_positive_lt (i : Fin 5) (hi : i ≠ 0)
    (b : AES.State) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a) :
    (2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) i < AESPaper.initialProfile i := by
  have he := OneSourceBounds.scaled_positive_energy_lt i hi k a ha
  have hs : ((2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) i)^2 =
      q^5 * (∑ y, degreeComponent (0 : AES.Word) i
        (OneSourceLaw.law k a-uniformExcept (0 : AES.WordState)) y ^ 2) := by
    rw [mul_pow, centeredError_one b k a hsource, profile_energy_toLp]
    norm_num [q]
  have hv : 0 < AESPaper.initialProfile i := by
    fin_cases i <;> norm_num [AESPaper.initialProfile]
  have hsq := hs.trans_lt he
  nlinarith

/-- All five entries are now established for the actual four-round law of
one nonzero source word. This leaves the several-source cases explicit. -/
theorem physical_initial (b : AES.State) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (hsource : StartingWord.sourceInput b = BoundarySourceCoordinates.singleWord k a)
    (i : Fin 5) :
    ConcreteProfile.physicalProfile b 0 i ≤ AESPaper.initialEnvelope i := by
  by_cases hi : i=0
  · subst i
    exact physical_activity_initial b k a ha hsource
  · have h := scaled_positive_lt i hi b k a ha hsource
    change (2:ℝ)^80 * profile (ConcreteProfile.centeredError 1 b) i / AESPaper.weights i ≤ _
    exact (div_le_div_of_nonneg_right h.le (weights_positive i).le).trans
      (AESPaper.initial_envelope_valid i)

end AESPaper.OneSourceProfile
