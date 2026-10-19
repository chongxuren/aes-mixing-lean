import AESPaper.ActualMixedPatternBounds
import AESPaper.MixedDegreeBudgets
import AESPaper.PureBiasActivity
import AESPaper.OneSourceProfile

/-!
# Actual several-source initialization from literal residual degrees

Each positive residual degree is the exact orthogonal sum of its literal
J/Z/R patterns. The actual per-pattern estimates are supplied by
`ActualMixedPatternBounds`; the rational scalar aggregation is supplied by
`MixedDegreeBudgets`. Only R labels count toward the degree. The nonzero-state
reference has no positive-degree component.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.SeveralSourcePositiveProfile
open AESMixing AESConcrete AESPaper.ProfileSpace
open AESPaper.StartingWord (q)
open AESPaper.ManySourceBounds (activeSourceCount)

/-- The stationary nonzero-state reference lies entirely in degree zero. -/
theorem uniform_positive_degree (j : Fin 5) (hj : j ≠ 0) :
    degreeComponent (0 : AES.Word) j (uniformExcept (0 : AES.WordState)) = 0 := by
  have hz : degreeComponent (0 : AES.Word) 0
      (uniformExcept (0 : AES.WordState)) = uniformExcept 0 :=
    ActivityReferenceCorrection.degree_zero_uniformExcept
      (0 : AES.Word) AES.word_card_gt_one
  calc
    _ = degreeComponent (0 : AES.Word) j
        (degreeComponent (0 : AES.Word) 0 (uniformExcept (0 : AES.WordState))) :=
      congrArg (degreeComponent (0 : AES.Word) j) hz.symm
    _ = 0 := by
      rw [degreeComponent_compose (0 : AES.Word) AES.word_card_gt_one, if_neg hj]

/-- Removing the actual nonzero-state reference leaves every positive
residual component unchanged. -/
theorem actual_positive_degree (b : AES.State) (j : Fin 5) (hj : j ≠ 0) :
    degreeComponent (0 : AES.Word) j (GroupedLaw.error 1 b) =
      degreeComponent (0 : AES.Word) j (GroupedLaw.groupedLaw 1 b) := by
  have hs : degreeComponent (0 : AES.Word) j (GroupedLaw.error 1 b) =
      degreeComponent (0 : AES.Word) j (GroupedLaw.groupedLaw 1 b) -
        degreeComponent (0 : AES.Word) j (uniformExcept (0 : AES.WordState)) := by
    change degreeComponent (0 : AES.Word) j
      (GroupedLaw.groupedLaw 1 b - uniformExcept (0 : AES.WordState)) = _
    simp only [← degreeKernel_action, action_sub]
  rw [hs, uniform_positive_degree j hj, sub_zero]

/-- The exact degree identity sums actual pattern bounds with the residual
index fixed. Bias factors are not included in that index. -/
theorem degree_scaled_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (j : Fin 5) (hj : j ≠ 0) :
    q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) j
      (GroupedLaw.groupedLaw 1 b) y ^ 2) ≤ MixedDegreeBudgets.degreeBudget j := by
  rw [BiasStartup.degree_energy]
  have hp : ∀ a : Fin 4 → Fin 3, TernaryDegree.residualIndex a = j →
      q ^ 5 * (∑ y, BiasStartup.term b a y ^ 2) ≤ MixedDegreeBudgets.budget a := by
    intro a ha
    have hr : TernaryDegree.residualIndex a ≠ 0 := by
      intro h0
      exact hj (ha.symm.trans h0)
    simpa only [BiasStartup.term] using
      ActualMixedPatternBounds.pattern_energy_le b hb a hr
  simpa only [Finset.mul_sum, mul_ite, mul_zero] using
    MixedDegreeBudgets.sum_le_degreeBudget
      (fun a : Fin 4 → Fin 3 => q ^ 5 * (∑ y, BiasStartup.term b a y ^ 2)) j hp

/-- Every positive residual-degree energy fits strictly inside its original
initial-profile entry, after the actual reference is removed. -/
theorem actual_positive_scaled_energy_lt (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) (j : Fin 5) (hj : j ≠ 0) :
    q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) j
      (GroupedLaw.error 1 b) y ^ 2) < AESPaper.initialProfile j ^ 2 := by
  rw [actual_positive_degree b j hj]
  exact (degree_scaled_energy_le b hb j hj).trans_lt
    (MixedDegreeBudgets.degreeBudget_lt_initialProfile j hj)

/-- The several-source positive-degree norm uses exactly q^(5/2)=2^80. -/
theorem scaled_positive_lt (i : Fin 5) (hi : i ≠ 0)
    (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    (2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i <
      AESPaper.initialProfile i := by
  have he := actual_positive_scaled_energy_lt b hb i hi
  have hs : ((2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i) ^ 2 =
      q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) i
        (GroupedLaw.error 1 b) y ^ 2) := by
    rw [mul_pow, ConcreteProfile.centeredError, OneSourceProfile.profile_energy_toLp]
    norm_num [q]
  have hv : 0 < AESPaper.initialProfile i := by
    fin_cases i <;> norm_num [AESPaper.initialProfile]
  have hsq := hs.trans_lt he
  nlinarith

theorem physical_positive_initial (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) (i : Fin 5) (hi : i ≠ 0) :
    ConcreteProfile.physicalProfile b 0 i ≤ AESPaper.initialEnvelope i := by
  have h := scaled_positive_lt i hi b hb
  change (2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i /
    AESPaper.weights i ≤ _
  exact (div_le_div_of_nonneg_right h.le (weights_positive i).le).trans
    (AESPaper.initial_envelope_valid i)

/-- The activity entry is imported from its checked reference-corrected
estimate; positive entries use the literal-pattern aggregation above. -/
theorem actual_scaled_energy_lt (b : AES.State) (hb0 : b ≠ 0)
    (hb : 2 ≤ activeSourceCount b) (j : Fin 5) :
    q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) j
      (GroupedLaw.error 1 b) y ^ 2) < AESPaper.initialProfile j ^ 2 := by
  by_cases hj : j = 0
  · subst j
    simpa only [AESPaper.initialProfile, Matrix.cons_val_zero] using
      PureBiasActivity.actual_activity_envelope b hb0 hb
  · exact actual_positive_scaled_energy_lt b hb j hj

/-- All five several-source entries satisfy the unnormalized initial profile. -/
theorem scaled_entry_lt (b : AES.State) (hb0 : b ≠ 0)
    (hb : 2 ≤ activeSourceCount b) (i : Fin 5) :
    (2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i <
      AESPaper.initialProfile i := by
  have he := actual_scaled_energy_lt b hb0 hb i
  have hs : ((2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i) ^ 2 =
      q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) i
        (GroupedLaw.error 1 b) y ^ 2) := by
    rw [mul_pow, ConcreteProfile.centeredError, OneSourceProfile.profile_energy_toLp]
    norm_num [q]
  have hv : 0 < AESPaper.initialProfile i := by
    fin_cases i <;> norm_num [AESPaper.initialProfile]
  have hsq := hs.trans_lt he
  nlinarith

/-- Complete initialization for the actual four-round law whenever at least
two first-layer source words are active. The one-source case is separate. -/
theorem physical_initial (b : AES.State) (hb0 : b ≠ 0)
    (hb : 2 ≤ activeSourceCount b) (i : Fin 5) :
    ConcreteProfile.physicalProfile b 0 i ≤ AESPaper.initialEnvelope i := by
  have h := scaled_entry_lt b hb0 hb i
  change (2 : ℝ) ^ 80 * profile (ConcreteProfile.centeredError 1 b) i /
    AESPaper.weights i ≤ _
  exact (div_le_div_of_nonneg_right h.le (weights_positive i).le).trans
    (AESPaper.initial_envelope_valid i)

end AESPaper.SeveralSourcePositiveProfile
