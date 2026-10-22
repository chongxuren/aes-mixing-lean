/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ActivityAverageEnergy
import AES8.Reductions.Source.ConditionalSourceResponse
import AES8.Reductions.Support.NineActivityPatterns
import AES8.Estimates.Source.OneSourceEventMoment
import AES8.Estimates.FirstHigh.FirstHighNine

/-!
# Actual universal projected-boundary moment for first-high output nine

Choose one nonzero ORIGINAL initial source word and condition the other
three initial words jointly. The exact existing mixture preserves the
common source weight and four affine source-coordinate permutations.
The activity-average bound applies to each signed conditional response;
twelve orthogonal support/residual patterns give its component-nine energy.
The same boundary/projection operator is linear on the exact mixture, so
finite probability Jensen gives the actual universal energy bound.

The local atom, ordinary residual-column and total-trace resources give
q^5 times the projected-boundary energy at most
1542058752/(q*(q-1)), which is strictly below 1/10^10. The existing scalar
first-high-nine bridge is then instantiated with its 49/10^10 allowance.
No independence of the four later boundary words is assumed.

 No local Lean/scientific
execution, active-source/root/Audit edits, attacks, manuscript changes or
predecessor edits. No RemainingCaps witness or global closure is supplied.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ActualNineMoment
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component profile)
open AES8.FirstHighSupportEvent (boundaryInput)
open AES8.ConditionalSourceResponse
open AES8.OneSourceEventMoment (atomCap columnCap traceCap)

def residualLegs : Fin 4 → AES.Word → AES.Word → ℝ :=
  fun _ => residualMatrix AES.wordSuperboxKernel 0

def activityBudget : ℝ :=
  atomCap ^ 2 * columnCap ^ 2 * traceCap ^ 2 / ActivityAverageEnergy.denominator AES.Word

def projectedBudget : ℝ := 12 * activityBudget

/-- The imported tensor response puts its weight last; the activity theorem
puts the same original weight first. Only scalar commutativity is used. -/
theorem conditionalResponse_eq_activityResponse
    (b : AES.State) (k : Fin 4) (w : OtherAssignments k) :
    conditionalResponse b k w =
      ActivityAverageEnergy.response residualLegs (affineEquiv k w)
        (wordLaw (sourceInput b k)) := by
  funext y
  unfold conditionalResponse tensorResponse tensorColumn
    ActivityAverageEnergy.response residualLegs
  apply Finset.sum_congr rfl
  intro x _
  exact _root_.mul_comm _ _

/-- Each condition keeps arbitrary affine permutations; they need not fix zero.
The only word-law cap is charged to the chosen nonzero initial source. -/
theorem conditional_activity_energy_le (b : AES.State) (k : Fin 4)
    (hk : sourceInput b k ≠ 0) (w : OtherAssignments k)
    (c d : Fin 4) (hcd : c ≠ d) :
    (∑ y, ActivityAverageEnergy.projection c d
      (boundaryInput (conditionalResponse b k w)) y ^ 2) ≤ activityBudget := by
  rw [conditionalResponse_eq_activityResponse b k w]
  have h := ActivityAverageEnergy.wordMix_response_energy_le c d hcd
    residualLegs (affineEquiv k w) (wordLaw (sourceInput b k))
    atomCap columnCap traceCap (by norm_num [atomCap, q])
    (by norm_num [columnCap, q]) (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun _ x => OneSourceEventMoment.residual_column_le x)
    (fun _ => OneSourceEventMoment.residual_trace_le)
  change (∑ y, ActivityAverageEnergy.projection c d
    (fun z => ActivityAverageEnergy.response residualLegs (affineEquiv k w)
      (wordLaw (sourceInput b k)) (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
        atomCap ^ 2 * columnCap ^ 2 * traceCap ^ 2 /
          ActivityAverageEnergy.denominator AES.Word
  exact h

/-- Pythagoras on the twelve actual patterns is used before Jensen. -/
theorem conditional_projected_boundary_energy_le (b : AES.State) (k : Fin 4)
    (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    (∑ y, component (boundaryInput (conditionalResponse b k w)) 9 y ^ 2) ≤
      projectedBudget :=
  NineActivityPatterns.component_nine_energy_le_twelve
    (boundaryInput (conditionalResponse b k w)) activityBudget
    (fun c d hcd => conditional_activity_energy_le b k hk w c d hcd)

section MixtureLinearity
variable {W : Type*} [Fintype W]

/-- Exact finite-mixture transport through the actual boundary and component.
There is no convexity step or energy inequality in this identity. -/
theorem component_boundary_weighted_sum
    (eta : W → ℝ) (F : W → WordState → ℝ) (c : Fin 14) :
    component (boundaryInput (fun x => ∑ w, eta w * F w x)) c =
      fun y => ∑ w, eta w * component (boundaryInput (F w)) c y := by
  simp_rw [LegacyProjection.component_eq_projectionKernel_action]
  funext y
  unfold boundaryInput action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro x _
  ring

end MixtureLinearity

/-- The mixture is formed from the proved product law of initial sources.
Jensen is applied only after the exact signed operator identity above. -/
theorem actual_projected_boundary_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) ≤
      projectedBudget := by
  obtain ⟨k, hk, heta, htotal, hmixture⟩ :=
    exists_nonzero_source_probability_mixture b hb
  rw [hmixture, component_boundary_weighted_sum
    (conditionWeight b k) (conditionalResponse b k) (9 : Fin 14)]
  exact weighted_energy_le_uniform (conditionWeight b k)
    (fun w => component (boundaryInput (conditionalResponse b k w)) (9 : Fin 14))
    heta htotal projectedBudget
    (fun w => conditional_projected_boundary_energy_le b k hk w)

/-- Exact resource arithmetic; the word-cardinality theorem is symbolic and
no AES word/state enumeration is involved. -/
theorem scaled_projectedBudget :
    q ^ 5 * projectedBudget = (1542058752 : ℝ) / (q * (q - 1)) := by
  unfold projectedBudget activityBudget ActivityAverageEnergy.denominator
  rw [AES.word_card]
  norm_num [atomCap, columnCap, traceCap, q]

theorem rational_budget_lt :
    (1542058752 : ℝ) / (q * (q - 1)) < (1 : ℝ) / 10000000000 := by
  norm_num [q]

theorem small_budget_le_target :
    (1 : ℝ) / 10000000000 ≤ (49 : ℝ) / 10000000000 := by norm_num

/-- The universal actual moment, with its exact intermediate rational. -/
theorem scaled_projected_boundary_moment_le (b : AES.State) (hb : b ≠ 0) :
    q ^ 5 *
      (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) ≤
        (1542058752 : ℝ) / (q * (q - 1)) := by
  calc
    _ ≤ q ^ 5 * projectedBudget :=
      mul_le_mul_of_nonneg_left (actual_projected_boundary_energy_le b hb)
        (by norm_num [q])
    _ = _ := scaled_projectedBudget

theorem scaled_projected_boundary_moment_lt (b : AES.State) (hb : b ≠ 0) :
    q ^ 5 *
      (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) <
        (1 : ℝ) / 10000000000 :=
  (scaled_projected_boundary_moment_le b hb).trans_lt rational_budget_lt

/-- Exact allowance expected by the separately staged first-high scalar bridge. -/
theorem projected_boundary_moment_le_target (b : AES.State) (hb : b ≠ 0) :
    q ^ 5 *
      (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) ≤
        (49 : ℝ) / 10000000000 :=
  (scaled_projected_boundary_moment_lt b hb).le.trans small_budget_le_target

/-- Actual universal coordinate-nine first-high cap. This supplies one cap;
RemainingCaps, root-level assembly and the complete AES endpoint are separate. -/
theorem firstHigh_nine (b : AES.State) (hb : b ≠ 0) :
    profile (TransferAssembly.centeredStep
      (SupportEvolution.highPart (error 1 b))) (9 : Fin 14) ≤
      (d (9 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (9 : Fin 14)) :=
  FirstHighNine.firstHigh_nine_of_projected_boundary_moment b hb
    (projected_boundary_moment_le_target b hb)

end AES8.ActualNineMoment
