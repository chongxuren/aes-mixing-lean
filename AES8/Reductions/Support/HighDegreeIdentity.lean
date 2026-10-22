/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.LegacyProjection
import AES8.Recurrence.TransferAssembly
import AESConcrete.PhysicalLowHigh

/-!
# The actual support high part in whole-word degree coordinates

The generic kernel identities `PhysicalLowHigh.degree_three_refined` and
`degree_four_refined` already exist. This module does not reprove them.
It transports those identities through the exact support/refined-kernel
action bridge to the current `SupportEvolution.highPart`, then expands the
current `TransferAssembly.highReturn` with both centered steps retained.

Inputs are arbitrary signed joint real functions on the full word-state
space. No zero-extension premise is needed: only positive degrees three
and four occur, whose support refinements are already complete without the
omitted degree-zero, support-zero component.

This supplies exact interface identities only. It does not identify the
fixed marked diffusion graphs, expand their shared activity metric, prove
any norm cap, or close a return cell or the complete AES theorem.
Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.HighDegreeIdentity
open AESMixing AESMixing.AES
open AESConcrete.RefinedWordProjection (refinedKernel)
open AES8.SupportProfile (component)
open AES8.SupportEvolution (highPart)
open AES8.TransferAssembly (centeredStep highReturn)

/-- Exact high projection on the full space, for arbitrary signed joint input.
The generic legacy kernel splitting is reused through the existing adapter;
the fourteen-coordinate decomposition of the entire input is not invoked. -/
theorem highPart_eq_degrees (f : WordState → ℝ) :
    highPart f =
      degreeComponent (0 : AES.Word) 3 f +
        degreeComponent (0 : AES.Word) 4 f := by
  have h11 : component f 11 = action (refinedKernel (0 : AES.Word) 3 3) f :=
    LegacyProjection.component_eq_refinedKernel_action f 11
  have h12 : component f 12 = action (refinedKernel (0 : AES.Word) 3 4) f :=
    LegacyProjection.component_eq_refinedKernel_action f 12
  have h13 : component f 13 = action (refinedKernel (0 : AES.Word) 4 4) f :=
    LegacyProjection.component_eq_refinedKernel_action f 13
  have h3 : degreeComponent (0 : AES.Word) 3 f =
      component f 11 + component f 12 := by
    rw [← degreeKernel_action,
      AESConcrete.PhysicalLowHigh.degree_three_refined, kernel_action_add]
    rw [← h11, ← h12]
  have h4 : degreeComponent (0 : AES.Word) 4 f = component f 13 := by
    rw [← degreeKernel_action,
      AESConcrete.PhysicalLowHigh.degree_four_refined]
    exact h13.symm
  rw [h3, h4]
  funext x
  simp [SupportEvolution.highPart, Fin.sum_univ_succ, add_assoc]

/-- The actual high return retains a centered step on both sides of the exact
sum of the degree-three and degree-four intermediate projections. -/
theorem highReturn_eq_centered_degree_sum (f : WordState → ℝ) :
    highReturn f = centeredStep
      (degreeComponent (0 : AES.Word) 3 (centeredStep f) +
        degreeComponent (0 : AES.Word) 4 (centeredStep f)) := by
  unfold highReturn
  rw [highPart_eq_degrees]

/-- Additive expansion of that same actual centered return; the intermediate
projections and the inner centered physical update are present in both terms. -/
theorem highReturn_eq_degree_returns (f : WordState → ℝ) :
    highReturn f =
      centeredStep (degreeComponent (0 : AES.Word) 3 (centeredStep f)) +
        centeredStep (degreeComponent (0 : AES.Word) 4 (centeredStep f)) := by
  rw [highReturn_eq_centered_degree_sum, TransferAssembly.centeredStep_add]

end AES8.HighDegreeIdentity
