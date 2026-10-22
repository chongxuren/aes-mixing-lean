/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.HighDegreeIdentity

/-!
# Exact removal of the global uniform correction inside a high return

The physical return is defined with both centered steps. Positive middle
degree annihilates the global uniform kernel on either side, so the two
corrections can be removed by exact identities for arbitrary signed joint
inputs. The actual middle projection remains degree three plus degree four.
This prepares the literal physical-kernel expansion used by marked graphs;
it supplies no norm cap or target mixing estimate.

Constructive proofs only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnCentering
open AESMixing
open AESMixing.AES (WordState)
open AES8.SupportEvolution (highPart)
open AES8.TransferAssembly (centeredStep highReturn)
open AESPaper.GroupedRecurrence (step)

theorem positive_degree_uniform_action (j : Fin 5) (hj : j ≠ 0)
    (f : WordState → ℝ) :
    degreeComponent (0 : AESMixing.AES.Word) j
      (action (AESConcrete.DegreeCentering.globalUniformKernel
        (0 : AESMixing.AES.Word)) f) = 0 := by
  rw [← degreeKernel_action, ← kernelCompose_action,
    AESConcrete.DegreeCentering.degreeKernel_compose_globalUniformKernel
      (0 : AESMixing.AES.Word) SupportProfile.word_card_gt_one j hj]
  exact zero_kernel_action f

theorem highPart_uniform_action (f : WordState → ℝ) :
    highPart (action (AESConcrete.DegreeCentering.globalUniformKernel
      (0 : AESMixing.AES.Word)) f) = 0 := by
  rw [HighDegreeIdentity.highPart_eq_degrees,
    positive_degree_uniform_action 3 (by decide),
    positive_degree_uniform_action 4 (by decide), add_zero]

theorem degree_sub (j : Fin 5) (f g : WordState → ℝ) :
    degreeComponent (0 : AESMixing.AES.Word) j (f - g) =
      degreeComponent (0 : AESMixing.AES.Word) j f -
        degreeComponent (0 : AESMixing.AES.Word) j g := by
  simp only [← degreeKernel_action, action_sub]

theorem highPart_sub (f g : WordState → ℝ) :
    highPart (f - g) = highPart f - highPart g := by
  simp only [HighDegreeIdentity.highPart_eq_degrees, degree_sub]
  abel

/-- No condition on the input: the positive middle projection itself kills
the inner uniform correction. -/
theorem highPart_centeredStep (f : WordState → ℝ) :
    highPart (centeredStep f) = highPart (step f) := by
  rw [TransferAssembly.centeredStep_formula, highPart_sub,
    highPart_uniform_action, sub_zero]

/-- Both cancellations are proved; the middle projection is retained. -/
theorem highReturn_eq_uncentered (f : WordState → ℝ) :
    highReturn f = step (highPart (step f)) := by
  rw [TransferAssembly.highReturn, TransferAssembly.centeredStep_high_eq_step,
    highPart_centeredStep]

def physicalReturnKernel : WordState → WordState → ℝ :=
  kernelCompose AESConcrete.WordStepZeros.wordStepKernel
    (kernelCompose
      (degreeKernel (0 : AESMixing.AES.Word) 3 +
        degreeKernel (0 : AESMixing.AES.Word) 4)
      AESConcrete.WordStepZeros.wordStepKernel)

/-- Literal two-step physical kernel with the exact high middle projection.
The cancellation above justifies this representation on all signed inputs. -/
theorem highReturn_eq_physical_action (f : WordState → ℝ) :
    highReturn f = action physicalReturnKernel f := by
  have hstep (g : WordState → ℝ) :
      action AESConcrete.WordStepZeros.wordStepKernel g = step g :=
    TransferZeros.physicalWordStep_eq_step g
  rw [highReturn_eq_uncentered, HighDegreeIdentity.highPart_eq_degrees]
  unfold physicalReturnKernel
  simp only [kernelCompose_action, kernel_action_add, degreeKernel_action, hstep]

end AES8.ReturnCentering
