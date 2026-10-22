/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.LegacyProjection
import AES8.Recurrence.TransferAssembly

/-!
# Exact centered-operator transfer bridge

The locally stated kernel is the expanded formula used by the predecessor's
`RefinedStepZeros.physicalBlock`, in the same fourteen-type order.  Only the
already vendored projection, centered-step and Euclidean interfaces are used;
the predecessor's numerical cap modules are not imported here.

The new counting profile is bounded by the norm of precisely this projected
centered operator, applied to its source component.  Thus a checked legacy
operator-norm cap can be transported without removing centering on an
individual component or introducing a state-space normalization factor.
The final low-cap statement remains conditional on its operator-norm bounds;
it does not provide those bounds, high returns, startup, or a mixing theorem.
Constructive proof work only; no attacks or predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.LegacyTransfer
open AESMixing AESMixing.AES AESConcrete
open AES8.SupportProfile AES8.LegacyProjection
open AES8.TransferAssembly (centeredStep physicalCoeff lowCoeff)

/-- The exact centered word kernel, retained on every individual input component. -/
def centeredKernel : WordState → WordState → ℝ :=
  AESConcrete.WordStepZeros.wordStepKernel -
    AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word)

theorem centeredStep_eq_centeredKernel_action (f : WordState → ℝ) :
    centeredStep f = action centeredKernel f := rfl

/-- The old physical sandwich, stated without importing its numerical cap closure. -/
def physicalBlock (i j : Fin 14) : WordState → WordState → ℝ :=
  kernelCompose (projectionKernel i)
    (kernelCompose centeredKernel (projectionKernel j))

-- Source correspondence: predecessor AESConcrete/RefinedStepZeros.lean,
-- physicalBlock/refinedCenteredBlock, and CenteredWordStepZeros.lean.
-- Keep this literal formula available for a later imported-provider equality.
theorem physicalBlock_eq_refined_sandwich (i j : Fin 14) :
    physicalBlock i j =
      kernelCompose
        (AESConcrete.RefinedWordProjection.refinedKernel (0 : AES.Word)
          (blockType i).1 (blockType i).2)
        (kernelCompose
          (AESConcrete.WordStepZeros.wordStepKernel -
            AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word))
          (AESConcrete.RefinedWordProjection.refinedKernel (0 : AES.Word)
            (blockType j).1 (blockType j).2)) := rfl

/-- Each grouped support component is an idempotent projection. -/
theorem component_idempotent (f : WordState → ℝ) (j : Fin 14) :
    component (component f j) j = component f j := by
  funext x
  change (∑ p : Label, if coord p = j.succ then
      raw p (component f j) x else 0) =
    ∑ p : Label, if coord p = j.succ then raw p f x else 0
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : coord p = j.succ <;>
    simp only [TransferZeros.raw_component, hp, if_true, if_false, ite_apply,
      Pi.zero_apply]

/-- The sandwich acts as source component, centered step, then target component. -/
theorem physicalBlock_action (f : WordState → ℝ) (i j : Fin 14) :
    action (physicalBlock i j) f = component (centeredStep (component f j)) i := by
  unfold physicalBlock
  rw [kernelCompose_action, kernelCompose_action]
  rw [← component_eq_projectionKernel_action f j]
  change action (projectionKernel i) (centeredStep (component f j)) = _
  exact (component_eq_projectionKernel_action (centeredStep (component f j)) i).symm

/-- The continuous linear operator whose norm is used by the old physical caps. -/
def euclideanBlock (i j : Fin 14) : EuclideanState →L[ℝ] EuclideanState :=
  kernelOperator (physicalBlock i j)

theorem euclideanBlock_apply (i j : Fin 14) (f : EuclideanState) (x : WordState) :
    euclideanBlock i j f x =
      component (centeredStep (component (fun y => f y) j)) i x := by
  unfold euclideanBlock
  rw [kernelOperator_apply]
  exact congrFun (physicalBlock_action (fun y => f y) i j) x

/-- Projecting the source first gives exactly the input norm measured by its profile. -/
theorem profile_centered_component_eq_norm (f : WordState → ℝ) (i j : Fin 14) :
    profile (centeredStep (component f j)) i =
      ‖euclideanBlock i j (toEuclidean (component f j))‖ := by
  have he :
      (fun x => euclideanBlock i j (toEuclidean (component f j)) x) =
        component (centeredStep (component f j)) i := by
    funext x
    rw [euclideanBlock_apply]
    simp only [toEuclidean_apply, component_idempotent]
  calc
    profile (centeredStep (component f j)) i =
        l2 (fun x => euclideanBlock i j (toEuclidean (component f j)) x) := by
      change l2 _ = l2 _
      rw [he]
    _ = ‖euclideanBlock i j (toEuclidean (component f j))‖ :=
      l2_eq_euclidean_norm _

/-- Counting-profile estimate with no normalization loss. -/
theorem profile_le_block_norm_mul (f : WordState → ℝ) (i j : Fin 14) :
    profile (centeredStep (component f j)) i ≤
      ‖euclideanBlock i j‖ * profile f j := by
  calc
    profile (centeredStep (component f j)) i =
        ‖euclideanBlock i j (toEuclidean (component f j))‖ :=
      profile_centered_component_eq_norm f i j
    _ ≤ ‖euclideanBlock i j‖ * ‖toEuclidean (component f j)‖ :=
      (euclideanBlock i j).le_opNorm _
    _ = ‖euclideanBlock i j‖ * profile f j := by
      rw [← l2_eq_toEuclidean_norm (component f j)]
      rfl

/-- Transport any checked operator cap to the corresponding arbitrary-input profile cap. -/
theorem profile_le_of_operator_cap (f : WordState → ℝ) (i j : Fin 14) {c : ℝ}
    (hcap : ‖euclideanBlock i j‖ ≤ c) :
    profile (centeredStep (component f j)) i ≤ c * profile f j :=
  (profile_le_block_norm_mul f i j).trans
    (mul_le_mul_of_nonneg_right hcap (profile_nonneg f j))

/-- Exact low-field interface of `TransferAssembly.PhysicalCaps`.
Numerical provider import and scalar coefficient domination remain separate obligations. -/
theorem low_profile_caps_of_operator_caps
    (hcap : ∀ (i : Fin 14) (k : Fin 11),
      ‖euclideanBlock i (Fin.castAdd 3 k)‖ ≤
        physicalCoeff 1 i (Fin.castAdd 3 k) (lowCoeff i k)) :
    ∀ (f : WordState → ℝ) (i : Fin 14) (k : Fin 11),
      profile (centeredStep (component f (Fin.castAdd 3 k))) i ≤
        physicalCoeff 1 i (Fin.castAdd 3 k) (lowCoeff i k) *
          profile f (Fin.castAdd 3 k) := by
  intro f i k
  exact profile_le_of_operator_cap f i (Fin.castAdd 3 k) (hcap i k)

end AES8.LegacyTransfer
