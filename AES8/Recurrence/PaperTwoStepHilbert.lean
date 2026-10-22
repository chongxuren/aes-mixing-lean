/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.PaperTwoStep
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The exact finite-dimensional Hilbert-space instance of Proposition 1

The scalar field is any `RCLike` field, hence includes both real and complex
Hilbert spaces. Scalar restriction preserves each map and its operator norm.
The finite-dimensional wrapper constructs canonical orthogonal projections
from subspaces and obtains continuity of the arbitrary linear transition from
finite dimensionality. It adds no analytic hypothesis to the paper's statement.
Constructive mathematics only; no numerical AES data or manuscript edits.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperTwoStep
open AESRound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section ScalarRestriction
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The same selected projection sum over the original scalar field. -/
def selectedProjectionK (P : ι → E →L[𝕜] E) (selected : Finset ι) : E →L[𝕜] E :=
  ∑ j, if j ∈ selected then P j else 0

theorem selectedProjectionK_eq_sum (P : ι → E →L[𝕜] E) (selected : Finset ι) :
    selectedProjectionK P selected = ∑ j ∈ selected, P j := by
  unfold selectedProjectionK
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

/-- Complex (or real) block norms give the identical memory bound after
restricting scalars to `ℝ`: no new operator estimate is required. -/
theorem rclike_projection_memory_bound
    (P : ι → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hcomplete : ∀ v, (∑ i, P i v) = v)
    (hidempotent : ∀ i v, P i (P i v) = P i v)
    (selected : Finset ι) {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B)
    (hBzero : ∀ i j, j ∈ selected → B i j = 0)
    (hstep : ∀ i j, j ∉ selected →
      ‖(P i).comp (T.comp (P j))‖ ≤ B i j)
    (hreturn : ∀ i j,
      ‖(P i).comp (T.comp ((selectedProjectionK P selected).comp
        (T.comp (P j))))‖ ≤ C i j)
    (state : ℕ → E) (hevolve : ∀ n, state (n + 1) = T (state n)) :
    MemoryRecurrence B C (fun n i => ‖P i (state n)‖) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have hselected : selectedProjection (fun i => (P i).restrictScalars ℝ) selected =
      (selectedProjectionK P selected).restrictScalars ℝ := by
    ext v
    change (∑ j, if j ∈ selected then (P j).restrictScalars ℝ else 0) v =
      (∑ j, if j ∈ selected then P j else 0) v
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ selected <;> simp [hj]
  apply projection_memory_bound (fun i => (P i).restrictScalars ℝ)
    (T.restrictScalars ℝ) hcomplete hidempotent selected hB hBzero
      ?_ ?_ state hevolve
  · intro i j hj
    have he : ((P i).restrictScalars ℝ).comp
        ((T.restrictScalars ℝ).comp ((P j).restrictScalars ℝ)) =
        ((P i).comp (T.comp (P j))).restrictScalars ℝ := by ext v; rfl
    rw [he, ContinuousLinearMap.norm_restrictScalars]
    exact hstep i j hj
  · intro i j
    rw [hselected]
    have he : ((P i).restrictScalars ℝ).comp ((T.restrictScalars ℝ).comp
        (((selectedProjectionK P selected).restrictScalars ℝ).comp
          ((T.restrictScalars ℝ).comp ((P j).restrictScalars ℝ)))) =
        ((P i).comp (T.comp ((selectedProjectionK P selected).comp
          (T.comp (P j))))).restrictScalars ℝ := by ext v; rfl
    rw [he, ContinuousLinearMap.norm_restrictScalars]
    exact hreturn i j

end ScalarRestriction

section FiniteHilbert
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Proposition 1 with its finite-dimensional Hilbert and orthogonal-projection
quantifiers. The transition is an arbitrary linear operator: finite
dimensionality supplies its continuous version automatically. Pairwise
orthogonality is retained in the interface although the bound only needs
completeness and the idempotence supplied by `starProjection`.

The orbit is written as function iteration of the given linear operator, so
the scalar restriction in the proof changes neither the orbit nor any norm. -/
theorem finite_hilbert_two_step_contraction
    (K : ι → Submodule 𝕜 E)
    (_horthogonal : Pairwise (fun i j => K i ⟂ K j))
    (hcomplete : ∀ v, (∑ i, (K i).starProjection v) = v)
    (T : E →ₗ[𝕜] E) (selected : Finset ι) {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    (hBzero : ∀ i j, j ∈ selected → B i j = 0)
    (hstep : ∀ i j, j ∉ selected →
      ‖((K i).starProjection).comp
        (T.toContinuousLinearMap.comp ((K j).starProjection))‖ ≤ B i j)
    (hreturn : ∀ i j,
      ‖((K i).starProjection).comp (T.toContinuousLinearMap.comp
        ((selectedProjectionK (fun j => (K j).starProjection) selected).comp
          (T.toContinuousLinearMap.comp ((K j).starProjection))))‖ ≤ C i j)
    (v : E) {d : Profile ι} {lambda a : ℝ}
    (hd : ∀ i, 0 < d i) (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (htest : matVec (fun i j => lambda * B i j + C i j) d ≤
      fun i => lambda ^ 2 * d i)
    (hzero : (fun i => ‖(K i).starProjection v‖) ≤ fun i => a * d i)
    (hone : (fun i => ‖(K i).starProjection (T v)‖) ≤
      fun i => a * lambda * d i) :
    MemoryRecurrence B C
        (fun m i => ‖(K i).starProjection (((T : E → E)^[m]) v)‖) ∧
      ∀ m, (fun i => ‖(K i).starProjection (((T : E → E)^[m]) v)‖) ≤
        fun i => a * lambda ^ m * d i := by
  let state : ℕ → E := fun m => ((T : E → E)^[m]) v
  have hevolve : ∀ m, state (m + 1) = T.toContinuousLinearMap (state m) := by
    intro m
    exact Function.iterate_succ_apply' (T : E → E) m v
  have hidempotent : ∀ i w,
      (K i).starProjection ((K i).starProjection w) = (K i).starProjection w := by
    intro i w
    exact Submodule.starProjection_eq_self_iff.mpr ((K i).starProjection_apply_mem w)
  have hrec := rclike_projection_memory_bound (fun i => (K i).starProjection)
    T.toContinuousLinearMap hcomplete hidempotent selected hB hBzero
    hstep hreturn state hevolve
  refine ⟨hrec, ?_⟩
  exact sequence_two_step_contraction hB hC (fun m i => norm_nonneg _) hd
    hlambda ha hrec htest (by simpa [state] using hzero) (by simpa [state] using hone)

end FiniteHilbert
end AES8.PaperTwoStep
