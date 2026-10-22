/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESRound.ProjectionAssembly

/-!
# The paper's general two-step contraction criterion

This file formalizes Proposition `prop:two-step` in the authoritative paper's
`writing/sections/04-memory.tex`. The comparison uses only the memory recurrence;
it does not assume the minimum of a one-step bound and a memory bound. All
matrices, the positive weight, the rate, and the initial scale are arbitrary.

The operator argument reuses the exact projection assembly and the triangle-
inequality bridge. A complete family of idempotent continuous linear maps is
enough: orthogonality and finite-dimensional Hilbert structure are stronger
than needed for this implication. Actual orthogonal projections are therefore
covered without adding numerical AES hypotheses. No manuscript/vendor edits,
custom axioms, proof placeholders, or cryptanalytic experiments belong here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperTwoStep
open AESRound

variable {ι : Type*} [Fintype ι]

/-- The memory-only comparison inequality of the paper. -/
def MemoryRecurrence (B C : ι → ι → ℝ) (x : ℕ → Profile ι) : Prop :=
  ∀ n, x (n + 2) ≤ fun i =>
    matVec B (x (n + 1)) i + matVec C (x n) i

/-- Expand the paper's matrix test without changing its source columns. -/
theorem weighted_test_apply (B C : ι → ι → ℝ) (lambda : ℝ)
    (d : Profile ι) (i : ι) :
    matVec (fun i j => lambda * B i j + C i j) d i =
      lambda * matVec B d i + matVec C d i := by
  simp only [matVec, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Stronger algebraic form of the sequence clause: neither nonnegativity of
the sequence nor positivity of the weight is needed once both initial upper
bounds have been supplied. The paper uses a positive rate and positive weight. -/
theorem geometric_bound {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d : Profile ι} {lambda a : ℝ}
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest : matVec (fun i j => lambda * B i j + C i j) d ≤
      fun i => lambda ^ 2 * d i)
    (hzero : x 0 ≤ fun i => a * d i)
    (hone : x 1 ≤ fun i => a * lambda * d i) :
    ∀ n, x n ≤ fun i => a * lambda ^ n * d i := by
  apply Nat.twoStepInduction
  · simpa using hzero
  · simpa using hone
  · intro n hn hn₁ i
    have hfactor : 0 ≤ a * lambda ^ n :=
      mul_nonneg ha (pow_nonneg hlambda n)
    calc
      x (n + 2) i ≤
          matVec B (x (n + 1)) i + matVec C (x n) i := hrec n i
      _ ≤ matVec B (fun j => a * lambda ^ (n + 1) * d j) i +
          matVec C (fun j => a * lambda ^ n * d j) i :=
        add_le_add ((matVec_mono hB hn₁) i) ((matVec_mono hC hn) i)
      _ = (a * lambda ^ n) *
          matVec (fun i j => lambda * B i j + C i j) d i := by
        rw [matVec_scale, matVec_scale, weighted_test_apply, pow_succ]
        ring
      _ ≤ (a * lambda ^ n) * (lambda ^ 2 * d i) :=
        mul_le_mul_of_nonneg_left (htest i) hfactor
      _ = a * lambda ^ (n + 2) * d i := by
        simp only [pow_succ]
        ring

/-- The arbitrary nonnegative-sequence clause with the paper's exact sign
hypotheses. Positivity of `d` gives the intended positive-weight interpretation. -/
theorem sequence_two_step_contraction {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d : Profile ι} {lambda a : ℝ}
    (_hx : ∀ n i, 0 ≤ x n i) (_hd : ∀ i, 0 < d i)
    (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest : matVec (fun i j => lambda * B i j + C i j) d ≤
      fun i => lambda ^ 2 * d i)
    (hzero : x 0 ≤ fun i => a * d i)
    (hone : x 1 ≤ fun i => a * lambda * d i) :
    ∀ n, x n ≤ fun i => a * lambda ^ n * d i :=
  geometric_bound hB hC hlambda.le ha hrec htest hzero hone

/-- A nonnegative profile is the natural domain of an output functional. -/
def NonnegativeProfile (x : Profile ι) : Prop := ∀ i, 0 ≤ x i

/-- The paragraph following Proposition 1: every monotone, nonnegatively
homogeneous output obeys the same geometric envelope. The functional is
represented on real profiles, but only its restriction to nonnegative profiles
is constrained or used. -/
theorem output_bound {x : ℕ → Profile ι} {d : Profile ι} {lambda a : ℝ}
    (hx : ∀ n i, 0 ≤ x n i) (hd : ∀ i, 0 ≤ d i)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (henvelope : ∀ n, x n ≤ fun i => a * lambda ^ n * d i)
    (output : Profile ι → ℝ)
    (hmono : MonotoneOn output {z | NonnegativeProfile z})
    (hhom : ∀ (b : ℝ), 0 ≤ b → ∀ z : Profile ι,
      NonnegativeProfile z → output (fun i => b * z i) = b * output z) :
    ∀ n, output (x n) ≤ a * lambda ^ n * output d := by
  intro n
  have hfactor : 0 ≤ a * lambda ^ n :=
    mul_nonneg ha (pow_nonneg hlambda n)
  calc
    output (x n) ≤ output (fun i => (a * lambda ^ n) * d i) :=
      hmono (hx n) (fun i => mul_nonneg hfactor (hd i)) (henvelope n)
    _ = (a * lambda ^ n) * output d := hhom _ hfactor d hd

/-- Combine the sequence test and the general output conversion. -/
theorem sequence_output_bound {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d : Profile ι} {lambda a : ℝ}
    (hx : ∀ n i, 0 ≤ x n i) (hd : ∀ i, 0 < d i)
    (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest : matVec (fun i j => lambda * B i j + C i j) d ≤
      fun i => lambda ^ 2 * d i)
    (hzero : x 0 ≤ fun i => a * d i)
    (hone : x 1 ≤ fun i => a * lambda * d i)
    (output : Profile ι → ℝ)
    (hmono : MonotoneOn output {z | NonnegativeProfile z})
    (hhom : ∀ (b : ℝ), 0 ≤ b → ∀ z : Profile ι,
      NonnegativeProfile z → output (fun i => b * z i) = b * output z) :
    ∀ n, output (x n) ≤ a * lambda ^ n * output d :=
  output_bound hx (fun i => (hd i).le) hlambda.le ha
    (sequence_two_step_contraction hB hC hx hd hlambda ha hrec htest hzero hone)
    output hmono hhom

section Operators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complete projection family has zero remainder in the existing assembly.
Idempotence is the only projection property used by that assembly. -/
def completeDecomposition (P : ι → E →L[ℝ] E) (T : E →L[ℝ] E)
    (hcomplete : ∀ v, (∑ i, P i v) = v)
    (hidempotent : ∀ i v, P i (P i v) = P i v) :
    ProjectionAssembly.Decomposition ι E where
  project := P
  update := T
  remainder := 0
  complete := by
    intro v
    simpa using hcomplete v
  project_idempotent := hidempotent
  remainder_invisible := by
    intro v i
    simp

variable [DecidableEq ι]

/-- Sum of the selected middle projections, retaining that projection once
inside the composed return operator. The indicator sum equals the subset sum. -/
def selectedProjection (P : ι → E →L[ℝ] E) (selected : Finset ι) : E →L[ℝ] E :=
  ∑ j, if j ∈ selected then P j else 0

theorem selectedProjection_eq_sum (P : ι → E →L[ℝ] E) (selected : Finset ι) :
    selectedProjection P selected = ∑ j ∈ selected, P j := by
  unfold selectedProjection
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

/-- `true` marks the unselected one-step source columns in the existing bridge. -/
def isLow (selected : Finset ι) (j : ι) : Bool := decide (j ∉ selected)

theorem highProject_eq_selected
    (G : ProjectionAssembly.Decomposition ι E) (selected : Finset ι) :
    G.highProject (isLow selected) = selectedProjection G.project selected := by
  unfold ProjectionAssembly.Decomposition.highProject selectedProjection
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ selected <;> simp [isLow, hj]

/-- The exact state recurrence is obtained from operator caps and the existing
algebraic assembly; it is not an assumed inequality about profiles. -/
theorem decomposition_memory_bound
    (G : ProjectionAssembly.Decomposition ι E) (selected : Finset ι)
    (state : ℕ → E) (hevolve : ∀ n, state (n + 1) = G.update (state n))
    {B C : ι → ι → ℝ}
    (hB : ∀ i j, ‖G.low (isLow selected) i j‖ ≤ B i j)
    (hC : ∀ i j, ‖G.ret (isLow selected) i j‖ ≤ C i j) :
    MemoryRecurrence B C (fun n i => ‖G.project i (state n)‖) := by
  let system := G.toProjectionSystem (isLow selected)
  let evolution := system.toBlockEvolution state hevolve
  exact evolution.memory_bound hB hC

/-- First clause of Proposition 1. A finite-dimensional Hilbert operator and
complete orthogonal projections supply these continuous maps, completeness,
and idempotence. Only unselected columns need one-step caps; selected columns
of `B` are exactly zero, as in the paper. -/
theorem projection_memory_bound
    (P : ι → E →L[ℝ] E) (T : E →L[ℝ] E)
    (hcomplete : ∀ v, (∑ i, P i v) = v)
    (hidempotent : ∀ i v, P i (P i v) = P i v)
    (selected : Finset ι) {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B)
    (hBzero : ∀ i j, j ∈ selected → B i j = 0)
    (hstep : ∀ i j, j ∉ selected →
      ‖(P i).comp (T.comp (P j))‖ ≤ B i j)
    (hreturn : ∀ i j,
      ‖(P i).comp (T.comp ((selectedProjection P selected).comp
        (T.comp (P j))))‖ ≤ C i j)
    (state : ℕ → E) (hevolve : ∀ n, state (n + 1) = T (state n)) :
    MemoryRecurrence B C (fun n i => ‖P i (state n)‖) := by
  let G := completeDecomposition P T hcomplete hidempotent
  apply decomposition_memory_bound G selected state hevolve
  · intro i j
    by_cases hj : j ∈ selected
    · simpa [ProjectionAssembly.Decomposition.low, isLow, hj, hBzero i j hj]
        using hB i j
    · simpa [ProjectionAssembly.Decomposition.low, isLow, hj,
        ProjectionAssembly.Decomposition.step, G, completeDecomposition]
        using hstep i j hj
  · intro i j
    change ‖(G.project i).comp (G.update.comp
      ((G.highProject (isLow selected)).comp (G.update.comp (G.project j))))‖ ≤ C i j
    rw [highProject_eq_selected]
    exact hreturn i j

/-- Iteration of the actual linear operator, beginning at the given vector. -/
def orbit (T : E →L[ℝ] E) (v : E) : ℕ → E
  | 0 => v
  | n + 1 => T (orbit T v n)

@[simp] theorem orbit_zero (T : E →L[ℝ] E) (v : E) : orbit T v 0 = v := rfl

@[simp] theorem orbit_succ (T : E →L[ℝ] E) (v : E) (n : ℕ) :
    orbit T v (n + 1) = T (orbit T v n) := rfl

/-- Both clauses of Proposition 1, specialized to the actual operator orbit.
The first conclusion is the derived memory recurrence; the second follows
from the positive weight test and the two initial profile estimates. -/
theorem two_step_contraction
    (P : ι → E →L[ℝ] E) (T : E →L[ℝ] E)
    (hcomplete : ∀ v, (∑ i, P i v) = v)
    (hidempotent : ∀ i v, P i (P i v) = P i v)
    (selected : Finset ι) {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    (hBzero : ∀ i j, j ∈ selected → B i j = 0)
    (hstep : ∀ i j, j ∉ selected →
      ‖(P i).comp (T.comp (P j))‖ ≤ B i j)
    (hreturn : ∀ i j,
      ‖(P i).comp (T.comp ((selectedProjection P selected).comp
        (T.comp (P j))))‖ ≤ C i j)
    (v : E) {d : Profile ι} {lambda a : ℝ}
    (hd : ∀ i, 0 < d i) (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (htest : matVec (fun i j => lambda * B i j + C i j) d ≤
      fun i => lambda ^ 2 * d i)
    (hzero : (fun i => ‖P i v‖) ≤ fun i => a * d i)
    (hone : (fun i => ‖P i (T v)‖) ≤ fun i => a * lambda * d i) :
    MemoryRecurrence B C (fun n i => ‖P i (orbit T v n)‖) ∧
      ∀ n, (fun i => ‖P i (orbit T v n)‖) ≤
        fun i => a * lambda ^ n * d i := by
  have hrec := projection_memory_bound P T hcomplete hidempotent selected hB
    hBzero hstep hreturn (orbit T v) (orbit_succ T v)
  refine ⟨hrec, ?_⟩
  exact sequence_two_step_contraction hB hC (fun n i => norm_nonneg _) hd
    hlambda ha hrec htest (by simpa using hzero) (by simpa using hone)

end Operators
end AES8.PaperTwoStep
