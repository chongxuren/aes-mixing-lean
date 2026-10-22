/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.PaperTwoStepHilbert

/-!
# Alternating weights for the paper's two-step criterion

The current `prop:two-step` allows distinct even and odd weight vectors.
The operator-to-memory argument is unchanged from `PaperTwoStepHilbert`;
only the scalar comparison induction and its output conversion are extended.
All matrices, weights, rates, and initial scales remain symbolic. This file
contains no concrete AES estimates or cryptanalytic experiments.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperTwoStep
open AESRound

variable {ι : Type*} [Fintype ι]

/-- The algebraic alternating comparison. Weight positivity and sequence
nonnegativity are unnecessary once both initial upper bounds are given. -/
theorem alternating_geometric_bound {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d0 d1 : Profile ι} {lambda a : ℝ}
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest0 : (fun i => lambda * matVec B d1 i + matVec C d0 i) ≤
      fun i => lambda ^ 2 * d0 i)
    (htest1 : (fun i => lambda * matVec B d0 i + matVec C d1 i) ≤
      fun i => lambda ^ 2 * d1 i)
    (hzero : x 0 ≤ fun i => a * d0 i)
    (hone : x 1 ≤ fun i => a * lambda * d1 i) :
    ∀ n, (x (2 * n) ≤ fun i => a * lambda ^ (2 * n) * d0 i) ∧
      (x (2 * n + 1) ≤ fun i => a * lambda ^ (2 * n + 1) * d1 i) := by
  intro n
  induction n with
  | zero =>
      constructor
      · simpa using hzero
      · simpa using hone
  | succ n ih =>
      have heven : x (2 * n + 2) ≤
          fun i => a * lambda ^ (2 * n + 2) * d0 i := by
        intro i
        have hfactor : 0 ≤ a * lambda ^ (2 * n) :=
          mul_nonneg ha (pow_nonneg hlambda _)
        calc
          x (2 * n + 2) i ≤
              matVec B (x (2 * n + 1)) i + matVec C (x (2 * n)) i :=
            hrec (2 * n) i
          _ ≤ matVec B (fun j => a * lambda ^ (2 * n + 1) * d1 j) i +
              matVec C (fun j => a * lambda ^ (2 * n) * d0 j) i :=
            add_le_add ((matVec_mono hB ih.2) i) ((matVec_mono hC ih.1) i)
          _ = (a * lambda ^ (2 * n)) *
              (lambda * matVec B d1 i + matVec C d0 i) := by
            rw [matVec_scale, matVec_scale, pow_succ]
            ring
          _ ≤ (a * lambda ^ (2 * n)) * (lambda ^ 2 * d0 i) :=
            mul_le_mul_of_nonneg_left (htest0 i) hfactor
          _ = a * lambda ^ (2 * n + 2) * d0 i := by
            simp only [pow_succ]
            ring
      have hodd : x (2 * n + 2 + 1) ≤
          fun i => a * lambda ^ (2 * n + 2 + 1) * d1 i := by
        intro i
        have hfactor : 0 ≤ a * lambda ^ (2 * n + 1) :=
          mul_nonneg ha (pow_nonneg hlambda _)
        have hindex1 : 2 * n + 1 + 1 = 2 * n + 2 := by omega
        have hindex2 : 2 * n + 1 + 2 = 2 * n + 2 + 1 := by omega
        have hpow : lambda ^ (2 * n + 2) = lambda ^ (2 * n + 1) * lambda := by
          rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
        calc
          x (2 * n + 2 + 1) i ≤
              matVec B (x (2 * n + 2)) i + matVec C (x (2 * n + 1)) i := by
            simpa only [hindex1, hindex2] using hrec (2 * n + 1) i
          _ ≤ matVec B (fun j => a * lambda ^ (2 * n + 2) * d0 j) i +
              matVec C (fun j => a * lambda ^ (2 * n + 1) * d1 j) i :=
            add_le_add ((matVec_mono hB heven) i) ((matVec_mono hC ih.2) i)
          _ = (a * lambda ^ (2 * n + 1)) *
              (lambda * matVec B d0 i + matVec C d1 i) := by
            rw [matVec_scale, matVec_scale, hpow]
            ring
          _ ≤ (a * lambda ^ (2 * n + 1)) * (lambda ^ 2 * d1 i) :=
            mul_le_mul_of_nonneg_left (htest1 i) hfactor
          _ = a * lambda ^ (2 * n + 2 + 1) * d1 i := by
            simp only [pow_succ]
            ring
      constructor
      · simpa only [Nat.mul_succ] using heven
      · simpa only [Nat.mul_succ] using hodd

/-- The alternating sequence clause with exactly the paper's sign interface. -/
theorem sequence_alternating_two_step_contraction {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d0 d1 : Profile ι} {lambda a : ℝ}
    (_hx : ∀ n i, 0 ≤ x n i)
    (_hd0 : ∀ i, 0 < d0 i) (_hd1 : ∀ i, 0 < d1 i)
    (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest0 : (fun i => lambda * matVec B d1 i + matVec C d0 i) ≤
      fun i => lambda ^ 2 * d0 i)
    (htest1 : (fun i => lambda * matVec B d0 i + matVec C d1 i) ≤
      fun i => lambda ^ 2 * d1 i)
    (hzero : x 0 ≤ fun i => a * d0 i)
    (hone : x 1 ≤ fun i => a * lambda * d1 i) :
    ∀ n, (x (2 * n) ≤ fun i => a * lambda ^ (2 * n) * d0 i) ∧
      (x (2 * n + 1) ≤ fun i => a * lambda ^ (2 * n + 1) * d1 i) :=
  alternating_geometric_bound hB hC hlambda.le ha hrec htest0 htest1 hzero hone

/-- Every monotone, nonnegatively homogeneous output is controlled by the
larger output of the two phase weights, at every original sequence index. -/
theorem alternating_output_bound
    {x : ℕ → Profile ι} {d0 d1 : Profile ι} {lambda a : ℝ}
    (hx : ∀ n i, 0 ≤ x n i)
    (hd0 : ∀ i, 0 ≤ d0 i) (hd1 : ∀ i, 0 ≤ d1 i)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (henvelope : ∀ n,
      (x (2 * n) ≤ fun i => a * lambda ^ (2 * n) * d0 i) ∧
      (x (2 * n + 1) ≤ fun i => a * lambda ^ (2 * n + 1) * d1 i))
    (output : Profile ι → ℝ)
    (hmono : MonotoneOn output {z | NonnegativeProfile z})
    (hhom : ∀ (b : ℝ), 0 ≤ b → ∀ z : Profile ι,
      NonnegativeProfile z → output (fun i => b * z i) = b * output z) :
    ∀ n, output (x n) ≤ a * lambda ^ n * max (output d0) (output d1) := by
  intro n
  have hfactor : 0 ≤ a * lambda ^ n :=
    mul_nonneg ha (pow_nonneg hlambda _)
  have houtput (d : Profile ι) (hd : ∀ i, 0 ≤ d i)
      (hbound : x n ≤ fun i => a * lambda ^ n * d i) :
      output (x n) ≤ (a * lambda ^ n) * output d := by
    calc
      output (x n) ≤ output (fun i => (a * lambda ^ n) * d i) :=
        hmono (hx n) (fun i => mul_nonneg hfactor (hd i)) hbound
      _ = (a * lambda ^ n) * output d := hhom _ hfactor d hd
  have hparity : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hparity with heven | hodd
  · have hindex : 2 * (n / 2) = n := by omega
    have hbound : x n ≤ fun i => a * lambda ^ n * d0 i := by
      simpa only [hindex] using (henvelope (n / 2)).1
    exact (houtput d0 hd0 hbound).trans
      (mul_le_mul_of_nonneg_left (le_max_left (output d0) (output d1)) hfactor)
  · have hindex : 2 * (n / 2) + 1 = n := by omega
    have hbound : x n ≤ fun i => a * lambda ^ n * d1 i := by
      simpa only [hindex] using (henvelope (n / 2)).2
    exact (houtput d1 hd1 hbound).trans
      (mul_le_mul_of_nonneg_left (le_max_right (output d0) (output d1)) hfactor)

/-- The current sequence test and its max-of-two-weights output conversion. -/
theorem sequence_alternating_output_bound {B C : ι → ι → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {x : ℕ → Profile ι} {d0 d1 : Profile ι} {lambda a : ℝ}
    (hx : ∀ n i, 0 ≤ x n i)
    (hd0 : ∀ i, 0 < d0 i) (hd1 : ∀ i, 0 < d1 i)
    (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (hrec : MemoryRecurrence B C x)
    (htest0 : (fun i => lambda * matVec B d1 i + matVec C d0 i) ≤
      fun i => lambda ^ 2 * d0 i)
    (htest1 : (fun i => lambda * matVec B d0 i + matVec C d1 i) ≤
      fun i => lambda ^ 2 * d1 i)
    (hzero : x 0 ≤ fun i => a * d0 i)
    (hone : x 1 ≤ fun i => a * lambda * d1 i)
    (output : Profile ι → ℝ)
    (hmono : MonotoneOn output {z | NonnegativeProfile z})
    (hhom : ∀ (b : ℝ), 0 ≤ b → ∀ z : Profile ι,
      NonnegativeProfile z → output (fun i => b * z i) = b * output z) :
    ∀ n, output (x n) ≤ a * lambda ^ n * max (output d0) (output d1) :=
  alternating_output_bound hx (fun i => (hd0 i).le) (fun i => (hd1 i).le)
    hlambda.le ha
    (sequence_alternating_two_step_contraction hB hC hx hd0 hd1 hlambda ha
      hrec htest0 htest1 hzero hone) output hmono hhom

section FiniteHilbert
variable [DecidableEq ι]
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The current proposition with its exact finite Hilbert/operator interface.
The memory recurrence is derived from literal block norm caps; it is not an
additional assumed property of the operator orbit. -/
theorem finite_hilbert_alternating_two_step_contraction
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
    (v : E) {d0 d1 : Profile ι} {lambda a : ℝ}
    (hd0 : ∀ i, 0 < d0 i) (hd1 : ∀ i, 0 < d1 i)
    (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (htest0 : (fun i => lambda * matVec B d1 i + matVec C d0 i) ≤
      fun i => lambda ^ 2 * d0 i)
    (htest1 : (fun i => lambda * matVec B d0 i + matVec C d1 i) ≤
      fun i => lambda ^ 2 * d1 i)
    (hzero : (fun i => ‖(K i).starProjection v‖) ≤ fun i => a * d0 i)
    (hone : (fun i => ‖(K i).starProjection (T v)‖) ≤
      fun i => a * lambda * d1 i) :
    MemoryRecurrence B C
        (fun m i => ‖(K i).starProjection (((T : E → E)^[m]) v)‖) ∧
      ∀ m,
        ((fun i => ‖(K i).starProjection (((T : E → E)^[2 * m]) v)‖) ≤
          fun i => a * lambda ^ (2 * m) * d0 i) ∧
        ((fun i => ‖(K i).starProjection (((T : E → E)^[2 * m + 1]) v)‖) ≤
          fun i => a * lambda ^ (2 * m + 1) * d1 i) := by
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
  exact sequence_alternating_two_step_contraction hB hC (fun m i => norm_nonneg _)
    hd0 hd1 hlambda ha hrec htest0 htest1
    (by simpa [state] using hzero) (by simpa [state] using hone)

end FiniteHilbert
end AES8.PaperTwoStep
