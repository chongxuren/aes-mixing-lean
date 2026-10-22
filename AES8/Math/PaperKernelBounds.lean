/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.NormalizedSchur
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Nonnegative kernel bounds over the real or complex scalars

These are the raw-kernel ingredients of the earlier Lemma 9, including
the entrywise dominated signed/complex extension. The current normalized
fiber statement is proved in PaperFiberKernel and PaperFiberKernelPower.
All norms use counting measure. The normalization parameters are arbitrary
finite fiber cardinalities, rather than fixed AES constants.

`RCLike` includes both `ℝ` and `ℂ`. In particular the energy in this file
is squared modulus, not a complex square or a real-part restriction.
`operator_norm_sq_le_of_energy` supplies the complete Euclidean bridge.
Constructive proof work only; no attacks or manuscript/vendor changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperKernelBounds

variable {𝕜 I J : Type*} [RCLike 𝕜] [Fintype I] [Fintype J]

/-- Literal rectangular matrix action; no averaging factor is hidden. -/
def kernelAction (K : J → I → 𝕜) (f : I → 𝕜) (y : J) : 𝕜 :=
  ∑ x, K y x * f x

/-- Entrywise domination controls arbitrary real or complex inputs. -/
theorem norm_action_le (K : J → I → 𝕜) (A : J → I → ℝ)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x) (f : I → 𝕜) (y : J) :
    ‖kernelAction K f y‖ ≤ AESMixing.action A (fun x => ‖f x‖) y := by
  calc
    _ ≤ ∑ x, ‖K y x * f x‖ := norm_sum_le _ _
    _ = ∑ x, ‖K y x‖ * ‖f x‖ := by simp only [norm_mul]
    _ ≤ _ := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_right (hdom y x) (norm_nonneg _))

/-- Schur's bound with the full squared-modulus energy. -/
theorem schur_energy (K : J → I → 𝕜) (A : J → I → ℝ) (r c : ℝ)
    (hr : 0 ≤ r) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c) (f : I → 𝕜) :
    (∑ y, ‖kernelAction K f y‖ ^ 2) ≤ (r * c) * ∑ x, ‖f x‖ ^ 2 := by
  have he : (∑ y, ‖kernelAction K f y‖ ^ 2) ≤
      ∑ y, AESMixing.action A (fun x => ‖f x‖) y ^ 2 := by
    apply Finset.sum_le_sum
    intro y _
    exact (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hA y x) (norm_nonneg _)))).mpr
      (norm_action_le K A hdom f y)
  exact he.trans (AESMixing.rectangular_schur_energy A r c hr hA hrow hcol
    (fun x => ‖f x‖))

/-- The ordinary rectangular Euclidean operator of the same matrix. -/
def kernelOperator [DecidableEq I] (K : J → I → 𝕜) :
    EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J :=
  (Matrix.toEuclideanLin K).toContinuousLinearMap

@[simp] theorem kernelOperator_apply [DecidableEq I] (K : J → I → 𝕜)
    (f : EuclideanSpace 𝕜 I) (y : J) :
    kernelOperator K f y = kernelAction K (fun x => f x) y := rfl

/-- Energy and Euclidean norm have exactly the same counting normalization. -/
theorem energy_eq_norm_sq (f : I → 𝕜) :
    (∑ x, ‖f x‖ ^ 2) = ‖WithLp.toLp 2 f‖ ^ 2 := by
  exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 f)).symm

/-- Complete bridge from an all-input energy estimate to the squared
operator norm; this is also valid when a finite index type is empty. -/
theorem operator_norm_sq_le_of_energy [DecidableEq I] (K : J → I → 𝕜)
    (b : ℝ) (hb : 0 ≤ b)
    (henergy : ∀ f : I → 𝕜,
      (∑ y, ‖kernelAction K f y‖ ^ 2) ≤ b * ∑ x, ‖f x‖ ^ 2) :
    ‖kernelOperator K‖ ^ 2 ≤ b := by
  have hn : ‖kernelOperator K‖ ≤ Real.sqrt b := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hb, EuclideanSpace.norm_sq_eq,
      kernelOperator_apply] using henergy (fun x => f x)
  have hs := (sq_le_sq₀ (norm_nonneg (kernelOperator K))
    (Real.sqrt_nonneg b)).mpr hn
  simpa only [Real.sq_sqrt hb] using hs

/-- First raw-kernel bound of the earlier Lemma 9, for every dominated real/complex kernel. -/
theorem schur_operator_norm_sq [DecidableEq I]
    (K : J → I → 𝕜) (A : J → I → ℝ) (r c : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c) :
    ‖kernelOperator K‖ ^ 2 ≤ r * c :=
  operator_norm_sq_le_of_energy K (r * c) (mul_nonneg hr hc)
    (schur_energy K A r c hr hA hdom hrow hcol)

/-- Column sums after left multiplication by the all-ones vector. -/
def leftSum (K : J → I → 𝕜) (x : I) : 𝕜 := ∑ y, K y x

/-- Row sums after right multiplication by the all-ones vector. -/
def rightSum (K : J → I → 𝕜) (y : J) : 𝕜 := ∑ x, K y x

theorem norm_leftSum_le (K : J → I → 𝕜) (A : J → I → ℝ)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x) (x : I) :
    ‖leftSum K x‖ ≤ ∑ y, A y x := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun y _ => hdom y x))

/-- Second raw-kernel bound of the earlier Lemma 9, in squared-modulus coordinates. -/
theorem left_sum_energy (K : J → I → 𝕜) (A : J → I → ℝ) (c S : ℝ)
    (hc : 0 ≤ c) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) :
    (∑ x, ‖leftSum K x‖ ^ 2) ≤ c * S := by
  have hpoint (x : I) : ‖leftSum K x‖ ^ 2 ≤ c * ∑ y, A y x := by
    have hm : 0 ≤ ∑ y, A y x := Finset.sum_nonneg (fun y _ => hA y x)
    calc
      _ ≤ (∑ y, A y x) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hm).mpr (norm_leftSum_le K A hdom x)
      _ ≤ _ := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hcol x) hm
  calc
    _ ≤ ∑ x, c * ∑ y, A y x := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = c * ∑ y, ∑ x, A y x := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal hc

/-- Third raw-kernel bound of the earlier Lemma 9, obtained by literal transposition. -/
theorem right_sum_energy (K : J → I → 𝕜) (A : J → I → ℝ) (r S : ℝ)
    (hr : 0 ≤ r) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) :
    (∑ y, ‖rightSum K y‖ ^ 2) ≤ r * S := by
  have ht : (∑ x, ∑ y, A y x) ≤ S := by
    rw [Finset.sum_comm]
    exact htotal
  exact left_sum_energy (fun x y => K y x) (fun x y => A y x)
    r S hr (fun x y => hA y x) (fun x y => hdom y x) hrow ht

/-- All three displayed inequalities, in the paper's ordinary Euclidean norms.
Specializing `𝕜` to `ℂ` supplies the full complex extension; specializing it
to `ℝ` includes signed kernels and the nonnegative matrix itself. -/
theorem nonnegative_kernel_bounds [DecidableEq I]
    (K : J → I → 𝕜) (A : J → I → ℝ) (r c S : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) :
    ‖kernelOperator K‖ ^ 2 ≤ r * c ∧
      ‖WithLp.toLp 2 (leftSum K)‖ ^ 2 ≤ c * S ∧
      ‖WithLp.toLp 2 (rightSum K)‖ ^ 2 ≤ r * S := by
  refine ⟨schur_operator_norm_sq K A r c hr hc hA hdom hrow hcol, ?_, ?_⟩
  · rw [← energy_eq_norm_sq]
    exact left_sum_energy K A c S hc hA hdom hcol htotal
  · rw [← energy_eq_norm_sq]
    exact right_sum_energy K A r S hr hA hdom hrow htotal

/-- For nonempty row and column types, the nonnegative kernel and its caps
already imply the cap signs needed in the general bound. -/
theorem paper_nonnegative_kernel_bounds [DecidableEq I] [Nonempty I] [Nonempty J]
    (K : J → I → 𝕜) (A : J → I → ℝ) (r c S : ℝ)
    (hA : ∀ y x, 0 ≤ A y x) (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) :
    ‖kernelOperator K‖ ^ 2 ≤ r * c ∧
      ‖WithLp.toLp 2 (leftSum K)‖ ^ 2 ≤ c * S ∧
      ‖WithLp.toLp 2 (rightSum K)‖ ^ 2 ≤ r * S := by
  classical
  have hr : 0 ≤ r :=
    (Finset.sum_nonneg (fun x _ => hA (Classical.arbitrary J) x)).trans
      (hrow (Classical.arbitrary J))
  have hc : 0 ≤ c :=
    (Finset.sum_nonneg (fun y _ => hA y (Classical.arbitrary I))).trans
      (hcol (Classical.arbitrary I))
  exact nonnegative_kernel_bounds K A r c S hr hc hA hdom hrow hcol htotal

/-- The exact row-fiber normalization, with no input-law assumption. -/
def normalizedLeftSum (K : J → I → 𝕜) (m : ℕ) (x : I) : 𝕜 :=
  leftSum K x / (Real.sqrt (m : ℝ) : 𝕜)

theorem normalized_left_sum_energy (K : J → I → 𝕜) (A : J → I → ℝ)
    (c S : ℝ) (hc : 0 ≤ c) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) (m : ℕ) :
    (∑ x, ‖normalizedLeftSum K m x‖ ^ 2) ≤ c * S / (m : ℝ) := by
  have hraw := left_sum_energy K A c S hc hA hdom hcol htotal
  simp only [normalizedLeftSum, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg m), ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hraw (Nat.cast_nonneg m)

/-- Normalized right sums are the same theorem on the transposed matrix. -/
def normalizedRightSum (K : J → I → 𝕜) (n : ℕ) (y : J) : 𝕜 :=
  rightSum K y / (Real.sqrt (n : ℝ) : 𝕜)

theorem normalized_right_sum_energy (K : J → I → 𝕜) (A : J → I → ℝ)
    (r S : ℝ) (hr : 0 ≤ r) (hA : ∀ y x, 0 ≤ A y x)
    (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) (n : ℕ) :
    (∑ y, ‖normalizedRightSum K n y‖ ^ 2) ≤ r * S / (n : ℝ) := by
  have hraw := right_sum_energy K A r S hr hA hdom hrow htotal
  simp only [normalizedRightSum, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hraw (Nat.cast_nonneg n)

/-- The doubly summed scalar with the two incidence normalizations. -/
def normalizedTotalSum (K : J → I → 𝕜) (m n : ℕ) : 𝕜 :=
  (∑ y, ∑ x, K y x) /
    ((Real.sqrt (m : ℝ) : 𝕜) * (Real.sqrt (n : ℝ) : 𝕜))

theorem normalized_total_sum_norm (K : J → I → 𝕜) (A : J → I → ℝ)
    (S : ℝ) (hdom : ∀ y x, ‖K y x‖ ≤ A y x)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) (m n : ℕ) :
    ‖normalizedTotalSum K m n‖ ≤
      S / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  have hraw : ‖∑ y, ∑ x, K y x‖ ≤ S := by
    calc
      _ ≤ ∑ y, ‖∑ x, K y x‖ := norm_sum_le _ _
      _ ≤ ∑ y, ∑ x, A y x := by
        apply Finset.sum_le_sum
        intro y _
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun x _ => hdom y x))
      _ ≤ S := htotal
  simp only [normalizedTotalSum, norm_div, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hraw
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end AES8.PaperKernelBounds
