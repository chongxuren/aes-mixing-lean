import AESConcrete.ActualThreePairBounds
import AESConcrete.SignedThreeAssembly
import AESConcrete.ActualUnsignedHS

/-!
# Actual AES word trace and second Gram moment

The actual physical survivor pair estimates discharge the signed
three-mark premise. Combining that result with the unsigned marked bounds
supplies the complete degree Hilbert--Schmidt table. The existing
orthogonal assembly and Gram ideal inequalities then give the actual
word moments, with no quantitative resource premise left in these wrappers.

These are word-kernel results for the existing independent-key model,
both diffusion directions and independently selected byte orientations.
The concrete AES round theorem remains separate. Constructive mathematics
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActualWordMoments
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.MarkedBlockVectorization (Marked)
open AESConcrete.ActualMarkedFrameBound (centeredPattern)
open AESConcrete.HilbertSchmidtEnergy (hs)
open AESConcrete.WordMomentAssembly (residual)

/-- Every signed survivor endpoint is supplied by the actual physical
line/plane pair theorems before the finite signed sum is applied. -/
theorem actual_three_mark_strict (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 < 22 := by
  apply SignedThreeAssembly.centered_energy_lt_twenty_two left right inverse m hlen
  intro s t
  exact ActualThreePairBounds.actual_pairEstimate left right inverse m hlen
    s.val t.val s.property t.property

theorem actual_three_mark_bound (left right : Orientation) (inverse : Bool) :
    ActualUnsignedHS.HasThreeMarkBounds left right inverse := by
  intro m hlen
  exact (actual_three_mark_strict left right inverse m hlen).le

/-- All twenty-five actual degree HS bounds, including total degree three. -/
theorem actual_degree_hs_bounds (left right : Orientation) (inverse : Bool) :
    WordMomentAssembly.HasDegreeHSBounds left right inverse :=
  ActualUnsignedHS.degree_table_of_three_mark_bounds left right inverse
    (actual_three_mark_bound left right inverse)

theorem actual_trace_bound (left right : Orientation) (inverse : Bool) :
    (∑ y, ∑ x, residual left right inverse y x ^ 2) < 4251 / 4294967296 :=
  WordMomentAssembly.trace_lt_of_degree_bounds left right inverse
    (actual_degree_hs_bounds left right inverse)

theorem actual_gram_moment_bound (left right : Orientation) (inverse : Bool) :
    (∑ x, ∑ z, (∑ y, residual left right inverse y x * residual left right inverse y z)^2) <
      (300 / 4294967296 : ℝ)^2 :=
  WordMomentAssembly.gram_moment_lt_of_degree_bounds left right inverse
    (actual_degree_hs_bounds left right inverse)

end AESConcrete.ActualWordMoments
