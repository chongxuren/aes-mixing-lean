import AESPaper.FiveComponentPropagation
import AESPaper.RawBoundaryTable

/-!
# concrete closure for the fixed 14.3+73.1k target

The conditional propagation theorem is instantiated with the actual raw-boundary
table. No operator estimate remains a hypothesis. Universal initialization,
physical-law transfer and the exact rational/decimal arithmetic are imported
from their separate proved modules.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.Propagation
open AESMixing AESMixing.AES AESPaper.ProfileSpace

/-- The concrete H Pi H Pi estimate, for arbitrary signed centered joint input. -/
theorem operator (f : ProfileSpace.State) (hf : Centered f) (i : Fin 5) :
    normalizedProfile (ConcreteProfile.fourRound f) i ≤
      step (normalizedProfile f) i :=
  FiveComponentPropagation.operator RawBoundaryTable.boundary_C
    RawBoundaryTable.boundary_t_to_activity f hf i

/-- The exact rational target followed by the paper's rational decimal exponent. -/
theorem epsilon_bound (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k :=
  ConcreteProfile.epsilon_of_initialization_and_operator
    UniversalInitialization.physical_initial operator k r hr

theorem rounds_128 : epsilon 12 < (2 : ℝ) ^ (-128 : ℝ) :=
  ((epsilon_bound 2 12 (by norm_num)).1.trans
    (epsilon_bound 2 12 (by norm_num)).2).trans decimal_rounds_128

theorem rounds_192 : epsilon 16 < (2 : ℝ) ^ (-192 : ℝ) :=
  ((epsilon_bound 3 16 (by norm_num)).1.trans
    (epsilon_bound 3 16 (by norm_num)).2).trans decimal_rounds_192

theorem rounds_256 : epsilon 20 < (2 : ℝ) ^ (-256 : ℝ) :=
  ((epsilon_bound 4 20 (by norm_num)).1.trans
    (epsilon_bound 4 20 (by norm_num)).2).trans decimal_rounds_256

/-- Finite private randomness and independent prior information, with two
adaptive forward answers in the existing retained-key private-view experiment. -/
theorem private_view {R : Type*} [Fintype R]
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (k r : ℕ) (hr : 4 + 4 * k ≤ r)
    (first : R → AES.State) (choose : R → AES.State → AES.State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) (first t) (choose t)))
      (independentView weight (fun t =>
        adaptiveDifferenceView randomPermutationDifference (fun y => choose t y-first t))) <
      decimalBound k :=
  UniversalInitialization.private_view_of_operator weight hw hs operator k r hr first choose

end AESPaper.Propagation
