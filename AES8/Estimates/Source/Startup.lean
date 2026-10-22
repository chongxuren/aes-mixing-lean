/- Module role: Concrete source bounds and startup estimates for the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.NormalizedProfile
import AES8.Model.SupportDegree
import AESPaper.UniversalInitialization

/-!
# Actual four-round startup for the fourteen-coordinate profile

The old five-degree initializer concerns the same grouped error at index one.
Equality of the squared counting-measure norms identifies its Euclidean
profile with the raw degree norm. Each fourteen-coordinate component is an
orthogonal refinement of one degree, so the old degree bounds control it.

The enlarged internal `u0` in `Data` pays for this coarser, already proved
initializer. It does not assert the sharper v17 support-specific startup.
The initial source is split into exactly one or at least two active words;
neither case changes the actual experiment. The first and later transfer
estimates remain explicit. Constructive proof work only; no attacks,
manuscript changes, or edits to predecessor modules.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
-- Concrete AES finite-set terms exceed the naming linter's recursion depth.
-- Only that linter is disabled; the declarations remain kernel checked.
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.Startup
open AESMixing AESMixing.AES

/-- The old Hilbert-space profile and the raw counting-measure degree norm
are equal, rather than merely compared through a choice of coordinates. -/
theorem degree_norm_eq (a : AES.State) (i : Fin 5) :
    l2 (degreeComponent (0 : AES.Word) i (AESPaper.GroupedLaw.error 1 a)) =
      AESPaper.ProfileSpace.profile (AESPaper.ConcreteProfile.centeredError 1 a) i := by
  apply (sq_eq_sq₀ (l2_nonneg _)
    (AESPaper.ProfileSpace.profile_nonnegative
      (AESPaper.ConcreteProfile.centeredError 1 a) i)).mp
  rw [l2_sq]
  exact (AESPaper.OneSourceProfile.profile_energy_toLp i
    (AESPaper.GroupedLaw.error 1 a)).symm

/-- The predecessor's genuine initializer, with its one-source and
several-source premises discharged for every nonzero actual input. -/
theorem scaled_degree_lt (a : AES.State) (ha : a ≠ 0) (i : Fin 5) :
    (2 : ℝ) ^ (80 : ℕ) *
        l2 (degreeComponent (0 : AES.Word) i (AESPaper.GroupedLaw.error 1 a)) <
      AESPaper.initialProfile i := by
  rw [degree_norm_eq]
  have hp := AESPaper.UniversalInitialization.activeSourceCount_pos a ha
  by_cases h1 : AESPaper.ManySourceBounds.activeSourceCount a = 1
  · obtain ⟨k, w, hw, hs⟩ := AESPaper.UniversalInitialization.one_active_source a h1
    by_cases hi : i = 0
    · subst i
      simpa only [AESPaper.initialProfile, Matrix.cons_val_zero] using
        AESPaper.OneSourceProfile.scaled_activity_lt a k w hw hs
    · exact AESPaper.OneSourceProfile.scaled_positive_lt i hi a k w hw hs
  · have h2 : 2 ≤ AESPaper.ManySourceBounds.activeSourceCount a := by omega
    exact AESPaper.SeveralSourcePositiveProfile.scaled_entry_lt a ha h2 i

private theorem initialProfile_apply (i : Fin 5) :
    AESPaper.initialProfile i = match i.val with
      | 0 => (21 / 10 : ℝ)
      | 1 => (63 / 10 : ℝ)
      | 2 => (1 / 4 : ℝ)
      | 3 => (7 / 100 : ℝ)
      | _ => (1 / 80 : ℝ) := by
  fin_cases i <;> rfl

/-- Rational slack for the enlarged internal startup vector. These fourteen
allowances are separate from the predecessor's scientific initializer. -/
theorem degree_allowance (c : Fin 14) :
    AESPaper.initialProfile (SupportDegree.degree c) ≤ (1000 * u0 c) * d c := by
  fin_cases c <;>
    norm_num [initialProfile_apply, SupportDegree.degree, SupportProfile.residualDegree,
      u0, d, vec14_apply]

/-- The actual normalized four-round profile satisfies the internal startup
certificate for every nonzero input difference. -/
theorem initial (a : AES.State) (ha : a ≠ 0) :
    NormalizedProfile.actual a 0 ≤ scale 1000 u0 := by
  intro c
  have hcomponent := SupportDegree.actual_le_degree a 0 c
  have hscaled := mul_le_mul_of_nonneg_left hcomponent
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (80 : ℕ))
  have hdegree := scaled_degree_lt a ha (SupportDegree.degree c)
  have hbound : (2 : ℝ) ^ (80 : ℕ) * SupportProfile.actual a 0 c ≤
      (1000 * u0 c) * d c :=
    (hscaled.trans_lt hdegree).le.trans (degree_allowance c)
  change NormalizedProfile.factor 0 * SupportProfile.actual a 0 c / d c ≤ 1000 * u0 c
  apply (div_le_iff₀ (NormalizedProfile.diagonal_pos c)).mpr
  simpa only [NormalizedProfile.factor, pow_zero, div_one] using hbound

/-- Only the first return and later transfer estimates remain; startup and
the output conversion are proved for the actual profile. -/
structure TransferEstimates : Prop where
  first : ∀ a : AES.State, a ≠ 0 →
    NormalizedProfile.actual a 1 ≤
      fun i => L (NormalizedProfile.actual a 0) i + 1000 * g i
  step : ∀ a : AES.State, a ≠ 0 → ∀ j : ℕ,
    NormalizedProfile.actual a (j + 2) ≤
      fun i => L (NormalizedProfile.actual a (j + 1)) i + M (NormalizedProfile.actual a j) i

theorem estimates_of_transfer (h : TransferEstimates) : NormalizedProfile.Estimates := {
  initial := initial
  first := h.first
  step := h.step
}

end AES8.Startup
