/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ActivityAverageEnergy
import AES8.Reductions.Support.ZeroOutsideProjection
import AESMixing.ResidualCoordinates

/-!
# Twelve orthogonal activity patterns for actual profile component nine

An ordered pair of distinct POSITION names (c,d) selects one zero coordinate,
one constant-nonzero coordinate, and two residual coordinates. These are
exactly the valid degree-two/support-three labels of component nine.
The decomposition and its Pythagorean energy identity hold for arbitrary
signed joint input, with no product-law or independence hypothesis.

Each fixed pattern equals the joint residual-coordinate projection of
ActivityAverageEnergy.projection c d f. The latter keeps the other two
coordinates unchanged; its c coordinate is zero and its d coordinate is
the constant-NONZERO block. The existing product projection contraction
therefore bounds each pattern energy by its activity-average energy.

The final result retains an explicit bound B on every distinct-pair
activity-average energy and sums exactly twelve bounds. It supplies no
such cap, numerical output-nine closure, source identification or full
concrete AES endpoint.  No Lean/scientific
execution, active-source/root/Audit edits, attacks, manuscript changes,
predecessor edits or proof bypasses in this branch.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.NineActivityPatterns
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection (singleMask)

/-- Only the four coordinate POSITION names are enumerated. -/
abbrev Pattern := {cd : Fin 4 × Fin 4 // cd.1 ≠ cd.2}

def residualMask (c d : Fin 4) : Fin 16 :=
  maskComplement (maskUnion (singleMask c) (singleMask d))

-- All decidable certificates below concern positions and four-bit masks.
-- No word, state, channel, source law or AES value is enumerated.
theorem pattern_card : Fintype.card Pattern = 12 := by decide

private theorem singleMask_bit : ∀ c i : Fin 4,
    maskBit (singleMask c) i = decide (i = c) := by decide

theorem residualMask_bit : ∀ c d i : Fin 4,
    maskBit (residualMask c d) i = decide (i ≠ c ∧ i ≠ d) := by decide

open AES8.SupportProfile (Label Valid raw)

def patternLabel (p : Pattern) : Label :=
  (residualMask p.val.1 p.val.2, singleMask p.val.1)

def SelectedLabel (p : Label) : Prop :=
  Valid p ∧ maskSize p.1 = 2 ∧ 4 - maskSize p.2 = 3

instance (p : Label) : Decidable (SelectedLabel p) := by
  unfold SelectedLabel
  infer_instance

theorem patternLabel_selected : ∀ p : Pattern, SelectedLabel (patternLabel p) := by
  decide

theorem patternLabel_injective : Function.Injective patternLabel := by decide

def patternLabelEquiv : Pattern ≃ {p : Label // SelectedLabel p} :=
  Equiv.ofBijective (fun p => ⟨patternLabel p, patternLabel_selected p⟩) (by decide)

section GenericPatterns
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Z at c, constant-nonzero at d, residual at the other two positions. -/
def Q (p : Pattern) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (supportProduct (0 : V)
    (maskBit (residualMask p.val.1 p.val.2)) (maskBit (singleMask p.val.1))) f

theorem Q_orthogonal (hn : 1 < Fintype.card V) (p q : Pattern) (hpq : p ≠ q)
    (f g : (Fin 4 → V) → ℝ) : (∑ x, Q p f x * Q q g x) = 0 := by
  apply supportProduct_mixed_orthogonal (0 : V) hn
  rintro ⟨hm, hi⟩
  apply hpq
  apply patternLabel_injective
  exact Prod.ext (maskBits_injective hm) (maskBits_injective hi)

private theorem activity_zero_compose :
    kernelCompose (activityMatrix (0 : V)) (zeroMatrix 0) = zeroMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, zeroMatrix_action, activityMatrix_action,
    wordAverage_zeroPart]

private theorem activity_constant_compose (hn : 1 < Fintype.card V) :
    kernelCompose (activityMatrix (0 : V)) (constantMatrix 0) = constantMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, constantMatrix_action, activityMatrix_action,
    wordAverage_sub, wordAverage_idempotent (0 : V) f hn, wordAverage_zeroPart]

private theorem kernelCompose_identity_right (K : V → V → ℝ) :
    kernelCompose K identityKernel = K := by
  funext y x
  simp [kernelCompose, identityKernel]

/-- Coordinatewise composition retains the exact Z and nonzero-constant
blocks; only the other two coordinates receive residual projections. -/
private theorem coordinate_factor (hn : 1 < Fintype.card V) (c d i : Fin 4) :
    kernelCompose (degreePiece (0 : V) (maskBit (residualMask c d) i))
      (ActivityAverageEnergy.coordinatePiece c d i) =
      supportPiece 0 (maskBit (residualMask c d) i) (maskBit (singleMask c) i) := by
  by_cases hic : i = c
  · subst i
    simpa [residualMask_bit, singleMask_bit, ActivityAverageEnergy.coordinatePiece,
      degreePiece, supportPiece] using (activity_zero_compose (V := V))
  · by_cases hid : i = d
    · subst i
      simpa [residualMask_bit, singleMask_bit, ActivityAverageEnergy.coordinatePiece,
        degreePiece, supportPiece, hic] using (activity_constant_compose (V := V) hn)
    · simpa [residualMask_bit, singleMask_bit, ActivityAverageEnergy.coordinatePiece,
        degreePiece, supportPiece, hic, hid] using
        (kernelCompose_identity_right (residualProjection (0 : V)))

theorem patternKernel_eq_residual_activity (hn : 1 < Fintype.card V) (p : Pattern) :
    supportProduct (0 : V) (maskBit (residualMask p.val.1 p.val.2))
      (maskBit (singleMask p.val.1)) =
      kernelCompose (productProjection 0 (maskBit (residualMask p.val.1 p.val.2)))
        (ActivityAverageEnergy.kernel p.val.1 p.val.2) := by
  change coordinateKernel (fun i : Fin 4 => supportPiece (0 : V)
      (maskBit (residualMask p.val.1 p.val.2) i) (maskBit (singleMask p.val.1) i)) =
    kernelCompose
      (coordinateKernel (fun i => degreePiece 0 (maskBit (residualMask p.val.1 p.val.2) i)))
      (coordinateKernel (ActivityAverageEnergy.coordinatePiece p.val.1 p.val.2))
  rw [coordinateKernel_compose]
  funext y x
  unfold coordinateKernel
  apply Finset.prod_congr rfl
  intro i _
  exact (congrFun (congrFun (coordinate_factor hn p.val.1 p.val.2 i) (y i)) (x i)).symm

/-- A literal operator identity on arbitrary signed joint input. -/
theorem Q_eq_residual_activity (hn : 1 < Fintype.card V) (p : Pattern)
    (f : (Fin 4 → V) → ℝ) :
    Q p f = action (productProjection 0 (maskBit (residualMask p.val.1 p.val.2)))
      (ActivityAverageEnergy.projection p.val.1 p.val.2 f) := by
  simpa only [Q, ActivityAverageEnergy.projection, kernelCompose_action] using
    congrArg (fun K : (Fin 4 → V) → (Fin 4 → V) → ℝ => action K f)
      (patternKernel_eq_residual_activity hn p)

theorem Q_energy_le_activity (hn : 1 < Fintype.card V) (p : Pattern)
    (f : (Fin 4 → V) → ℝ) :
    (∑ x, Q p f x ^ 2) ≤
      ∑ x, ActivityAverageEnergy.projection p.val.1 p.val.2 f x ^ 2 := by
  rw [Q_eq_residual_activity hn]
  exact productProjection_energy_le (0 : V) hn
    (maskBit (residualMask p.val.1 p.val.2)) _

end GenericPatterns

section ComponentNine

theorem Q_eq_raw (p : Pattern) (f : AES.WordState → ℝ) :
    Q p f = raw (patternLabel p) f := rfl

/-- Actual component nine has residual degree two and exact support three.
Invalid overlapping mask pairs vanish before the finite-label reindexing. -/
theorem component_nine_eq_sum_Q (f : AES.WordState → ℝ) :
    SupportProfile.component f 9 = fun y => ∑ p : Pattern, Q p f y := by
  funext y
  rw [SupportProfile.component_eq_support_residual]
  change (∑ p : Label, if maskSize p.1 = 2 ∧ 4 - maskSize p.2 = 3
    then raw p f y else 0) = _
  have ht (p : Label) :
      (if maskSize p.1 = 2 ∧ 4 - maskSize p.2 = 3 then raw p f y else 0) =
        if SelectedLabel p then raw p f y else 0 := by
    by_cases hv : Valid p
    · simp only [SelectedLabel, hv, true_and]
    · simp [SelectedLabel, hv, SupportProfile.raw_invalid p hv f]
  simp_rw [ht]
  have hs : (∑ p : {p : Label // SelectedLabel p}, raw p.val f y) =
      ∑ p : Label, if SelectedLabel p then raw p f y else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs]
  calc
    _ = ∑ p : Pattern, raw (patternLabel p) f y :=
      (patternLabelEquiv.sum_comp (fun p => raw p.val f y)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      exact congrFun (Q_eq_raw p f).symm y

/-- Pythagoras charges twelve energies, with no triangle-inequality factor. -/
theorem component_nine_energy (f : AES.WordState → ℝ) :
    (∑ x, SupportProfile.component f 9 x ^ 2) =
      ∑ p : Pattern, ∑ x, Q p f x ^ 2 := by
  rw [component_nine_eq_sum_Q]
  exact orthogonal_family_energy (fun p : Pattern => Q p f)
    (fun p q hpq => Q_orthogonal SupportProfile.word_card_gt_one p q hpq f f)

theorem component_nine_energy_le_sum_activity (f : AES.WordState → ℝ) :
    (∑ x, SupportProfile.component f 9 x ^ 2) ≤
      ∑ p : Pattern, ∑ x, ActivityAverageEnergy.projection p.val.1 p.val.2 f x ^ 2 := by
  rw [component_nine_energy]
  apply Finset.sum_le_sum
  intro p _
  exact Q_energy_le_activity SupportProfile.word_card_gt_one p f

/-- The numerical cap remains an explicit assumption on each actual
distinct-pair activity average. This theorem does not discharge that cap. -/
theorem component_nine_energy_le_twelve (f : AES.WordState → ℝ) (B : ℝ)
    (hB : ∀ c d : Fin 4, c ≠ d →
      (∑ x, ActivityAverageEnergy.projection c d f x ^ 2) ≤ B) :
    (∑ x, SupportProfile.component f 9 x ^ 2) ≤ 12 * B := by
  calc
    _ ≤ ∑ p : Pattern, ∑ x,
        ActivityAverageEnergy.projection p.val.1 p.val.2 f x ^ 2 :=
      component_nine_energy_le_sum_activity f
    _ ≤ ∑ _p : Pattern, B := by
      apply Finset.sum_le_sum
      intro p _
      exact hB p.val.1 p.val.2 p.property
    _ = 12 * B := by
      simp only [Finset.sum_const, Finset.card_univ, pattern_card, nsmul_eq_mul,
        Nat.cast_ofNat]

end ComponentNine
end AES8.NineActivityPatterns
