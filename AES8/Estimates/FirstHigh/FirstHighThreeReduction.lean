/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.ActivityThreeCancellation
import AES8.Estimates.FirstHigh.FirstHighOne

/-!
# Coordinate three from a slightly slack coordinate-two length

The new analytic premise is displayed explicitly: normalized coordinate two
must be at most 366749, one unit below its existing allowance 366750. The
already proved coordinates zero and one and exact activity-mass cancellation
then give the fixed coordinate-three allowance. This does not prove the new
coordinate-two premise or close an additional universal first-high coordinate.

Constructive only; no attacks, proof bypasses or manuscript/predecessor edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.FirstHighThreeReduction
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (profile)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)

/-- A physical step preserves zero-extension and mass on the complete high part. -/
theorem high_output_centered (f : WordState → ℝ) :
    centeredStep (highPart f) 0 = 0 ∧
      (∑ x, centeredStep (highPart f) x) = 0 := by
  have hp : PointedBistochastic AES.parallelSuperboxKernel (0 : WordState) :=
    coordinateKernel_pointed _ _ (fun _ => AES.word_superbox_pointed)
  have hg := AESConcrete.DegreeCentering.globalUniformKernel_action_eq_zero
    (0 : AES.Word) (highPart f) (by exact TransferAssembly.highPart_zero f)
    (TransferAssembly.highPart_mass f)
  -- Use the existing literal-kernel action identity. Delta-reducing `step`
  -- through its concrete physical boundary caused recursive elaboration.
  have he : centeredStep (highPart f) = action AES.parallelSuperboxKernel
      (fun x => highPart f (AESConcrete.WordCrossZero.wordMixAddEquiv.symm x)) := by
    unfold centeredStep
    rw [kernel_action_sub, hg, sub_zero,
      AESConcrete.WordStepZeros.wordStepKernel_action]
  constructor
  · exact (congrFun he 0).trans ((hp.action_zero _).trans (by
      rw [map_zero, TransferAssembly.highPart_zero]))
  · exact (congrArg (fun g : WordState → ℝ => ∑ x, g x) he).trans
      ((hp.action_sum _).trans
        ((AESConcrete.WordCrossZero.wordMixAddEquiv.symm.toEquiv.sum_comp
          (highPart f)).trans (TransferAssembly.highPart_mass f)))

/-- One unit of slack at coordinate two absorbs the smaller activity lengths. -/
theorem scalar_three_le :
    (2 : ℝ) ^ 17 * ((1000 * g (0 : Fin 14)) * d (0 : Fin 14)) +
      (5 * (2 : ℝ) ^ 31 * ((1000 * g (1 : Fin 14)) * d (1 : Fin 14)) +
        (2 : ℝ) ^ 49 * 366749) ≤
    (q - 1) ^ 2 * ((1000 * g (3 : Fin 14)) * d (3 : Fin 14)) := by
  norm_num [q, g, d, vec14_apply, Fin.ext_iff]

/-- Structural reduction with all three normalized length inputs visible. -/
theorem normalized_three_le (f : WordState → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0)
    (h0 : NormalizedProfile.factor 1 * profile f 0 ≤
      (1000 * g (0 : Fin 14)) * d (0 : Fin 14))
    (h1 : NormalizedProfile.factor 1 * profile f 1 ≤
      (1000 * g (1 : Fin 14)) * d (1 : Fin 14))
    (h2 : NormalizedProfile.factor 1 * profile f 2 ≤ 366749) :
    NormalizedProfile.factor 1 * profile f 3 ≤
      (1000 * g (3 : Fin 14)) * d (3 : Fin 14) := by
  have hscaled : (q - 1) ^ 2 * (NormalizedProfile.factor 1 * profile f 3) ≤
      (q - 1) ^ 2 * ((1000 * g (3 : Fin 14)) * d (3 : Fin 14)) := by
    calc
      _ = NormalizedProfile.factor 1 * ((q - 1) ^ 2 * profile f 3) := by ring
      _ ≤ NormalizedProfile.factor 1 *
          ((2 : ℝ) ^ 17 * profile f 0 +
            (5 * (2 : ℝ) ^ 31 * profile f 1 + (2 : ℝ) ^ 49 * profile f 2)) :=
        mul_le_mul_of_nonneg_left (ActivityThreeCancellation.profile_three_le f hz hs)
          (NormalizedProfile.factor_pos 1).le
      _ = (2 : ℝ) ^ 17 * (NormalizedProfile.factor 1 * profile f 0) +
          (5 * (2 : ℝ) ^ 31 * (NormalizedProfile.factor 1 * profile f 1) +
            (2 : ℝ) ^ 49 * (NormalizedProfile.factor 1 * profile f 2)) := by ring
      _ ≤ (2 : ℝ) ^ 17 * ((1000 * g (0 : Fin 14)) * d (0 : Fin 14)) +
          (5 * (2 : ℝ) ^ 31 * ((1000 * g (1 : Fin 14)) * d (1 : Fin 14)) +
            (2 : ℝ) ^ 49 * 366749) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
          (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
            (mul_le_mul_of_nonneg_left h2 (by positivity)))
      _ ≤ _ := scalar_three_le
  norm_num only [q] at hscaled
  nlinarith only [hscaled]

theorem normalization_of_cap (f : WordState → ℝ) (i : Fin 14)
    (h : profile f i ≤ (d i / NormalizedProfile.factor 1) * (1000 * g i)) :
    NormalizedProfile.factor 1 * profile f i ≤ (1000 * g i) * d i := by
  calc
    _ ≤ NormalizedProfile.factor 1 *
        ((d i / NormalizedProfile.factor 1) * (1000 * g i)) :=
      mul_le_mul_of_nonneg_left h (NormalizedProfile.factor_pos 1).le
    _ = _ := by
      field_simp [ne_of_gt (NormalizedProfile.factor_pos 1)] <;> ring

/-- The only unproved input is the displayed stronger coordinate-two estimate. -/
theorem firstHigh_three_of_coordinate_two (b : AES.State) (hb : b ≠ 0)
    (h2 : NormalizedProfile.factor 1 *
      profile (centeredStep (highPart (error 1 b))) 2 ≤ 366749) :
    profile (centeredStep (highPart (error 1 b))) 3 ≤
      (d (3 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (3 : Fin 14)) := by
  have hf := high_output_centered (error 1 b)
  have h0 := normalization_of_cap _ 0 (FirstHighZero.firstHigh_zero b hb)
  have h1 := normalization_of_cap _ 1 (FirstHighOne.firstHigh_one b hb)
  have ht := normalized_three_le _ hf.1 hf.2 h0 h1 h2
  calc
    _ ≤ ((1000 * g (3 : Fin 14)) * d (3 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

end AES8.FirstHighThreeReduction
