/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ElevenConditionalResponse
import AES8.Reductions.Source.PinnedSourceAverage
import AES8.Reductions.Fibers.WordMixTwoZeroPinnedFiber
import AES8.Estimates.FirstHigh.TwoZeroThirteenMoment

/-!
# Incoming component eleven on the first-high output-eight event

One-source initialization is exactly zero. With two active original sources,
one supplies the common conditional response and the other averages its zero
pin coefficient. The four incoming patterns are pointwise disjoint. Each
two-output-zero fiber, after fixing its input zero, has one information input
coordinate; two ordinary entry-square caps and one column energy finish it.
Six output zero masks and the existing support restriction contraction give
the projected output-eight length allowance.

All probabilities refer to original source words. No later-boundary coordinate
independence, custom axiom or target estimate is assumed.
Constructive proofs only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwoZeroElevenMoment
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount activeSourceMask activeSourceMask_iff)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.ElevenConditionalResponse
open AES8.FirstHighSupportEvent (boundaryInput boundaryEventEnergy restrictSupport)
open AES8.OneSourceEventMoment (columnCap)
open AES8.TwoZeroThirteenMoment (entryCap residual_entry_le zeroMask zeroMask_size)

-- Position tables only; no AES word/state enumeration is performed.
def retained : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem retained_ne : ∀ j : Fin 4, ∀ i : Fin 3, retained j i ≠ j := by decide

def retainedEquiv (j : Fin 4) : Fin 3 ≃ OtherCoordinates j :=
  Equiv.ofBijective (fun i => ⟨retained j i, retained_ne j i⟩) (by fin_cases j <;> decide)

theorem prod_retained (j : Fin 4) (F : OtherCoordinates j → ℝ) :
    (∏ i : OtherCoordinates j, F i) = ∏ i : Fin 3, F (retainedEquiv j i) :=
  ((retainedEquiv j).prod_comp F).symm

theorem three_product_sq_le (F : Fin 3 → ℝ) (epsilon : ℝ)
    (h1 : F 1 ^ 2 ≤ epsilon ^ 2) (h2 : F 2 ^ 2 ≤ epsilon ^ 2) :
    (∏ i : Fin 3, F i) ^ 2 ≤ epsilon ^ 4 * F 0 ^ 2 := by
  calc
    _ = F 0 ^ 2 * (F 1 ^ 2 * F 2 ^ 2) := by simp only [Fin.prod_univ_three]; ring
    _ ≤ F 0 ^ 2 * (epsilon ^ 2 * epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

def factor : ℝ := entryCap ^ 4 * columnCap
def fiberBudget : ℝ := (23 / q ^ 2) * factor

/-- Two entry caps are paid before the remaining information coordinate is
summed. The sole surviving sum is an ordinary column energy. -/
theorem pinned_pattern_fiber_energy_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) :
    (∑ g : WordMixTwoZeroFiber.G r, pinnedPattern b k w j g.val ^ 2) ≤
      wordLaw (sourceInput b k) (zeroPin k w j) ^ 2 * factor := by
  let a := zeroPin k w j
  let mu := wordLaw (sourceInput b k) a
  let v := retained j 0
  let R := residualMatrix AES.wordSuperboxKernel (0 : AES.Word)
  have hentry (i : Fin 4) (y : WordState) :
      R (y i) (affineEquiv k w i a) ^ 2 ≤ entryCap ^ 2 :=
    TwoZeroResponseEnergy.entry_sq_le R entryCap residual_entry_le (y i) (affineEquiv k w i a)
  have hproduct (y : WordState) :
      (∏ i : OtherCoordinates j, R (y i.val) (affineEquiv k w i.val a)) ^ 2 ≤
        entryCap ^ 4 * R (y v) (affineEquiv k w v a) ^ 2 := by
    rw [prod_retained]
    exact three_product_sq_le
      (fun i : Fin 3 => R (y (retained j i)) (affineEquiv k w (retained j i) a))
      entryCap (hentry (retained j 1) y) (hentry (retained j 2) y)
  have hpoint (g : WordMixTwoZeroFiber.G r) :
      pinnedPattern b k w j g.val ^ 2 ≤
        if g.val j = 0 then mu ^ 2 * entryCap ^ 4 *
          R (g.val v) (affineEquiv k w v a) ^ 2 else 0 := by
    by_cases hy : g.val j = 0
    · rw [if_pos hy]
      change (if g.val j = 0 then _ else 0) ^ 2 ≤ _
      rw [if_pos hy, mul_pow]
      calc
        _ ≤ mu ^ 2 * (entryCap ^ 4 * R (g.val v) (affineEquiv k w v a) ^ 2) :=
          mul_le_mul_of_nonneg_left (hproduct g.val) (sq_nonneg mu)
        _ = _ := by ring
    · simp [pinnedPattern, hy]
  calc
    _ ≤ ∑ g : WordMixTwoZeroFiber.G r,
        if g.val j = 0 then mu ^ 2 * entryCap ^ 4 *
          R (g.val v) (affineEquiv k w v a) ^ 2 else 0 :=
      Finset.sum_le_sum (fun g _ => hpoint g)
    _ = ∑ h : WordMixTwoZeroPinnedFiber.H r j,
        mu ^ 2 * entryCap ^ 4 * R (h.val.val v) (affineEquiv k w v a) ^ 2 :=
      WordMixTwoZeroPinnedFiber.sum_input_zero r j
        (fun g => mu ^ 2 * entryCap ^ 4 * R (g.val v) (affineEquiv k w v a) ^ 2)
    _ = (mu ^ 2 * entryCap ^ 4) * ∑ x : AES.Word, R x (affineEquiv k w v a) ^ 2 := by
      rw [← Finset.mul_sum]
      rw [WordMixTwoZeroPinnedFiber.sum_coordinate r hr j v (retained_ne j 0)
        (fun x => R x (affineEquiv k w v a) ^ 2)]
    _ ≤ (mu ^ 2 * entryCap ^ 4) * columnCap :=
      mul_le_mul_of_nonneg_left (OneSourceEventMoment.residual_column_le (affineEquiv k w v a))
        (mul_nonneg (sq_nonneg mu) (pow_nonneg (by norm_num [entryCap, q]) 4))
    _ = _ := by dsimp [mu, a, factor]; ring

theorem conditional_fiber_energy_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (w : OtherAssignments k) :
    (∑ g : WordMixTwoZeroFiber.G r, (∑ j : Fin 4, pinnedPattern b k w j g.val) ^ 2) ≤
      ∑ j : Fin 4, wordLaw (sourceInput b k) (zeroPin k w j) ^ 2 * factor := by
  simp_rw [pinnedPattern_sum_sq]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun j _ => pinned_pattern_fiber_energy_le r hr b k w j)

/-- Jensen precedes pointwise disjoint assembly; the second original source
then averages the four squared pin coefficients separately. -/
theorem actual_zero_fiber_energy_le_of_sources (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (t : OtherCoordinates k) (ht : sourceInput b t.val ≠ 0) :
    (∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) (11 : Fin 14) g.val ^ 2) ≤
      4 * fiberBudget := by
  rw [actual_component_eleven_eq_probability_mixture b k]
  calc
    _ ≤ ∑ w : OtherAssignments k, conditionWeight b k w *
        ∑ g : WordMixTwoZeroFiber.G r, (∑ j : Fin 4, pinnedPattern b k w j g.val) ^ 2 :=
      weighted_energy_le (conditionWeight b k)
        (fun w (g : WordMixTwoZeroFiber.G r) => ∑ j : Fin 4, pinnedPattern b k w j g.val)
        (conditionWeight_nonnegative b k) (conditionWeight_total b k)
    _ ≤ ∑ w : OtherAssignments k, conditionWeight b k w *
        ∑ j : Fin 4, wordLaw (sourceInput b k) (zeroPin k w j) ^ 2 * factor :=
      Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
        (conditional_fiber_energy_le r hr b k w) (conditionWeight_nonnegative b k w))
    _ = ∑ j : Fin 4, (∑ w : OtherAssignments k, conditionWeight b k w *
        wordLaw (sourceInput b k) (zeroPin k w j) ^ 2) * factor := by
      simp only [Finset.mul_sum, ← _root_.mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
    _ ≤ ∑ _j : Fin 4, (23 / q ^ 2) * factor :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (PinnedSourceAverage.actual_pin_average_le b k hk t ht j)
        (by norm_num [factor, entryCap, columnCap, q]))
    _ = 4 * fiberBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat, fiberBudget]

private theorem two_active_positions : ∀ bits : Fin 4 → Bool,
    2 ≤ residualDegree bits → ∃ k t : Fin 4, k ≠ t ∧ bits k = true ∧ bits t = true := by decide

theorem actual_zero_fiber_energy_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    (∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) (11 : Fin 14) g.val ^ 2) ≤
      4 * fiberBudget := by
  obtain ⟨k, t, hkt, hk, ht⟩ := two_active_positions (activeSourceMask b) hb
  exact actual_zero_fiber_energy_le_of_sources r hr b k ((activeSourceMask_iff b k).mp hk)
    ⟨t, hkt.symm⟩ ((activeSourceMask_iff b t).mp ht)

theorem actual_support_two_event_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    boundaryEventEnergy 2 (component (error 1 b) (11 : Fin 14)) ≤ 24 * fiberBudget := by
  calc
    _ ≤ ∑ j : Fin 6, ∑ g : WordMixTwoZeroFiber.G (zeroMask j),
        component (error 1 b) (11 : Fin 14) g.val ^ 2 :=
      TwoZeroThirteenMoment.support_two_energy_le_zero_fibers (component (error 1 b) (11 : Fin 14))
    _ ≤ ∑ _j : Fin 6, 4 * fiberBudget :=
      Finset.sum_le_sum (fun j _ => actual_zero_fiber_energy_le (zeroMask j) (zeroMask_size j) b hb)
    _ = 24 * fiberBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem actual_projected_eight_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    (∑ y, component (boundaryInput (component (error 1 b) (11 : Fin 14)))
      (8 : Fin 14) y ^ 2) ≤ 24 * fiberBudget := by
  have h := FirstHighSupportEvent.component_energy_le_restriction
    (boundaryInput (component (error 1 b) (11 : Fin 14))) (8 : Fin 14)
  change (∑ y, component (boundaryInput (component (error 1 b) (11 : Fin 14)))
    (8 : Fin 14) y ^ 2) ≤
      ∑ y, restrictSupport 2 (boundaryInput (component (error 1 b) (11 : Fin 14))) y ^ 2 at h
  rw [FirstHighSupportEvent.restriction_energy_eq_boundaryEvent] at h
  exact h.trans (actual_support_two_event_energy_le b hb)

theorem scaled_fiber_budget_le : q ^ 5 * (24 * fiberBudget) ≤ (1 : ℝ) / 1000000000000 := by
  norm_num [fiberBudget, factor, entryCap, columnCap, q]

theorem actual_projected_eight_scaled_length_le_of_several
    (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    (2 : ℝ) ^ 80 * l2 (component
      (boundaryInput (component (error 1 b) (11 : Fin 14))) (8 : Fin 14)) ≤
        1 / 1000000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ) ^ 80) ^ 2 = q ^ 5 := by norm_num [q]
  rw [hs]
  exact (mul_le_mul_of_nonneg_left (actual_projected_eight_energy_le b hb)
    (by norm_num [q])).trans (scaled_fiber_budget_le.trans (by norm_num))

/-- Uniform incoming-eleven allowance: exact zero for one active original
source, and the correlated affine-pin estimate for all remaining nonzero b. -/
theorem actual_projected_eight_scaled_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component
      (boundaryInput (component (error 1 b) (11 : Fin 14))) (8 : Fin 14)) ≤
        1 / 1000000 := by
  by_cases h1 : activeSourceCount b = 1
  · rw [OneSourceSupport.actual_component_eleven_eq_zero b h1]
    have hz : boundaryInput (0 : WordState → ℝ) = 0 := rfl
    rw [hz]
    have hc : component (0 : WordState → ℝ) (8 : Fin 14) = 0 := by
      funext y
      rw [SupportProfile.component_eq_support_residual]
      simp [SupportProfile.raw, action]
    rw [hc]
    change (2 : ℝ)^80 * l2 (fun _ : WordState => (0 : ℝ)) ≤ 1/1000000
    rw [l2_zero, mul_zero]
    norm_num
  · have hp := AESPaper.UniversalInitialization.activeSourceCount_pos b hb
    exact actual_projected_eight_scaled_length_le_of_several b (by omega)

end AES8.TwoZeroElevenMoment
