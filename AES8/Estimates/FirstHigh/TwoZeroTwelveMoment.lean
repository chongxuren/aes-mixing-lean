/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ThreeResidualConstantEnergy
import AES8.Reductions.Source.TwelvePatternCoordinates
import AES8.Reductions.Source.TwelveConditionalResponse
import AES8.Estimates.FirstHigh.TwoZeroThirteenMoment

/-!
# Incoming-twelve projected output-eight length from actual constant channels

Each conditional pattern has three residual factors and one literal
constant-nonzero factor. A position permutation exposes two residual input
information coordinates and the third residual entry. The generic moment
uses the source atom cap, constant cap, residual entry cap and two traces.
The four incoming patterns overlap after fiber restriction, so squared
triangle charges sixteen pattern bounds per fiber. Jensen preserves this
bound for the actual component. Six zero fibers and the existing support
restriction contraction give the projected output-eight length.

Only initial source laws are factored.  No attacks, proof bypasses,
active source, root/Audit, manuscript or predecessor changes in this branch.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwoZeroTwelveMoment
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.TwelveConditionalResponse
open AES8.TwelvePatternCoordinates (order order_zero order_ne_zero)
open AES8.OneSourceEventMoment (atomCap traceCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.FirstHighSupportEvent (boundaryInput boundaryEventEnergy restrictSupport)

def constantCap : ℝ := 1 / (q - 1)
def patternBudget : ℝ := atomCap ^ 2 * constantCap ^ 2 * entryCap ^ 2 * traceCap ^ 2

theorem constant_entry_le (y x : AES.Word) : |constantMatrix (0 : AES.Word) y x| ≤ constantCap := by
  have hcard : (Fintype.card AES.Word : ℝ) = q := AESPaper.StartingWord.q_eq_word_card.symm
  change |activityMatrix (0 : AES.Word) y x - identityKernel y 0 * identityKernel x 0| ≤
    1 / (q - 1)
  -- Rewrite the literal word cardinality before any concrete Word reduction.
  by_cases hy : y = 0 <;> by_cases hx : x = 0 <;>
    simp only [activityMatrix, identityKernel, hy, hx, ite_true, ite_false, hcard,
      one_mul, mul_one, zero_mul, mul_zero, sub_self, sub_zero, abs_zero]
    <;> norm_num [q]

section Conditional
variable {G : Type*} [Fintype G]

/-- Reorder literal POSITION labels only; neither source nor observation laws
are replaced. All four factors still carry the same original source word. -/
theorem conditionalPattern_eq_response (coords : G → WordState)
    (b : AES.State) (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) (g : G) :
    conditionalPattern b k w j (coords g) =
      ZeroFiberResponseEnergy.response
        (fun i => patternChannel j (order j i))
        (fun i => affineEquiv k w (order j i))
        (fun g i => coords g (order j i)) (wordLaw (sourceInput b k)) g := by
  unfold conditionalPattern conditionalTensorResponse tensorResponse
    ZeroFiberResponseEnergy.response tensorColumn
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (fun a : ℝ => a * wordLaw (sourceInput b k) x)
    (Equiv.prod_comp (order j)
      (fun i => patternChannel j i (coords g i) (affineEquiv k w i x))).symm

theorem conditional_pattern_energy_le (coords : G → WordState)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (w : OtherAssignments k) (j : Fin 4)
    (hinfo : Function.Bijective (fun g => (coords g (order j 1), coords g (order j 2)))) :
    (∑ g, conditionalPattern b k w j (coords g) ^ 2) ≤ patternBudget := by
  have h := ThreeResidualConstantEnergy.response_energy_le
    (fun i => patternChannel j (order j i))
    (fun i => affineEquiv k w (order j i))
    (fun g i => coords g (order j i)) (wordLaw (sourceInput b k)) hinfo
    atomCap constantCap entryCap traceCap (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun y x => by
      simpa only [order_zero, patternChannel, if_pos rfl, ite_true] using constant_entry_le y x)
    (fun y x => by
      simpa only [patternChannel, if_neg (order_ne_zero j 3 (by decide))] using
        TwoZeroThirteenMoment.residual_entry_le y x)
    (by
      simpa only [patternChannel, if_neg (order_ne_zero j 1 (by decide))] using
        OneSourceEventMoment.residual_trace_le)
    (by
      simpa only [patternChannel, if_neg (order_ne_zero j 2 (by decide))] using
        OneSourceEventMoment.residual_trace_le)
  calc
    _ = ∑ g, ZeroFiberResponseEnergy.response
        (fun i => patternChannel j (order j i))
        (fun i => affineEquiv k w (order j i))
        (fun g i => coords g (order j i)) (wordLaw (sourceInput b k)) g ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [conditionalPattern_eq_response]
    _ ≤ patternBudget := h

theorem square_sum_four_le (a : Fin 4 → ℝ) : (∑ j, a j) ^ 2 ≤ 4 * ∑ j, a j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun _ : Fin 4 => (1 : ℝ))
  have hone : (∑ _j : Fin 4, (1 : ℝ) ^ 2) = 4 := by norm_num
  calc
    _ = (∑ j, a j * 1) ^ 2 := by simp only [_root_.mul_one]
    _ ≤ (∑ j, a j ^ 2) * (∑ _j : Fin 4, (1 : ℝ) ^ 2) := h
    _ = 4 * ∑ j, a j ^ 2 := by
      rw [hone]
      exact mul_comm _ _

/-- Restricted incoming patterns need not remain orthogonal. Charge four
from squared triangle and four pattern bounds, giving the safe factor 16. -/
theorem conditional_sum_energy_le (coords : G → WordState)
    (hinfo : ∀ j : Fin 4, Function.Bijective
      (fun g => (coords g (order j 1), coords g (order j 2))))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    (∑ g, (∑ j : Fin 4, conditionalPattern b k w j (coords g)) ^ 2) ≤ 16 * patternBudget := by
  calc
    _ ≤ ∑ g, 4 * ∑ j : Fin 4, conditionalPattern b k w j (coords g) ^ 2 :=
      Finset.sum_le_sum (fun g _ => square_sum_four_le (fun j => conditionalPattern b k w j (coords g)))
    _ = 4 * ∑ j : Fin 4, ∑ g, conditionalPattern b k w j (coords g) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 4 * ∑ _j : Fin 4, patternBudget := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun j _ => conditional_pattern_energy_le coords b k hk w j (hinfo j))
    _ = 16 * patternBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem actual_energy_le_of_source (coords : G → WordState)
    (hinfo : ∀ j : Fin 4, Function.Bijective
      (fun g => (coords g (order j 1), coords g (order j 2))))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) :
    (∑ g, component (error 1 b) (12 : Fin 14) (coords g) ^ 2) ≤ 16 * patternBudget := by
  rw [actual_component_twelve_eq_probability_mixture b k]
  exact weighted_energy_le_uniform (conditionWeight b k)
    (fun w g => ∑ j : Fin 4, conditionalPattern b k w j (coords g))
    (conditionWeight_nonnegative b k) (conditionWeight_total b k) (16 * patternBudget)
    (fun w => conditional_sum_energy_le coords hinfo b k hk w)

theorem actual_energy_le (coords : G → WordState)
    (hinfo : ∀ j : Fin 4, Function.Bijective
      (fun g => (coords g (order j 1), coords g (order j 2))))
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g, component (error 1 b) (12 : Fin 14) (coords g) ^ 2) ≤ 16 * patternBudget := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  exact actual_energy_le_of_source coords hinfo b k hk

end Conditional

theorem actual_zero_fiber_energy_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) (12 : Fin 14) g.val ^ 2) ≤
      16 * patternBudget :=
  actual_energy_le (fun g : WordMixTwoZeroFiber.G r => g.val)
    (fun j => TwelvePatternCoordinates.residual_coords_bijective r hr j) b hb

theorem actual_support_two_event_energy_le (b : AES.State) (hb : b ≠ 0) :
    boundaryEventEnergy 2 (component (error 1 b) (12 : Fin 14)) ≤ 96 * patternBudget := by
  calc
    _ ≤ ∑ j : Fin 6, ∑ g : WordMixTwoZeroFiber.G (TwoZeroThirteenMoment.zeroMask j),
        component (error 1 b) (12 : Fin 14) g.val ^ 2 :=
      TwoZeroThirteenMoment.support_two_energy_le_zero_fibers (component (error 1 b) (12 : Fin 14))
    _ ≤ ∑ _j : Fin 6, 16 * patternBudget :=
      Finset.sum_le_sum (fun j _ => actual_zero_fiber_energy_le
        (TwoZeroThirteenMoment.zeroMask j) (TwoZeroThirteenMoment.zeroMask_size j) b hb)
    _ = 96 * patternBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem actual_projected_eight_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) (12 : Fin 14)))
      (8 : Fin 14) y ^ 2) ≤ 96 * patternBudget := by
  have h := FirstHighSupportEvent.component_energy_le_restriction
    (boundaryInput (component (error 1 b) (12 : Fin 14))) (8 : Fin 14)
  change (∑ y, component (boundaryInput (component (error 1 b) (12 : Fin 14)))
    (8 : Fin 14) y ^ 2) ≤
      ∑ y, restrictSupport 2 (boundaryInput (component (error 1 b) (12 : Fin 14))) y ^ 2 at h
  rw [FirstHighSupportEvent.restriction_energy_eq_boundaryEvent] at h
  exact h.trans (actual_support_two_event_energy_le b hb)

theorem scaled_pattern_budget_le : q ^ 5 * (96 * patternBudget) ≤ (1 : ℝ) / 100000000000000 := by
  norm_num [patternBudget, constantCap, entryCap, atomCap, traceCap, q]

theorem actual_projected_eight_scaled_energy_le (b : AES.State) (hb : b ≠ 0) :
    q ^ 5 * (∑ y, component (boundaryInput (component (error 1 b) (12 : Fin 14)))
      (8 : Fin 14) y ^ 2) ≤ (1 : ℝ) / 100000000000000 :=
  (mul_le_mul_of_nonneg_left (actual_projected_eight_energy_le b hb)
    (by norm_num [q])).trans scaled_pattern_budget_le

/-- Incoming-twelve consumer for output eight, with every constant-channel
and pattern-count obligation retained in the preceding actual proof chain. -/
theorem actual_projected_eight_scaled_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component
      (boundaryInput (component (error 1 b) (12 : Fin 14))) (8 : Fin 14)) ≤
        1 / 10000000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ) ^ 80) ^ 2 = q ^ 5 := by norm_num [q]
  rw [hs]
  exact (actual_projected_eight_scaled_energy_le b hb).trans (by norm_num)

end AES8.TwoZeroTwelveMoment
