/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwoZeroResponseEnergy
import AES8.Reductions.Fibers.WordMixTwoZeroFiber
import AES8.Estimates.Word.OrdinaryResidualEntry
import AES8.Reductions.Source.ConditionalSourceResponse
import AES8.Estimates.Source.OneSourceEventMoment

/-!
# Incoming degree-four moment for the projected two-zero output

The actual component thirteen is a probability mixture of four-residual
responses in one original nonzero source word. On every literal two-zero
forward wordMix fiber, input coordinates 0,1 are information coordinates.
The generic entry/row/column/trace argument bounds every conditional response,
then Jensen preserves the bound for the actual signed centered component.

Six zero masks cover the two-active-word event. The existing exact support
restriction bridge controls projected output eight by that nonnegative event.
Only the original source product law is used; current boundary coordinates
are never assumed independent.
 No attacks,
active source, root/Audit, manuscript or predecessor edits are authorized here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwoZeroThirteenMoment
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component activeCount)
open AES8.ConditionalSourceResponse
open AES8.FirstHighSupportEvent (boundaryInput boundaryEventEnergy restrictSupport)
open AES8.OneSourceEventMoment (atomCap columnCap traceCap)

def entryCap : ℝ := 20 / q
def fiberBudget : ℝ := atomCap ^ 2 * entryCap ^ 2 * columnCap ^ 2 * traceCap

theorem residual_entry_le (y x : AES.Word) :
    |residualMatrix AES.wordSuperboxKernel 0 y x| ≤ entryCap := by
  have h := OrdinaryResidualEntry.actual_word_residual_entry_le x y
  simpa only [entryCap, q, show (2 : ℝ) ^ 32 = 4294967296 by norm_num] using h

section Conditional
variable {G : Type*} [Fintype G]

/-- Geometry is explicit and independent of the actual initial source count. -/
theorem conditional_energy_le (coords : G → WordState)
    (hinfo : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (w : OtherAssignments k) :
    (∑ g, conditionalResponse b k w (coords g) ^ 2) ≤ fiberBudget := by
  have h := TwoZeroResponseEnergy.response_energy_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun i => affineEquiv k w i) coords (wordLaw (sourceInput b k)) hinfo
    atomCap entryCap columnCap traceCap (by norm_num [columnCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun _ y x => residual_entry_le y x)
    (fun _ y => OneSourceEventMoment.residual_row_le y)
    (fun _ x => OneSourceEventMoment.residual_column_le x)
    (fun _ => OneSourceEventMoment.residual_trace_le)
  change (∑ g, conditionalResponse b k w (coords g) ^ 2) ≤ fiberBudget at h
  exact h

/-- Jensen uses only the actual nonnegative weights of the other original
sources. The conditional responses and component thirteen may be signed. -/
theorem actual_energy_le_of_source (coords : G → WordState)
    (hinfo : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) :
    (∑ g, component (error 1 b) (13 : Fin 14) (coords g) ^ 2) ≤ fiberBudget := by
  rw [actual_component_thirteen_eq_probability_mixture b k]
  exact weighted_energy_le_uniform (conditionWeight b k)
    (fun w g => conditionalResponse b k w (coords g))
    (conditionWeight_nonnegative b k) (conditionWeight_total b k) fiberBudget
    (fun w => conditional_energy_le coords hinfo b k hk w)

theorem actual_energy_le (coords : G → WordState)
    (hinfo : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g, component (error 1 b) (13 : Fin 14) (coords g) ^ 2) ≤ fiberBudget := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  exact actual_energy_le_of_source coords hinfo b k hk

end Conditional

/-- Full-vector actual initialization on one literal two-zero output fiber. -/
theorem actual_zero_fiber_energy_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g : WordMixTwoZeroFiber.G r,
      component (error 1 b) (13 : Fin 14) g.val ^ 2) ≤ fiberBudget :=
  actual_energy_le (fun g : WordMixTwoZeroFiber.G r => g.val)
    (WordMixTwoZeroFiber.coords01_bijective r hr) b hb

section SupportEvent

/-- This finite list enumerates zero POSITION masks only, never words/states. -/
def zeroMask : Fin 6 → Fin 16 := ![3, 5, 6, 9, 10, 12]

theorem zeroMask_size : ∀ j : Fin 6, maskSize (zeroMask j) = 2 := by decide

private theorem emptyMask_mem : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide

private theorem zeroMask_of_two_false : ∀ bits : Fin 4 → Bool,
    (Finset.univ.filter (fun i => bits i = false)).card = 2 →
      ∃ j : Fin 6, ∀ i : Fin 4, maskBit (zeroMask j) i = true → bits i = true := by decide

theorem activeCount_two_has_zeroMask (y : WordState) (hy : activeCount y = 2) :
    ∃ j : Fin 6, ∀ i : Fin 4, maskBit (zeroMask j) i = true → y i = 0 := by
  have hf : Finset.univ.filter (fun i : Fin 4 => decide (y i = 0) = false) =
      Finset.univ.filter (fun i : Fin 4 => y i ≠ 0) := by
    ext i
    simp
  have hc : (Finset.univ.filter (fun i : Fin 4 => decide (y i = 0) = false)).card = 2 := by
    rw [hf]
    exact hy
  obtain ⟨j, hj⟩ := zeroMask_of_two_false (fun i => decide (y i = 0)) hc
  exact ⟨j, fun i hi => of_decide_eq_true (hj i hi)⟩

/-- A six-fiber union is used only after taking nonnegative squared values. -/
theorem support_two_energy_le_zero_fibers (f : WordState → ℝ) :
    (∑ y, if activeCount (WordCrossZero.wordMixAddEquiv y) = 2 then f y ^ 2 else 0) ≤
      ∑ j : Fin 6, ∑ g : WordMixTwoZeroFiber.G (zeroMask j), f g.val ^ 2 := by
  classical
  calc
    _ ≤ ∑ y : WordState, ∑ j : Fin 6,
        if graphPrescribed WordMixTwoZeroFiber.L (zeroMask j) 0 0 0 y
          then f y ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : activeCount (WordCrossZero.wordMixAddEquiv y) = 2
      · rw [if_pos hy]
        obtain ⟨j, hj⟩ := activeCount_two_has_zeroMask (WordCrossZero.wordMixAddEquiv y) hy
        have hg : graphPrescribed WordMixTwoZeroFiber.L (zeroMask j) 0 0 0 y := by
          constructor
          · intro i hi
            exact hj i hi
          · intro i hi
            rw [emptyMask_mem] at hi
            exact Bool.noConfusion hi
        calc
          _ = (if graphPrescribed WordMixTwoZeroFiber.L (zeroMask j) 0 0 0 y
              then f y ^ 2 else 0) := by rw [if_pos hg]
          _ ≤ ∑ t : Fin 6,
              if graphPrescribed WordMixTwoZeroFiber.L (zeroMask t) 0 0 0 y
                then f y ^ 2 else 0 :=
            Finset.single_le_sum (f := fun t : Fin 6 =>
              if graphPrescribed WordMixTwoZeroFiber.L (zeroMask t) 0 0 0 y
                then f y ^ 2 else 0)
              (fun t _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
              (Finset.mem_univ j)
      · rw [if_neg hy]
        exact Finset.sum_nonneg
          (fun j _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
    _ = ∑ j : Fin 6, ∑ y : WordState,
        if graphPrescribed WordMixTwoZeroFiber.L (zeroMask j) 0 0 0 y
          then f y ^ 2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact WordMixTwoZeroFiber.sum_zero_event (zeroMask j) (fun y => f y ^ 2)

theorem actual_support_two_event_energy_le (b : AES.State) (hb : b ≠ 0) :
    boundaryEventEnergy 2 (component (error 1 b) (13 : Fin 14)) ≤ 6 * fiberBudget := by
  calc
    _ ≤ ∑ j : Fin 6, ∑ g : WordMixTwoZeroFiber.G (zeroMask j),
        component (error 1 b) (13 : Fin 14) g.val ^ 2 :=
      support_two_energy_le_zero_fibers (component (error 1 b) (13 : Fin 14))
    _ ≤ ∑ _j : Fin 6, fiberBudget :=
      Finset.sum_le_sum (fun j _ => actual_zero_fiber_energy_le (zeroMask j) (zeroMask_size j) b hb)
    _ = 6 * fiberBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]

/-- Existing support restriction contraction supplies the projected consumer. -/
theorem actual_projected_eight_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) (13 : Fin 14)))
      (8 : Fin 14) y ^ 2) ≤ 6 * fiberBudget := by
  have h := FirstHighSupportEvent.component_energy_le_restriction
    (boundaryInput (component (error 1 b) (13 : Fin 14))) (8 : Fin 14)
  change (∑ y, component (boundaryInput (component (error 1 b) (13 : Fin 14)))
    (8 : Fin 14) y ^ 2) ≤
      ∑ y, restrictSupport 2 (boundaryInput (component (error 1 b) (13 : Fin 14))) y ^ 2 at h
  rw [FirstHighSupportEvent.restriction_energy_eq_boundaryEvent] at h
  exact h.trans (actual_support_two_event_energy_le b hb)

end SupportEvent

theorem scaled_fiber_budget_le : q ^ 5 * (6 * fiberBudget) ≤ (1 : ℝ) / 160000000000 := by
  norm_num [fiberBudget, entryCap, atomCap, columnCap, traceCap, q]

theorem actual_projected_eight_scaled_energy_le (b : AES.State) (hb : b ≠ 0) :
    q ^ 5 * (∑ y, component (boundaryInput (component (error 1 b) (13 : Fin 14)))
      (8 : Fin 14) y ^ 2) ≤ (1 : ℝ) / 160000000000 :=
  (mul_le_mul_of_nonneg_left (actual_projected_eight_energy_le b hb)
    (by norm_num [q])).trans scaled_fiber_budget_le

/-- The incoming-thirteen allowance from the candidate output-eight note.
Other incoming components and final first-high assembly remain separate. -/
theorem actual_projected_eight_scaled_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component
      (boundaryInput (component (error 1 b) (13 : Fin 14))) (8 : Fin 14)) ≤
        1 / 400000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ) ^ 80) ^ 2 = q ^ 5 := by norm_num [q]
  rw [hs]
  exact (actual_projected_eight_scaled_energy_le b hb).trans (by norm_num)

end AES8.TwoZeroThirteenMoment
