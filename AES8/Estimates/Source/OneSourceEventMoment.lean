/- Module role: Concrete source bounds and startup estimates for the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighSupportEvent
import AES8.Reductions.Source.ZeroFiberResponseEnergy
import AES8.Reductions.Fibers.WordMixEventFiber
import AES8.Estimates.Word.PaperWordTraceVariants

/-!
# Close the retained one-source support-three event moment

On each literal one-zero fiber of forward wordMix, the two input triples
(0,2,3) and (1,2,3) are information coordinates. The signed common-source
Cauchy theorem therefore bounds that fiber's response energy by
(20/q)^2 * (2/(15q))^3 * (4251/q), using actual ordinary AES row/column
energies and trace. The three-active event is contained in the union of the
four zero fibers. Its scaled moment fits the explicit 1/62500 allowance.

Together with FirstHighSupportEvent this closes first-high coordinate eleven
for one-source inputs; the existing several-source theorem covers the rest.
The source weight is never replaced by independent coordinate laws. Both
centering and the actual physical boundary are retained by the imported
exact bridge. No claim about other remaining caps or the full AES theorem.

No attacks, local execution, manuscript edits or predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.OneSourceEventMoment
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (activeCount)
open AES8.FirstHighSupportEvent

def atomCap : ℝ := 20 / q
def columnCap : ℝ := 2 / (15 * q)
def traceCap : ℝ := 4251 / q
def fiberBudget : ℝ := atomCap ^ 2 * columnCap ^ 3 * traceCap

def commonResponse (k : Fin 4) (a : AES.Word) (y : WordState) : ℝ :=
  ∑ x, oneSourceResidualColumn k y x * wordLaw a x

theorem residual_column_le (x : AES.Word) :
    (∑ y, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) ≤ columnCap := by
  have h := AESPaper.LocalAES.local_column_energy false false x
  change (∑ y, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) < columnCap at h
  exact h.le

/-- The transpose variant is essential: the retained moment uses row energies. -/
theorem residual_row_le (y : AES.Word) :
    (∑ x, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) ≤ columnCap := by
  have h := AESPaper.LocalAES.local_column_energy true false y
  change (∑ x, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) < columnCap at h
  exact h.le

-- Route dependency: the trace premise uses the owned physical degree-HS assembly.
theorem residual_trace_le :
    (∑ y, ∑ x, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) ≤ traceCap := by
  have h := (PaperWordTraceVariants.variant_trace_lt false false).le
  change (∑ y, ∑ x, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) ≤
    (4251 / 4294967296 : ℝ) at h
  calc
    _ ≤ (4251 / 4294967296 : ℝ) := h
    _ = traceCap := by norm_num [traceCap, q]

/-- Literal forward boundary fiber, with exactly one common source label. -/
theorem zero_fiber_energy_le (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) (c : Fin 4) :
    (∑ g : WordMixEventFiber.G c, commonResponse k a g.val ^ 2) ≤ fiberBudget := by
  have h := ZeroFiberResponseEnergy.response_energy_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun i => AESPaper.BoundarySourceCoordinates.outputEquiv k i)
    (fun g : WordMixEventFiber.G c => g.val) (wordLaw a)
    (WordMixEventFiber.coords023_bijective c) (WordMixEventFiber.coords123_bijective c)
    atomCap columnCap traceCap (by norm_num [atomCap, q])
    (by norm_num [columnCap, q]) (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt a x ha).le)
    (fun _ y => residual_row_le y) (fun _ => residual_trace_le)
    (fun _ x => residual_column_le x)
  exact h

/-- The event remains a condition on the actual forward diffusion. -/
theorem event_quadratic_eq_energy (n : ℕ) (k : Fin 4) (a : AES.Word) :
    oneSourceEventQuadratic n k a =
      ∑ y : WordState, if activeCount (WordCrossZero.wordMixAddEquiv y) = n then
        commonResponse k a y ^ 2 else 0 := by
  exact (event_response_energy (oneSourceResidualColumn k) (wordLaw a)
    (fun y => activeCount (WordCrossZero.wordMixAddEquiv y) = n)).symm

theorem activeCount_three_has_zero (y : WordState) (hy : SupportProfile.activeCount y = 3) :
    ∃ i : Fin 4, y i = 0 := by
  by_contra h
  push Not at h
  have hfour : SupportProfile.activeCount y = 4 := by
    simp [SupportProfile.activeCount, h]
  omega

/-- A nonnegative energy union bound, without a distributional assumption. -/
theorem three_event_energy_le_zero_fibers (f : WordState → ℝ) :
    (∑ y, if SupportProfile.activeCount (WordCrossZero.wordMixAddEquiv y) = 3 then
      f y ^ 2 else 0) ≤
      ∑ c : Fin 4, ∑ y : WordState,
        if WordCrossZero.wordMixAddEquiv y c = 0 then f y ^ 2 else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : SupportProfile.activeCount (WordCrossZero.wordMixAddEquiv y) = 3
  · rw [if_pos hy]
    obtain ⟨c, hc⟩ := activeCount_three_has_zero (WordCrossZero.wordMixAddEquiv y) hy
    calc
      _ = (if WordCrossZero.wordMixAddEquiv y c = 0 then f y ^ 2 else 0) := by
        rw [if_pos hc]
      _ ≤ ∑ j : Fin 4, if WordCrossZero.wordMixAddEquiv y j = 0 then f y ^ 2 else 0 :=
        Finset.single_le_sum (f := fun j : Fin 4 =>
          if WordCrossZero.wordMixAddEquiv y j = 0 then f y ^ 2 else 0)
          (fun j _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
          (Finset.mem_univ c)
  · rw [if_neg hy]
    exact Finset.sum_nonneg
      (fun j _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)

/-- The exact constrained Gram is bounded using its actual signed response.
Only at this nonnegative event-energy stage is the four-fiber union used. -/
theorem event_quadratic_le (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    oneSourceEventQuadratic 3 k a ≤ 4 * fiberBudget := by
  rw [event_quadratic_eq_energy]
  calc
    _ ≤ ∑ c : Fin 4, ∑ y : WordState,
        if WordCrossZero.wordMixAddEquiv y c = 0 then commonResponse k a y ^ 2 else 0 :=
      three_event_energy_le_zero_fibers (commonResponse k a)
    _ = ∑ c : Fin 4, ∑ g : WordMixEventFiber.G c, commonResponse k a g.val ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      exact WordMixEventFiber.sum_zero_event c (fun y => commonResponse k a y ^ 2)
    _ ≤ ∑ _c : Fin 4, fiberBudget :=
      Finset.sum_le_sum (fun c _ => zero_fiber_energy_le k a ha c)
    _ = 4 * fiberBudget := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- Exact rational sufficiency. The local resource formulas, not the target
AES conclusion, supply this scalar certificate. -/
theorem event_budget_le : q ^ 5 * (4 * fiberBudget) ≤ (1 : ℝ) / 62500 := by
  norm_num [fiberBudget, atomCap, columnCap, traceCap, q]

/-- The previously explicit missing event moment is discharged for every
actual nonzero source word and each of its four physical positions. -/
theorem scaled_event_quadratic_le (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    q ^ 5 * oneSourceEventQuadratic 3 k a ≤ (1 : ℝ) / 62500 :=
  (mul_le_mul_of_nonneg_left (event_quadratic_le k a ha) (by norm_num [q])).trans
    event_budget_le

theorem firstHigh_eleven_of_one (b : AES.State) (hb : activeSourceCount b = 1) :
    SupportProfile.profile (TransferAssembly.centeredStep
      (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      (d (11 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (11 : Fin 14)) := by
  obtain ⟨k, a, ha, hsource⟩ := AESPaper.UniversalInitialization.one_active_source b hb
  exact FirstHighSupportEvent.firstHigh_eleven_of_event_moment b hb k a hsource
    (scaled_event_quadratic_le k a ha)

/-- Complete first-high coordinate eleven for the actual AES grouped error. -/
theorem firstHigh_eleven (b : AES.State) (hb : b ≠ 0) :
    SupportProfile.profile (TransferAssembly.centeredStep
      (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      (d (11 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (11 : Fin 14)) := by
  by_cases h1 : activeSourceCount b = 1
  · exact firstHigh_eleven_of_one b h1
  · have hp := AESPaper.UniversalInitialization.activeSourceCount_pos b hb
    exact FirstHighSeveralSource.firstHigh_eleven_of_several b (by omega)

end AES8.OneSourceEventMoment
