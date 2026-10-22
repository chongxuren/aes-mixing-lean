/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighZero

/-!
# Rational scalar screen for the next degree-zero coordinate

These are resource arithmetic and sufficient allowances only. They do not
assert any signed mass estimate or projected energy theorem. Exact support
two requires subtracting two three-zero endpoint fibers before squaring.

Constructive work only; no attacks or predecessor/manuscript edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section

namespace AES8.TwoActiveScalars
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q)
open AES8.OneSourceEventMoment (atomCap columnCap traceCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.TwoZeroTwelveMoment (constantCap)

def thirteenFullMassCap : ℝ := atomCap * columnCap * traceCap
def twelvePatternFullMassCap : ℝ := atomCap * traceCap * (11 / (30 * q))
def elevenExactMassCap : ℝ := 4 * atomCap * entryCap * columnCap
def twelveExactMassCap : ℝ :=
  4 * twelvePatternFullMassCap + 8 * ActualZeroMoment.twelvePatternMassCap
def thirteenExactMassCap : ℝ :=
  thirteenFullMassCap + 2 * ActualZeroMoment.thirteenMassCap

def elevenBudget : ℝ := 6 * elevenExactMassCap ^ 2 / (q - 1) ^ 2
def twelveBudget : ℝ := 6 * twelveExactMassCap ^ 2 / (q - 1) ^ 2
def thirteenBudget : ℝ := 6 * thirteenExactMassCap ^ 2 / (q - 1) ^ 2

/-- A rational enclosure for sqrt(kappa*delta), avoiding a square-root
constant in the forthcoming signed-mass interface. -/
theorem constant_column_product_le :
    constantCap * columnCap ≤ (11 / (30 * q)) ^ 2 := by
  norm_num [constantCap, columnCap, q]

theorem exact_thirteen_full_mass_cap : thirteenFullMassCap = 11336 / q ^ 3 := by
  norm_num [thirteenFullMassCap, atomCap, columnCap, traceCap, q]

theorem exact_twelve_pattern_full_mass_cap : twelvePatternFullMassCap = 31174 / q ^ 3 := by
  norm_num [twelvePatternFullMassCap, atomCap, traceCap, q]

theorem exact_eleven_budget : q ^ 5 * elevenBudget =
    (819200 : ℝ) / (3 * q * (q - 1) ^ 2) := by
  norm_num [elevenBudget, elevenExactMassCap, atomCap, entryCap, columnCap, q]

theorem exact_twelve_budget : q ^ 5 * twelveBudget =
    6 * (124696 * q + 13478504) ^ 2 / (q * (q - 1) ^ 4) := by
  norm_num [twelveBudget, twelveExactMassCap, twelvePatternFullMassCap,
    ActualZeroMoment.twelvePatternMassCap, atomCap, constantCap, entryCap, columnCap, traceCap, q]

theorem exact_thirteen_budget : q ^ 5 * thirteenBudget =
    (771029376 : ℝ) * (q + 6000) ^ 2 / (q ^ 3 * (q - 1) ^ 2) := by
  norm_num [thirteenBudget, thirteenExactMassCap, thirteenFullMassCap,
    ActualZeroMoment.thirteenMassCap, atomCap, entryCap, columnCap, traceCap, q]

theorem eleven_budget_le : q ^ 5 * elevenBudget ≤ (1 / 100000000000 : ℝ) ^ 2 := by
  rw [exact_eleven_budget]
  norm_num [q]

theorem twelve_budget_le : q ^ 5 * twelveBudget ≤ (11 / 10000000000 : ℝ) ^ 2 := by
  rw [exact_twelve_budget]
  norm_num [q]

theorem thirteen_budget_le : q ^ 5 * thirteenBudget ≤ (1 / 10000000000 : ℝ) ^ 2 := by
  rw [exact_thirteen_budget]
  norm_num [q]

/-- Scalar sufficiency only; all three actual length premises remain open. -/
theorem scalar_one_le :
    (2 : ℝ) ^ 41 * ((1 / 100000000000) +
      ((11 / 10000000000) + (1 / 10000000000))) ≤
        (1000 * g (1 : Fin 14)) * d (1 : Fin 14) := by
  norm_num [g, d, vec14_apply, Fin.ext_iff]

end AES8.TwoActiveScalars
