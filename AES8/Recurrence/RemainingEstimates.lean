/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighOne
import AES8.Estimates.FirstHigh.FirstHighZero
import AES8.Estimates.Return.ReturnEleven
import AES8.Estimates.FirstHigh.FirstHighFour
import AES8.Estimates.FirstHigh.FirstHighEight
import AES8.Estimates.FirstHigh.ActualNineMoment
import AES8.Estimates.Source.OneSourceEventMoment
import AES8.Estimates.FirstHigh.FirstHighTwelve
import AES8.Estimates.FirstHigh.FirstHighDegreeFour
import AES8.Estimates.Return.ReturnDegreeFour
import AES8.Estimates.Return.ComposedReturn
import AES8.Estimates.FirstHigh.FirstHighSeveralSource

/-!
# Remaining concrete estimates after legacy reuse

The low-input transfer family, the actual startup, the degree-four first-high
coordinate, first-high coordinates zero, one, four, eight, nine, eleven and twelve, and twenty-one high-return cells
are supplied by proved declarations.
This interface records only the other physical estimates. Its final mixing
statement remains conditional until an actual witness of `RemainingCaps` is
constructed. No empirical check or stated paper claim supplies such a witness.
Constructive proof development only; no attacks or manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

noncomputable section
namespace AES8.RemainingEstimates
open AESMixing AESMixing.AES
open AES8.TransferAssembly

/-- Exact union of ordinary composition cells and the actual overlap return. -/
def ReturnCovered (i k : Fin 14) : Prop :=
  ComposedReturn.Covered i k ∨ (i = 11 ∧ k = 11)

instance (i k : Fin 14) : Decidable (ReturnCovered i k) := by
  unfold ReturnCovered
  infer_instance

theorem return_covered_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ik : Fin 14 × Fin 14 => ReturnCovered ik.1 ik.2)).card = 21 := by decide

/-- The estimates not yet discharged for the concrete AES operators. -/
structure RemainingCaps : Prop where
  high : ∀ (f : WordState → ℝ) (i k : Fin 14), ¬ ReturnCovered i k →
    SupportProfile.profile (highReturn (SupportProfile.component f k)) i ≤
      physicalCoeff 2 i k (returnCoeff i k) * SupportProfile.profile f k
  firstHigh : ∀ (a : AES.State), a ≠ 0 → ∀ (i : Fin 14), i ≠ 13 → i ≠ 12 →
    i ≠ 11 → i ≠ 9 → i ≠ 8 → i ≠ 4 → i ≠ 0 → i ≠ 1 →
    SupportProfile.profile
        (centeredStep (SupportEvolution.highPart (AESPaper.GroupedLaw.error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * g i)

theorem physicalCaps (h : RemainingCaps) : PhysicalCaps where
  low := LowTransfer.low_profile_cap
  high := by
    intro f i k
    by_cases hc : ReturnCovered i k
    · rcases hc with hc | ⟨rfl, rfl⟩
      · exact ComposedReturn.high_profile_cap f i k hc
      · exact ReturnEleven.highReturn_profile_le f
    · exact h.high f i k hc
  firstHigh := by
    intro a ha i
    by_cases hi : i = 13
    · subst i
      exact FirstHighDegreeFour.firstHigh_thirteen a ha
    · by_cases h12 : i = 12
      · subst i
        exact FirstHighTwelve.firstHigh_twelve a ha
      · by_cases h11 : i = 11
        · subst i
          exact OneSourceEventMoment.firstHigh_eleven a ha
        · by_cases h9 : i = 9
          · subst i
            exact ActualNineMoment.firstHigh_nine a ha
          · by_cases h8 : i = 8
            · subst i
              exact FirstHighEight.firstHigh_eight a ha
            · by_cases h4 : i = 4
              · subst i
                exact FirstHighFour.firstHigh_four a ha
              · by_cases h0 : i = 0
                · subst i
                  exact FirstHighZero.firstHigh_zero a ha
                · by_cases h1 : i = 1
                  · subst i
                    exact FirstHighOne.firstHigh_one a ha
                  · exact h.firstHigh a ha i hi h12 h11 h9 h8 h4 h0 h1


theorem estimates (h : RemainingCaps) : NormalizedProfile.Estimates :=
  Startup.estimates_of_transfer (transferEstimates (physicalCaps h))

/-- Conditional endpoint with only the remaining physical-cap premises. -/
theorem epsilon_eight_plus_two (h : RemainingCaps) (k : ℕ) :
    AES.epsilon (8 + 2 * k) < (1 : ℝ) / 2 ^ (92 + 41 * k) :=
  NormalizedProfile.epsilon_eight_plus_two (estimates h) k

end AES8.RemainingEstimates
