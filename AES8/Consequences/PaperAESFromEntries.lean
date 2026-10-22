import AES8.Estimates.Source.PaperAESCurrentStartup
import AES8.Estimates.Transfer.PaperAESCurrentTransfer
import AES8.Estimates.Word.PaperSharpEntriesResidual
import AES8.Recurrence.PaperCurrentRecurrence

/-! The complete current analytic chain from two finite byte predicates.
All actual startup, transfer, first-return and recurrence obligations are
proved upstream. The finite predicates remain explicit until certified. -/
noncomputable section
namespace AES8.PaperAESFromEntries
open AESMixing PaperSharpEntriesFinite
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Both physical orientations consume their own finite byte resource. -/
theorem mixed_entry (ordinary : OrdinaryRawBound)
    (fourier : FourierRawBound fourierMap) (bit : Bool) (y x : AES.Word) :
    |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry := by
  cases bit
  · have h := PaperSharpEntriesResidual.ordinary_residual_entry_lt_fourteen
      ordinary false x y
    have he : PaperWordMixedGram.mixed false false false =
        residualMatrix AES.wordSuperboxKernel 0 := rfl
    rw [he]
    apply h.le.trans
    norm_num [PaperAESOverlapResources.entry, PaperAESOverlapResources.q]
  · have h := PaperSharpEntriesResidual.actual_fourier_residual_entry_lt_twenty_seven
      fourier x y
    change |AESConcrete.WordFourierCore.wordConjugate
      (residualMatrix AES.wordSuperboxKernel 0) y x| ≤ _
    apply h.le.trans
    norm_num [PaperAESOverlapResources.entry, PaperAESOverlapResources.q]

/-- No physical estimate remains a premise of this analytic interface. -/
theorem physicalEstimates (ordinary : OrdinaryRawBound)
    (fourier : FourierRawBound fourierMap) : PaperCurrentRecurrence.PhysicalEstimates where
  transfer := PaperAESCurrentTransfer.physicalCaps (mixed_entry ordinary fourier)
  initial := PaperAESCurrentStartup.initial (PaperSharpEntriesProfiles.ordinary_bound ordinary)

/-- Exact current theorem, with only the finite byte certificates explicit. -/
theorem epsilon_eight_plus_two (ordinary : OrdinaryRawBound)
    (fourier : FourierRawBound fourierMap) (k : ℕ) :
    AES.epsilon (8 + 2*k) < 7 / (2 : ℝ)^(95 + 41*k) :=
  PaperCurrentRecurrence.epsilon_eight_plus_two (physicalEstimates ordinary fourier) k

theorem round_corollaries (ordinary : OrdinaryRawBound)
    (fourier : FourierRawBound fourierMap) :
    AES.epsilon 10 < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  PaperCurrentRecurrence.round_corollaries (physicalEstimates ordinary fourier)

end AES8.PaperAESFromEntries
