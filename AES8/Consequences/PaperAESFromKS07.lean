import AES8.Estimates.Source.PaperAESCurrentStartup
import AES8.Estimates.Transfer.PaperAESCurrentTransfer
import AES8.Estimates.Word.PaperKS07AssumedEntries
import AES8.Recurrence.PaperCurrentRecurrence

/-! The current AES family from the paper's cited KS07 inputs.
The external maxima are explicit hypotheses. Startup, transfer, first-return,
recurrence and output deductions remain proved obligations. This endpoint does
not require the alternative mixed-moment certificate predicates. -/
noncomputable section
namespace AES8.PaperAESFromKS07
open AESMixing PaperKS07AssumedEntries
set_option autoImplicit false
set_option maxRecDepth 100000

theorem mixed_entry (h : KS07Bounds) (bit : Bool) (y x : AES.Word) :
    |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry := by
  cases bit
  · change |residualMatrix AES.wordSuperboxKernel 0 y x| ≤ _
    apply (ordinary_residual_entry_lt_fourteen h x y).le.trans
    norm_num [PaperAESOverlapResources.entry, PaperAESOverlapResources.q]
  · change |AESConcrete.WordFourierCore.wordConjugate
      (residualMatrix AES.wordSuperboxKernel 0) y x| ≤ _
    apply (actual_fourier_residual_entry_lt h x y).le.trans
    norm_num [PaperAESOverlapResources.entry, PaperAESOverlapResources.q]

theorem physicalEstimates (h : KS07Bounds) : PaperCurrentRecurrence.PhysicalEstimates where
  transfer := PaperAESCurrentTransfer.physicalCaps (mixed_entry h)
  initial := PaperAESCurrentStartup.initial (ordinary_bound h)

theorem epsilon_eight_plus_two (h : KS07Bounds) (k : ℕ) :
    AES.epsilon (8 + 2*k) < 7 / (2 : ℝ)^(95 + 41*k) :=
  PaperCurrentRecurrence.epsilon_eight_plus_two (physicalEstimates h) k

theorem round_corollaries (h : KS07Bounds) :
    AES.epsilon 10 < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  PaperCurrentRecurrence.round_corollaries (physicalEstimates h)

theorem parity_profiles (h : KS07Bounds) (a : AES.State) (ha : a ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    NormalizedProfile.actual a (2*k) ≤ scale 1000 PaperOutputEnvelopes.evenEnvelope ∧
    NormalizedProfile.actual a (2*k+1) ≤ scale 1000 PaperOutputEnvelopes.oddEnvelope := by
  have hp := PaperCurrentRecurrence.actual_parity (physicalEstimates h) a ha (k-1)
  have he : 2*(k-1)+2=2*k := by omega
  have ho : 2*(k-1)+3=2*k+1 := by omega
  simpa only [he, ho] using hp

theorem tail (h : KS07Bounds) (a : AES.State) (ha : a ≠ 0) (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) < 112 :=
  PaperCurrentBound.output_lt (PaperCurrentRecurrence.actual_boxes (physicalEstimates h)) a ha j hj

#print axioms epsilon_eight_plus_two
#print axioms round_corollaries
#print axioms parity_profiles
#print axioms tail

end AES8.PaperAESFromKS07
