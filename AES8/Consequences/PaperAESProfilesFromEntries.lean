import AES8.Consequences.PaperAESFromEntries

/-! Literal current parity and tail statements on actual AES profiles.
Both finite entry obligations are explicit and shared with the main theorem. -/
noncomputable section
namespace AES8.PaperAESProfilesFromEntries
open AESMixing PaperSharpEntriesFinite
set_option autoImplicit false

theorem parity_profiles (ordinary : OrdinaryRawBound)
    (fourier : FourierRawBound fourierMap) (a : AES.State) (ha : a ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    NormalizedProfile.actual a (2*k) ≤ scale 1000 PaperOutputEnvelopes.evenEnvelope ∧
    NormalizedProfile.actual a (2*k+1) ≤ scale 1000 PaperOutputEnvelopes.oddEnvelope := by
  have h := PaperCurrentRecurrence.actual_parity
    (PaperAESFromEntries.physicalEstimates ordinary fourier) a ha (k-1)
  have he : 2*(k-1)+2=2*k := by omega
  have ho : 2*(k-1)+3=2*k+1 := by omega
  simpa only [he, ho] using h

theorem tail (ordinary : OrdinaryRawBound) (fourier : FourierRawBound fourierMap)
    (a : AES.State) (ha : a ≠ 0) (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) < 112 :=
  PaperCurrentBound.output_lt
    (PaperCurrentRecurrence.actual_boxes
      (PaperAESFromEntries.physicalEstimates ordinary fourier)) a ha j hj

end AES8.PaperAESProfilesFromEntries
