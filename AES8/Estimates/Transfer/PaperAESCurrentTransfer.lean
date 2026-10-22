import AES8.Estimates.Transfer.PaperAESActivityTransfer
import AES8.Estimates.Transfer.PaperAESPureActivityTransfer
import AES8.Estimates.FirstHigh.PaperAESFirstReturn
import AES8.Recurrence.PaperProfileAssembly

/-! The current paper's physical transfer interface on literal AES operators.
All low-degree one-step columns are unconditional. Return and first-return
columns require only the common mixed-entry resource. Startup is separate. -/
noncomputable section
namespace AES8.PaperAESCurrentTransfer
open AESMixing AESMixing.AES PaperComparison TransferAssembly
set_option autoImplicit false

theorem low_cap (f : WordState → ℝ) (a : Fin 14) (b : Fin 11) :
    SupportProfile.profile (centeredStep (SupportProfile.component f (Fin.castAdd 3 b))) a ≤
      physicalCoeff 1 a (Fin.castAdd 3 b) (realStep a (Fin.castAdd 3 b)) *
        SupportProfile.profile f (Fin.castAdd 3 b) := by
  have hlow : SupportProfile.residualDegree (Fin.castAdd 3 b) ≤ 2 := by
    fin_cases b <;> decide
  by_cases hb : SupportProfile.residualDegree (Fin.castAdd 3 b) = 0
  · by_cases ha : SupportProfile.residualDegree a = 0
    · exact PaperAESPureActivityTransfer.low_activity_cap f a _ ha hb
    · exact PaperAESActivityTransfer.low_activity_positive_cap f a _ ha hb
  · exact PaperAESResidualTransfer.low_residual_cap f a _ hb hlow

/-- Concrete current first-step, return, and first-high bounds, retaining one
explicit finite-resource premise. This does not assume four-round startup. -/
theorem physicalCaps
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    PaperProfileAssembly.PhysicalCaps realStep realReturn (fun i => (firstReturn i : ℝ)) where
  low := low_cap
  high := fun f i k => PaperAESCurrentReturn.high_cap f i k hentry
  firstHigh := fun a ha i => PaperAESFirstReturn.firstHigh_le a ha hentry i

end AES8.PaperAESCurrentTransfer
