import AES8.Estimates.FirstHigh.PaperAESOneFirstReturn
import AESPaper.UniversalInitialization

/-! The first-high estimate for every nonzero AES input difference.
The support dichotomy uses the actual initial ShiftRows equivalence. The only
remaining premise is the common finite mixed-entry resource, not firstHigh. -/
noncomputable section
namespace AES8.PaperAESFirstReturn
open AESMixing PaperComparison TransferAssembly SupportEvolution
open PaperSupportProjection PaperAESTwoRoundSource
open AESPaper.GroupedLaw (error)
set_option autoImplicit false

theorem source_support_pos (a : AES.State) (ha : a ≠ 0) :
    0 < supportCount (sourceMask a) := by
  have hn := AESPaper.UniversalInitialization.sourceInput_ne_zero a ha
  have hex : ∃ k, AESPaper.StartingWord.sourceInput a k ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨k,hk⟩ := hex
  apply Finset.card_pos.mpr
  exact ⟨k, by simp [sourceMask,hk]⟩

/-- All input supports, in exactly the current PhysicalCaps.firstHigh units. -/
theorem firstHigh_le (a : AES.State) (ha : a ≠ 0)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (i : Fin 14) :
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * (firstReturn i : ℝ)) := by
  by_cases hw : supportCount (sourceMask a) = 1
  · exact PaperAESOneFirstReturn.firstHigh_le a hw hentry i
  · have hp := source_support_pos a ha
    exact PaperAESSeveralFirstReturn.firstHigh_le a ha (by omega) hentry i

end AES8.PaperAESFirstReturn
