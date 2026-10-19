import AESMixing.PhysicalMarkov
import AESMixing.LawRelabel

/-! Actions of the three concrete AES layers on difference laws. -/
noncomputable section
namespace AESMixing.AES

def substituteLaw : (State → ℝ) → (State → ℝ) := action (differenceChannel subBytesPerm)
def shiftLaw : (State → ℝ) → (State → ℝ) := lawRelabel shiftRowsEquiv.toEquiv
def mixLaw : (State → ℝ) → (State → ℝ) := lawRelabel mixColumnsEquiv.toEquiv
def superboxLaw : (State → ℝ) → (State → ℝ) := substituteLaw ∘ mixLaw ∘ substituteLaw
def interSuperboxLaw : (State → ℝ) → (State → ℝ) := shiftLaw ∘ mixLaw ∘ shiftLaw

theorem substitute_shift_commutes (f : State → ℝ) :
    substituteLaw (shiftLaw f) = shiftLaw (substituteLaw f) := by
  apply difference_action_commuting subBytesPerm shiftRowsEquiv
  intro x
  rfl

theorem ordinary_difference_action (f : State → ℝ) :
    action (differenceChannel ordinaryLayer) f = mixLaw (shiftLaw (substituteLaw f)) := by
  rw [ordinaryLayer, difference_action_linearOutput]
  exact (lawRelabel_trans mixColumnsEquiv.toEquiv shiftRowsEquiv.toEquiv
    (action (differenceChannel subBytesPerm) f)).symm

theorem final_difference_action (f : State → ℝ) :
    action (differenceChannel finalLayer) f = shiftLaw (substituteLaw f) :=
  difference_action_linearOutput subBytesPerm shiftRowsEquiv f

end AESMixing.AES
