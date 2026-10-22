import AES8.Math.PaperActivityFrameJoin
import AES8.Reductions.Return.PhysicalZeroPattern

/-! The actual degree-three middle frame is a literal retained-coordinate join.
No inverse metric or norm estimate is introduced. Constructive identities only. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnIdentification
open AESMixing AESMixing.AES
open PaperActivityMinorTransport PaperActivityFrameJoin
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

def middle (c : Fin 4) : Finset (Fin 4) := Finset.univ.erase c
def middleUniform (c : Fin 4) (s : Bool) : Finset (Fin 4) := if s then {c} else ∅

theorem middle_card (c : Fin 4) : (middle c).card = 3 := by simp [middle]

theorem middle_frame_bit (c : Fin 4) (s : Bool) (k : Fin 4) :
    decide (k ∈ middleUniform c s) = (if k = c then s else false) := by
  cases s <;> by_cases h : k = c <;> simp [middleUniform, h]

/-- The coordinate join is precisely the physical degree-three frame atom. -/
theorem middle_join (c : Fin 4) (s t : Bool) :
    kernelCompose (synthesis (V := AES.Word) (middle c)
      (fun k => decide (k ∈ middleUniform c s)))
      (analysis (middle c) (fun k => decide (k ∈ middleUniform c t))) =
      MiddleFrameExpansion.frameAtom 0 c s t := by
  funext y x
  rw [join_coordinates _ _ _ AESConcrete.AES.word_card_gt_one,
    PhysicalMiddleKernel.frameAtom_coordinates]
  simp only [coordinateKernel, ite_apply]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k = c <;>
    simp [middle, middle_frame_bit, hk, PhysicalMiddleKernel.framePair]

end AES8.PaperAESReturnIdentification
