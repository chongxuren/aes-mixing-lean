import AESMixing.ProductDifference
import AESMixing.WordMDS

/-! Actual AES layer permutations and their difference kernels, in physical
row/column byte coordinates. No norm or mixing conclusion is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing.AES

def subBytesPerm : Equiv.Perm State :=
  coordinatePerm (fun _ : Fin 4 => coordinatePerm (fun _ : Fin 4 => BinaryWord.sboxPerm))

theorem subBytesPerm_apply (x : State) : subBytesPerm x = subBytes x := rfl

def shiftRowsEquiv : State ≃+ State :=
  AddEquiv.ofBijective shiftRowsHom
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨shiftRows_injective,rfl⟩)

def mixColumnsEquiv : State ≃+ State :=
  AddEquiv.ofBijective mixColumnsHom
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨mixColumns_injective,rfl⟩)

def ordinaryLinearEquiv : State ≃+ State := shiftRowsEquiv.trans mixColumnsEquiv
def ordinaryLayer : Equiv.Perm State := subBytesPerm.trans ordinaryLinearEquiv.toEquiv
def finalLayer : Equiv.Perm State := subBytesPerm.trans shiftRowsEquiv.toEquiv

theorem ordinaryLayer_round (x key : State) : ordinaryLayer x + key = round x key := rfl
theorem finalLayer_round (x key : State) : finalLayer x + key = finalRound x key := rfl

theorem subBytes_difference_channel (b a : State) :
    differenceChannel subBytesPerm b a =
      ∏ row, ∏ col, aesByteChannel (b row col) (a row col) := by
  unfold subBytesPerm
  rw [differenceChannel_coordinates]
  simp_rw [differenceChannel_coordinates]
  rfl

theorem ordinaryLayer_difference_channel (b a : State) :
    differenceChannel ordinaryLayer b a =
      ∏ row, ∏ col, aesByteChannel (ordinaryLinearEquiv.symm b row col) (a row col) := by
  rw [ordinaryLayer, differenceChannel_linearOutput, subBytes_difference_channel]

theorem finalLayer_difference_channel (b a : State) :
    differenceChannel finalLayer b a =
      ∏ row, ∏ col, aesByteChannel (shiftRowsEquiv.symm b row col) (a row col) := by
  rw [finalLayer, differenceChannel_linearOutput, subBytes_difference_channel]

end AESMixing.AES
