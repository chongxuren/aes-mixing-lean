import AES8.Model.Byte.PaperAESBase

noncomputable section
namespace AES8.PaperAESAlgebraic
open Polynomial AESMixing
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 8192

theorem generator_pow_basis (i : Fin 8) : generator ^ i.val = AES.byteBasis i := by
  fin_cases i <;> decide


def modulus : (ZMod 2)[X] := X^8+X^4+X^3+X+1

theorem modulus_monic : modulus.Monic := by unfold modulus; monicity <;> norm_num

theorem modulus_degree : modulus.natDegree = 8 := by unfold modulus; compute_degree!

theorem modulus_root : aeval generator modulus = 0 := by
  simp only [modulus, map_add, map_pow, aeval_X, map_one]
  decide

end AES8.PaperAESAlgebraic
