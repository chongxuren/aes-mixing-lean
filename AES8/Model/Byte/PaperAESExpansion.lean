import AES8.Model.Byte.PaperAESPowers
import AES8.Model.Byte.PaperAESBits

noncomputable section
namespace AES8.PaperAESAlgebraic
open Polynomial AESMixing
open scoped BigOperators
set_option autoImplicit false


theorem eval_coeff_sum (v : Fin 8 → ZMod 2) :
    aeval generator (∑ i : Fin 8, monomial i.val (v i)) = byteEval v := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [aeval_monomial, generator_pow_basis]
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc (v i) with hi | hi <;> simp [hi]


end AES8.PaperAESAlgebraic
