import AES8.Reductions.Return.PaperAESActivityInputSharpAssembly
import AES8.Reductions.Return.PaperAESActivityInputDegree

/-! Orthogonal residual-position aggregation of the sharp physical frame bounds.
The counts 6,4,1 are structural Boolean counts; response analysis is separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputSharpDegree
open AESMixing WordActivityFrame PaperActivityInputAssembly
open PaperActivityInputCoordinates PaperAESActivityIdentification
open PaperAESActivityInputResponse PaperActivityInputSharpArithmetic
open PaperAESActivityInputSharpAssembly
open PaperAESActivityInputDegree (aggregate_fixed_energy)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem count_two :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (2 : Fin 5) then 1 else 0 : ℕ) = 6 := by decide
private theorem count_three :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (3 : Fin 5) then 1 else 0 : ℕ) = 4 := by decide
private theorem count_four :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (4 : Fin 5) then 1 else 0 : ℕ) = 1 := by decide

theorem degree_two_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 2
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (72*C^6*tau^2/wordQ^3)*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 2 (C^6*(12*(tau^2/wordQ^3))) adjoint c
    (fun O hO => degree_two_fixed_energy O hO adjoint c)
  rw [count_two] at h
  apply h.trans_eq
  ring

theorem degree_three_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 3
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (64*C^5*tau^2*beta/wordQ^2)*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 3 (C^5*(16*(tau^2*beta/wordQ^2))) adjoint c
    (fun O hO => degree_three_fixed_energy O hO adjoint c)
  rw [count_three] at h
  apply h.trans_eq
  ring

theorem degree_four_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 4
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (C^4*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2))*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 4
    (C^4*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)) adjoint c
    (fun O hO => degree_four_fixed_energy O hO adjoint c)
  simpa only [count_four,Nat.cast_one,one_mul] using h

end AES8.PaperAESActivityInputSharpDegree
