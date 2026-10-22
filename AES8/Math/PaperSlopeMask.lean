import AES8.Math.PaperSlopeCoincidenceMatrix
import AESConcrete.ActivityEffectiveMetric

/-! Literal correspondence between subset labels and the physical sixteen
activity masks, independent of the diffusion map. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeMask
open PaperSlopeCoincidenceMatrix
open AESMixing AESMixing.AES
set_option autoImplicit false
set_option maxRecDepth 100000

def subsetDistance (A B : Finset (Fin 4)) : ℕ := ((A \ B) ∪ (B \ A)).card

theorem mask_bound (A : Finset (Fin 4)) : (∑ i ∈ A, 2^i.val) < 16 := by
  revert A
  decide

def mask (A : Finset (Fin 4)) : Fin 16 := ⟨∑ i ∈ A, 2^i.val, mask_bound A⟩

theorem mask_bit (A : Finset (Fin 4)) (i : Fin 4) :
    maskBit (mask A) i = decide (i ∈ A) := by
  revert A i
  decide

theorem mask_size (A : Finset (Fin 4)) : maskSize (mask A) = A.card := by
  revert A
  decide

theorem mask_inter_size (A B : Finset (Fin 4)) :
    maskSize (maskIntersection (mask A) (mask B)) = (A ∩ B).card := by
  revert A B
  decide

theorem distance_formula (A B : Finset (Fin 4)) :
    subsetDistance A B = A.card+B.card-2*(A ∩ B).card := by
  revert A B
  decide

theorem mask_interior (A : Interior) : mask A.val ≠ 0 ∧ mask A.val ≠ 15 := by
  revert A
  decide

theorem mask_bijective : Function.Bijective mask := by decide

def maskEquiv : Finset (Fin 4) ≃ Fin 16 := Equiv.ofBijective mask mask_bijective

theorem restricted_bijective : Function.Bijective
    (fun A : Interior => (⟨mask A.val, mask_interior A⟩ : AESConcrete.ActivityEffectiveMetric.Interior)) := by
  decide

def interiorEquiv : Interior ≃ AESConcrete.ActivityEffectiveMetric.Interior :=
  Equiv.ofBijective _ restricted_bijective

end AES8.PaperSlopeMask
