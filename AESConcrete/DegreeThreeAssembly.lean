import AESConcrete.TripleOutputCoordinates
import AESMixing.SupportDegreeDecomposition

/-!
# Four orthogonal physical output triples

The degree-three projection is the sum over the four choices of the one
unmarked physical byte. Orthogonality holds for arbitrary input vectors;
the Gram identity does not assume permutation symmetry of AES coordinates.
Constructive scope only. This module supplies identities, not norm bounds.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.DegreeThreeAssembly
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (singletonMask)

def tripleMask (r : Fin 4) : Fin 16 := maskComplement (singletonMask r)

theorem tripleMask_size : ∀ r : Fin 4, maskSize (tripleMask r) = 3 := by decide
theorem tripleMask_unmarked : ∀ r : Fin 4, maskBit (tripleMask r) r ≠ true := by decide
theorem tripleMask_injective : Function.Injective tripleMask := by decide

def tripleEquiv : Fin 4 ≃ {m : Fin 16 // maskSize m = 3} :=
  Equiv.ofBijective (fun r => ⟨tripleMask r, tripleMask_size r⟩) (by decide)

theorem sum_triples (F : Fin 16 → ℝ) :
    (∑ m : Fin 16, if maskSize m = 3 then F m else 0) =
      ∑ r : Fin 4, F (tripleMask r) := by
  have hs : (∑ m : {m : Fin 16 // maskSize m = 3}, F m.val) =
      ∑ m : Fin 16, if maskSize m = 3 then F m else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs]
  exact (tripleEquiv.sum_comp (fun m => F m.val)).symm

section Generic
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_three_decomposition (z : V) (f : (Fin 4 → V) → ℝ) (y : Fin 4 → V) :
    degreeComponent z 3 f y =
      ∑ r : Fin 4, action (productProjection z (maskBit (tripleMask r))) f y := by
  unfold degreeComponent groupedFamily
  rw [← maskBitsEquiv.sum_comp]
  have he (m : Fin 16) : degreeIndex (maskBit m) = 3 ↔ maskSize m = 3 := by
    rw [Fin.ext_iff, mask_degree_size]
    rfl
  change (∑ m : Fin 16, if degreeIndex (maskBit m) = 3 then
    action (productProjection z (maskBit m)) f y else 0) = _
  simp_rw [he]
  exact sum_triples _

theorem triples_orthogonal (z : V) (hV : 1 < Fintype.card V)
    (r s : Fin 4) (hrs : r ≠ s) (f g : (Fin 4 → V) → ℝ) :
    (∑ y, action (productProjection z (maskBit (tripleMask r))) f y *
      action (productProjection z (maskBit (tripleMask s))) g y) = 0 := by
  apply productProjection_orthogonal z hV _ _ _ f g
  intro h
  exact hrs (tripleMask_injective (maskBitsEquiv.injective h))

theorem degree_three_inner (z : V) (hV : 1 < Fintype.card V)
    (f g : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z 3 f y * degreeComponent z 3 g y) =
      ∑ r : Fin 4, ∑ y,
        action (productProjection z (maskBit (tripleMask r))) f y *
        action (productProjection z (maskBit (tripleMask r))) g y := by
  simp_rw [degree_three_decomposition, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm, Finset.sum_eq_single r]
  · intro s _ hsr
    exact triples_orthogonal z hV r s hsr.symm f g
  · simp

theorem degree_three_energy (z : V) (hV : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z 3 f y ^ 2) =
      ∑ r : Fin 4, ∑ y, action (productProjection z (maskBit (tripleMask r))) f y ^ 2 := by
  simpa only [pow_two] using degree_three_inner z hV f f

end Generic
end AESConcrete.DegreeThreeAssembly
