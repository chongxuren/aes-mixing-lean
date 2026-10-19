import Mathlib.Logic.Function.Iterate

/-!
The algebra behind two-round grouping. It is an identity of functions,
using only commutation of the substitution layer and the row permutation.
-/
namespace AESMixing

theorem two_layer_grouping {X : Type*} (A S M : X → X)
    (h : ∀ x, A (S x) = S (A x)) (n : ℕ) (x : X) :
    ((M ∘ S ∘ A)^[2*n+2]) x =
      M (S ((A ∘ M ∘ A) ((((S ∘ M ∘ S) ∘ (A ∘ M ∘ A))^[n]) (S x)))) := by
  have htwo (y : X) : S (((M ∘ S ∘ A)^[2]) y) =
      ((S ∘ M ∘ S) ∘ (A ∘ M ∘ A)) (S y) := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, Function.comp_apply]
    rw [h]
  induction n generalizing x with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_succ_apply,
      Function.iterate_zero_apply, Function.comp_apply]
    rw [h]
  | succ n ih =>
    have hn : 2*(n+1)+2 = (2*n+2)+2 := by omega
    rw [hn, Function.iterate_add_apply, ih, htwo, Function.iterate_succ_apply]

end AESMixing
