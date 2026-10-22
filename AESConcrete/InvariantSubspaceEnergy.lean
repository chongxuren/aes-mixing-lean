import AESConcrete.IndexedTripleEnergy

/-!
# Exact zero extension of signed subgroup amplitudes

The source is a finite additive group embedded in the full retained-coordinate
space. A finite fiber sum defines zero extension without choosing an inverse
outside its image. Injectivity gives exact counting energy, while reindexing
by an internal translation proves invariance at every ambient point. Raw
retained responses use the existing `IndexedTripleEnergy.response` interface.

No AES geometry, physical cap or inventory increment is asserted. Independent
uniform retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and fixed 10/14/16 remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.InvariantSubspaceEnergy
open AESMixing

section Extension
variable {S X : Type*} [Fintype S]

/-- The finite fiber sum is zero off the image; for an injective map it is
exactly the source amplitude at the unique source preimage. -/
def zeroExtend (E : S → X) (mu : S → ℝ) (x : X) : ℝ := by
  classical
  exact ∑ s, if E s = x then mu s else 0

theorem zeroExtend_apply (E : S → X) (hE : Function.Injective E)
    (mu : S → ℝ) (s : S) : zeroExtend E mu (E s) = mu s := by
  classical
  unfold zeroExtend
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs'
    exact if_neg (fun h => hs' (hE h))
  · simp

theorem zeroExtend_eq_zero (E : S → X) (mu : S → ℝ) (x : X)
    (hx : ¬ ∃ s, E s = x) : zeroExtend E mu x = 0 := by
  classical
  unfold zeroExtend
  apply Finset.sum_eq_zero
  intro s _
  exact if_neg (fun hs => hx ⟨s, hs⟩)

variable [Fintype X]

/-- Exact transfer of a counting sum against the zero-extended amplitude.
No injectivity is required for this finite pushforward identity. -/
theorem sum_mul_zeroExtend (E : S → X) (mu : S → ℝ) (a : X → ℝ) :
    (∑ x, a x * zeroExtend E mu x) = ∑ s, a (E s) * mu s := by
  classical
  simp only [zeroExtend, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (E s)]
  · simp
  · intro x _ hx
    simp only [if_neg (Ne.symm hx), mul_zero]
  · simp

/-- Injective zero extension preserves the exact signed source energy. -/
theorem zeroExtend_energy (E : S → X) (hE : Function.Injective E)
    (mu : S → ℝ) :
    (∑ x, zeroExtend E mu x ^ 2) = ∑ s, mu s ^ 2 := by
  calc
    (∑ x, zeroExtend E mu x ^ 2) =
        ∑ x, zeroExtend E mu x * zeroExtend E mu x := by
      simp only [pow_two]
    _ = ∑ s, zeroExtend E mu (E s) * mu s :=
      sum_mul_zeroExtend E mu (zeroExtend E mu)
    _ = ∑ s, mu s ^ 2 := by
      simp only [zeroExtend_apply E hE, pow_two]

end Extension

section Translation
variable {S X P : Type*} [Fintype S] [AddCommGroup S] [AddCommGroup X]

/-- Internal translation invariance extends to every ambient point, including
points outside the additive source image. The parameter type is arbitrary. -/
theorem zeroExtend_translation (E : S →+ X) (translations : P → S)
    (mu : S → ℝ) (hinv : ∀ s t, mu (s + translations t) = mu s)
    (x : X) (t : P) :
    zeroExtend E mu (x + E (translations t)) = zeroExtend E mu x := by
  classical
  unfold zeroExtend
  rw [← Equiv.sum_comp (Equiv.addRight (translations t))
    (fun s => if E s = x + E (translations t) then mu s else 0)]
  apply Finset.sum_congr rfl
  intro s _
  change (if E (s + translations t) = x + E (translations t)
    then mu (s + translations t) else 0) =
      if E s = x then mu s else 0
  simp only [map_add, add_right_cancel_iff, hinv]

end Translation

section Response
variable {I V S : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Fintype S]

/-- The raw source response is the ambient coordinate-kernel action on its
zero extension. No normalization or amplitude factorization is introduced. -/
theorem response_eq_action (T : V → V → ℝ) (E : S → I → V)
    (mu : S → ℝ) (y : I → V) :
    IndexedTripleEnergy.response T E mu y =
      action (coordinateKernel (fun _ : I => T)) (zeroExtend E mu) y := by
  rw [action, sum_mul_zeroExtend]
  unfold IndexedTripleEnergy.response coordinateKernel
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

end Response
end AESConcrete.InvariantSubspaceEnergy
