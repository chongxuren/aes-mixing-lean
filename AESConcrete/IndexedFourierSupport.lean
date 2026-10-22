import AESConcrete.IndexedGraphEnergy
import AESConcrete.FourierGraphSupport

/-!
# Fourier support on arbitrary retained physical labels

Translation invariance and surjectivity of one translation coordinate force
that frequency coordinate to be unique over all the other labels. The index
type is arbitrary, so the statement applies to the actual retained pair.
All functions are signed and use counting measure. The translation geometry
is an explicit premise, separate from the energy estimate.

Constructive AES 10/14/16 continuation only; no attacks. Independent retained
keys, whitening, omitted final MixColumns and ordered-distinct pairs are fixed.
This candidate does not add a physical cap or change an accepted source.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.IndexedFourierSupport
open AESMixing
open AESConcrete.IndexedGraphEnergy

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

omit [Fintype V] in
/-- Only the distinguished physical label contributes to this character. -/
theorem product_pairing_single_left
    (B : CharacterPairing V) (s : I) (v : V) (x : I → V) :
    (B.product I).value (Pi.single s v) x = B.value v (x s) := by
  classical
  change (∏ i : I, B.value ((Pi.single s v : I → V) i) (x i)) = B.value v (x s)
  rw [Finset.prod_eq_single s]
  · simp
  · intro i _ hi
    simp [hi, B.zero_left]
  · simp

/-- A translation family with surjective coordinate `s` separates supported
frequencies agreeing at every other physical label. -/
theorem invariant_fourier_coordinate_eq
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (s : I) (translations : V → I → V)
    (hsurj : Function.Surjective (fun t => translations t s))
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x)
    (z z' : I → V)
    (hz : action (coordinateKernel (fun _ : I => pairingFourier B)) f z ≠ 0)
    (hz' : action (coordinateKernel (fun _ : I => pairingFourier B)) f z' ≠ 0)
    (heq : ∀ i, i ≠ s → z i = z' i) : z s = z' s := by
  classical
  have hzF : action (pairingFourier (B.product I)) f z ≠ 0 := by
    simpa only [productPairing_fourier] using hz
  have hzF' : action (pairingFourier (B.product I)) f z' ≠ 0 := by
    simpa only [productPairing_fourier] using hz'
  have hsingle : z + z' = Pi.single s (z s + z' s) := by
    funext i
    by_cases hi : i = s
    · subst i
      simp
    · simp only [Pi.add_apply, heq i hi, hchar, Pi.single_eq_of_ne hi]
  have hpair (a : V) : B.value (z s + z' s) a = 1 := by
    obtain ⟨t, ht⟩ := hsurj a
    have hz1 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product I) f (translations t) (fun x => hinv x t) z hzF
    have hz2 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product I) f (translations t) (fun x => hinv x t) z' hzF'
    have hh : (B.product I).value (z + z') (translations t) = 1 := by
      rw [CharacterPairing.add_left, hz1, hz2, one_mul]
    have ht' : translations t s = a := ht
    rw [hsingle, product_pairing_single_left, ht'] at hh
    exact hh
  have hzero : z s + z' s = 0 := by
    by_contra hzero
    obtain ⟨a, ha⟩ := B.nondegenerate (z s + z' s) hzero
    exact ha (hpair a)
  calc
    z s = z s + (z' s + z' s) := by rw [hchar, add_zero]
    _ = z' s := by rw [← add_assoc, hzero, zero_add]

/-- The same support statement in the exact generic graph-energy interface. -/
theorem invariant_fourier_fiber_unique
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (s : I) (translations : V → I → V)
    (hsurj : Function.Surjective (fun t => translations t s))
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x) :
    ∀ (w : FreeCoordinates (fun i : I => i ≠ s) → V)
      (v v' : DependentCoordinates (fun i : I => i ≠ s) → V),
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates (fun i : I => i ≠ s)).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates (fun i : I => i ≠ s)).symm (v', w)) ≠ 0 → v = v' := by
  classical
  intro w v v' hv hv'
  have he := invariant_fourier_coordinate_eq B hchar s translations hsurj f hinv
    ((splitCoordinates (fun i : I => i ≠ s)).symm (v, w))
    ((splitCoordinates (fun i : I => i ≠ s)).symm (v', w)) hv hv'
    (by
      intro i hi
      simp [splitCoordinates, joinCoordinates, hi])
  funext i
  have hi : i.val = s := Classical.not_not.mp i.property
  have hei : ((splitCoordinates (fun j : I => j ≠ s)).symm (v, w)) i.val =
      ((splitCoordinates (fun j : I => j ≠ s)).symm (v', w)) i.val := by
    simpa only [hi] using he
  simpa [splitCoordinates, joinCoordinates, i.property] using hei

/-- The dependent tuple has one coordinate, with its original label. -/
theorem dependentCoordinates_card (s : I) :
    Fintype.card (DependentCoordinates (fun i : I => i ≠ s)) = 1 := by
  classical
  letI : Unique (DependentCoordinates (fun i : I => i ≠ s)) :=
    { default := ⟨s, by simp⟩
      uniq := fun i => Subtype.ext (Classical.not_not.mp i.property) }
  exact Fintype.card_unique

/-- On a two-label retained set there is one free operator factor and one
dependent column factor, both for the actual two-sided conjugate kernel. -/
theorem invariant_pair_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (s : I) (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 1)
    (translations : V → I → V)
    (hsurj : Function.Surjective (fun t => translations t s))
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2) ≤
      rho ^ 2 * kappa * ∑ x, f x ^ 2 := by
  classical
  have he := coordinate_fourier_partial_graph_energy B hchar T
    (fun i : I => i ≠ s) (fun _ => rho) (fun _ => kappa)
    (fun _ => hkappa) (fun _ => hT) (fun _ => hcolumn) f
    (invariant_fourier_fiber_unique B hchar s translations hsurj f hinv)
  simpa only [Finset.prod_const, Finset.card_univ, hfree,
    dependentCoordinates_card, pow_one] using he

end AESConcrete.IndexedFourierSupport
