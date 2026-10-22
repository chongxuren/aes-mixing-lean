import AESConcrete.InvariantSubspaceEnergy

/-!
# Fourier graph energy from a projected translation family

The dependent physical labels form an arbitrary tuple. Surjectivity of the
translation family's projection onto that entire tuple makes supported Fourier
frequencies unique over the complementary free tuple. This separates support
geometry from the existing heterogeneous coordinate energy theorem. Injective
source embeddings transfer the result to raw signed responses by zero
extension.

no actual AES geometry, cap or inventory change is asserted. Independent
uniform retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.InvariantSubspaceFourier
open AESMixing
open AESConcrete.IndexedGraphEnergy
open AESConcrete.InvariantSubspaceEnergy

variable {I V P : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

omit [Fintype I] [DecidableEq I] [AddCommGroup V] [Fintype V] in
/-- A surjective physical coordinate is also surjective onto the entire
singleton dependent tuple, with no coordinate enumeration. -/
theorem dependent_projection_surjective_of_coordinate
    (s : I) (translations : P → I → V)
    (hsurj : Function.Surjective (fun t => translations t s)) :
    Function.Surjective
      (fun t => fun j : DependentCoordinates (fun i : I => i ≠ s) =>
        translations t j.val) := by
  classical
  intro v
  obtain ⟨t, ht⟩ := hsurj (v ⟨s, by simp⟩)
  refine ⟨t, ?_⟩
  funext j
  have hj : j.val = s := Classical.not_not.mp j.property
  calc
    translations t j.val = translations t s := congrArg (translations t) hj
    _ = v ⟨s, by simp⟩ := ht
    _ = v j := congrArg v (Subtype.ext hj.symm)

omit [Fintype V] in
/-- A character with zero free frequencies is exactly the character on the
dependent tuple. The original physical labels are preserved. -/
theorem product_pairing_eq_dependent
    (B : CharacterPairing V) (free : I → Prop) [DecidablePred free]
    (z x : I → V) (hzero : ∀ i : FreeCoordinates free, z i.val = 0) :
    (B.product I).value z x =
      (B.product (DependentCoordinates free)).value
        (fun j => z j.val) (fun j => x j.val) := by
  classical
  change (∏ i : I, B.value (z i) (x i)) =
    ∏ j : DependentCoordinates free, B.value (z j.val) (x j.val)
  rw [← Fintype.prod_subtype_mul_prod_subtype free]
  have hf : (∏ i : FreeCoordinates free, B.value (z i.val) (x i.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [hzero i, B.zero_left]
  rw [hf, one_mul]

/-- Surjectivity onto the entire dependent translation tuple separates two
supported frequencies agreeing on the free labels. No additivity or finiteness
of the translation parameter type is needed. -/
theorem invariant_fourier_dependent_eq
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (free : I → Prop) [DecidablePred free]
    (translations : P → I → V)
    (hsurj : Function.Surjective
      (fun t => fun j : DependentCoordinates free => translations t j.val))
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x)
    (z z' : I → V)
    (hz : action (coordinateKernel (fun _ : I => pairingFourier B)) f z ≠ 0)
    (hz' : action (coordinateKernel (fun _ : I => pairingFourier B)) f z' ≠ 0)
    (heq : ∀ i : FreeCoordinates free, z i.val = z' i.val) :
    (fun j : DependentCoordinates free => z j.val) =
      (fun j : DependentCoordinates free => z' j.val) := by
  classical
  have hzF : action (pairingFourier (B.product I)) f z ≠ 0 := by
    simpa only [productPairing_fourier] using hz
  have hzF' : action (pairingFourier (B.product I)) f z' ≠ 0 := by
    simpa only [productPairing_fourier] using hz'
  have hfreezero : ∀ i : FreeCoordinates free, (z + z') i.val = 0 := by
    intro i
    simp only [Pi.add_apply, heq i, hchar]
  have hpair (a : DependentCoordinates free → V) :
      (B.product (DependentCoordinates free)).value
        (fun j => z j.val + z' j.val) a = 1 := by
    obtain ⟨t, ht⟩ := hsurj a
    change (fun j : DependentCoordinates free => translations t j.val) = a at ht
    have hz1 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product I) f (translations t) (fun x => hinv x t) z hzF
    have hz2 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product I) f (translations t) (fun x => hinv x t) z' hzF'
    have hh : (B.product I).value (z + z') (translations t) = 1 := by
      rw [CharacterPairing.add_left, hz1, hz2, one_mul]
    rw [product_pairing_eq_dependent B free (z + z') (translations t) hfreezero,
      ht] at hh
    exact hh
  have hzero : (fun j : DependentCoordinates free => z j.val + z' j.val) = 0 := by
    by_contra hn
    obtain ⟨a, ha⟩ := (B.product (DependentCoordinates free)).nondegenerate _ hn
    exact ha (hpair a)
  funext j
  have hj : z j.val + z' j.val = 0 := congrFun hzero j
  calc
    z j.val = z j.val + (z' j.val + z' j.val) := by rw [hchar, add_zero]
    _ = z' j.val := by rw [← add_assoc, hj, zero_add]

/-- Translation invariance supplies precisely the partial-graph premise of
`IndexedGraphEnergy.coordinate_fourier_partial_graph_energy`. Empty fibers and
empty free/dependent label sets are allowed. -/
theorem invariant_fourier_fiber_unique
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (free : I → Prop) [DecidablePred free]
    (translations : P → I → V)
    (hsurj : Function.Surjective
      (fun t => fun j : DependentCoordinates free => translations t j.val))
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x) :
    ∀ (w : FreeCoordinates free → V) (v v' : DependentCoordinates free → V),
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates free).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates free).symm (v', w)) ≠ 0 → v = v' := by
  classical
  intro w v v' hv hv'
  have he := invariant_fourier_dependent_eq B hchar free translations hsurj f hinv
    ((splitCoordinates free).symm (v, w))
    ((splitCoordinates free).symm (v', w)) hv hv'
    (by
      intro i
      simp [splitCoordinates, joinCoordinates, i.property])
  funext j
  have hj := congrFun he j
  simpa [splitCoordinates, joinCoordinates, j.property] using hj

/-- One operator resource per free label and one column resource per dependent
label, obtained from a jointly surjective projected translation family. -/
theorem coordinate_fourier_partial_graph_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (free : I → Prop) [DecidablePred free]
    (nu : FreeCoordinates free → ℝ) (delta : DependentCoordinates free → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates free) (g : V → ℝ),
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates free) (v : V),
      (∑ y, fourierConjugate B T y v ^ 2) ≤ delta j)
    (translations : P → I → V)
    (hsurj : Function.Surjective
      (fun t => fun j : DependentCoordinates free => translations t j.val))
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) * ∑ x, f x ^ 2 := by
  apply IndexedGraphEnergy.coordinate_fourier_partial_graph_energy
    B hchar T free nu delta hdelta hT hcolumn f
  exact invariant_fourier_fiber_unique B hchar free translations hsurj f hinv

section Source
variable {S : Type*} [Fintype S] [AddCommGroup S]

/-- Raw source response on an injective additive retained image. Source
invariance is extended by zero before the ambient product Fourier transform. -/
theorem response_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (free : I → Prop) [DecidablePred free]
    (nu : FreeCoordinates free → ℝ) (delta : DependentCoordinates free → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates free) (g : V → ℝ),
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates free) (v : V),
      (∑ y, fourierConjugate B T y v ^ 2) ≤ delta j)
    (E : S →+ (I → V)) (hE : Function.Injective E)
    (translations : P → S)
    (hsurj : Function.Surjective
      (fun t => fun j : DependentCoordinates free => E (translations t) j.val))
    (mu : S → ℝ) (hinv : ∀ s t, mu (s + translations t) = mu s) :
    (∑ y : I → V, IndexedTripleEnergy.response T E mu y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) * ∑ s, mu s ^ 2 := by
  have he := coordinate_fourier_partial_graph_energy B hchar T free
    nu delta hdelta hT hcolumn (fun t => E (translations t)) hsurj
    (zeroExtend E mu) (zeroExtend_translation E translations mu hinv)
  rw [zeroExtend_energy E hE mu] at he
  simp_rw [response_eq_action T E mu]
  exact he

/-- Uniform resource form with explicit free and dependent cardinalities. -/
theorem response_uniform_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (free : I → Prop) [DecidablePred free]
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (E : S →+ (I → V)) (hE : Function.Injective E)
    (translations : P → S)
    (hsurj : Function.Surjective
      (fun t => fun j : DependentCoordinates free => E (translations t) j.val))
    (mu : S → ℝ) (hinv : ∀ s t, mu (s + translations t) = mu s) :
    (∑ y : I → V, IndexedTripleEnergy.response T E mu y ^ 2) ≤
      (rho ^ Fintype.card (FreeCoordinates free)) ^ 2 *
        kappa ^ Fintype.card (DependentCoordinates free) * ∑ s, mu s ^ 2 := by
  have he := response_energy B hchar T free (fun _ => rho) (fun _ => kappa)
    (fun _ => hkappa) (fun _ => hT) (fun _ => hcolumn)
    E hE translations hsurj mu hinv
  simpa only [Finset.prod_const, Finset.card_univ] using he

end Source
end AESConcrete.InvariantSubspaceFourier
