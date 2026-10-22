import AESConcrete.IndexedFourierSupport

/-!
# Signed graph responses on three retained physical labels

The response is reindexed through its actual free-coordinate projection. All
labels retain their identities, and the amplitude remains one arbitrary signed
function. The Fourier lemma adds two free operator factors to the existing
one-coordinate annihilator argument.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the fixed 10/14/16 target are unchanged. No
physical cap or inventory is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.IndexedTripleEnergy
open AESMixing
open AESConcrete.IndexedGraphEnergy

section Fourier
variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

/-- A surjective uniform translation coordinate determines the one dependent
frequency over the other two retained frequencies. Both resources concern the
actual two-sided Fourier conjugate. -/
theorem invariant_triple_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (s : I) (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2)
    (translations : V → I → V)
    (hsurj : Function.Surjective (fun t => translations t s))
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (f : (I → V) → ℝ)
    (hinv : ∀ x t, f (x + translations t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, f x ^ 2 := by
  classical
  have he := coordinate_fourier_partial_graph_energy B hchar T
    (fun i : I => i ≠ s) (fun _ => rho) (fun _ => kappa)
    (fun _ => hkappa) (fun _ => hT) (fun _ => hcolumn) f
    (IndexedFourierSupport.invariant_fourier_fiber_unique
      B hchar s translations hsurj f hinv)
  simpa only [Finset.prod_const, Finset.card_univ, hfree,
    IndexedFourierSupport.dependentCoordinates_card, pow_one, ← pow_mul] using he

end Fourier

section Response
variable {I V C : Type*} [Fintype I] [DecidableEq I] [Fintype C]

/-- Raw retained response with exact counting measure and no normalization. -/
def response (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (y : I → V) : ℝ :=
  ∑ c, mu c * ∏ i : I, T (y i) (curve c i)

variable [Fintype V]

/-- Reindex the source through its actual free retained tuple. The dependent
tuple is a genuine graph over that tuple, with the same amplitude. -/
theorem response_eq_graph
    (p : I → Prop) [DecidablePred p]
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (e : C ≃ (FreeCoordinates p → V))
    (he : ∀ c i, e c i = curve c i.val) (y : I → V) :
    response T curve mu y =
      action (GraphColumnEnergy.graphKernel
        (coordinateKernel (fun _ : DependentCoordinates p => T))
        (coordinateKernel (fun _ : FreeCoordinates p => T))
        (fun w j => curve (e.symm w) j.val))
        (fun w => mu (e.symm w)) (splitCoordinates p y) := by
  unfold response
  rw [← e.symm.sum_comp (fun c => mu c * ∏ i : I, T (y i) (curve c i))]
  unfold action GraphColumnEnergy.graphKernel coordinateKernel
  apply Finset.sum_congr rfl
  intro w _
  have hsplit : (∏ i : I, T (y i) (curve (e.symm w) i)) =
      (∏ j : DependentCoordinates p, T (y j.val) (curve (e.symm w) j.val)) *
        ∏ i : FreeCoordinates p, T (y i.val) (curve (e.symm w) i.val) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    exact mul_comm _ _
  have hw (i : FreeCoordinates p) : curve (e.symm w) i.val = w i :=
    (he (e.symm w) i).symm.trans (congrFun (e.apply_symm_apply w) i)
  rw [hsplit]
  simp only [hw, splitCoordinates, Equiv.coe_fn_mk]
  ring

/-- Counting energy is exactly preserved when the signed source amplitude is
reindexed by its free retained-coordinate equivalence. -/
theorem amplitude_energy (p : I → Prop) [DecidablePred p]
    (e : C ≃ (FreeCoordinates p → V)) (mu : C → ℝ) :
    (∑ w, mu (e.symm w) ^ 2) = ∑ c, mu c ^ 2 :=
  e.symm.sum_comp (fun c => mu c ^ 2)

/-- Generic signed graph response with one operator bound per free label and
one column bound per dependent label. No source factorization is assumed. -/
theorem response_energy_of_equiv
    (p : I → Prop) [DecidablePred p]
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (e : C ≃ (FreeCoordinates p → V))
    (he : ∀ c i, e c i = curve c i.val)
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, response T curve mu y ^ 2) ≤
      (∏ _ : FreeCoordinates p, rho) ^ 2 *
        (∏ _ : DependentCoordinates p, kappa) * ∑ c, mu c ^ 2 := by
  classical
  let A := coordinateKernel (fun _ : FreeCoordinates p => T)
  let B := coordinateKernel (fun _ : DependentCoordinates p => T)
  let a : ℝ := ∏ _ : FreeCoordinates p, rho
  let D : ℝ := ∏ _ : DependentCoordinates p, kappa
  have hD : 0 ≤ D := Finset.prod_nonneg (fun _ _ => hkappa)
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hA : ∀ g : (FreeCoordinates p → V) → ℝ,
      (∑ y, action A g y ^ 2) ≤ a ^ 2 * ∑ x, g x ^ 2 :=
    FiniteTensorEnergy.coordinate_energy
      (fun _ : FreeCoordinates p => T) (fun _ => rho) (fun _ => hT)
  have hB : ∀ v : DependentCoordinates p → V,
      (∑ y, B y v ^ 2) ≤ (Real.sqrt D) ^ 2 := by
    intro v
    rw [hsqrt]
    change (∑ y : DependentCoordinates p → V,
      (∏ j : DependentCoordinates p, T (y j) (v j)) ^ 2) ≤ D
    rw [product_column_energy (fun j y => T y (v j))]
    exact Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun y _ => sq_nonneg (T y (v j))))
      (fun j _ => hcolumn (v j))
  have hb := GraphColumnEnergy.graphKernel_energy B A
    (fun w j => curve (e.symm w) j.val) a (Real.sqrt D) hA hB
    (fun w => mu (e.symm w))
  rw [hsqrt, amplitude_energy p e mu] at hb
  simp_rw [response_eq_graph p T curve mu e he]
  rw [(splitCoordinates (V := V) p).sum_comp
    (fun y => action (GraphColumnEnergy.graphKernel B A
      (fun w j => curve (e.symm w) j.val)) (fun w => mu (e.symm w)) y ^ 2)]
  exact hb

end Response

section Restriction
variable {C U : Type*} [Fintype C] [Fintype U]

/-- The restriction energy is a sub-sum of the original squared amplitude.
An intersection line need not have zero response or full residual energy. -/
theorem restriction_energy_le (r : C → U) (hr : Function.Injective r)
    (h : U → ℝ) :
    (∑ c, h (r c) ^ 2) ≤ ∑ u, h u ^ 2 := by
  classical
  calc
    (∑ c, h (r c) ^ 2) = ∑ u ∈ Finset.univ.image r, h u ^ 2 := by
      rw [Finset.sum_image]
      intro c _ c' _ he
      exact hr he
    _ ≤ ∑ u ∈ (Finset.univ : Finset U), h u ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => sq_nonneg (h u))
    _ = ∑ u, h u ^ 2 := by simp

end Restriction
end AESConcrete.IndexedTripleEnergy
