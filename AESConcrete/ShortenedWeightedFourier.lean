import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.InvariantSubspaceFourier

/-!
# Fourier interfaces for weighted shortened physical sources

A named physical dependent mask is transported to the dependent-label subtype
of a supplied free predicate. The complement equivalence is an explicit
premise, and both the label equivalence and tuple equivalence preserve the
physical labels. Residual-zero translations then supply the joint Fourier
projection hypothesis. Exact raw counting energies keep arbitrary signed h.

ShortenedWeightedGeometry and InvariantSubspaceFourier supply distinct
geometry and analytic interfaces. No physical event family, selected minor,
(12,7) cap or inventory is supplied. Independent retained keys, whitening,
omitted final MixColumns, ordered-distinct reference pairs and fixed AES
10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedWeightedFourier
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.IndexedGraphEnergy
open AESConcrete.ShortenedWeightedGeometry

section Labels

/-- The canonical free predicate uses the physical complement inside out. -/
def physicalFree (out dep : Fin 16) (i : MaskCoordinates out) : Prop :=
  maskBit dep i.val ≠ true

instance physicalFreeDecidable (out dep : Fin 16) : DecidablePred (physicalFree out dep) := by
  intro i
  unfold physicalFree
  infer_instance

theorem physicalFree_complement (out dep : Fin 16) (i : MaskCoordinates out) :
    ¬ physicalFree out dep i ↔ maskBit dep i.val = true := by
  simp only [physicalFree, not_not]

/-- A dependent physical label and its retained Fourier label have the same
original Fin 4 value. Complement identification is supplied explicitly. -/
def dependentLabelEquiv (out dep : Fin 16)
    (free : MaskCoordinates out → Prop)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true) :
    MaskCoordinates dep ≃ DependentCoordinates free where
  toFun i := ⟨⟨i.val, hsub i.val i.property⟩,
    (hcomplement ⟨i.val, hsub i.val i.property⟩).mpr i.property⟩
  invFun j := ⟨j.val.val, (hcomplement j.val).mp j.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Tuple transport uses that label equivalence, without an enumeration. -/
def dependentTupleEquiv {V : Type*} (out dep : Fin 16)
    (free : MaskCoordinates out → Prop)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true) :
    (MaskCoordinates dep → V) ≃ (DependentCoordinates free → V) where
  toFun x j := x ((dependentLabelEquiv out dep free hsub hcomplement).symm j)
  invFun x i := x (dependentLabelEquiv out dep free hsub hcomplement i)
  left_inv x := by
    funext i
    exact congrArg x ((dependentLabelEquiv out dep free hsub hcomplement).symm_apply_apply i)
  right_inv x := by
    funext j
    exact congrArg x ((dependentLabelEquiv out dep free hsub hcomplement).apply_symm_apply j)

@[simp]
theorem dependentTupleEquiv_apply {V : Type*} (out dep : Fin 16)
    (free : MaskCoordinates out → Prop)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (x : MaskCoordinates dep → V) (j : DependentCoordinates free) :
    dependentTupleEquiv out dep free hsub hcomplement x j =
      x ⟨j.val.val, (hcomplement j.val).mp j.property⟩ := rfl

theorem dependentCoordinates_card (out dep : Fin 16)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true) :
    Fintype.card (DependentCoordinates free) = maskSize dep := by
  calc
    _ = Fintype.card (MaskCoordinates dep) :=
      (Fintype.card_congr (dependentLabelEquiv out dep free hsub hcomplement)).symm
    _ = _ := maskCoordinates_card dep

theorem freeCoordinates_card (out dep : Fin 16)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true) :
    Fintype.card (FreeCoordinates free) = maskSize out - maskSize dep := by
  have hc := Fintype.card_subtype_compl free
  have hle := Fintype.card_subtype_le free
  change Fintype.card (DependentCoordinates free) =
    Fintype.card (MaskCoordinates out) - Fintype.card (FreeCoordinates free) at hc
  change Fintype.card (FreeCoordinates free) ≤ Fintype.card (MaskCoordinates out) at hle
  rw [dependentCoordinates_card out dep free hsub hcomplement, maskCoordinates_card] at hc
  rw [maskCoordinates_card] at hle
  omega

end Labels

section WeightedSource
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Actual residual-zero translations cover the whole Fourier dependent
tuple, rather than merely each of its coordinates separately. -/
theorem fourierDependentProjection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out dep : Fin 16) (u : Fin 4)
    (free : MaskCoordinates out → Prop)
    (hr : MaskDisjoint r dep)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + 1 + maskSize dep = 4) :
    Function.Bijective (fun t : Translation L r z u =>
      fun j : DependentCoordinates free =>
        retainedHom L r z out (translation L r z u t) j.val) := by
  have hb : Function.Bijective (fun t : Translation L r z u =>
      dependentTupleEquiv out dep free hsub hcomplement
        (retainedDependentProjection L r z out dep u hsub t)) :=
    (dependentTupleEquiv out dep free hsub hcomplement).bijective.comp
      (retainedDependentProjection_bijective L hL r z out dep u hr hsub hu hsize)
  have he : (fun t : Translation L r z u =>
      dependentTupleEquiv out dep free hsub hcomplement
        (retainedDependentProjection L r z out dep u hsub t)) =
      (fun t : Translation L r z u => fun j : DependentCoordinates free =>
        retainedHom L r z out (translation L r z u t) j.val) := by
    funext t j
    change retainedHom L r z out (translation L r z u t)
      ⟨j.val.val, hsub j.val.val ((hcomplement j.val).mp j.property)⟩ =
        retainedHom L r z out (translation L r z u t) j.val
    exact congrArg (retainedHom L r z out (translation L r z u t)) (Subtype.ext rfl)
  rw [he] at hb
  exact hb

/-- Extension over the complete retained ambient tuple. -/
def zeroExtension (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out : Fin 16) (u : Fin 4) (h : V → ℝ) :
    (MaskCoordinates out → V) → ℝ :=
  InvariantSubspaceEnergy.zeroExtend (retainedHom L r z out) (amplitude L r z u h)

omit [DecidableEq V] in
theorem zeroExtension_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out : Fin 16) (u : Fin 4) (h : V → ℝ)
    (x : MaskCoordinates out → V) (t : Translation L r z u) :
    zeroExtension L r z out u h
      (x + retainedHom L r z out (translation L r z u t)) =
        zeroExtension L r z out u h x :=
  InvariantSubspaceEnergy.zeroExtend_translation (retainedHom L r z out)
    (translation L r z u) (amplitude L r z u h) (amplitude_translation L r z u h) x t

/-- A named retained information mask supplies injectivity; a named mixed
information mask supplies the exact raw |V|^|dep| amplitude multiplicity. -/
theorem zeroExtension_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info dep : Fin 16) (u : Fin 4)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep) (hu : maskBit z u ≠ true)
    (hdepSize : maskSize r + maskSize z + 1 + maskSize dep = 4) (h : V → ℝ) :
    (∑ x, zeroExtension L r z out u h x ^ 2) =
      (Fintype.card V : ℝ) ^ maskSize dep * ∑ v, h v ^ 2 := by
  rw [zeroExtension, InvariantSubspaceEnergy.zeroExtend_energy
    (retainedHom L r z out) (retainedHom_injective L hL r z out info hrinfo hinfoSub hinfoSize)]
  exact amplitude_energy L hL r z dep u hrdep hu (by omega) h

-- Keep source geometry, complement identification and Fourier resources as
-- separate premises. No physical-event or ordinary/Fourier resource is implicit.
theorem zeroExtension_fourier_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info dep : Fin 16) (u : Fin 4)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hu : maskBit z u ≠ true)
    (hdepSize : maskSize r + maskSize z + 1 + maskSize dep = 4)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ)
    (nu : FreeCoordinates free → ℝ) (delta : DependentCoordinates free → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates free) (g : V → ℝ),
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates free) (v : V),
      (∑ y, fourierConjugate B T y v ^ 2) ≤ delta j)
    (h : V → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : MaskCoordinates out => T))
      (zeroExtension L r z out u h) y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) *
          ((Fintype.card V : ℝ) ^ maskSize dep * ∑ v, h v ^ 2) := by
  have he := InvariantSubspaceFourier.coordinate_fourier_partial_graph_energy
    B hchar T free nu delta hdelta hT hcolumn
    (fun t : Translation L r z u => retainedHom L r z out (translation L r z u t))
    (fourierDependentProjection_bijective L hL r z out dep u free
      hrdep hdepSub hcomplement hu hdepSize).surjective
    (zeroExtension L r z out u h) (zeroExtension_translation L r z out u h)
  rw [zeroExtension_energy L hL r z out info dep u
    hrinfo hinfoSub hinfoSize hrdep hu hdepSize h] at he
  exact he

/-- Raw physical-source response with heterogeneous Fourier resources and
the same unrestricted signed residual amplitude. -/
theorem response_fourier_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info dep : Fin 16) (u : Fin 4)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hu : maskBit z u ≠ true)
    (hdepSize : maskSize r + maskSize z + 1 + maskSize dep = 4)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ)
    (nu : FreeCoordinates free → ℝ) (delta : DependentCoordinates free → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates free) (g : V → ℝ),
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates free) (v : V),
      (∑ y, fourierConjugate B T y v ^ 2) ≤ delta j)
    (h : V → ℝ) :
    (∑ y, IndexedTripleEnergy.response T (retainedHom L r z out)
      (amplitude L r z u h) y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) *
          ((Fintype.card V : ℝ) ^ maskSize dep * ∑ v, h v ^ 2) := by
  simp_rw [InvariantSubspaceEnergy.response_eq_action]
  exact zeroExtension_fourier_energy L hL r z out info dep u
    hrinfo hinfoSub hinfoSize hrdep hdepSub hu hdepSize free hcomplement
    B hchar T nu delta hdelta hT hcolumn h

/-- Uniform resource interface with all exponents expressed by named physical
mask sizes. The |V|^|dep| factor is raw counting, before exclusions. -/
theorem response_uniform_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info dep : Fin 16) (u : Fin 4)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hu : maskBit z u ≠ true)
    (hdepSize : maskSize r + maskSize z + 1 + maskSize dep = 4)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : V → ℝ) :
    (∑ y, IndexedTripleEnergy.response T (retainedHom L r z out)
      (amplitude L r z u h) y ^ 2) ≤
      (rho ^ (maskSize out - maskSize dep)) ^ 2 * kappa ^ maskSize dep *
        ((Fintype.card V : ℝ) ^ maskSize dep * ∑ v, h v ^ 2) := by
  have he := response_fourier_energy L hL r z out info dep u
    hrinfo hinfoSub hinfoSize hrdep hdepSub hu hdepSize free hcomplement
    B hchar T (fun _ => rho) (fun _ => kappa)
    (fun _ => hkappa) (fun _ => hT) (fun _ => hcolumn) h
  simpa only [Finset.prod_const, Finset.card_univ,
    freeCoordinates_card out dep free hdepSub hcomplement,
    dependentCoordinates_card out dep free hdepSub hcomplement] using he

end WeightedSource
end AESConcrete.ShortenedWeightedFourier
