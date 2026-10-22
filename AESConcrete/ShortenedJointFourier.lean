import AESConcrete.ShortenedJointGeometry
import AESConcrete.ShortenedWeightedFourier
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Fourier energy for shortened sources with joint residual-mask amplitudes

ShortenedJointGeometry owns the new joint geometry. The frozen
ShortenedWeightedFourier label/tuple transport is reused unchanged; it
concerns physical labels and does not require a singleton residual domain.

Injectivity is proved from a named physical information subset of the retained
mask. The residual-zero subgroup projects jointly onto the named dependent
output tuple. Exact source energy retains arbitrary signed joint h, with no
product, centering or h(0)=0 premise. Generic Fourier resources are explicit;
the final word specialization supplies the ordinary/ordinary/false
resources rather than an assumed response operator cap.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedJointFourier
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.IndexedGraphEnergy
open AESConcrete.ShortenedWeightedGeometry
  (ShortenedCode retainedHom retainedHom_injective)
open AESConcrete.ShortenedJointGeometry
open AESConcrete.ShortenedWeightedFourier
  (physicalFree physicalFree_complement dependentTupleEquiv
    dependentCoordinates_card freeCoordinates_card)

section JointSource
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Physical dependent-label transport preserves one JOINT bijection; it
does not replace it by separate coordinate-surjectivity assertions. -/
theorem fourierDependentProjection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out E dep : Fin 16) (free : MaskCoordinates out → Prop)
    (hr : MaskDisjoint r dep)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4) :
    Function.Bijective (fun t : Translation L r z E =>
      fun j : DependentCoordinates free =>
        retainedHom L r z out (translation L r z E t) j.val) := by
  have hb : Function.Bijective (fun t : Translation L r z E =>
      dependentTupleEquiv out dep free hsub hcomplement
        (retainedDependentProjection L r z out E dep hsub t)) :=
    (dependentTupleEquiv out dep free hsub hcomplement).bijective.comp
      (retainedDependentProjection_bijective L hL r z out E dep hr hsub hzE hsize)
  have he : (fun t : Translation L r z E =>
      dependentTupleEquiv out dep free hsub hcomplement
        (retainedDependentProjection L r z out E dep hsub t)) =
      (fun t : Translation L r z E => fun j : DependentCoordinates free =>
        retainedHom L r z out (translation L r z E t) j.val) := by
    funext t j
    change retainedHom L r z out (translation L r z E t)
      ⟨j.val.val, hsub j.val.val ((hcomplement j.val).mp j.property)⟩ =
        retainedHom L r z out (translation L r z E t) j.val
    exact congrArg (retainedHom L r z out (translation L r z E t)) (Subtype.ext rfl)
  rw [he] at hb
  exact hb

/-- Extend the actual shortened-source amplitude to the full retained tuple. -/
def zeroExtension (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) : (MaskCoordinates out → V) → ℝ :=
  InvariantSubspaceEnergy.zeroExtend (retainedHom L r z out) (amplitude L r z E h)

omit [DecidableEq V] in
theorem zeroExtension_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out E : Fin 16) (h : (MaskCoordinates E → V) → ℝ)
    (x : MaskCoordinates out → V) (t : Translation L r z E) :
    zeroExtension L r z out E h
      (x + retainedHom L r z out (translation L r z E t)) =
        zeroExtension L r z out E h x :=
  InvariantSubspaceEnergy.zeroExtend_translation (retainedHom L r z out)
    (translation L r z E) (amplitude L r z E h) (amplitude_translation L r z E h) x t

/-- A physical retained information subset proves injectivity. The mixed
input/output information set proves the exact joint-amplitude multiplicity. -/
theorem zeroExtension_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info E dep : Fin 16)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hdepSize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ x, zeroExtension L r z out E h x ^ 2) =
      (Fintype.card V : ℝ) ^ maskSize dep * ∑ u, h u ^ 2 := by
  rw [zeroExtension, InvariantSubspaceEnergy.zeroExtend_energy
    (retainedHom L r z out)
      (retainedHom_injective L hL r z out info hrinfo hinfoSub hinfoSize)]
  exact amplitude_energy L hL r z E dep hrdep hzE hdepSize h

/-- Heterogeneous operator/column resources on the actual retained labels.
No needed source or translation bijection is an unproved premise. -/
theorem zeroExtension_fourier_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info E dep : Fin 16)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hdepSize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
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
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : MaskCoordinates out => T))
      (zeroExtension L r z out E h) y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) *
          ((Fintype.card V : ℝ) ^ maskSize dep * ∑ u, h u ^ 2) := by
  have he := InvariantSubspaceFourier.coordinate_fourier_partial_graph_energy
    B hchar T free nu delta hdelta hT hcolumn
    (fun t : Translation L r z E => retainedHom L r z out (translation L r z E t))
    (fourierDependentProjection_bijective L hL r z out E dep free
      hrdep hdepSub hcomplement hzE hdepSize).surjective
    (zeroExtension L r z out E h) (zeroExtension_translation L r z out E h)
  rw [zeroExtension_energy L hL r z out info E dep
    hrinfo hinfoSub hinfoSize hrdep hzE hdepSize h] at he
  exact he

/-- Raw response over the actual shortened physical source, with its
unrestricted signed JOINT residual amplitude and no uniform normalization. -/
theorem response_fourier_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info E dep : Fin 16)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hdepSize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
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
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ y, IndexedTripleEnergy.response T (retainedHom L r z out)
      (amplitude L r z E h) y ^ 2) ≤
      (∏ i : FreeCoordinates free, nu i) ^ 2 *
        (∏ j : DependentCoordinates free, delta j) *
          ((Fintype.card V : ℝ) ^ maskSize dep * ∑ u, h u ^ 2) := by
  simp_rw [InvariantSubspaceEnergy.response_eq_action]
  exact zeroExtension_fourier_energy L hL r z out info E dep
    hrinfo hinfoSub hinfoSize hrdep hdepSub hzE hdepSize free hcomplement
    B hchar T nu delta hdelta hT hcolumn h

/-- One operator factor per free retained label, one column factor per
dependent label, and the exact raw |V|^|dep| source multiplicity. -/
theorem response_uniform_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info E dep : Fin 16)
    (hrinfo : MaskDisjoint r info)
    (hinfoSub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hinfoSize : maskSize r + maskSize z + maskSize info = 4)
    (hrdep : MaskDisjoint r dep)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hdepSize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
    (free : MaskCoordinates out → Prop) [DecidablePred free]
    (hcomplement : ∀ i : MaskCoordinates out, ¬ free i ↔ maskBit dep i.val = true)
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ y, IndexedTripleEnergy.response T (retainedHom L r z out)
      (amplitude L r z E h) y ^ 2) ≤
      (rho ^ (maskSize out - maskSize dep)) ^ 2 * kappa ^ maskSize dep *
        ((Fintype.card V : ℝ) ^ maskSize dep * ∑ u, h u ^ 2) := by
  have he := response_fourier_energy L hL r z out info E dep
    hrinfo hinfoSub hinfoSize hrdep hdepSub hzE hdepSize free hcomplement
    B hchar T (fun _ => rho) (fun _ => kappa)
    (fun _ => hkappa) (fun _ => hT) (fun _ => hcolumn) h
  simpa only [Finset.prod_const, Finset.card_univ,
    freeCoordinates_card out dep free hdepSub hcomplement,
    dependentCoordinates_card out dep free hdepSub hcomplement] using he

/-- One zero event with two original residual inputs and three retained
outputs. The retained mask itself is an information set; the dependent mask
has one physical label. All required bijections are derived above. -/
theorem response_single_event_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out E dep : Fin 16)
    (hrout : MaskDisjoint r out)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hrzSize : maskSize r + maskSize z = 1)
    (hout : maskSize out = 3) (hE : maskSize E = 2) (hdep : maskSize dep = 1)
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ y, IndexedTripleEnergy.response T (retainedHom L r z out)
      (amplitude L r z E h) y ^ 2) ≤
      ((Fintype.card V : ℝ) * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have hrdep : MaskDisjoint r dep := by
    intro i hri hdi
    exact hrout i hri (hdepSub i hdi)
  have hinfoSize : maskSize r + maskSize z + maskSize out = 4 := by omega
  have hdepSize : maskSize r + maskSize z + maskSize E + maskSize dep = 4 := by omega
  have he := response_uniform_energy L hL r z out out E dep
    hrout (fun _ hi => hi) hinfoSize hrdep hdepSub hzE hdepSize
    (physicalFree out dep) (physicalFree_complement out dep)
    B hchar T rho kappa hkappa hT hcolumn h
  rw [hout, hdep] at he
  exact he.trans_eq (by ring)

end JointSource

/-- Actual ordinary two-sided word resources remove the generic Fourier
resource premises. E may be the residual mask of any SelectedSupport 2 4;
the joint h is unchanged on the complete physical shortened source. -/
theorem word_single_event_energy
    (r z out E dep : Fin 16)
    (hrout : MaskDisjoint r out)
    (hdepSub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hrzSize : maskSize r + maskSize z = 1)
    (hout : maskSize out = 3) (hE : maskSize E = 2) (hdep : maskSize dep = 1)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (retainedHom WordCrossZero.wordMixAddEquiv.toAddMonoidHom r z out)
      (amplitude WordCrossZero.wordMixAddEquiv.toAddMonoidHom r z E h) y ^ 2) ≤
      (ActivityCodeScalar.q * UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ u, h u ^ 2 := by
  have he := response_single_event_energy WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS r z out E dep hrout hdepSub hzE
    hrzSize hout hE hdep WordFourierCore.wordPairing word_add_self
    (residualMatrix AES.wordSuperboxKernel 0)
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
    DoubleUniformFourierEnergy.word_fourier_operator_energy
    DoubleUniformFourierEnergy.word_fourier_column_energy h
  rw [DoubleUniformFourierEnergy.word_card_real] at he
  exact he

end AESConcrete.ShortenedJointFourier
