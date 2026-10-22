import AESConcrete.ShortenedWeightedGeometry

/-!
# Shortened-source geometry for arbitrary joint residual-mask amplitudes

The frozen ShortenedWeightedGeometry owns the additive shortened source, its
graph equivalence and the retained output homomorphism. This module adds only
the residual-MASK amplitude and its actual translations.

The first zero mask r constrains outputs; z constrains inputs. E contains
original residual INPUT labels and is disjoint from z. The amplitude on the
whole E tuple is arbitrary and signed; no tensor factorization, h(0)=0 or
centering is imposed. ZeroMDS and explicit physical information masks prove
the needed equivalences and counts; no required bijection is assumed.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedJointGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedWeightedGeometry
  (ShortenedCode graphEquiv retainedHom retainedHom_injective)

section Additive
variable {V : Type*} [AddCommGroup V]

/-- Restrict the physical source to the entire original residual input mask. -/
def residualHom (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :
    ShortenedCode L r z →+ (MaskCoordinates E → V) where
  toFun x := restrictCoordinates E x.val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem residualHom_apply (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16)
    (x : ShortenedCode L r z) (i : MaskCoordinates E) :
    residualHom L r z E x i = x.val i.val := rfl

/-- One arbitrary signed JOINT amplitude on the original residual tuple. -/
def amplitude (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) : ShortenedCode L r z → ℝ :=
  fun x => h (residualHom L r z E x)

/-- Every residual coordinate is zero in this internal translation subgroup. -/
def translationSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :
    AddSubgroup (ShortenedCode L r z) := (residualHom L r z E).ker

abbrev Translation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :=
  ↥(translationSubgroup L r z E)

def translation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :
    Translation L r z E →+ ShortenedCode L r z := (translationSubgroup L r z E).subtype

@[simp]
theorem translation_residual_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z E : Fin 16) (t : Translation L r z E) (i : MaskCoordinates E) :
    t.val.val i.val = 0 := by
  have ht : residualHom L r z E t.val = 0 := t.property
  exact congrFun ht i

theorem amplitude_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z E : Fin 16) (h : (MaskCoordinates E → V) → ℝ)
    (x : ShortenedCode L r z) (t : Translation L r z E) :
    amplitude L r z E h (x + translation L r z E t) = amplitude L r z E h x := by
  change h (residualHom L r z E (x + translation L r z E t)) =
    h (residualHom L r z E x)
  rw [map_add]
  have ht : residualHom L r z E (translation L r z E t) = 0 := t.property
  rw [ht, add_zero]

/-- The whole residual-zero kernel is the actual source with input zeros z∪E. -/
def translationGraphEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :
    Translation L r z E ≃ ShortenedGraph L r (maskUnion z E) where
  toFun t := ⟨t.val.val, by
    constructor
    · exact t.val.property.1
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact t.val.property.2 i hi
      · exact translation_residual_zero L r z E t ⟨i, hi⟩⟩
  invFun x := by
    refine ⟨⟨x.val, ⟨x.property.1, ?_⟩⟩, ?_⟩
    · intro i hi
      apply x.property.2 i
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi
    · change (fun i : MaskCoordinates E => x.val i.val) = 0
      funext i
      apply x.property.2 i.val
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inr i.property
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

end Additive

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

instance translationFintype (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z E : Fin 16) :
    Fintype (Translation L r z E) := Fintype.ofFinite _

/-- The actual residual input tuple and named dependent outputs form one
mixed information set. Neither part is replaced by an enumerated tuple. -/
def mixedResidualEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z E dep : Fin 16) (hr : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4) :
    ShortenedCode L r z ≃ (MaskCoordinates E → V) × (MaskCoordinates dep → V) :=
  (graphEquiv L r z).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv L hL r z dep E hr hzE (by omega))

@[simp]
theorem mixedResidualEquiv_fst (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z E dep : Fin 16) (hr : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
    (x : ShortenedCode L r z) :
    (mixedResidualEquiv L hL r z E dep hr hzE hsize x).1 = residualHom L r z E x := rfl

@[simp]
theorem mixedResidualEquiv_snd (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z E dep : Fin 16) (hr : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
    (x : ShortenedCode L r z) :
    (mixedResidualEquiv L hL r z E dep hr hzE hsize x).2 =
      fun i : MaskCoordinates dep => L x.val i.val := rfl

/-- Exact raw energy for arbitrary signed joint h. Each entire residual tuple
has |V|^|dep| preimages in the actual shortened source. -/
theorem amplitude_energy (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z E dep : Fin 16) (hr : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4)
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ x : ShortenedCode L r z, amplitude L r z E h x ^ 2) =
      (Fintype.card V : ℝ) ^ maskSize dep * ∑ u, h u ^ 2 := by
  have he := (mixedResidualEquiv L hL r z E dep hr hzE hsize).sum_comp
    (fun p : (MaskCoordinates E → V) × (MaskCoordinates dep → V) => h p.1 ^ 2)
  change (∑ x : ShortenedCode L r z, amplitude L r z E h x ^ 2) =
    ∑ p : (MaskCoordinates E → V) × (MaskCoordinates dep → V), h p.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_fun, maskCoordinates_card, Nat.cast_pow]
  exact (Finset.mul_sum _ _ _).symm

/-- Joint bijectivity onto the complete dependent output tuple follows from
the actual enlarged input-zero mask and its MDS information-set count. -/
theorem translation_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z E dep : Fin 16) (hr : MaskDisjoint r dep) (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4) :
    Function.Bijective (fun t : Translation L r z E =>
      fun i : MaskCoordinates dep => L t.val.val i.val) := by
  have hunion : maskSize (maskUnion z E) = maskSize z + maskSize E :=
    maskUnion_size z E hzE
  have hs : maskSize r + maskSize (maskUnion z E) + maskSize dep = 4 := by
    rw [hunion]
    omega
  exact (RestrictedMDSCoordinates.output_projection_bijective L hL r
    (maskUnion z E) dep hr hs).comp (translationGraphEquiv L r z E).bijective

/-- Inclusion of the named dependent physical labels in the retained tuple. -/
def retainedDependentProjection (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out E dep : Fin 16)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true) :
    Translation L r z E → (MaskCoordinates dep → V) :=
  fun t i => retainedHom L r z out (translation L r z E t)
    ⟨i.val, hsub i.val i.property⟩

theorem retainedDependentProjection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out E dep : Fin 16) (hr : MaskDisjoint r dep)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hzE : MaskDisjoint z E)
    (hsize : maskSize r + maskSize z + maskSize E + maskSize dep = 4) :
    Function.Bijective (retainedDependentProjection L r z out E dep hsub) :=
  translation_output_bijective L hL r z E dep hr hzE hsize

end FiniteMDS
end AESConcrete.ShortenedJointGeometry
