import AESConcrete.RestrictedMDSCoordinates

/-!
# Future generic weighted geometry of actual shortened graphs

The first zero mask r always constrains outputs; the second zero mask z
always constrains inputs. A physical residual input label is separate from
both masks. Mixed information sets give exact signed-amplitude energies,
while a residual-zero kernel subgroup supplies internal translations and
their physical retained dependent projections.

Future draft only, outside the current double-uniform compile/acceptance
inventory. This module has no event enumeration, Fourier cap, selected minor
or physical AES bound. Constructive mathematics only; no attacks. Independent
retained keys, whitening, omitted final MixColumns, ordered-distinct reference
pairs and fixed AES 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedWeightedGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

section Additive
variable {V : Type*} [AddCommGroup V]

/-- Additive realization of the existing output-zero/input-zero conditions. -/
def shortenedSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    AddSubgroup (Fin 4 → V) where
  carrier := {x | graphZeroConditions L r z x}
  zero_mem' := by constructor <;> intro i _ <;> simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      rw [map_add]
      change L x i + L y i = 0
      rw [hx.1 i hi, hy.1 i hi, zero_add]
    · intro i hi
      change x i + y i = 0
      rw [hx.2 i hi, hy.2 i hi, zero_add]
  neg_mem' := by
    intro x hx
    constructor
    · intro i hi
      rw [map_neg]
      change -L x i = 0
      rw [hx.1 i hi, neg_zero]
    · intro i hi
      change -x i = 0
      rw [hx.2 i hi, neg_zero]

abbrev ShortenedCode (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :=
  ↥(shortenedSubgroup L r z)

/-- Identity on physical states; this supplies the imported shortened-graph API
without installing a competing global group instance on its legacy subtype. -/
def graphEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    ShortenedCode L r z ≃ ShortenedGraph L r z where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Actual physical output restriction, with all original labels preserved. -/
def retainedHom (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out : Fin 16) :
    ShortenedCode L r z →+ (MaskCoordinates out → V) where
  toFun x := fun i => L x.val i.val
  map_zero' := by funext i; simp
  map_add' x y := by
    funext i
    change L (x.val + y.val) i.val = (L x.val + L y.val) i.val
    rw [map_add]

@[simp]
theorem retainedHom_apply (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out : Fin 16)
    (x : ShortenedCode L r z) (i : MaskCoordinates out) :
    retainedHom L r z out x i = L x.val i.val := rfl

def residualHom (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u : Fin 4) :
    ShortenedCode L r z →+ V where
  toFun x := x.val u
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Signed amplitude depends only on the original residual input label. -/
def amplitude (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (u : Fin 4) (h : V → ℝ) : ShortenedCode L r z → ℝ := fun x => h (x.val u)

def translationSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u : Fin 4) :
    AddSubgroup (ShortenedCode L r z) := (residualHom L r z u).ker

abbrev Translation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u : Fin 4) :=
  ↥(translationSubgroup L r z u)

def translation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u : Fin 4) :
    Translation L r z u →+ ShortenedCode L r z := (translationSubgroup L r z u).subtype

@[simp]
theorem translation_residual_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (u : Fin 4) (t : Translation L r z u) : t.val.val u = 0 := t.property

theorem amplitude_translation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (u : Fin 4) (h : V → ℝ) (x : ShortenedCode L r z) (t : Translation L r z u) :
    amplitude L r z u h (x + translation L r z u t) = amplitude L r z u h x := by
  change h (x.val u + t.val.val u) = h (x.val u)
  rw [translation_residual_zero, add_zero]

/-- Translation subgroup expressed as one additional physical input zero. -/
def translationGraphEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u : Fin 4) :
    Translation L r z u ≃ ShortenedGraph L r (maskUnion z (singletonMask u)) where
  toFun t := ⟨t.val.val, by
    constructor
    · exact t.val.property.1
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact t.val.property.2 i hi
      · rw [(singletonMask_bit u i).mp hi]
        exact translation_residual_zero L r z u t⟩
  invFun x := by
    refine ⟨⟨x.val, ⟨x.property.1, ?_⟩⟩, ?_⟩
    · intro i hi
      apply x.property.2 i
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi
    · change x.val u = 0
      apply x.property.2 u
      rw [maskUnion_bit, Bool.or_eq_true]
      exact Or.inr ((singletonMask_bit u u).mpr rfl)
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

end Additive

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

instance shortenedCodeFintype (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    Fintype (ShortenedCode L r z) := Fintype.ofFinite _

instance translationFintype (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (u : Fin 4) : Fintype (Translation L r z u) := Fintype.ofFinite _

/-- Injectivity follows from an explicit physical output information set
contained in the retained mask; no assertion about arbitrary projections is made. -/
theorem retainedHom_injective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out info : Fin 16) (hr : MaskDisjoint r info)
    (hsub : ∀ i, maskBit info i = true → maskBit out i = true)
    (hsize : maskSize r + maskSize z + maskSize info = 4) :
    Function.Injective (retainedHom L r z out) := by
  intro x y hxy
  apply (graphEquiv L r z).injective
  apply (RestrictedMDSCoordinates.output_projection_bijective L hL r z info hr hsize).1
  funext i
  exact congrFun hxy ⟨i.val, hsub i.val i.property⟩

def singletonTupleEquiv (u : Fin 4) : (MaskCoordinates (singletonMask u) → V) ≃ V where
  toFun x := x ⟨u, (singletonMask_bit u u).mpr rfl⟩
  invFun v := fun _ => v
  left_inv x := by
    funext i
    have hi : i.val = u := (singletonMask_bit u i.val).mp i.property
    exact congrArg x (Subtype.ext hi).symm
  right_inv _ := rfl

theorem residual_singleton_disjoint (z : Fin 16) (u : Fin 4)
    (hu : maskBit z u ≠ true) : MaskDisjoint z (singletonMask u) := by
  intro i hi hs
  exact hu (((singletonMask_bit u i).mp hs) ▸ hi)

/-- Original residual value and free physical outputs form one mixed information set. -/
def mixedResidualEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z free : Fin 16) (u : Fin 4) (hr : MaskDisjoint r free)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + maskSize free + 1 = 4) :
    ShortenedCode L r z ≃ V × (MaskCoordinates free → V) :=
  ((graphEquiv L r z).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv L hL r z free (singletonMask u)
      hr (residual_singleton_disjoint z u hu)
      (by simpa only [singletonMask_size] using hsize))).trans
        (Equiv.prodCongr (singletonTupleEquiv u) (Equiv.refl _))

@[simp]
theorem mixedResidualEquiv_fst (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z free : Fin 16) (u : Fin 4) (hr : MaskDisjoint r free)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + maskSize free + 1 = 4)
    (x : ShortenedCode L r z) :
    (mixedResidualEquiv L hL r z free u hr hu hsize x).1 = x.val u := rfl

/-- Exact counting energy for any signed h: each residual value has exactly
q^maskSize(free) points. No h(0), sum, positivity or independence premise is used. -/
theorem amplitude_energy (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z free : Fin 16) (u : Fin 4) (hr : MaskDisjoint r free)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + maskSize free + 1 = 4) (h : V → ℝ) :
    (∑ x : ShortenedCode L r z, amplitude L r z u h x ^ 2) =
      (Fintype.card V : ℝ) ^ maskSize free * ∑ v : V, h v ^ 2 := by
  have he := (mixedResidualEquiv L hL r z free u hr hu hsize).sum_comp
    (fun p : V × (MaskCoordinates free → V) => h p.1 ^ 2)
  change (∑ x : ShortenedCode L r z, amplitude L r z u h x ^ 2) =
    ∑ p : V × (MaskCoordinates free → V), h p.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_fun, maskCoordinates_card, Nat.cast_pow]
  exact (Finset.mul_sum _ _ _).symm

/-- Residual-zero translations parameterize exactly their physical dependent
output tuple when the enlarged zero masks and that tuple total four labels. -/
theorem translation_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z dep : Fin 16) (u : Fin 4) (hr : MaskDisjoint r dep)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + 1 + maskSize dep = 4) :
    Function.Bijective (fun t : Translation L r z u =>
      fun i : MaskCoordinates dep => L t.val.val i.val) := by
  have hunion : maskSize (maskUnion z (singletonMask u)) = maskSize z + 1 := by
    rw [maskUnion_size _ _ (residual_singleton_disjoint z u hu), singletonMask_size]
  have hs : maskSize r + maskSize (maskUnion z (singletonMask u)) + maskSize dep = 4 := by
    rw [hunion]
    omega
  exact (RestrictedMDSCoordinates.output_projection_bijective L hL r
    (maskUnion z (singletonMask u)) dep hr hs).comp (translationGraphEquiv L r z u).bijective

/-- Inclusion of a named physical dependent mask in the retained tuple.
The codomain keeps the dependent mask labels rather than choosing an ordering. -/
def retainedDependentProjection (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out dep : Fin 16) (u : Fin 4)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true) :
    Translation L r z u → (MaskCoordinates dep → V) :=
  fun t i => retainedHom L r z out (translation L r z u t)
    ⟨i.val, hsub i.val i.property⟩

theorem retainedDependentProjection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out dep : Fin 16) (u : Fin 4) (hr : MaskDisjoint r dep)
    (hsub : ∀ i, maskBit dep i = true → maskBit out i = true)
    (hu : maskBit z u ≠ true)
    (hsize : maskSize r + maskSize z + 1 + maskSize dep = 4) :
    Function.Bijective (retainedDependentProjection L r z out dep u hsub) :=
  translation_output_bijective L hL r z dep u hr hu hsize

end FiniteMDS
end AESConcrete.ShortenedWeightedGeometry
