import AESConcrete.DoubleUniformSource
import AESConcrete.ThreeActiveGeometry

/-!
# Actual retained-triple geometry with two uniform input directions

The source has one residual and two original uniform coordinates. Its full
three-coordinate retained map is an additive equivalence. The entire uniform
plane, holding the residual coordinate at zero, projects bijectively onto
every physical output pair. These are separate information-set statements;
no Fourier support, norm estimate or physical cap is asserted here.

Candidate only; compilation and independent review remain separate. No attacks.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference pairs and fixed 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource

set_option maxRecDepth 100000

def activeMask (p : SelectedSupport 1 3) : Fin 16 := maskComplement p.val.val.2

theorem activeMask_size (p : SelectedSupport 1 3) : maskSize (activeMask p) = 3 := by
  have hz : maskSize p.val.val.2 = 1 := by
    have hp := p.property
    omega
  rw [activeMask, maskComplement_size, hz]

theorem retainedMask_size (p : SelectedSupport 3 4) : maskSize p.val.val.1 = 3 :=
  ThreeActiveGeometry.retainedMask_size p

theorem retainedCoordinates_card (p : SelectedSupport 3 4) :
    Fintype.card (MaskCoordinates p.val.val.1) = 3 :=
  ThreeActiveGeometry.retainedCoordinates_card p

theorem retained_other_card (p : SelectedSupport 3 4) (s : MaskCoordinates p.val.val.1) :
    Fintype.card {i : MaskCoordinates p.val.val.1 // i ≠ s} = 2 :=
  ThreeActiveGeometry.retained_other_card p s

abbrev OmittedPositions (p : SelectedSupport 3 4) := ThreeActiveGeometry.OmittedPositions p

def omittedPosition (p : SelectedSupport 3 4) : OmittedPositions p :=
  ThreeActiveGeometry.omittedPosition p

def omittedLabel (p : SelectedSupport 3 4) : Fin 4 := ThreeActiveGeometry.omittedLabel p

theorem omittedPositions_card (p : SelectedSupport 3 4) :
    Fintype.card (OmittedPositions p) = 1 := ThreeActiveGeometry.omittedPositions_card p

theorem omittedPosition_unique (p : SelectedSupport 3 4) (i : OmittedPositions p) :
    i = omittedPosition p := ThreeActiveGeometry.omittedPosition_unique p i

theorem omittedLabel_not_retained (p : SelectedSupport 3 4) :
    maskBit p.val.val.1 (omittedLabel p) ≠ true :=
  ThreeActiveGeometry.omittedLabel_not_retained p

theorem retained_ne_omitted (p : SelectedSupport 3 4) (i : MaskCoordinates p.val.val.1) :
    i.val ≠ omittedLabel p := ThreeActiveGeometry.retained_ne_omitted p i

/-- The two original nonresidual active inputs, with both other inputs zero. -/
def uniformMask (p : SelectedSupport 1 3) : Fin 16 :=
  maskComplement (maskUnion p.val.val.2 p.val.val.1)

theorem uniformMask_bit (p : SelectedSupport 1 3) (i : Fin 4) :
    maskBit (uniformMask p) i = true ↔
      maskBit p.val.val.1 i ≠ true ∧ maskBit p.val.val.2 i ≠ true := by
  rw [uniformMask, maskComplement_bit, maskUnion_bit]
  cases hE : maskBit p.val.val.1 i <;> cases hz : maskBit p.val.val.2 i <;> simp

theorem uniformMask_size (p : SelectedSupport 1 3) : maskSize (uniformMask p) = 2 := by
  rw [uniformMask, maskComplement_size, maskUnion_size _ _ p.val.property.1]
  have hp := p.property
  have hd := p.val.property.2
  omega

/-- Reindexing only: each uniform tuple entry keeps its physical input label. -/
def uniformPositionEquiv (p : SelectedSupport 1 3) :
    SourceUniformPositions p ≃ MaskCoordinates (uniformMask p) where
  toFun i := ⟨i.val.val, (uniformMask_bit p i.val.val).mpr ⟨i.val.property, i.property⟩⟩
  invFun i := ⟨⟨i.val, ((uniformMask_bit p i.val).mp i.property).1⟩,
    ((uniformMask_bit p i.val).mp i.property).2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

section ZeroCoordinates
variable {V : Type*} [Zero V]

theorem onSource_iff_projection_zero (p : SelectedSupport 1 3) (x : Fin 4 → V) :
    OnSource p x ↔ maskProjection p.val.val.2 x = 0 := by
  constructor
  · intro hx
    funext i
    by_cases hi : maskBit p.val.val.2 i = true
    · simp [maskProjection, hi, hx i hi]
    · simp [maskProjection, hi]
  · intro hx i hi
    have he := congrFun hx i
    simpa only [maskProjection, hi, if_true, Pi.zero_apply] using he

def activeCoordinatesEquiv (p : SelectedSupport 1 3) :
    {x : Fin 4 → V // OnSource p x} ≃ (MaskCoordinates (activeMask p) → V) where
  toFun x := restrictCoordinates (activeMask p) x.val
  invFun w := ⟨extendCoordinates (activeMask p) w, by
    apply (onSource_iff_projection_zero p _).mpr
    exact (maskProjection_complement_iff p.val.val.2 _).mp
      (extend_supported (activeMask p) w)⟩
  left_inv x := by
    apply Subtype.ext
    change extendCoordinates (activeMask p)
      (restrictCoordinates (activeMask p) x.val) = x.val
    rw [extend_restrict]
    exact (maskProjection_complement_iff p.val.val.2 x.val).mpr
      ((onSource_iff_projection_zero p x.val).mp x.property)
  right_inv w := restrict_extend (activeMask p) w

def sourceActiveEquiv (p : SelectedSupport 1 3) :
    (V × (SourceUniformPositions p → V)) ≃ (MaskCoordinates (activeMask p) → V) :=
  (sourceEquiv p).trans (activeCoordinatesEquiv p)

theorem extend_sourceActiveEquiv (p : SelectedSupport 1 3)
    (uv : V × (SourceUniformPositions p → V)) :
    extendCoordinates (activeMask p) (sourceActiveEquiv p uv) = source p uv.1 uv.2 := by
  change extendCoordinates (activeMask p)
    (restrictCoordinates (activeMask p) (source p uv.1 uv.2)) = source p uv.1 uv.2
  rw [extend_restrict]
  exact (maskProjection_complement_iff p.val.val.2 _).mpr
    ((onSource_iff_projection_zero p _).mp (source_onSource p uv.1 uv.2))

def uniformCoordinatesEquiv (p : SelectedSupport 1 3) :
    (SourceUniformPositions p → V) ≃ (MaskCoordinates (uniformMask p) → V) where
  toFun v := fun i => v ((uniformPositionEquiv p).symm i)
  invFun w := fun i => w (uniformPositionEquiv p i)
  left_inv v := by
    funext i
    simp only [Equiv.symm_apply_apply]
  right_inv w := by
    funext i
    simp only [Equiv.apply_symm_apply]

theorem extend_uniformCoordinatesEquiv (p : SelectedSupport 1 3)
    (v : SourceUniformPositions p → V) :
    extendCoordinates (uniformMask p) (uniformCoordinatesEquiv p v) = source p 0 v := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · have hi : maskBit (uniformMask p) i ≠ true := by
      intro hi
      exact ((uniformMask_bit p i).mp hi).1 hE
    simp [extendCoordinates, hi, source, hE]
  · by_cases hz : maskBit p.val.val.2 i = true
    · have hi : maskBit (uniformMask p) i ≠ true := by
        intro hi
        exact ((uniformMask_bit p i).mp hi).2 hz
      simp [extendCoordinates, hi, source, hE, hz]
    · have hi : maskBit (uniformMask p) i = true := (uniformMask_bit p i).mpr ⟨hE, hz⟩
      simp only [extendCoordinates, dif_pos hi, uniformCoordinatesEquiv,
        source, dif_neg hE, dif_neg hz]
      rfl

theorem source_residual_axis (p : SelectedSupport 1 3) (u : V) :
    source p u 0 = Pi.single (residualLabel p) u := by
  funext i
  by_cases hi : i = residualLabel p
  · subst i
    simp
  · have hE : maskBit p.val.val.1 i ≠ true := by
      intro hE
      exact hi (residualLabel_eq_of_mem p i hE)
    simp [source, hE, hi]

end ZeroCoordinates

section AdditiveCoordinates
variable {V : Type*} [AddCommGroup V]

theorem source_zero (p : SelectedSupport 1 3) : source p (0 : V) 0 = 0 := by
  funext i
  unfold source
  split_ifs <;> rfl

theorem source_pair_add (p : SelectedSupport 1 3)
    (uv uv' : V × (SourceUniformPositions p → V)) :
    source p (uv + uv').1 (uv + uv').2 = source p uv.1 uv.2 + source p uv'.1 uv'.2 := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · simp [source, hE]
  · by_cases hz : maskBit p.val.val.2 i = true
    · simp [source, hE, hz]
    · simp [source, hE, hz]

theorem source_add (p : SelectedSupport 1 3) (u u' : V)
    (v v' : SourceUniformPositions p → V) :
    source p (u + u') (v + v') = source p u v + source p u' v' :=
  source_pair_add p (u, v) (u', v')

/-- Restriction of the actual physical diffusion to the output mask. -/
def sourceMap (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 1 3)
    (out : Fin 16) (uv : V × (SourceUniformPositions p → V)) : MaskCoordinates out → V :=
  fun i => L (source p uv.1 uv.2) i.val

theorem sourceMap_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (out : Fin 16) : sourceMap L p out (0, 0) = 0 := by
  funext i
  change L (source p (0 : V) 0) i.val = 0
  simp only [source_zero, map_zero, Pi.zero_apply]

theorem sourceMap_add (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (out : Fin 16)
    (uv uv' : V × (SourceUniformPositions p → V)) :
    sourceMap L p out (uv + uv') = sourceMap L p out uv + sourceMap L p out uv' := by
  funext i
  change L (source p (uv + uv').1 (uv + uv').2) i.val =
    (L (source p uv.1 uv.2) + L (source p uv'.1 uv'.2)) i.val
  rw [source_pair_add, map_add]

def sourceAddHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (out : Fin 16) :
    (V × (SourceUniformPositions p → V)) →+ (MaskCoordinates out → V) where
  toFun := sourceMap L p out
  map_zero' := sourceMap_zero L p out
  map_add' := sourceMap_add L p out

theorem sourceMap_uniform_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (out : Fin 16) (u : V)
    (v t : SourceUniformPositions p → V) :
    sourceMap L p out (u, v + t) =
      sourceMap L p out (u, v) + sourceMap L p out (0, t) := by
  have hp : (u, v) + (0, t) = (u, v + t) := by ext <;> simp
  simpa only [hp] using sourceMap_add L p out (u, v) (0, t)

end AdditiveCoordinates

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V]

theorem sourceMap_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3) :
    Function.Bijective (sourceMap L p out) := by
  have hsize : maskSize out = maskSize (activeMask p) :=
    hout.trans (activeMask_size p).symm
  have hb := (mds_restricted_bijective L hL out (activeMask p) hsize).comp
    (sourceActiveEquiv (V := V) p).bijective
  have he : restrictedMap L out (activeMask p) ∘ sourceActiveEquiv p = sourceMap L p out := by
    funext uv i
    change L (extendCoordinates (activeMask p) (sourceActiveEquiv p uv)) i.val =
      L (source p uv.1 uv.2) i.val
    rw [extend_sourceActiveEquiv]
  exact he ▸ hb

/-- All three active source coordinates are recovered from three outputs. -/
def sourceDiffusionEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3) :
    (V × (SourceUniformPositions p → V)) ≃+ (MaskCoordinates out → V) :=
  { Equiv.ofBijective (sourceMap L p out) (sourceMap_bijective L hL p out hout) with
    map_add' := sourceMap_add L p out }

@[simp]
theorem sourceDiffusionEquiv_apply (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3)
    (uv : V × (SourceUniformPositions p → V)) :
    sourceDiffusionEquiv L hL p out hout uv = sourceMap L p out uv := rfl

theorem sourceDiffusionEquiv_symm_uniform_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3)
    (x : MaskCoordinates out → V) (t : SourceUniformPositions p → V) :
    (sourceDiffusionEquiv L hL p out hout).symm (x + sourceMap L p out (0, t)) =
      (sourceDiffusionEquiv L hL p out hout).symm x + (0, t) := by
  change (sourceDiffusionEquiv L hL p out hout).symm
    (x + sourceDiffusionEquiv L hL p out hout (0, t)) = _
  rw [map_add, AddEquiv.symm_apply_apply]

theorem sourceDiffusionEquiv_symm_uniform_fst
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3)
    (x : MaskCoordinates out → V) (t : SourceUniformPositions p → V) :
    ((sourceDiffusionEquiv L hL p out hout).symm
      (x + sourceMap L p out (0, t))).1 =
        ((sourceDiffusionEquiv L hL p out hout).symm x).1 := by
  rw [sourceDiffusionEquiv_symm_uniform_translation]
  simp

/-- The full two-dimensional uniform translation plane projects bijectively
onto every actual pair; it is not replaced by either uniform axis. -/
theorem uniform_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (pair : Fin 16) (hpair : maskSize pair = 2) :
    Function.Bijective
      (fun v : SourceUniformPositions p → V => sourceMap L p pair (0, v)) := by
  have hsize : maskSize pair = maskSize (uniformMask p) :=
    hpair.trans (uniformMask_size p).symm
  have hb := (mds_restricted_bijective L hL pair (uniformMask p) hsize).comp
    (uniformCoordinatesEquiv (V := V) p).bijective
  have he : restrictedMap L pair (uniformMask p) ∘ uniformCoordinatesEquiv p =
      (fun v : SourceUniformPositions p → V => sourceMap L p pair (0, v)) := by
    funext v i
    change L (extendCoordinates (uniformMask p) (uniformCoordinatesEquiv p v)) i.val =
      L (source p 0 v) i.val
    rw [extend_uniformCoordinatesEquiv]
  exact he ▸ hb

end FiniteMDS

/-- The physical retained mask after removing one designated retained label. -/
def retainedPairMask (out : Fin 16) (s : MaskCoordinates out) : Fin 16 :=
  maskBitsEquiv.symm (fun i => maskBit out i && decide (i ≠ s.val))

theorem retainedPairMask_bit (out : Fin 16) (s : MaskCoordinates out) (i : Fin 4) :
    maskBit (retainedPairMask out s) i = true ↔
      maskBit out i = true ∧ i ≠ s.val := by
  have he := congrFun (maskBitsEquiv.apply_symm_apply
    (fun i => maskBit out i && decide (i ≠ s.val))) i
  change maskBit (retainedPairMask out s) i = _ at he
  rw [he]
  simp

/-- The complement subtype and the physical pair mask have identical labels. -/
def retainedPairIndexEquiv (out : Fin 16) (s : MaskCoordinates out) :
    MaskCoordinates (retainedPairMask out s) ≃ {i : MaskCoordinates out // i ≠ s} where
  toFun i := ⟨⟨i.val, ((retainedPairMask_bit out s i.val).mp i.property).1⟩, by
    intro he
    exact ((retainedPairMask_bit out s i.val).mp i.property).2 (congrArg Subtype.val he)⟩
  invFun i := ⟨i.val.val, (retainedPairMask_bit out s i.val.val).mpr ⟨i.val.property, by
    intro he
    exact i.property (Subtype.ext he)⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem retainedPairMask_size (out : Fin 16) (hout : maskSize out = 3)
    (s : MaskCoordinates out) : maskSize (retainedPairMask out s) = 2 := by
  have hc : Fintype.card {i : MaskCoordinates out // i ≠ s} = 2 := by
    rw [Fintype.card_subtype_compl (fun i : MaskCoordinates out => i = s),
      Fintype.card_subtype_eq, maskCoordinates_card, hout]
  have he := Fintype.card_congr (retainedPairIndexEquiv out s)
  rw [maskCoordinates_card, hc] at he
  exact he

def retainedPairCoordinatesEquiv {V : Type*} (out : Fin 16) (s : MaskCoordinates out) :
    (MaskCoordinates (retainedPairMask out s) → V) ≃
      ({i : MaskCoordinates out // i ≠ s} → V) where
  toFun w := fun i => w ((retainedPairIndexEquiv out s).symm i)
  invFun w := fun i => w (retainedPairIndexEquiv out s i)
  left_inv w := by
    funext i
    simp only [Equiv.symm_apply_apply]
  right_inv w := by
    funext i
    simp only [Equiv.apply_symm_apply]

section RetainedPair
variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- Pair projection in exactly the subtype form used by retained Fourier
coordinates; all simultaneous uniform translations are present. -/
theorem retained_uniform_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (out : Fin 16) (hout : maskSize out = 3)
    (s : MaskCoordinates out) :
    Function.Bijective (fun v : SourceUniformPositions p → V =>
      fun i : {i : MaskCoordinates out // i ≠ s} => sourceMap L p out (0, v) i.val) := by
  have hb := (retainedPairCoordinatesEquiv (V := V) out s).bijective.comp
    (uniform_pair_bijective L hL p (retainedPairMask out s)
      (retainedPairMask_size out hout s))
  have he : retainedPairCoordinatesEquiv (V := V) out s ∘
      (fun v : SourceUniformPositions p → V => sourceMap L p (retainedPairMask out s) (0, v)) =
      (fun v : SourceUniformPositions p → V =>
        fun i : {i : MaskCoordinates out // i ≠ s} => sourceMap L p out (0, v) i.val) := by
    rfl
  exact he ▸ hb

end RetainedPair

def retainedEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) :
    (AES.Word × (SourceUniformPositions pIn → AES.Word)) ≃+
      (MaskCoordinates pOut.val.val.1 → AES.Word) :=
  sourceDiffusionEquiv WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pIn pOut.val.val.1 (retainedMask_size pOut)

theorem word_retained_uniform_pair_bijective
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective (fun v : SourceUniformPositions pIn → AES.Word =>
      fun i : {i : MaskCoordinates pOut.val.val.1 // i ≠ s} => retainedEquiv pOut pIn (0, v) i.val) :=
  retained_uniform_pair_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pIn pOut.val.val.1 (retainedMask_size pOut) s

end AESConcrete.DoubleUniformGeometry
