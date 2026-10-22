import AESConcrete.ThreeActiveSource
import AESConcrete.TwoActiveGeometry
import AESConcrete.RestrictedMDSCoordinates

/-!
# Actual three-input/three-output additive MDS geometry

The full source is three-dimensional, with a physical residual pair and one
uniform input. Its retained triple is an additive information set. Uniform
translations preserve the residual pair under the inverse map, and every
physical output sees that translation line bijectively. No energy estimate or
Fourier-support claim is bundled into these geometry interfaces.

The fixed independent uniform retained-key model, whitening, omitted final
MixColumns, ordered-distinct pairs and 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeActiveSource

set_option maxRecDepth 100000

def activeMask (p : SelectedSupport 2 3) : Fin 16 := maskComplement p.val.val.2

theorem activeMask_size (p : SelectedSupport 2 3) : maskSize (activeMask p) = 3 := by
  have hz : maskSize p.val.val.2 = 1 := by
    have hp := p.property
    omega
  rw [activeMask, maskComplement_size, hz]

theorem retainedMask_size (p : SelectedSupport 3 4) : maskSize p.val.val.1 = 3 := by
  have hd := p.val.property.2
  norm_num at hd
  exact hd

theorem retainedCoordinates_card (p : SelectedSupport 3 4) :
    Fintype.card (MaskCoordinates p.val.val.1) = 3 := by
  rw [maskCoordinates_card, retainedMask_size]

theorem retained_other_card (p : SelectedSupport 3 4) (s : MaskCoordinates p.val.val.1) :
    Fintype.card {i : MaskCoordinates p.val.val.1 // i ≠ s} = 2 := by
  rw [Fintype.card_subtype_compl (fun i : MaskCoordinates p.val.val.1 => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

abbrev OmittedPositions (p : SelectedSupport 3 4) :=
  MaskCoordinates (maskComplement p.val.val.1)

theorem omittedPositions_card (p : SelectedSupport 3 4) :
    Fintype.card (OmittedPositions p) = 1 := by
  change Fintype.card (MaskCoordinates (maskComplement p.val.val.1)) = 1
  rw [maskCoordinates_card, maskComplement_size, retainedMask_size]

def omittedIndexEquiv (p : SelectedSupport 3 4) : OmittedPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [omittedPositions_card]; simp)

def omittedPosition (p : SelectedSupport 3 4) : OmittedPositions p :=
  (omittedIndexEquiv p).symm 0

def omittedLabel (p : SelectedSupport 3 4) : Fin 4 := (omittedPosition p).val

theorem omittedPosition_unique (p : SelectedSupport 3 4) (i : OmittedPositions p) :
    i = omittedPosition p := by
  apply (omittedIndexEquiv p).injective
  exact Subsingleton.elim _ _

theorem omittedLabel_not_retained (p : SelectedSupport 3 4) :
    maskBit p.val.val.1 (omittedLabel p) ≠ true := by
  have h : maskBit (maskComplement p.val.val.1) (omittedLabel p) = true :=
    (omittedPosition p).property
  rw [maskComplement_bit] at h
  cases hb : maskBit p.val.val.1 (omittedLabel p) <;> simp_all

theorem retained_ne_omitted (p : SelectedSupport 3 4) (i : MaskCoordinates p.val.val.1) :
    i.val ≠ omittedLabel p := by
  intro hi
  exact omittedLabel_not_retained p (hi ▸ i.property)

section ZeroCoordinates
variable {V : Type*} [Zero V]

theorem onSource_iff_projection_zero (p : SelectedSupport 2 3) (x : Fin 4 → V) :
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

def activeCoordinatesEquiv (p : SelectedSupport 2 3) :
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

def sourceActiveEquiv (p : SelectedSupport 2 3) :
    ((ResidualPositions p → V) × V) ≃ (MaskCoordinates (activeMask p) → V) :=
  (ThreeActiveSource.sourceEquiv p).trans (activeCoordinatesEquiv p)

theorem extend_sourceActiveEquiv (p : SelectedSupport 2 3)
    (uv : (ResidualPositions p → V) × V) :
    extendCoordinates (activeMask p) (sourceActiveEquiv p uv) = source p uv.1 uv.2 := by
  change extendCoordinates (activeMask p)
    (restrictCoordinates (activeMask p) (source p uv.1 uv.2)) = source p uv.1 uv.2
  rw [extend_restrict]
  exact (maskProjection_complement_iff p.val.val.2 _).mpr
    ((onSource_iff_projection_zero p _).mp (source_onSource p uv.1 uv.2))

theorem source_uniform_axis (p : SelectedSupport 2 3) (v : V) :
    source p 0 v = Pi.single (uniformLabel p) v := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · have hi : i ≠ uniformLabel p := by
      intro hi
      exact uniformLabel_not_residual p (hi ▸ hE)
    simp [source, hE, hi]
  · by_cases hi : i = uniformLabel p
    · subst i
      simp
    · simp [source, hE, hi]

end ZeroCoordinates

section AdditiveCoordinates
variable {V : Type*} [AddCommGroup V]

theorem source_zero (p : SelectedSupport 2 3) : source p (0 : ResidualPositions p → V) 0 = 0 := by
  funext i
  simp [source]

theorem source_pair_add (p : SelectedSupport 2 3)
    (uv uv' : (ResidualPositions p → V) × V) :
    source p (uv + uv').1 (uv + uv').2 = source p uv.1 uv.2 + source p uv'.1 uv'.2 := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · simp [source, hE]
  · by_cases hu : i = uniformLabel p
    · subst i
      simp
    · simp [source, hE, hu]

/-- Actual diffusion restricted to the original physical output mask. -/
def sourceMap (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 2 3)
    (out : Fin 16) (uv : (ResidualPositions p → V) × V) : MaskCoordinates out → V :=
  fun i => L (source p uv.1 uv.2) i.val

theorem sourceMap_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (out : Fin 16) : sourceMap L p out (0, 0) = 0 := by
  funext i
  change L (source p (0 : ResidualPositions p → V) 0) i.val = 0
  simp only [source_zero, map_zero, Pi.zero_apply]

theorem sourceMap_add (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (out : Fin 16) (uv uv' : (ResidualPositions p → V) × V) :
    sourceMap L p out (uv + uv') = sourceMap L p out uv + sourceMap L p out uv' := by
  funext i
  change L (source p (uv + uv').1 (uv + uv').2) i.val =
    (L (source p uv.1 uv.2) + L (source p uv'.1 uv'.2)) i.val
  rw [source_pair_add, map_add]

def sourceAddHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (out : Fin 16) :
    ((ResidualPositions p → V) × V) →+ (MaskCoordinates out → V) where
  toFun := sourceMap L p out
  map_zero' := sourceMap_zero L p out
  map_add' := sourceMap_add L p out

theorem sourceMap_uniform_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (out : Fin 16) (u : ResidualPositions p → V) (v t : V) :
    sourceMap L p out (u, v + t) =
      sourceMap L p out (u, v) + sourceMap L p out (0, t) := by
  have hp : (u, v) + (0, t) = (u, v + t) := by ext <;> simp
  simpa only [hp] using sourceMap_add L p out (u, v) (0, t)

end AdditiveCoordinates

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V]

theorem sourceMap_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 3) :
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

/-- The actual three-dimensional source and a three-output information set. -/
def sourceDiffusionEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 3) :
    ((ResidualPositions p → V) × V) ≃+ (MaskCoordinates out → V) :=
  { Equiv.ofBijective (sourceMap L p out) (sourceMap_bijective L hL p out hout) with
    map_add' := sourceMap_add L p out }

@[simp]
theorem sourceDiffusionEquiv_apply (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 3)
    (uv : (ResidualPositions p → V) × V) :
    sourceDiffusionEquiv L hL p out hout uv = sourceMap L p out uv := rfl

theorem sourceDiffusionEquiv_symm_uniform_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 3)
    (x : MaskCoordinates out → V) (t : V) :
    (sourceDiffusionEquiv L hL p out hout).symm (x + sourceMap L p out (0, t)) =
      (sourceDiffusionEquiv L hL p out hout).symm x + (0, t) := by
  change (sourceDiffusionEquiv L hL p out hout).symm
    (x + sourceDiffusionEquiv L hL p out hout (0, t)) = _
  rw [map_add, AddEquiv.symm_apply_apply]

theorem sourceDiffusionEquiv_symm_uniform_fst
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 3)
    (x : MaskCoordinates out → V) (t : V) :
    ((sourceDiffusionEquiv L hL p out hout).symm
      (x + sourceMap L p out (0, t))).1 =
        ((sourceDiffusionEquiv L hL p out hout).symm x).1 := by
  rw [sourceDiffusionEquiv_symm_uniform_translation]
  simp

theorem uniform_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (i : Fin 4) :
    Function.Bijective (fun t : V => L (source p 0 t) i) := by
  have he : (fun t : V => L (source p 0 t) i) =
      TwoActiveGeometry.singletonCoordinateEquiv L hL (uniformLabel p) i := by
    funext t
    rw [TwoActiveGeometry.singletonCoordinateEquiv_apply, source_uniform_axis]
  rw [he]
  exact (TwoActiveGeometry.singletonCoordinateEquiv L hL (uniformLabel p) i).bijective

theorem retained_uniform_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (i : MaskCoordinates out) :
    Function.Bijective (fun t : V => sourceMap L p out (0, t) i) :=
  uniform_coordinate_bijective L hL p i.val

end FiniteMDS

def retainedEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3) :
    ((ResidualPositions pIn → AES.Word) × AES.Word) ≃+
      (MaskCoordinates pOut.val.val.1 → AES.Word) :=
  sourceDiffusionEquiv WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pIn pOut.val.val.1 (retainedMask_size pOut)

theorem word_uniform_coordinate_bijective (p : SelectedSupport 2 3) (i : Fin 4) :
    Function.Bijective (fun t : AES.Word => WordCrossZero.wordMixAddEquiv (source p 0 t) i) :=
  uniform_coordinate_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p i

end AESConcrete.ThreeActiveGeometry
