import AESConcrete.TwoActiveSource
import AESConcrete.ShortenedLineResponse
import AESConcrete.WordCrossZero
import AESMixing.ActivityColumns
import AESMixing.MDSInverse

/-!
# Actual two-active source geometry on retained physical coordinates

The source-plane equivalence is transported through the actual two-
input/two-output MDS restriction. All finite coordinates retain their physical
labels. The result is additive, includes zero values, and supplies the
uniform-coordinate translations and zero intersections needed downstream. No
norm estimate, normalized amplitude, Fourier theorem, physical cap or
inventory extension is supplied here.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and fixed 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoActiveGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoActiveSource
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

set_option maxRecDepth 100000

/-- The original two active input labels, complementary to the inactive mask. -/
def activeMask (p : SelectedSupport 1 2) : Fin 16 := maskComplement p.val.val.2

theorem activeMask_size (p : SelectedSupport 1 2) : maskSize (activeMask p) = 2 := by
  have hz : maskSize p.val.val.2 = 2 := by
    have hp := p.property
    omega
  rw [activeMask, maskComplement_size, hz]

theorem retainedMask_size (p : SelectedSupport 2 4) : maskSize p.val.val.1 = 2 := by
  have hd := p.val.property.2
  norm_num at hd
  exact hd

/-- The other member of a physical retained pair is a singleton subtype. -/
theorem pair_other_card (out : Fin 16) (hout : maskSize out = 2)
    (s : MaskCoordinates out) :
    Fintype.card {i : MaskCoordinates out // i ≠ s} = 1 := by
  rw [Fintype.card_subtype_compl (fun i : MaskCoordinates out => i = s),
    Fintype.card_subtype_eq, maskCoordinates_card, hout]

/-- A mask on two specified distinct physical output labels. -/
def pairMask (i j : Fin 4) : Fin 16 := maskUnion (singletonMask i) (singletonMask j)

theorem pairMask_size (i j : Fin 4) (hij : i ≠ j) : maskSize (pairMask i j) = 2 := by
  have hd : MaskDisjoint (singletonMask i) (singletonMask j) := by
    intro k hki hkj
    exact hij (((singletonMask_bit i k).mp hki).symm.trans
      ((singletonMask_bit j k).mp hkj))
  rw [pairMask, maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]

section ZeroCoordinates
variable {V : Type*} [Zero V]

theorem onPlane_iff_projection_zero (p : SelectedSupport 1 2) (x : Fin 4 → V) :
    OnPlane p x ↔ maskProjection p.val.val.2 x = 0 := by
  constructor
  · intro hx
    funext i
    by_cases hi : maskBit p.val.val.2 i = true
    · simp [maskProjection, hi, hx i hi]
    · simp [maskProjection, hi]
  · intro hx i hi
    have he := congrFun hx i
    simpa only [maskProjection, hi, if_true, Pi.zero_apply] using he

/-- Restriction to the original active input labels is an exact equivalence. -/
def activeCoordinatesEquiv (p : SelectedSupport 1 2) :
    {x : Fin 4 → V // OnPlane p x} ≃ (MaskCoordinates (activeMask p) → V) where
  toFun x := restrictCoordinates (activeMask p) x.val
  invFun w := ⟨extendCoordinates (activeMask p) w, by
    apply (onPlane_iff_projection_zero p _).mpr
    exact (maskProjection_complement_iff p.val.val.2 _).mp
      (extend_supported (activeMask p) w)⟩
  left_inv x := by
    apply Subtype.ext
    change extendCoordinates (activeMask p)
      (restrictCoordinates (activeMask p) x.val) = x.val
    rw [extend_restrict]
    exact (maskProjection_complement_iff p.val.val.2 x.val).mpr
      ((onPlane_iff_projection_zero p x.val).mp x.property)
  right_inv w := restrict_extend (activeMask p) w

/-- Both original source coordinates remain present in this equivalence. -/
def sourceActiveEquiv (p : SelectedSupport 1 2) :
    (V × V) ≃ (MaskCoordinates (activeMask p) → V) :=
  (sourcePlaneEquiv p).trans (activeCoordinatesEquiv p)

theorem extend_sourceActiveEquiv (p : SelectedSupport 1 2) (uv : V × V) :
    extendCoordinates (activeMask p) (sourceActiveEquiv p uv) = source p uv.1 uv.2 := by
  change extendCoordinates (activeMask p)
    (restrictCoordinates (activeMask p) (source p uv.1 uv.2)) = source p uv.1 uv.2
  rw [extend_restrict]
  exact (maskProjection_complement_iff p.val.val.2 _).mpr
    ((onPlane_iff_projection_zero p _).mp (source_onPlane p uv.1 uv.2))

/-- Constant data on an actual singleton mask extends to its physical axis. -/
theorem extend_singleton_constant (r : Fin 4) (v : V) :
    extendCoordinates (singletonMask r) (fun _ => v) = Pi.single r v := by
  funext i
  by_cases hi : i = r
  · subst i
    simp [extendCoordinates, (singletonMask_bit r r).mpr rfl]
  · have hb : maskBit (singletonMask r) i ≠ true := by
      intro hb
      exact hi ((singletonMask_bit r i).mp hb)
    simp [extendCoordinates, hb, hi]

theorem source_residual_axis (p : SelectedSupport 1 2) (u : V) :
    source p u 0 = Pi.single (residualLabel p) u := by
  funext i
  by_cases hi : i = residualLabel p
  · subst i
    simp
  · simp [source, hi]

theorem source_uniform_axis (p : SelectedSupport 1 2) (v : V) :
    source p 0 v = Pi.single (uniformLabel p) v := by
  funext i
  by_cases hi : i = uniformLabel p
  · subst i
    simp
  · simp [source, hi]

end ZeroCoordinates

section AdditiveCoordinates
variable {V : Type*} [AddCommGroup V]

theorem source_zero (p : SelectedSupport 1 2) : source p (0 : V) 0 = 0 := by
  funext i
  simp [source]

theorem source_pair_add (p : SelectedSupport 1 2) (uv uv' : V × V) :
    source p (uv + uv').1 (uv + uv').2 = source p uv.1 uv.2 + source p uv'.1 uv'.2 := by
  funext i
  by_cases hr : i = residualLabel p
  · subst i
    simp
  · by_cases hu : i = uniformLabel p
    · subst i
      simp
    · simp [source, hr, hu]

/-- Restrict actual diffusion of the physical source to an arbitrary output mask. -/
def planeMap (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 1 2)
    (out : Fin 16) (uv : V × V) : MaskCoordinates out → V :=
  fun i => L (source p uv.1 uv.2) i.val

theorem planeMap_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 2) (out : Fin 16) : planeMap L p out (0, 0) = 0 := by
  funext i
  change L (source p (0 : V) 0) i.val = 0
  simp only [source_zero, map_zero, Pi.zero_apply]

theorem planeMap_add (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 2) (out : Fin 16) (uv uv' : V × V) :
    planeMap L p out (uv + uv') = planeMap L p out uv + planeMap L p out uv' := by
  funext i
  change L (source p (uv + uv').1 (uv + uv').2) i.val =
    (L (source p uv.1 uv.2) + L (source p uv'.1 uv'.2)) i.val
  rw [source_pair_add, map_add]

def planeAddHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 2) (out : Fin 16) :
    (V × V) →+ (MaskCoordinates out → V) where
  toFun := planeMap L p out
  map_zero' := planeMap_zero L p out
  map_add' := planeMap_add L p out

theorem planeMap_uniform_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 2) (out : Fin 16) (u v t : V) :
    planeMap L p out (u, v + t) = planeMap L p out (u, v) + planeMap L p out (0, t) := by
  have hp : (u, v) + (0, t) = (u, v + t) := by ext <;> simp
  simpa only [hp] using planeMap_add L p out (u, v) (0, t)

end AdditiveCoordinates

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V]

theorem planeMap_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (hout : maskSize out = 2) :
    Function.Bijective (planeMap L p out) := by
  have hsize : maskSize out = maskSize (activeMask p) :=
    hout.trans (activeMask_size p).symm
  have hb := (mds_restricted_bijective L hL out (activeMask p) hsize).comp
    (sourceActiveEquiv (V := V) p).bijective
  have he : restrictedMap L out (activeMask p) ∘ sourceActiveEquiv p = planeMap L p out := by
    funext uv i
    change L (extendCoordinates (activeMask p) (sourceActiveEquiv p uv)) i.val =
      L (source p uv.1 uv.2) i.val
    rw [extend_sourceActiveEquiv]
  exact he ▸ hb

/-- Actual two-input/two-output MDS equivalence, with original physical labels. -/
def planeEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (hout : maskSize out = 2) :
    (V × V) ≃+ (MaskCoordinates out → V) :=
  { Equiv.ofBijective (planeMap L p out) (planeMap_bijective L hL p out hout) with
    map_add' := planeMap_add L p out }

@[simp]
theorem planeEquiv_apply (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (hout : maskSize out = 2) (uv : V × V) :
    planeEquiv L hL p out hout uv = planeMap L p out uv := rfl

/-- Inverting a retained uniform translation changes only the uniform source value. -/
theorem planeEquiv_symm_uniform_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (hout : maskSize out = 2)
    (x : MaskCoordinates out → V) (t : V) :
    (planeEquiv L hL p out hout).symm (x + planeMap L p out (0, t)) =
      (planeEquiv L hL p out hout).symm x + (0, t) := by
  change (planeEquiv L hL p out hout).symm
    (x + planeEquiv L hL p out hout (0, t)) = _
  rw [map_add, AddEquiv.symm_apply_apply]

theorem planeEquiv_symm_uniform_fst
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (hout : maskSize out = 2)
    (x : MaskCoordinates out → V) (t : V) :
    ((planeEquiv L hL p out hout).symm (x + planeMap L p out (0, t))).1 =
      ((planeEquiv L hL p out hout).symm x).1 := by
  rw [planeEquiv_symm_uniform_translation]
  simp

/-- Evaluation on a physical singleton tuple; its inverse has no normalization. -/
def singletonTupleEquiv (i : Fin 4) : (MaskCoordinates (singletonMask i) → V) ≃ V where
  toFun x := x ⟨i, (singletonMask_bit i i).mpr rfl⟩
  invFun v := fun _ => v
  left_inv x := by
    funext j
    have hj : j = (⟨i, (singletonMask_bit i i).mpr rfl⟩ : MaskCoordinates (singletonMask i)) :=
      Subtype.ext ((singletonMask_bit i j.val).mp j.property)
    exact congrArg x hj.symm
  right_inv _ := rfl

/-- The actual singleton MDS restriction from one input label to one output label. -/
def singletonCoordinateEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) : V ≃ V :=
  ((singletonTupleEquiv r).symm.trans
    (Equiv.ofBijective (restrictedMap L (singletonMask s) (singletonMask r))
      (mds_restricted_bijective L hL _ _
        (by rw [singletonMask_size, singletonMask_size])))).trans (singletonTupleEquiv s)

@[simp]
theorem singletonCoordinateEquiv_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) (v : V) :
    singletonCoordinateEquiv L hL r s v = L (Pi.single r v) s := by
  change L (extendCoordinates (singletonMask r) (fun _ => v)) s = _
  rw [extend_singleton_constant]

theorem singletonCoordinateEquiv_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) :
    singletonCoordinateEquiv L hL r s 0 = 0 := by
  rw [singletonCoordinateEquiv_apply]
  simp

/-- Every retained coordinate sees the full actual uniform translation line. -/
theorem uniform_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (i : Fin 4) :
    Function.Bijective (fun t : V => L (source p 0 t) i) := by
  have he : (fun t : V => L (source p 0 t) i) =
      singletonCoordinateEquiv L hL (uniformLabel p) i := by
    funext t
    rw [singletonCoordinateEquiv_apply, source_uniform_axis]
  rw [he]
  exact (singletonCoordinateEquiv L hL (uniformLabel p) i).bijective

theorem retained_uniform_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (out : Fin 16) (i : MaskCoordinates out) :
    Function.Bijective (fun t : V => planeMap L p out (0, t) i) :=
  uniform_coordinate_bijective L hL p i.val

theorem uniform_zero_and_output_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (uv : V × V) (i : Fin 4)
    (hv : uv.2 = 0) (hz : L (source p uv.1 uv.2) i = 0) : uv = (0, 0) := by
  have hz' : L (Pi.single (residualLabel p) uv.1) i = 0 := by
    simpa only [hv, source_residual_axis] using hz
  have hu : uv.1 = 0 := by
    apply (singletonCoordinateEquiv L hL (residualLabel p) i).injective
    calc
      singletonCoordinateEquiv L hL (residualLabel p) i uv.1 =
          L (Pi.single (residualLabel p) uv.1) i := singletonCoordinateEquiv_apply _ _ _ _ _
      _ = 0 := hz'
      _ = singletonCoordinateEquiv L hL (residualLabel p) i 0 :=
        (singletonCoordinateEquiv_zero L hL (residualLabel p) i).symm
  exact Prod.ext hu hv

/-- Any two distinct output zeros determine the zero point of the actual plane. -/
theorem two_output_zeros_force_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (uv : V × V) (i j : Fin 4) (hij : i ≠ j)
    (hi : L (source p uv.1 uv.2) i = 0)
    (hj : L (source p uv.1 uv.2) j = 0) : uv = (0, 0) := by
  apply (planeMap_bijective L hL p (pairMask i j) (pairMask_size i j hij)).injective
  rw [planeMap_zero]
  funext k
  change L (source p uv.1 uv.2) k.val = 0
  have hk : maskBit (singletonMask i) k.val = true ∨
      maskBit (singletonMask j) k.val = true := by
    simpa only [pairMask, maskUnion_bit, Bool.or_eq_true] using k.property
  rcases hk with hki | hkj
  · have he : k.val = i := (singletonMask_bit i k.val).mp hki
    simpa only [he] using hi
  · have he : k.val = j := (singletonMask_bit j k.val).mp hkj
    simpa only [he] using hj

/-- The two omitted physical coordinates form a second actual information set. -/
theorem omitted_zero_forces_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2) (uv : V × V)
    (hz : ∀ i : MaskCoordinates (maskComplement pOut.val.val.1),
      L (source pIn uv.1 uv.2) i.val = 0) : uv = (0, 0) := by
  have hout : maskSize (maskComplement pOut.val.val.1) = 2 := by
    rw [maskComplement_size, retainedMask_size]
  apply (planeMap_bijective L hL pIn (maskComplement pOut.val.val.1) hout).injective
  rw [planeMap_zero]
  funext i
  exact hz i

end FiniteMDS

/-- Actual AES-word retained pair, indexed by the original residual output mask. -/
def retainedEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2) :
    (AES.Word × AES.Word) ≃+ (MaskCoordinates pOut.val.val.1 → AES.Word) :=
  planeEquiv WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pIn pOut.val.val.1 (retainedMask_size pOut)

theorem word_uniform_zero_and_output_zero
    (p : SelectedSupport 1 2) (uv : AES.Word × AES.Word) (i : Fin 4)
    (hv : uv.2 = 0) (hz : WordCrossZero.wordMixAddEquiv (source p uv.1 uv.2) i = 0) :
    uv = (0, 0) :=
  uniform_zero_and_output_zero WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p uv i hv hz

theorem word_omitted_zero_forces_zero
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2) (uv : AES.Word × AES.Word)
    (hz : ∀ i : MaskCoordinates (maskComplement pOut.val.val.1),
      WordCrossZero.wordMixAddEquiv (source pIn uv.1 uv.2) i.val = 0) : uv = (0, 0) :=
  omitted_zero_forces_zero WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pOut pIn uv hz

theorem word_two_output_zeros_force_zero
    (p : SelectedSupport 1 2) (uv : AES.Word × AES.Word) (i j : Fin 4) (hij : i ≠ j)
    (hi : WordCrossZero.wordMixAddEquiv (source p uv.1 uv.2) i = 0)
    (hj : WordCrossZero.wordMixAddEquiv (source p uv.1 uv.2) j = 0) : uv = (0, 0) :=
  two_output_zeros_force_zero WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p uv i j hij hi hj

end AESConcrete.TwoActiveGeometry
