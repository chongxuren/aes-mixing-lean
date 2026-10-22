import AESConcrete.DoubleUniformShortening
import AESConcrete.InvariantSubspaceEnergy

/-!
# Retained embeddings and ambient zero extension of the omitted-zero plane

The source plane embeds additively in the actual retained triple. Its uniform
translations are the physical residual-zero shortened line. Their singleton
projections are bijective; they preserve the signed residual amplitude. The
zero extension is invariant on the entire retained ambient space, including
points outside the image. Source geometry, counting, and Fourier estimates
remain distinct interfaces.

Candidate only; compilation and independent review are separate. Constructive
mathematics only; no attacks. The fixed independent-key, whitening, omitted
final MixColumns, ordered-distinct and 10/14/16 model is unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformPlaneGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
open AESConcrete.DoubleUniformShortening
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

section Additive
variable {V : Type*} [AddCommGroup V]

/-- Restriction of the actual retained diffusion homomorphism to the plane. -/
def planeRetainedHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) :
    zeroPlane L p z →+ (MaskCoordinates out → V) :=
  (sourceAddHom L p out).comp (zeroPlaneSubgroup L p z).subtype

@[simp]
theorem planeRetainedHom_apply (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) (uv : zeroPlane L p z)
    (i : MaskCoordinates out) :
    planeRetainedHom L p z out uv i = L (source p uv.val.1 uv.val.2) i.val := rfl

def planeAmplitude (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (h : V → ℝ) : zeroPlane L p z → ℝ :=
  fun uv => h uv.val.1

theorem planeAmplitude_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (h : V → ℝ)
    (uv : zeroPlane L p z) (c : uniformLine L p z) :
    planeAmplitude L p z h (uv + uniformLineTranslation L p z c) =
      planeAmplitude L p z h uv := by
  unfold planeAmplitude
  rw [plane_residual_translation]

end Additive

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem planeRetainedHom_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) (hout : maskSize out = 3) :
    Function.Injective (planeRetainedHom L p z out) := by
  intro uv uv' he
  apply Subtype.ext
  exact (sourceMap_bijective L hL p out hout).1 he

/-- The actual retained plane is an additive subgroup of the full triple. -/
def retainedPlaneSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) :
    AddSubgroup (MaskCoordinates out → V) := (planeRetainedHom L p z out).range

/-- The actual correlated uniform line in the retained plane. -/
def retainedUniformLineSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) :
    AddSubgroup (MaskCoordinates out → V) :=
  ((planeRetainedHom L p z out).comp (uniformLineTranslation L p z)).range

omit [Fintype V] [DecidableEq V] in
theorem retainedUniformLine_le_plane (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) :
    retainedUniformLineSubgroup L p z out ≤ retainedPlaneSubgroup L p z out := by
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  exact ⟨uniformLineTranslation L p z c, rfl⟩

theorem retained_uniformLine_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective (fun c : uniformLine L pIn (omittedLabel pOut) =>
      planeRetainedHom L pIn (omittedLabel pOut) pOut.val.val.1
        (uniformLineTranslation L pIn (omittedLabel pOut) c) s) :=
  uniformLine_output_bijective L hL pIn (omittedLabel pOut) s.val
    (retained_ne_omitted pOut s)

theorem zeroPlane_retained_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective (fun uv : zeroPlane L pIn (omittedLabel pOut) =>
      fun i : {j : MaskCoordinates pOut.val.val.1 // j ≠ s} =>
        planeRetainedHom L pIn (omittedLabel pOut) pOut.val.val.1 uv i.val) := by
  have hnot : maskBit (retainedPairMask pOut.val.val.1 s) (omittedLabel pOut) ≠ true := by
    intro he
    exact omittedLabel_not_retained pOut
      ((retainedPairMask_bit pOut.val.val.1 s (omittedLabel pOut)).mp he).1
  exact (retainedPairCoordinatesEquiv (V := V) pOut.val.val.1 s).bijective.comp
    (zeroPlane_output_bijective L hL pIn (omittedLabel pOut)
      (retainedPairMask pOut.val.val.1 s)
      (retainedPairMask_size pOut.val.val.1 (retainedMask_size pOut) s) hnot)

/-- Zero extension over every ambient retained triple, with no multiplicity. -/
def planeZeroExtension (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) (h : V → ℝ) :
    (MaskCoordinates out → V) → ℝ :=
  InvariantSubspaceEnergy.zeroExtend (planeRetainedHom L p z out) (planeAmplitude L p z h)

omit [DecidableEq V] in
theorem planeZeroExtension_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) (h : V → ℝ)
    (x : MaskCoordinates out → V) (c : uniformLine L p z) :
    planeZeroExtension L p z out h
      (x + planeRetainedHom L p z out (uniformLineTranslation L p z c)) =
        planeZeroExtension L p z out h x := by
  exact InvariantSubspaceEnergy.zeroExtend_translation (planeRetainedHom L p z out)
    (uniformLineTranslation L p z) (planeAmplitude L p z h)
    (planeAmplitude_translation L p z h) x c

theorem planeZeroExtension_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16) (hout : maskSize out = 3)
    (j : SourceUniformPositions p) (h : V → ℝ) :
    (∑ x, planeZeroExtension L p z out h x ^ 2) =
      (Fintype.card V : ℝ) * ∑ u : V, h u ^ 2 := by
  rw [planeZeroExtension, InvariantSubspaceEnergy.zeroExtend_energy
    (planeRetainedHom L p z out) (planeRetainedHom_injective L hL p z out hout)]
  exact zeroPlane_residual_energy L hL p z j h

end FiniteMDS

section SourceZeroPlanes
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def sourceZeroPlaneRetainedHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p) (out : Fin 16) :
    sourceZeroPlane (V := V) p j →+ (MaskCoordinates out → V) :=
  (sourceAddHom L p out).comp (sourceZeroPlaneSubgroup p j).subtype

omit [DecidableEq V] in
theorem sourceZeroPlaneRetainedHom_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p)
    (out : Fin 16) (hout : maskSize out = 3) :
    Function.Injective (sourceZeroPlaneRetainedHom L p j out) := by
  intro uv uv' he
  apply Subtype.ext
  exact (sourceMap_bijective L hL p out hout).1 he

/-- A residual input and any physical output parameterize the source-zero plane. -/
theorem sourceZeroPlane_mixed_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p) (i : Fin 4) :
    Function.Bijective (fun uv : sourceZeroPlane (V := V) p j =>
      (uv.val.1, L (source p uv.val.1 uv.val.2) i)) := by
  have hr : MaskDisjoint 0 (singletonMask i) := by
    intro k hk _
    exact (empty_mask_coordinate ⟨k, hk⟩).elim
  have hz : MaskDisjoint (sourceZeroInputMask p j) (singletonMask (residualLabel p)) := by
    intro k hk hs
    exact sourceZeroInputMask_not_residual p j
      (((ShortenedLineResponse.singletonMask_bit (residualLabel p) k).mp hs) ▸ hk)
  have hs : maskSize (0 : Fin 16) + maskSize (sourceZeroInputMask p j) +
      maskSize (singletonMask i) + maskSize (singletonMask (residualLabel p)) = 4 := by
    rw [show maskSize (0 : Fin 16) = 0 by decide, sourceZeroInputMask_size,
      ShortenedLineResponse.singletonMask_size, ShortenedLineResponse.singletonMask_size]
  let e := ((sourceZeroPlaneEquiv L p j).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv L hL 0 (sourceZeroInputMask p j)
      (singletonMask i) (singletonMask (residualLabel p)) hr hz hs)).trans
        (Equiv.prodCongr (singletonTupleEquiv (residualLabel p)) (singletonTupleEquiv i))
  have hb := e.bijective
  change Function.Bijective (fun uv : sourceZeroPlane (V := V) p j =>
    (source p uv.val.1 uv.val.2 (residualLabel p), L (source p uv.val.1 uv.val.2) i)) at hb
  simpa only [source_residual] using hb

def sourceZeroPlaneMixedEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p) (i : Fin 4) :
    sourceZeroPlane (V := V) p j ≃ V × V :=
  Equiv.ofBijective (fun uv => (uv.val.1, L (source p uv.val.1 uv.val.2) i))
    (sourceZeroPlane_mixed_bijective L hL p j i)

/-- Only the other original uniform input varies; the residual value is zero. -/
def sourceZeroPlaneTranslation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j)
    (t : V) : sourceZeroPlane (V := V) p j :=
  (sourceZeroPlaneParameterEquiv L hL p j k hkj).symm (0,t)

theorem sourceZeroPlaneTranslation_residual
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j) (t : V) :
    (sourceZeroPlaneTranslation L hL p j k hkj t).val.1 = 0 :=
  congrArg Prod.fst ((sourceZeroPlaneParameterEquiv L hL p j k hkj).apply_symm_apply (0,t))

theorem sourceZeroPlaneTranslation_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j) (i : Fin 4) :
    Function.Bijective (fun t : V => L (source p
      (sourceZeroPlaneTranslation L hL p j k hkj t).val.1
      (sourceZeroPlaneTranslation L hL p j k hkj t).val.2) i) :=
  RestrictedMDSCoordinates.section_bijective
    (sourceZeroPlaneParameterEquiv L hL p j k hkj)
    (sourceZeroPlaneMixedEquiv L hL p j i) (fun _ => rfl) (0 : V)

theorem sourceZeroPlaneAmplitude_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j)
    (h : V → ℝ) (uv : sourceZeroPlane (V := V) p j) (t : V) :
    h (uv + sourceZeroPlaneTranslation L hL p j k hkj t).val.1 = h uv.val.1 := by
  change h (uv.val.1 + (sourceZeroPlaneTranslation L hL p j k hkj t).val.1) = h uv.val.1
  rw [sourceZeroPlaneTranslation_residual, add_zero]

def sourceZeroPlaneZeroExtension (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p) (out : Fin 16) (h : V → ℝ) :
    (MaskCoordinates out → V) → ℝ :=
  InvariantSubspaceEnergy.zeroExtend (sourceZeroPlaneRetainedHom L p j out)
    (fun uv => h uv.val.1)

theorem sourceZeroPlaneZeroExtension_translation
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j)
    (out : Fin 16) (h : V → ℝ) (x : MaskCoordinates out → V) (t : V) :
    sourceZeroPlaneZeroExtension L p j out h
      (x + sourceZeroPlaneRetainedHom L p j out
        (sourceZeroPlaneTranslation L hL p j k hkj t)) =
      sourceZeroPlaneZeroExtension L p j out h x :=
  InvariantSubspaceEnergy.zeroExtend_translation (sourceZeroPlaneRetainedHom L p j out)
    (sourceZeroPlaneTranslation L hL p j k hkj) (fun uv => h uv.val.1)
    (sourceZeroPlaneAmplitude_translation L hL p j k hkj h) x t

theorem sourceZeroPlaneZeroExtension_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j)
    (out : Fin 16) (hout : maskSize out = 3) (h : V → ℝ) :
    (∑ x, sourceZeroPlaneZeroExtension L p j out h x ^ 2) =
      (Fintype.card V : ℝ) * ∑ u : V, h u ^ 2 := by
  rw [sourceZeroPlaneZeroExtension, InvariantSubspaceEnergy.zeroExtend_energy
    (sourceZeroPlaneRetainedHom L p j out)
    (sourceZeroPlaneRetainedHom_injective L hL p j out hout)]
  exact sourceZeroPlane_residual_energy L hL p j k hkj h

omit [DecidableEq V] in
/-- The third double-zero line is exactly the original residual axis. -/
theorem residualLine_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (i : Fin 4) :
    Function.Bijective (fun u : V => L (source p u 0) i) := by
  have he : (fun u : V => L (source p u 0) i) =
      TwoActiveGeometry.singletonCoordinateEquiv L hL (residualLabel p) i := by
    funext u
    rw [TwoActiveGeometry.singletonCoordinateEquiv_apply, source_residual_axis]
  rw [he]
  exact (TwoActiveGeometry.singletonCoordinateEquiv L hL (residualLabel p) i).bijective

omit [DecidableEq V] in
/-- The triple zero restriction collapses to the zero source, independently of h(0). -/
theorem residualLine_eq_zero_of_output_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (i : Fin 4) (u : V)
    (hu : L (source p u 0) i = 0) : u = 0 := by
  apply (residualLine_output_bijective L hL p i).1
  change L (source p u 0) i = L (source p 0 0) i
  rw [hu, source_zero, map_zero, Pi.zero_apply]

end SourceZeroPlanes
end AESConcrete.DoubleUniformPlaneGeometry
