import AESConcrete.ThreeActiveGeometry

/-!
# The two planes and their intersection line in the three-active source

The `v=0` and one-output-zero planes each have a bijective projection to the
entire physical residual pair. Any two allowed output coordinates are also
information sets. Their intersection is a genuine line: it injects into the
residual pair, so its amplitude has subenergy, and each remaining output is
a bijective line parameter. No equality with the full residual energy is
asserted for the line.

Candidate interfaces only; compilation and independent review are separate.
Constructive mathematics only; no attacks. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct pairs and the fixed
10/14/16 target remain unchanged. Accepted sources and records stay frozen.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveShortening
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeActiveSource
open AESConcrete.ThreeActiveGeometry
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

set_option maxRecDepth 100000

section SourceRestrictions
variable {V : Type*} [Zero V]

/-- The actual plane obtained by setting the uniform source input to zero. -/
abbrev vPlane (p : SelectedSupport 2 3) :=
  {uv : (ResidualPositions p → V) × V // uv.2 = 0}

def vPlaneResidualEquiv (p : SelectedSupport 2 3) :
    vPlane (V := V) p ≃ (ResidualPositions p → V) where
  toFun uv := uv.val.1
  invFun u := ⟨(u, 0), rfl⟩
  left_inv uv := by
    apply Subtype.ext
    exact Prod.ext rfl uv.property.symm
  right_inv _ := rfl

theorem vPlane_residual_bijective (p : SelectedSupport 2 3) :
    Function.Bijective (fun uv : vPlane (V := V) p => uv.val.1) :=
  (vPlaneResidualEquiv p).bijective

/-- Setting `v=0` gives exactly extension from the original residual mask. -/
theorem source_residual_only (p : SelectedSupport 2 3) (u : ResidualPositions p → V) :
    source p u 0 = extendCoordinates p.val.val.1 u := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · simp only [source, extendCoordinates, dif_pos hE]
  · simp [source, extendCoordinates, hE]

theorem source_residual_reconstruct (p : SelectedSupport 2 3) (x : Fin 4 → V)
    (hx : ∀ i, maskBit (maskComplement p.val.val.1) i = true → x i = 0) :
    source p (fun i => x i.val) 0 = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · exact source_residual p _ _ ⟨i, hE⟩
  · have hc : maskBit (maskComplement p.val.val.1) i = true := by
      rw [maskComplement_bit]
      cases hb : maskBit p.val.val.1 i <;> simp_all
    simp [source, hE, hx i hc]

theorem residualComplement_size (p : SelectedSupport 2 3) :
    maskSize (maskComplement p.val.val.1) = 2 := by
  have hd := p.val.property.2
  norm_num at hd
  rw [maskComplement_size, hd]

end SourceRestrictions

/-- The two retained physical labels other than the marked one. -/
def retainedPairMask (p : SelectedSupport 3 4) (s : MaskCoordinates p.val.val.1) : Fin 16 :=
  maskBitsEquiv.symm (fun i => if i = s.val then false else maskBit p.val.val.1 i)

theorem retainedPairMask_bit (p : SelectedSupport 3 4)
    (s : MaskCoordinates p.val.val.1) (i : Fin 4) :
    maskBit (retainedPairMask p s) i =
      if i = s.val then false else maskBit p.val.val.1 i :=
  congrFun (maskBitsEquiv.apply_symm_apply _) i

/-- Index transport only; neither physical output coordinate is reordered. -/
def retainedPairIndexEquiv (p : SelectedSupport 3 4) (s : MaskCoordinates p.val.val.1) :
    MaskCoordinates (retainedPairMask p s) ≃ {i : MaskCoordinates p.val.val.1 // i ≠ s} where
  toFun j := by
    have hne : j.val ≠ s.val := by
      intro he
      have hj := j.property
      rw [retainedPairMask_bit, if_pos he] at hj
      exact Bool.false_ne_true hj
    have hm : maskBit p.val.val.1 j.val = true := by
      have hj := j.property
      rwa [retainedPairMask_bit, if_neg hne] at hj
    exact ⟨⟨j.val, hm⟩, fun he => hne (congrArg Subtype.val he)⟩
  invFun j := ⟨j.val.val, by
    have hne : j.val.val ≠ s.val := fun he => j.property (Subtype.ext he)
    rw [retainedPairMask_bit, if_neg hne]
    exact j.val.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

theorem retainedPairMask_size (p : SelectedSupport 3 4) (s : MaskCoordinates p.val.val.1) :
    maskSize (retainedPairMask p s) = 2 := by
  have hc := Fintype.card_congr (retainedPairIndexEquiv p s)
  rw [maskCoordinates_card, retained_other_card] at hc
  exact hc

theorem retainedPairMask_not_omitted (p : SelectedSupport 3 4)
    (s : MaskCoordinates p.val.val.1) :
    maskBit (retainedPairMask p s) (omittedLabel p) ≠ true := by
  rw [retainedPairMask_bit]
  split_ifs
  · exact Bool.false_ne_true
  · exact omittedLabel_not_retained p

def retainedPairTupleEquiv {V : Type*} (p : SelectedSupport 3 4)
    (s : MaskCoordinates p.val.val.1) :
    (MaskCoordinates (retainedPairMask p s) → V) ≃
      ({i : MaskCoordinates p.val.val.1 // i ≠ s} → V) where
  toFun x := fun i => x ((retainedPairIndexEquiv p s).symm i)
  invFun x := fun i => x (retainedPairIndexEquiv p s i)
  left_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The actual source plane with one imposed physical output zero. -/
abbrev zeroPlane (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 2 3) (z : Fin 4) :=
  {uv : (ResidualPositions p → V) × V // L (source p uv.1 uv.2) z = 0}

/-- Both source and output zero conditions; this is a line, including zero. -/
abbrev intersectionLine (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (z : Fin 4) :=
  {uv : (ResidualPositions p → V) × V // uv.2 = 0 ∧ L (source p uv.1 uv.2) z = 0}

omit [DecidableEq V] in
theorem vPlane_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (out : Fin 16) (hout : maskSize out = 2) :
    Function.Bijective (fun uv : vPlane (V := V) p =>
      fun i : MaskCoordinates out => L (source p uv.val.1 uv.val.2) i.val) := by
  have hsize : maskSize out = maskSize p.val.val.1 := by
    have hd := p.val.property.2
    norm_num at hd
    exact hout.trans hd.symm
  have hb := (mds_restricted_bijective L hL out p.val.val.1 hsize).comp
    (vPlaneResidualEquiv (V := V) p).bijective
  have he : restrictedMap L out p.val.val.1 ∘ vPlaneResidualEquiv p =
      (fun uv : vPlane (V := V) p =>
        fun i : MaskCoordinates out => L (source p uv.val.1 uv.val.2) i.val) := by
    funext uv i
    change L (extendCoordinates p.val.val.1 uv.val.1) i.val =
      L (source p uv.val.1 uv.val.2) i.val
    rw [uv.property, source_residual_only]
  exact he ▸ hb

/-- Actual physical graph: one output zero and the original inactive input. -/
def zeroPlaneEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (z : Fin 4) :
    zeroPlane L p z ≃ ShortenedGraph L (singletonMask z) p.val.val.2 where
  toFun uv := ⟨source p uv.val.1 uv.val.2, by
    constructor
    · intro j hj
      have he : j = z := (singletonMask_bit z j).mp hj
      simpa only [he] using uv.property
    · exact source_onSource p uv.val.1 uv.val.2⟩
  invFun x := ⟨(fun i => x.val i.val, x.val (uniformLabel p)), by
    change L (source p (fun i => x.val i.val) (x.val (uniformLabel p))) z = 0
    rw [source_reconstruct p x.val x.property.2]
    exact x.property.1 z ((singletonMask_bit z z).mpr rfl)⟩
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact source_residual p uv.val.1 uv.val.2 i
    · exact source_uniform p uv.val.1 uv.val.2
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property.2

theorem zeroPlane_shortening (p : SelectedSupport 2 3) (z : Fin 4) :
    maskSize (singletonMask z) + maskSize p.val.val.2 = 2 := by
  rw [singletonMask_size]
  have hp := p.property
  omega

/-- The complete residual pair has exactly one point on the output-zero plane. -/
theorem zeroPlane_residual_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z : Fin 4) :
    Function.Bijective (fun uv : zeroPlane L p z => uv.val.1) := by
  have hsize : maskSize (singletonMask z) + maskSize p.val.val.2 +
      maskSize p.val.val.1 = 4 := by
    have hs := zeroPlane_shortening p z
    have hd := p.val.property.2
    norm_num at hd
    omega
  have hb := (RestrictedMDSCoordinates.input_projection_bijective L hL
    (singletonMask z) p.val.val.2 p.val.val.1 p.val.property.1 hsize).comp
      (zeroPlaneEquiv L p z).bijective
  change Function.Bijective
    (fun uv : zeroPlane L p z => fun i : ResidualPositions p =>
      source p uv.val.1 uv.val.2 i.val) at hb
  simpa only [source_residual] using hb

def zeroPlaneResidualEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z : Fin 4) :
    zeroPlane L p z ≃ (ResidualPositions p → V) :=
  Equiv.ofBijective (fun uv => uv.val.1) (zeroPlane_residual_bijective L hL p z)

/-- Any two physical outputs outside the imposed zero parameterize the plane. -/
theorem zeroPlane_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z : Fin 4) (out : Fin 16)
    (hout : maskSize out = 2) (hzout : maskBit out z ≠ true) :
    Function.Bijective (fun uv : zeroPlane L p z =>
      fun i : MaskCoordinates out => L (source p uv.val.1 uv.val.2) i.val) := by
  have hr : MaskDisjoint (singletonMask z) out := by
    intro i hi
    have hiz : i = z := (singletonMask_bit z i).mp hi
    simpa only [hiz] using hzout
  have hsize : maskSize (singletonMask z) + maskSize p.val.val.2 + maskSize out = 4 := by
    rw [zeroPlane_shortening, hout]
  exact (RestrictedMDSCoordinates.output_projection_bijective L hL
    (singletonMask z) p.val.val.2 out hr hsize).comp (zeroPlaneEquiv L p z).bijective

/-- Exact physical line with two original residual-complement input zeros. -/
def intersectionLineEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 2 3) (z : Fin 4) :
    intersectionLine L p z ≃
      ShortenedGraph L (singletonMask z) (maskComplement p.val.val.1) where
  toFun uv := ⟨source p uv.val.1 uv.val.2, by
    constructor
    · intro j hj
      have he : j = z := (singletonMask_bit z j).mp hj
      simpa only [he] using uv.property.2
    · intro j hj
      have hE : maskBit p.val.val.1 j ≠ true := by
        rw [maskComplement_bit] at hj
        cases hb : maskBit p.val.val.1 j <;> simp_all
      simp [source, hE, uv.property.1]⟩
  invFun x := ⟨(fun i => x.val i.val, 0), by
    refine ⟨rfl, ?_⟩
    change L (source p (fun i => x.val i.val) 0) z = 0
    rw [source_residual_reconstruct p x.val x.property.2]
    exact x.property.1 z ((singletonMask_bit z z).mpr rfl)⟩
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact source_residual p uv.val.1 uv.val.2 i
    · exact uv.property.1.symm
  right_inv x := by
    apply Subtype.ext
    exact source_residual_reconstruct p x.val x.property.2

theorem intersectionLine_shortening (p : SelectedSupport 2 3) (z : Fin 4) :
    maskSize (singletonMask z) + maskSize (maskComplement p.val.val.1) = 3 := by
  rw [singletonMask_size, residualComplement_size]

omit [Fintype V] [DecidableEq V] in
/-- The line has at most one source point for each full residual pair. -/
theorem intersectionLine_residual_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 2 3) (z : Fin 4) :
    Function.Injective (fun uv : intersectionLine L p z => uv.val.1) := by
  intro uv uv' he
  apply Subtype.ext
  exact Prod.ext he (uv.property.1.trans uv'.property.1.symm)

/-- Each original residual coordinate separately parameterizes the line. -/
theorem intersectionLine_residual_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z : Fin 4) (i : ResidualPositions p) :
    Function.Bijective (fun uv : intersectionLine L p z => uv.val.1 i) := by
  have hi : maskBit (maskComplement p.val.val.1) i.val ≠ true := by
    rw [maskComplement_bit, i.property]
    decide
  have hb := (ShortenedLineResponse.input_coordinate_bijective L hL
    (singletonMask z) (maskComplement p.val.val.1) (intersectionLine_shortening p z)
    i.val hi).comp (intersectionLineEquiv L p z).bijective
  change Function.Bijective
    (fun uv : intersectionLine L p z => source p uv.val.1 uv.val.2 i.val) at hb
  simpa only [source_residual] using hb

/-- Each physical output other than the imposed zero parameterizes the line. -/
theorem intersectionLine_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z k : Fin 4) (hk : k ≠ z) :
    Function.Bijective (fun uv : intersectionLine L p z =>
      L (source p uv.val.1 uv.val.2) k) := by
  have hkbit : maskBit (singletonMask z) k ≠ true := by
    intro hkbit
    exact hk ((singletonMask_bit z k).mp hkbit)
  exact (ShortenedLineResponse.output_coordinate_bijective L hL
    (singletonMask z) (maskComplement p.val.val.1) (intersectionLine_shortening p z)
    k hkbit).comp (intersectionLineEquiv L p z).bijective

/-- Exact counting energy on `v=0`, with the same arbitrary signed `h`. -/
theorem vPlane_residual_energy (p : SelectedSupport 2 3)
    (h : (ResidualPositions p → V) → ℝ) :
    (∑ uv : vPlane (V := V) p, h uv.val.1 ^ 2) = ∑ u, h u ^ 2 :=
  (vPlaneResidualEquiv p).sum_comp (fun u => h u ^ 2)

/-- Exact counting energy on the output-zero plane, without a source-fiber loss. -/
theorem zeroPlane_residual_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 2 3) (z : Fin 4) (h : (ResidualPositions p → V) → ℝ) :
    (∑ uv : zeroPlane L p z, h uv.val.1 ^ 2) = ∑ u, h u ^ 2 :=
  (zeroPlaneResidualEquiv L hL p z).sum_comp (fun u => h u ^ 2)

/-- Only a restriction inequality on the intersection line. Zero is included;
no condition on `h(0)` or pointwise bound on `h` is needed. -/
theorem intersectionLine_residual_subenergy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 2 3) (z : Fin 4)
    (h : (ResidualPositions p → V) → ℝ) :
    (∑ uv : intersectionLine L p z, h uv.val.1 ^ 2) ≤ ∑ u, h u ^ 2 := by
  classical
  let f : intersectionLine L p z → (ResidualPositions p → V) := fun uv => uv.val.1
  have hf : Function.Injective f := intersectionLine_residual_injective L p z
  have he : (∑ u ∈ Finset.univ.image f, h u ^ 2) =
      ∑ uv : intersectionLine L p z, h (f uv) ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hf hab
  change (∑ uv : intersectionLine L p z, h (f uv) ^ 2) ≤ ∑ u, h u ^ 2
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => sq_nonneg _)

omit [DecidableEq V] in
/-- The `v=0` plane projection in the original retained-label subtype API. -/
theorem vPlane_retained_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective (fun uv : vPlane (V := V) pIn =>
      fun i : {j : MaskCoordinates pOut.val.val.1 // j ≠ s} =>
        sourceMap L pIn pOut.val.val.1 uv.val i.val) := by
  have hb := (retainedPairTupleEquiv (V := V) pOut s).bijective.comp
    (vPlane_output_bijective L hL pIn (retainedPairMask pOut s)
      (retainedPairMask_size pOut s))
  exact hb

/-- The omitted-output-zero plane in the same retained-label subtype API. -/
theorem zeroPlane_retained_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective (fun uv : zeroPlane L pIn (omittedLabel pOut) =>
      fun i : {j : MaskCoordinates pOut.val.val.1 // j ≠ s} =>
        sourceMap L pIn pOut.val.val.1 uv.val i.val) := by
  have hb := (retainedPairTupleEquiv (V := V) pOut s).bijective.comp
    (zeroPlane_output_bijective L hL pIn (omittedLabel pOut) (retainedPairMask pOut s)
      (retainedPairMask_size pOut s) (retainedPairMask_not_omitted pOut s))
  exact hb

/-- Each retained output parameterizes the intersection line. -/
theorem intersectionLine_retained_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (s : MaskCoordinates pOut.val.val.1) :
    Function.Bijective
      (fun uv : intersectionLine L pIn (omittedLabel pOut) =>
        sourceMap L pIn pOut.val.val.1 uv.val s) :=
  intersectionLine_output_bijective L hL pIn (omittedLabel pOut) s.val
    (retained_ne_omitted pOut s)

end Generic

theorem word_zeroPlane_residual_bijective (p : SelectedSupport 2 3) (z : Fin 4) :
    Function.Bijective (fun uv : zeroPlane WordCrossZero.wordMixAddEquiv.toAddMonoidHom p z =>
      uv.val.1) :=
  zeroPlane_residual_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p z

theorem word_zeroPlane_output_bijective (p : SelectedSupport 2 3) (z : Fin 4)
    (out : Fin 16) (hout : maskSize out = 2) (hzout : maskBit out z ≠ true) :
    Function.Bijective (fun uv : zeroPlane WordCrossZero.wordMixAddEquiv.toAddMonoidHom p z =>
      fun i : MaskCoordinates out => WordCrossZero.wordMixAddEquiv (source p uv.val.1 uv.val.2) i.val) :=
  zeroPlane_output_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p z out hout hzout

theorem word_intersectionLine_output_bijective (p : SelectedSupport 2 3) (z k : Fin 4)
    (hk : k ≠ z) :
    Function.Bijective (fun uv : intersectionLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom p z =>
      WordCrossZero.wordMixAddEquiv (source p uv.val.1 uv.val.2) k) :=
  intersectionLine_output_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p z k hk

end AESConcrete.ThreeActiveShortening
