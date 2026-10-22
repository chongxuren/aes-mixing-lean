import AESConcrete.CoupledLineAverage
import AESConcrete.DoubleUniformGeometry
import AESConcrete.RestrictedMDSCoordinates

/-!
# Actual retained fibers with a joint residual pair

The source has the two physical residual labels of `SelectedSupport 2 4` and
their two ORIGINAL uniform complements. The amplitude on the residual pair is
arbitrary and signed. No factorization or centering is used.

The averaging interface is supplied by `CoupledLineAverage`. Geometry, exact
counting identities and translation invariance are separate interfaces below.
No Fourier estimate or physical cap is asserted.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairFiber
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

set_option maxRecDepth 100000

abbrev ResidualPositions (p : SelectedSupport 2 4) := MaskCoordinates p.val.val.1
abbrev RetainedPositions (p : SelectedSupport 3 4) := MaskCoordinates p.val.val.1

/-- These are the original nonresidual physical input labels. -/
def originalUniformMask (p : SelectedSupport 2 4) : Fin 16 :=
  maskComplement p.val.val.1

abbrev OriginalUniformPositions (p : SelectedSupport 2 4) :=
  MaskCoordinates (originalUniformMask p)

theorem residualMask_size (p : SelectedSupport 2 4) : maskSize p.val.val.1 = 2 := by
  have hd := p.val.property.2
  norm_num at hd
  exact hd

theorem inactiveMask_size (p : SelectedSupport 2 4) : maskSize p.val.val.2 = 0 := by
  have hp := p.property
  omega

theorem inactiveLabel_not (p : SelectedSupport 2 4) (i : Fin 4) :
    maskBit p.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates p.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inactiveMask_size] at hc
  omega

theorem originalUniformMask_bit (p : SelectedSupport 2 4) (i : Fin 4) :
    maskBit (originalUniformMask p) i = true ↔ maskBit p.val.val.1 i ≠ true := by
  rw [originalUniformMask, maskComplement_bit]
  cases hb : maskBit p.val.val.1 i <;> simp

/-- The complement labels are exactly the actual multi-uniform source labels. -/
def originalUniformPositionEquiv (p : SelectedSupport 2 4) :
    MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1 ≃
      OriginalUniformPositions p where
  toFun i := ⟨i.val.val, (originalUniformMask_bit p i.val.val).mpr i.val.property⟩
  invFun i := ⟨⟨i.val, (originalUniformMask_bit p i.val).mp i.property⟩,
    inactiveLabel_not p i.val⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

theorem originalUniformMask_size (p : SelectedSupport 2 4) :
    maskSize (originalUniformMask p) = 2 := by
  rw [originalUniformMask, maskComplement_size, residualMask_size]

theorem residualPositions_card (p : SelectedSupport 2 4) :
    Fintype.card (ResidualPositions p) = 2 := by
  rw [maskCoordinates_card, residualMask_size]

theorem originalUniformPositions_card (p : SelectedSupport 2 4) :
    Fintype.card (OriginalUniformPositions p) = 2 := by
  rw [maskCoordinates_card, originalUniformMask_size]

def omittedLabel (p : SelectedSupport 3 4) : Fin 4 :=
  ThreeActiveGeometry.omittedLabel p

theorem omitted_not_retained (p : SelectedSupport 3 4) :
    maskBit p.val.val.1 (omittedLabel p) ≠ true :=
  ThreeActiveGeometry.omittedLabel_not_retained p

theorem nonretained_eq_omitted (p : SelectedSupport 3 4) (i : Fin 4)
    (hi : maskBit p.val.val.1 i ≠ true) : i = omittedLabel p := by
  have hc : maskBit (maskComplement p.val.val.1) i = true := by
    rw [maskComplement_bit]
    cases hb : maskBit p.val.val.1 i <;> simp_all
  exact congrArg Subtype.val (ThreeActiveGeometry.omittedPosition_unique p ⟨i, hc⟩)

section Coordinates
variable {V : Type*} [AddCommGroup V]

/-- Complete a retained triple by its one omitted physical output value. -/
def complete (p : SelectedSupport 3 4) (x : RetainedPositions p → V) (z : V) :
    Fin 4 → V :=
  fun i => if hi : maskBit p.val.val.1 i = true then x ⟨i, hi⟩ else z

-- Preserve the existing implicit instance arguments while fixing lint locally.
set_option linter.unusedSectionVars false in
@[simp]
theorem complete_retained (p : SelectedSupport 3 4) (x : RetainedPositions p → V)
    (z : V) (i : RetainedPositions p) : complete p x z i.val = x i := by
  simp only [complete, dif_pos i.property]

set_option linter.unusedSectionVars false in
@[simp]
theorem complete_omitted (p : SelectedSupport 3 4) (x : RetainedPositions p → V)
    (z : V) : complete p x z (omittedLabel p) = z := by
  simp only [complete, dif_neg (omitted_not_retained p)]

set_option linter.unusedSectionVars false in
theorem complete_reconstruct (p : SelectedSupport 3 4) (y : Fin 4 → V) :
    complete p (restrictCoordinates p.val.val.1 y) (y (omittedLabel p)) = y := by
  funext i
  by_cases hi : maskBit p.val.val.1 i = true
  · simp only [complete, dif_pos hi, restrictCoordinates]
  · simp only [complete, dif_neg hi]
    exact congrArg y (nonretained_eq_omitted p i hi).symm

theorem complete_add (p : SelectedSupport 3 4) (x y : RetainedPositions p → V)
    (z w : V) : complete p (x + y) (z + w) = complete p x z + complete p y w := by
  funext i
  by_cases hi : maskBit p.val.val.1 i = true <;> simp [complete, hi]

@[simp]
theorem complete_zero (p : SelectedSupport 3 4) : complete p (0 : RetainedPositions p → V) 0 = 0 := by
  funext i
  simp [complete]

theorem complete_split (p : SelectedSupport 3 4) (x : RetainedPositions p → V) (z : V) :
    complete p x z = complete p x 0 + complete p 0 z := by
  simpa only [add_zero, zero_add] using complete_add p x 0 0 z

theorem complete_zero_left (p : SelectedSupport 3 4) (z : V) :
    complete p (0 : RetainedPositions p → V) z = Pi.single (omittedLabel p) z := by
  funext i
  by_cases hi : maskBit p.val.val.1 i = true
  · have hne : i ≠ omittedLabel p := by
      intro he
      exact omitted_not_retained p (he ▸ hi)
    simp [complete, hi, hne]
  · have he := nonretained_eq_omitted p i hi
    subst i
    simp [complete, omitted_not_retained]

def completeLeftHom (p : SelectedSupport 3 4) : (RetainedPositions p → V) →+ (Fin 4 → V) where
  toFun x := complete p x 0
  map_zero' := complete_zero p
  map_add' x y := by simpa only [zero_add] using complete_add p x y 0 0

def completeRightHom (p : SelectedSupport 3 4) : V →+ (Fin 4 → V) where
  toFun z := complete p 0 z
  map_zero' := complete_zero p
  map_add' z w := by simpa only [zero_add] using complete_add p 0 0 z w

def residualHom (p : SelectedSupport 2 4) : (Fin 4 → V) →+ (ResidualPositions p → V) where
  toFun := restrictCoordinates p.val.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

def retainedHom (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (p : SelectedSupport 3 4) :
    (Fin 4 → V) →+ (RetainedPositions p → V) where
  toFun s := restrictCoordinates p.val.val.1 (L s)
  map_zero' := by funext i; simp [restrictCoordinates]
  map_add' s t := by funext i; simp [restrictCoordinates, map_add]

/-- Inverse-output residual pair at omitted output zero. -/
def A (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → V) →+ (ResidualPositions pIn → V) :=
  (residualHom pIn).comp (L.symm.toAddMonoidHom.comp (completeLeftHom pOut))

/-- One common omitted-output parameter produces the coupled residual line. -/
def D (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    V →+ (ResidualPositions pIn → V) :=
  (residualHom pIn).comp (L.symm.toAddMonoidHom.comp (completeRightHom pOut))

theorem inverse_residual_complete (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) (z : V) :
    residualHom pIn (L.symm (complete pOut x z)) = A L pIn pOut x + D L pIn pOut z := by
  rw [complete_split, map_add, map_add]
  rfl

/-- The ORIGINAL two input directions, zero at both residual labels. -/
def originalUniformEmbedding (p : SelectedSupport 2 4) :
    (OriginalUniformPositions p → V) →+ (Fin 4 → V) where
  toFun := extendCoordinates (originalUniformMask p)
  map_zero' := by funext i; simp [extendCoordinates]
  map_add' s t := by
    funext i
    by_cases hi : maskBit (originalUniformMask p) i = true <;> simp [extendCoordinates, hi]

theorem originalUniform_residual_zero (p : SelectedSupport 2 4)
    (t : OriginalUniformPositions p → V) :
    residualHom p (originalUniformEmbedding p t) = 0 := by
  funext i
  have hi : maskBit (originalUniformMask p) i.val ≠ true := by
    rw [originalUniformMask, maskComplement_bit, i.property]
    decide
  change extendCoordinates (originalUniformMask p) t i.val = 0
  simp only [extendCoordinates, dif_neg hi]

def originalUniformTranslation (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    (OriginalUniformPositions pIn → V) →+ (RetainedPositions pOut → V) :=
  (retainedHom L pOut).comp (originalUniformEmbedding pIn)

end Coordinates

section Fibers
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

abbrev RetainedFiber (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :=
  {s : Fin 4 → V // retainedHom L pOut s = x}

/-- Exact parameterization of the actual full-source retained fiber by z. -/
def retainedFiberEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :
    V ≃ RetainedFiber L pOut x where
  toFun z := ⟨L.symm (complete pOut x z), by
    change restrictCoordinates pOut.val.val.1 (L (L.symm (complete pOut x z))) = x
    rw [L.apply_symm_apply]
    funext i
    exact complete_retained pOut x z i⟩
  invFun s := L s.val (omittedLabel pOut)
  left_inv z := by
    change L (L.symm (complete pOut x z)) (omittedLabel pOut) = z
    rw [L.apply_symm_apply]
    exact complete_omitted pOut x z
  right_inv s := by
    apply Subtype.ext
    apply L.injective
    rw [L.apply_symm_apply]
    have hs : restrictCoordinates pOut.val.val.1 (L s.val) = x := s.property
    simpa only [hs] using complete_reconstruct pOut (L s.val)

theorem retainedFiber_card (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :
    Fintype.card (RetainedFiber L pOut x) = Fintype.card V :=
  (Fintype.card_congr (retainedFiberEquiv L pOut x)).symm

/-- Counting sum of the same joint amplitude over every actual source point. -/
def fiberAmplitude (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ) (x : RetainedPositions pOut → V) : ℝ :=
  ∑ s : RetainedFiber L pOut x, h (residualHom pIn s.val)

theorem fiberAmplitude_eq_average (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ) (x : RetainedPositions pOut → V) :
    fiberAmplitude L pIn pOut h x = (Fintype.card V : ℝ) *
      CoupledLineAverage.average (D L pIn pOut) h (A L pIn pOut x) := by
  exact CoupledLineAverage.fiber_sum_eq_card_mul_average (D L pIn pOut) h
    (retainedFiberEquiv L pOut x) (fun s => residualHom pIn s.val) (A L pIn pOut x)
    (fun z => inverse_residual_complete L pIn pOut x z)

/-- Translation of actual source fibers by the ORIGINAL uniform pair. -/
def fiberTranslationEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) (t : OriginalUniformPositions pIn → V) :
    RetainedFiber L pOut x ≃
      RetainedFiber L pOut (x + originalUniformTranslation L pIn pOut t) where
  toFun s := ⟨s.val + originalUniformEmbedding pIn t, by
    rw [map_add, s.property]
    rfl⟩
  invFun s := ⟨s.val - originalUniformEmbedding pIn t, by
    rw [map_sub, s.property]
    exact add_sub_cancel_right x (originalUniformTranslation L pIn pOut t)⟩
  left_inv s := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv s := by apply Subtype.ext; exact sub_add_cancel _ _

theorem fiberAmplitude_originalUniform_translation
    (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ)
    (x : RetainedPositions pOut → V) (t : OriginalUniformPositions pIn → V) :
    fiberAmplitude L pIn pOut h (x + originalUniformTranslation L pIn pOut t) =
      fiberAmplitude L pIn pOut h x := by
  let e := fiberTranslationEquiv L pIn pOut x t
  change (∑ s : RetainedFiber L pOut (x + originalUniformTranslation L pIn pOut t),
    h (residualHom pIn s.val)) = ∑ s : RetainedFiber L pOut x, h (residualHom pIn s.val)
  rw [← e.sum_comp (fun s => h (residualHom pIn s.val))]
  apply Finset.sum_congr rfl
  intro s _
  change h (residualHom pIn (s.val + originalUniformEmbedding pIn t)) =
    h (residualHom pIn s.val)
  rw [map_add, originalUniform_residual_zero, add_zero]

end Fibers

section MDS
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Retained triples at omitted output zero are the actual inverse-input slice. -/
def zeroSliceEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → V) ≃
      ShortenedGraph L.symm.toAddMonoidHom 0 (maskComplement pOut.val.val.1) where
  toFun x := ⟨complete pOut x 0, by
    constructor
    · intro i hi
      exact (empty_mask_coordinate ⟨i, hi⟩).elim
    · intro i hi
      have hn : maskBit pOut.val.val.1 i ≠ true := by
        rw [maskComplement_bit] at hi
        cases hb : maskBit pOut.val.val.1 i <;> simp_all
      simp only [complete, dif_neg hn]⟩
  invFun y := restrictCoordinates pOut.val.val.1 y.val
  left_inv x := by funext i; exact complete_retained pOut x 0 i
  right_inv y := by
    apply Subtype.ext
    funext i
    by_cases hi : maskBit pOut.val.val.1 i = true
    · simp only [complete, dif_pos hi, restrictCoordinates]
    · have hc : maskBit (maskComplement pOut.val.val.1) i = true := by
        rw [maskComplement_bit]
        cases hb : maskBit pOut.val.val.1 i <;> simp_all
      simpa only [complete, dif_neg hi] using (y.property.2 i hc).symm

private theorem empty_disjoint (m : Fin 16) : MaskDisjoint 0 m := by
  intro i hi
  exact (empty_mask_coordinate ⟨i, hi⟩).elim

private theorem omitted_disjoint_singleton (pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) :
    MaskDisjoint (maskComplement pOut.val.val.1) (singletonMask s.val) := by
  intro i hi hs
  have he := (singletonMask_bit s.val i).mp hs
  subst i
  rw [maskComplement_bit, s.property] at hi
  simp at hi

/-- A residual pair and one retained physical coordinate parameterize the
entire omitted-output-zero slice. The mixed MDS information set is explicit. -/
def residualPairCoordinateEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) :
    (RetainedPositions pOut → V) ≃ V × (ResidualPositions pIn → V) :=
  ((zeroSliceEquiv L pOut).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv L.symm.toAddMonoidHom (zeroMDS_inverse L hL)
      0 (maskComplement pOut.val.val.1) pIn.val.val.1 (singletonMask s.val)
      (empty_disjoint _) (omitted_disjoint_singleton pOut s)
      (by rw [show maskSize (0 : Fin 16) = 0 by decide, maskComplement_size,
        ThreeActiveGeometry.retainedMask_size, residualMask_size, singletonMask_size]))).trans
    (Equiv.prodCongr (TwoActiveGeometry.singletonTupleEquiv s.val) (Equiv.refl _))

theorem residualPairCoordinateEquiv_apply
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) (x : RetainedPositions pOut → V) :
    residualPairCoordinateEquiv L hL pIn pOut s x = (x s, A L pIn pOut x) := by
  apply Prod.ext
  · change complete pOut x 0 s.val = x s
    exact complete_retained pOut x 0 s
  · rfl

private theorem retained_nonempty (pOut : SelectedSupport 3 4) :
    Nonempty (RetainedPositions pOut) := by
  apply Fintype.card_pos_iff.mp
  rw [ThreeActiveGeometry.retainedCoordinates_card]
  decide

theorem A_surjective (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    Function.Surjective (A L pIn pOut) := by
  obtain ⟨s⟩ := retained_nonempty pOut
  let e := residualPairCoordinateEquiv L hL pIn pOut s
  intro u
  refine ⟨e.symm (0, u), ?_⟩
  have he := e.apply_symm_apply (0, u)
  change residualPairCoordinateEquiv L hL pIn pOut s (e.symm (0, u)) = (0, u) at he
  rw [residualPairCoordinateEquiv_apply] at he
  exact congrArg Prod.snd he

/-- Exact finite-fiber pullback sum: every residual pair has q preimages.
This is proved by an actual mixed-coordinate equivalence, not a rank premise. -/
theorem A_pullback_sum (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (f : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, f (A L pIn pOut x)) = (Fintype.card V : ℝ) * ∑ u, f u := by
  obtain ⟨s⟩ := retained_nonempty pOut
  have he := (residualPairCoordinateEquiv L hL pIn pOut s).sum_comp
    (fun vu : V × (ResidualPositions pIn → V) => f vu.2)
  simp only [residualPairCoordinateEquiv_apply] at he
  calc
    _ = ∑ vu : V × (ResidualPositions pIn → V), f vu.2 := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option linter.unusedSectionVars false in
theorem D_coordinate_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (i : ResidualPositions pIn) : Function.Bijective (fun z => D L pIn pOut z i) := by
  have he : (fun z => D L pIn pOut z i) =
      TwoActiveGeometry.singletonCoordinateEquiv L.symm.toAddMonoidHom (zeroMDS_inverse L hL)
        (omittedLabel pOut) i.val := by
    funext z
    rw [TwoActiveGeometry.singletonCoordinateEquiv_apply]
    change L.symm (complete pOut 0 z) i.val = L.symm (Pi.single (omittedLabel pOut) z) i.val
    rw [complete_zero_left]
  rw [he]
  exact (TwoActiveGeometry.singletonCoordinateEquiv L.symm.toAddMonoidHom
    (zeroMDS_inverse L hL) (omittedLabel pOut) i.val).bijective

set_option linter.unusedSectionVars false in
/-- One joint bijection onto the entire physical retained pair. -/
theorem originalUniform_retained_pair_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) :
    Function.Bijective (fun t : OriginalUniformPositions pIn → V =>
      fun i : {i : RetainedPositions pOut // i ≠ s} =>
        originalUniformTranslation L pIn pOut t i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 s
  have hsize : maskSize pair = maskSize (originalUniformMask pIn) := by
    rw [DoubleUniformGeometry.retainedPairMask_size _
      (ThreeActiveGeometry.retainedMask_size pOut), originalUniformMask_size]
  have hb := (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := V)
    pOut.val.val.1 s).bijective.comp
      (mds_restricted_bijective L.toAddMonoidHom hL pair (originalUniformMask pIn) hsize)
  exact hb

theorem fiberAmplitude_energy_exact
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, fiberAmplitude L pIn pOut h x ^ 2) = (Fintype.card V : ℝ) ^ 3 *
      ∑ u, CoupledLineAverage.average (D L pIn pOut) h u ^ 2 := by
  simp_rw [fiberAmplitude_eq_average, mul_pow]
  rw [← Finset.mul_sum, A_pullback_sum L hL pIn pOut
    (fun u => CoupledLineAverage.average (D L pIn pOut) h u ^ 2)]
  ring

theorem fiberAmplitude_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, fiberAmplitude L pIn pOut h x ^ 2) ≤
      (Fintype.card V : ℝ) ^ 3 * ∑ u, h u ^ 2 := by
  rw [fiberAmplitude_energy_exact L hL pIn pOut]
  exact mul_le_mul_of_nonneg_left (CoupledLineAverage.average_energy (D L pIn pOut) h)
    (pow_nonneg (Nat.cast_nonneg _) 3)

end MDS

section ActualWord
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

def wordA (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → AES.Word) →+ (ResidualPositions pIn → AES.Word) :=
  A wordMixAddEquiv pIn pOut

def wordD (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    AES.Word →+ (ResidualPositions pIn → AES.Word) :=
  D wordMixAddEquiv pIn pOut

def wordFiberAmplitude (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  fiberAmplitude wordMixAddEquiv pIn pOut h

theorem word_A_surjective (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) :
    Function.Surjective (wordA pIn pOut) :=
  A_surjective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut

theorem word_D_coordinate_bijective
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) (i : ResidualPositions pIn) :
    Function.Bijective (fun z => wordD pIn pOut z i) :=
  D_coordinate_bijective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut i

theorem word_fiberAmplitude_eq_average
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (x : RetainedPositions pOut → AES.Word) :
    wordFiberAmplitude pIn pOut h x = (Fintype.card AES.Word : ℝ) *
      CoupledLineAverage.average (wordD pIn pOut) h (wordA pIn pOut x) :=
  fiberAmplitude_eq_average wordMixAddEquiv pIn pOut h x

theorem word_fiberAmplitude_energy_exact
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ x, wordFiberAmplitude pIn pOut h x ^ 2) = (Fintype.card AES.Word : ℝ) ^ 3 *
      ∑ u, CoupledLineAverage.average (wordD pIn pOut) h u ^ 2 :=
  fiberAmplitude_energy_exact wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut h

theorem word_fiberAmplitude_energy_le
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ x, wordFiberAmplitude pIn pOut h x ^ 2) ≤
      (Fintype.card AES.Word : ℝ) ^ 3 * ∑ u, h u ^ 2 :=
  fiberAmplitude_energy_le wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut h

theorem word_fiberAmplitude_originalUniform_translation
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (x : RetainedPositions pOut → AES.Word) (t : OriginalUniformPositions pIn → AES.Word) :
    wordFiberAmplitude pIn pOut h (x + originalUniformTranslation wordMixAddEquiv pIn pOut t) =
      wordFiberAmplitude pIn pOut h x :=
  fiberAmplitude_originalUniform_translation wordMixAddEquiv pIn pOut h x t

theorem word_originalUniform_retained_pair_bijective
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4) (s : RetainedPositions pOut) :
    Function.Bijective (fun t : OriginalUniformPositions pIn → AES.Word =>
      fun i : {i : RetainedPositions pOut // i ≠ s} =>
        originalUniformTranslation wordMixAddEquiv pIn pOut t i.val) :=
  originalUniform_retained_pair_bijective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut s

end ActualWord
end AESConcrete.CoupledPairFiber
