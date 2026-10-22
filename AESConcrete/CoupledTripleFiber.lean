import AESConcrete.CoupledLineAverage
import AESConcrete.ThreeActiveGeometry
import AESConcrete.WordCrossZero
import AESMixing.MDSInverse

/-!
# Actual retained fibers with a joint residual triple

The support indices are `(12,12)`.

The input and output supports both have type `SelectedSupport 3 4`. The source
contains the three ORIGINAL residual input labels and their sole ORIGINAL
uniform complement. The signed joint amplitude is never factored. The inverse
3-by-3 MDS slice is bijective, so the exact fiber energy factor is q^2, with
no additional q multiplicity from the residual pullback.

The averaging interface is supplied by `CoupledLineAverage`. Coordinate
geometry, finite fiber identities, energy and original-uniform translations
have separate interfaces below. No Fourier bound, normalized minor bridge,
endpoint estimate, physical cap or certificate is asserted.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleFiber
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

set_option maxRecDepth 100000

/-- The original residual input labels; no coordinate ordering is chosen. -/
abbrev ResidualPositions (p : SelectedSupport 3 4) := MaskCoordinates p.val.val.1

/-- The original retained output labels. -/
abbrev RetainedPositions (p : SelectedSupport 3 4) := MaskCoordinates p.val.val.1

theorem residualMask_size (p : SelectedSupport 3 4) : maskSize p.val.val.1 = 3 :=
  ThreeActiveGeometry.retainedMask_size p

theorem residualPositions_card (p : SelectedSupport 3 4) :
    Fintype.card (ResidualPositions p) = 3 :=
  ThreeActiveGeometry.retainedCoordinates_card p

theorem retainedPositions_card (p : SelectedSupport 3 4) :
    Fintype.card (RetainedPositions p) = 3 :=
  ThreeActiveGeometry.retainedCoordinates_card p

theorem inactiveMask_size (p : SelectedSupport 3 4) : maskSize p.val.val.2 = 0 := by
  have hp := p.property
  omega

theorem inactiveLabel_not (p : SelectedSupport 3 4) (i : Fin 4) :
    maskBit p.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates p.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inactiveMask_size] at hc
  omega

/-- The unique output label outside the actual retained triple. -/
def omittedLabel (pOut : SelectedSupport 3 4) : Fin 4 :=
  ThreeActiveGeometry.omittedLabel pOut

theorem omitted_not_retained (pOut : SelectedSupport 3 4) :
    maskBit pOut.val.val.1 (omittedLabel pOut) ≠ true :=
  ThreeActiveGeometry.omittedLabel_not_retained pOut

theorem nonretained_eq_omitted (pOut : SelectedSupport 3 4) (i : Fin 4)
    (hi : maskBit pOut.val.val.1 i ≠ true) : i = omittedLabel pOut := by
  have hc : maskBit (maskComplement pOut.val.val.1) i = true := by
    rw [maskComplement_bit]
    cases hb : maskBit pOut.val.val.1 i <;> simp_all
  exact congrArg Subtype.val (ThreeActiveGeometry.omittedPosition_unique pOut ⟨i, hc⟩)

/-- On an input support this complement is the ORIGINAL uniform input label. -/
def originalUniformLabel (pIn : SelectedSupport 3 4) : Fin 4 := omittedLabel pIn

theorem originalUniform_not_residual (pIn : SelectedSupport 3 4) :
    maskBit pIn.val.val.1 (originalUniformLabel pIn) ≠ true :=
  omitted_not_retained pIn

theorem originalUniform_not_inactive (pIn : SelectedSupport 3 4) :
    maskBit pIn.val.val.2 (originalUniformLabel pIn) ≠ true :=
  inactiveLabel_not pIn _

/-- The scalar uniform parameter is tied to the actual multi-uniform labels. -/
theorem multiUniformLabel_eq (pIn : SelectedSupport 3 4)
    (i : MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1) :
    i.val.val = originalUniformLabel pIn :=
  nonretained_eq_omitted pIn i.val.val i.val.property

theorem multiUniformPositions_card (pIn : SelectedSupport 3 4) :
    Fintype.card
      (MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1) = 1 := by
  have hc := MultiUniformExpansion.uniformPositions_card
    pIn.val.val.2 pIn.val.val.1 pIn.val.property.1
  rw [inactiveMask_size, residualMask_size] at hc
  exact hc

section Coordinates
variable {V : Type*} [AddCommGroup V]

/-- Complete the actual retained triple with its one omitted output value. -/
def complete (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) (z : V) :
    Fin 4 → V :=
  fun i => if hi : maskBit pOut.val.val.1 i = true then x ⟨i, hi⟩ else z

@[simp]
theorem complete_retained (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) (z : V) (i : RetainedPositions pOut) :
    complete pOut x z i.val = x i := by
  simp only [complete, dif_pos i.property]

@[simp]
theorem complete_omitted (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) (z : V) :
    complete pOut x z (omittedLabel pOut) = z := by
  simp only [complete, dif_neg (omitted_not_retained pOut)]

theorem complete_reconstruct (pOut : SelectedSupport 3 4) (y : Fin 4 → V) :
    complete pOut (restrictCoordinates pOut.val.val.1 y) (y (omittedLabel pOut)) = y := by
  funext i
  by_cases hi : maskBit pOut.val.val.1 i = true
  · simp only [complete, dif_pos hi, restrictCoordinates]
  · simp only [complete, dif_neg hi]
    exact congrArg y (nonretained_eq_omitted pOut i hi).symm

/-- The actual full input source, including every zero value. Completion at
an input support places the residual triple and sole original uniform value. -/
def sourceEquiv (pIn : SelectedSupport 3 4) :
    ((ResidualPositions pIn → V) × V) ≃ (Fin 4 → V) where
  toFun uv := complete pIn uv.1 uv.2
  invFun s := (restrictCoordinates pIn.val.val.1 s, s (originalUniformLabel pIn))
  left_inv uv := by
    apply Prod.ext
    · funext i
      exact complete_retained pIn uv.1 uv.2 i
    · exact complete_omitted pIn uv.1 uv.2
  right_inv s := complete_reconstruct pIn s

theorem complete_add (pOut : SelectedSupport 3 4)
    (x y : RetainedPositions pOut → V) (z w : V) :
    complete pOut (x + y) (z + w) = complete pOut x z + complete pOut y w := by
  funext i
  by_cases hi : maskBit pOut.val.val.1 i = true <;> simp [complete, hi]

@[simp]
theorem complete_zero (pOut : SelectedSupport 3 4) :
    complete pOut (0 : RetainedPositions pOut → V) 0 = 0 := by
  funext i
  simp [complete]

theorem complete_split (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) (z : V) :
    complete pOut x z = complete pOut x 0 + complete pOut 0 z := by
  simpa only [add_zero, zero_add] using complete_add pOut x 0 0 z

theorem complete_zero_right (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → V) :
    complete pOut x 0 = extendCoordinates pOut.val.val.1 x := rfl

theorem complete_zero_left (pOut : SelectedSupport 3 4) (z : V) :
    complete pOut (0 : RetainedPositions pOut → V) z = Pi.single (omittedLabel pOut) z := by
  funext i
  by_cases hi : maskBit pOut.val.val.1 i = true
  · have hne : i ≠ omittedLabel pOut := by
      intro he
      exact omitted_not_retained pOut (he ▸ hi)
    simp [complete, hi, Pi.single_apply, hne, Ne.symm hne]
  · have he := nonretained_eq_omitted pOut i hi
    subst i
    simp [complete, omitted_not_retained]

def completeLeftHom (pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → V) →+ (Fin 4 → V) where
  toFun x := complete pOut x 0
  map_zero' := complete_zero pOut
  map_add' x y := by simpa only [zero_add] using complete_add pOut x y 0 0

def completeRightHom (pOut : SelectedSupport 3 4) : V →+ (Fin 4 → V) where
  toFun z := complete pOut 0 z
  map_zero' := complete_zero pOut
  map_add' z w := by simpa only [zero_add] using complete_add pOut 0 0 z w

def residualHom (pIn : SelectedSupport 3 4) :
    (Fin 4 → V) →+ (ResidualPositions pIn → V) where
  toFun := restrictCoordinates pIn.val.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

def retainedHom (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (pOut : SelectedSupport 3 4) :
    (Fin 4 → V) →+ (RetainedPositions pOut → V) where
  toFun s := restrictCoordinates pOut.val.val.1 (L s)
  map_zero' := by funext i; simp [restrictCoordinates]
  map_add' s t := by funext i; simp [restrictCoordinates, map_add]

/-- Actual inverse-input residual triple on the omitted-output-zero slice. -/
def A (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → V) →+ (ResidualPositions pIn → V) :=
  (residualHom pIn).comp (L.symm.toAddMonoidHom.comp (completeLeftHom pOut))

/-- One common omitted-output parameter gives a coupled residual line. -/
def D (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) : V →+ (ResidualPositions pIn → V) :=
  (residualHom pIn).comp (L.symm.toAddMonoidHom.comp (completeRightHom pOut))

theorem A_eq_restricted (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :
    A L pIn pOut x =
      restrictedMap L.symm.toAddMonoidHom pIn.val.val.1 pOut.val.val.1 x := rfl

theorem inverse_residual_complete (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) (z : V) :
    residualHom pIn (L.symm (complete pOut x z)) = A L pIn pOut x + D L pIn pOut z := by
  rw [complete_split, map_add, map_add]
  rfl

/-- Only the ORIGINAL nonresidual input label is translated. -/
def originalUniformEmbedding (pIn : SelectedSupport 3 4) : V →+ (Fin 4 → V) where
  toFun t := Pi.single (originalUniformLabel pIn) t
  map_zero' := by funext i; simp
  map_add' s t := by
    funext i
    by_cases hi : i = originalUniformLabel pIn
    · subst i
      simp
    · simp [Pi.single_apply, hi, Ne.symm hi]

theorem originalUniform_residual_zero (pIn : SelectedSupport 3 4) (t : V) :
    residualHom pIn (originalUniformEmbedding pIn t) = 0 := by
  funext i
  have hne : i.val ≠ originalUniformLabel pIn := by
    intro he
    exact originalUniform_not_residual pIn (he ▸ i.property)
  change (Pi.single (originalUniformLabel pIn) t : Fin 4 → V) i.val = 0
  simp [Pi.single_apply, hne, Ne.symm hne]

def originalUniformTranslation (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) : V →+ (RetainedPositions pOut → V) :=
  (retainedHom L pOut).comp (originalUniformEmbedding pIn)

end Coordinates

section Fibers
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

abbrev RetainedFiber (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :=
  {s : Fin 4 → V // retainedHom L pOut s = x}

/-- The actual retained fiber has exactly one free omitted-output parameter. -/
def retainedFiberEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) :
    V ≃ RetainedFiber L pOut x where
  toFun z := ⟨L.symm (complete pOut x z), by
    change restrictCoordinates pOut.val.val.1 (L (L.symm (complete pOut x z))) = x
    rw [L.apply_symm_apply]
    funext i
    change complete pOut x z i.val = x i
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

/-- Counting sum of one arbitrary signed JOINT residual-triple amplitude. -/
def fiberAmplitude (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → V) → ℝ)
    (x : RetainedPositions pOut → V) : ℝ :=
  ∑ s : RetainedFiber L pOut x, h (residualHom pIn s.val)

theorem fiberAmplitude_eq_average (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → V) → ℝ)
    (x : RetainedPositions pOut → V) :
    fiberAmplitude L pIn pOut h x = (Fintype.card V : ℝ) *
      CoupledLineAverage.average (D L pIn pOut) h (A L pIn pOut x) := by
  exact CoupledLineAverage.fiber_sum_eq_card_mul_average (D L pIn pOut) h
    (retainedFiberEquiv L pOut x) (fun s => residualHom pIn s.val) (A L pIn pOut x)
    (fun z => inverse_residual_complete L pIn pOut x z)

/-- Actual source fibers are translated by the sole ORIGINAL uniform input. -/
def fiberTranslationEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (pIn pOut : SelectedSupport 3 4) (x : RetainedPositions pOut → V) (t : V) :
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
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → V) → ℝ) (x : RetainedPositions pOut → V) (t : V) :
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

/-- Both masks have size three: this is an inverse 3-by-3 MDS bijection. -/
theorem A_bijective (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) : Function.Bijective (A L pIn pOut) := by
  change Function.Bijective
    (restrictedMap L.symm.toAddMonoidHom pIn.val.val.1 pOut.val.val.1)
  exact mds_restricted_bijective L.symm.toAddMonoidHom (zeroMDS_inverse L hL)
    pIn.val.val.1 pOut.val.val.1
    (by rw [residualMask_size, ThreeActiveGeometry.retainedMask_size])

def AEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → V) ≃+ (ResidualPositions pIn → V) :=
  { Equiv.ofBijective (A L pIn pOut) (A_bijective L hL pIn pOut) with
    map_add' := fun x y => (A L pIn pOut).map_add x y }

/-- Exact bijective pullback: no additional q fiber is charged here. -/
theorem A_pullback_sum (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) (f : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, f (A L pIn pOut x)) = ∑ u, f u :=
  (AEquiv L hL pIn pOut).toEquiv.sum_comp f

theorem D_coordinate_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) (i : ResidualPositions pIn) :
    Function.Bijective (fun z => D L pIn pOut z i) := by
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

/-- Forward 1-by-1 MDS gives the actual uniform translation onto any retained label. -/
theorem originalUniform_retained_singleton_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) (i : RetainedPositions pOut) :
    Function.Bijective (fun t : V => originalUniformTranslation L pIn pOut t i) := by
  have he : (fun t : V => originalUniformTranslation L pIn pOut t i) =
      TwoActiveGeometry.singletonCoordinateEquiv L.toAddMonoidHom hL
        (originalUniformLabel pIn) i.val := by
    funext t
    rw [TwoActiveGeometry.singletonCoordinateEquiv_apply]
    rfl
  rw [he]
  exact (TwoActiveGeometry.singletonCoordinateEquiv L.toAddMonoidHom hL
    (originalUniformLabel pIn) i.val).bijective

/-- The q^2 factor comes only from squaring the one-parameter fiber sum. -/
theorem fiberAmplitude_energy_exact
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, fiberAmplitude L pIn pOut h x ^ 2) = (Fintype.card V : ℝ) ^ 2 *
      ∑ u, CoupledLineAverage.average (D L pIn pOut) h u ^ 2 := by
  simp_rw [fiberAmplitude_eq_average, mul_pow]
  rw [← Finset.mul_sum, A_pullback_sum L hL pIn pOut
    (fun u => CoupledLineAverage.average (D L pIn pOut) h u ^ 2)]

/-- Every arbitrary signed joint residual-triple amplitude has the same bound. -/
theorem fiberAmplitude_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → V) → ℝ) :
    (∑ x, fiberAmplitude L pIn pOut h x ^ 2) ≤
      (Fintype.card V : ℝ) ^ 2 * ∑ u, h u ^ 2 := by
  rw [fiberAmplitude_energy_exact L hL pIn pOut]
  exact mul_le_mul_of_nonneg_left (CoupledLineAverage.average_energy (D L pIn pOut) h)
    (pow_nonneg (Nat.cast_nonneg _) 2)

end MDS

section ActualWord
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

def wordA (pIn pOut : SelectedSupport 3 4) :
    (RetainedPositions pOut → AES.Word) →+ (ResidualPositions pIn → AES.Word) :=
  A wordMixAddEquiv pIn pOut

def wordD (pIn pOut : SelectedSupport 3 4) :
    AES.Word →+ (ResidualPositions pIn → AES.Word) := D wordMixAddEquiv pIn pOut

def wordFiberAmplitude (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  fiberAmplitude wordMixAddEquiv pIn pOut h

def wordUniformTranslation (pIn pOut : SelectedSupport 3 4) :
    AES.Word →+ (RetainedPositions pOut → AES.Word) :=
  originalUniformTranslation wordMixAddEquiv pIn pOut

def wordRetainedFiberEquiv (pOut : SelectedSupport 3 4)
    (x : RetainedPositions pOut → AES.Word) :
    AES.Word ≃ RetainedFiber wordMixAddEquiv pOut x :=
  retainedFiberEquiv wordMixAddEquiv pOut x

theorem word_A_bijective (pIn pOut : SelectedSupport 3 4) :
    Function.Bijective (wordA pIn pOut) :=
  A_bijective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut

theorem word_D_coordinate_bijective
    (pIn pOut : SelectedSupport 3 4) (i : ResidualPositions pIn) :
    Function.Bijective (fun z => wordD pIn pOut z i) :=
  D_coordinate_bijective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut i

theorem word_fiberAmplitude_eq_average
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (x : RetainedPositions pOut → AES.Word) :
    wordFiberAmplitude pIn pOut h x = (Fintype.card AES.Word : ℝ) *
      CoupledLineAverage.average (wordD pIn pOut) h (wordA pIn pOut x) :=
  fiberAmplitude_eq_average wordMixAddEquiv pIn pOut h x

theorem word_fiberAmplitude_energy_exact
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ x, wordFiberAmplitude pIn pOut h x ^ 2) = (Fintype.card AES.Word : ℝ) ^ 2 *
      ∑ u, CoupledLineAverage.average (wordD pIn pOut) h u ^ 2 :=
  fiberAmplitude_energy_exact wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut h

theorem word_fiberAmplitude_energy_le
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ x, wordFiberAmplitude pIn pOut h x ^ 2) ≤
      (Fintype.card AES.Word : ℝ) ^ 2 * ∑ u, h u ^ 2 :=
  fiberAmplitude_energy_le wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut h

theorem word_fiberAmplitude_originalUniform_translation
    (pIn pOut : SelectedSupport 3 4) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (x : RetainedPositions pOut → AES.Word) (t : AES.Word) :
    wordFiberAmplitude pIn pOut h (x + wordUniformTranslation pIn pOut t) =
      wordFiberAmplitude pIn pOut h x :=
  fiberAmplitude_originalUniform_translation wordMixAddEquiv pIn pOut h x t

theorem word_originalUniform_retained_singleton_bijective
    (pIn pOut : SelectedSupport 3 4) (i : RetainedPositions pOut) :
    Function.Bijective (fun t : AES.Word => wordUniformTranslation pIn pOut t i) :=
  originalUniform_retained_singleton_bijective wordMixAddEquiv wordMixAddEquiv_zeroMDS pIn pOut i

end ActualWord
end AESConcrete.CoupledTripleFiber
