import AESConcrete.MDSGraphSupport

/-!
# Equal-size MDS information sets for arbitrary active supports

Geometry and exact-support semantics are separate below. Every source function
is an arbitrary signed joint function; no factorization or independence
premise is used. All coordinates outside an information set are grouped into
one graph value.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct pairs stay fixed. This module does not assert an energy
estimate, cap, or complete AES 10/14/16 theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.GeneralMDSGraphSupport
open AESMixing
open AESMixing.AES (maskBit maskSize)

variable {V : Type*}

/-- Coordinates outside the chosen information set. -/
abbrev OtherCoordinates (m : Fin 16) := {i : Fin 4 // maskBit m i ≠ true}

def joinMask (m : Fin 16) (v : OtherCoordinates m → V)
    (w : MaskCoordinates m → V) (i : Fin 4) : V :=
  if h : maskBit m i = true then w ⟨i, h⟩ else v ⟨i, h⟩

/-- The dependent coordinates come first, matching `GraphColumnEnergy`.
The free tuple retains every original coordinate label. -/
def splitMask (m : Fin 16) :
    (Fin 4 → V) ≃ (OtherCoordinates m → V) × (MaskCoordinates m → V) where
  toFun x := (fun i => x i.val, fun i => x i.val)
  invFun p := joinMask m p.1 p.2
  left_inv x := by
    funext i
    by_cases h : maskBit m i = true <;> simp [joinMask, h]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp [joinMask, i.property]
    · funext i
      simp [joinMask, i.property]

set_option maxRecDepth 100000 in
theorem otherCoordinates_card : ∀ m : Fin 16,
    Fintype.card (OtherCoordinates m) = 4 - maskSize m := by decide

section Generic
variable [AddCommGroup V]

/-- Equal-size ZeroMDS restrictions recover every point of the input support
from the selected output coordinates. -/
theorem supported_points_equal
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (inp out : Fin 16) (hsize : maskSize out = maskSize inp)
    (x x' : Fin 4 → V)
    (hx : maskProjection inp x = x) (hx' : maskProjection inp x' = x')
    (heq : restrictCoordinates out (L x) = restrictCoordinates out (L x')) :
    x = x' := by
  apply sub_eq_zero.mp
  apply hL out inp hsize
  · funext i
    have hi := congrFun hx i
    have hi' := congrFun hx' i
    by_cases hb : maskBit inp i = true
    · simp [maskProjection, hb]
    · have hz : x i = 0 := by simpa [maskProjection, hb] using hi.symm
      have hz' : x' i = 0 := by simpa [maskProjection, hb] using hi'.symm
      simp [maskProjection, hb, hz, hz']
  · rw [map_sub]
    funext i
    by_cases hb : maskBit out i = true
    · have hi := congrFun heq (⟨i, hb⟩ : MaskCoordinates out)
      change L x i = L x' i at hi
      simp [maskProjection, hb, hi]
    · simp [maskProjection, hb]

/-- Projection onto any equally sized output information set is injective
on the nonzero support after actual diffusion. -/
theorem pullback_support_injective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (inp out : Fin 16) (hsize : maskSize out = maskSize inp)
    (f : (Fin 4 → V) → ℝ)
    (hsupport : ∀ x, f x ≠ 0 → maskProjection inp x = x)
    (z z' : Fin 4 → V) (hz : f (L.symm z) ≠ 0) (hz' : f (L.symm z') ≠ 0)
    (heq : restrictCoordinates out z = restrictCoordinates out z') : z = z' := by
  apply L.symm.injective
  apply supported_points_equal L.toAddMonoidHom hL inp out hsize
    (L.symm z) (L.symm z') (hsupport _ hz) (hsupport _ hz')
  -- Expose the equivalence coercion before its inverse-cancellation rewrite.
  change restrictCoordinates out (L (L.symm z)) =
    restrictCoordinates out (L (L.symm z'))
  simpa only [L.apply_symm_apply] using heq

/-- One fiber over the entire free tuple contains at most one nonzero
dependent tuple. Its coordinates may depend on every free coordinate. -/
theorem pullback_fiber_unique
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (inp out : Fin 16) (hsize : maskSize out = maskSize inp)
    (f : (Fin 4 → V) → ℝ)
    (hsupport : ∀ x, f x ≠ 0 → maskProjection inp x = x) :
    ∀ (w : MaskCoordinates out → V) (v v' : OtherCoordinates out → V),
      f (L.symm ((splitMask out).symm (v, w))) ≠ 0 →
      f (L.symm ((splitMask out).symm (v', w))) ≠ 0 → v = v' := by
  intro w v v' hv hv'
  have he : (splitMask out).symm (v, w) = (splitMask out).symm (v', w) := by
    apply pullback_support_injective L hL inp out hsize f hsupport _ _ hv hv'
    funext i
    simp [restrictCoordinates, splitMask, joinMask, i.property]
  have hp := congrArg (splitMask out) he
  have hvv : (v, w) = (v', w) := by simpa only [Equiv.apply_symm_apply] using hp
  exact congrArg Prod.fst hvv

end Generic

section ExactSupport
variable [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exact inactive-support projection semantics supply the entire active
input subspace, without assigning independent variables to its coordinates. -/
theorem supportIndexComponent_supported {d : ℕ} (p : SupportIndex d)
    (f : (Fin 4 → V) → ℝ) :
    ∀ x, supportIndexComponent (0 : V) p f x ≠ 0 →
      maskProjection (maskComplement p.val.2) x = x := by
  intro x hx
  apply (maskProjection_complement_iff p.val.2 x).mpr
  funext i
  by_cases hi : maskBit p.val.2 i = true
  · have hz := MDSGraphSupport.supportIndexComponent_inactive_zero p i hi f x hx
    simp [maskProjection, hi, hz]
  · simp [maskProjection, hi]

theorem supportIndex_pullback_fiber_unique {d : ℕ}
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SupportIndex d) (out : Fin 16)
    (hsize : maskSize out = maskSize (maskComplement p.val.2))
    (f : (Fin 4 → V) → ℝ) :
    ∀ (w : MaskCoordinates out → V) (v v' : OtherCoordinates out → V),
      supportIndexComponent (0 : V) p f
        (L.symm ((splitMask out).symm (v, w))) ≠ 0 →
      supportIndexComponent (0 : V) p f
        (L.symm ((splitMask out).symm (v', w))) ≠ 0 → v = v' :=
  pullback_fiber_unique L hL (maskComplement p.val.2) out hsize
    (supportIndexComponent (0 : V) p f) (supportIndexComponent_supported p f)

end ExactSupport
end AESConcrete.GeneralMDSGraphSupport
