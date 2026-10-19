import AESConcrete.MixedMarkedPlane
import AESConcrete.ShortenedPlaneLinearity

/-!
# Field-linear parameters of actual mixed-plane trace duals

Actual byte-field scaling preserves the raw graph and its marked image.
The trace pairing transfers that scalar to the plane argument, proving
scalar closure of the actual annihilator. Its coordinate equivalences
then identify each dual parameter with multiplication by its value at one.
No ratio separation, energy endpoint or signed aggregate is assumed.
Constructive mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPlaneLinearity
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedByteLinearity
open AESConcrete.ShortenedPlane (graphSubgroup)
open AESConcrete.MixedMarkedPlane

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

theorem plane_scale_mem (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (c : Byte) (x : Fin 3 → Byte) (hx : x ∈ plane inverse r z marked) :
    (fun i => c * x i) ∈ plane inverse r z marked := by
  change ∃ u : graphSubgroup inverse r z, projectionHom inverse r z marked u = x at hx
  obtain ⟨u, hu⟩ := hx
  let g : ShortenedGraph (byteDiffusionHom inverse) r z := ⟨u.val, u.property⟩
  let sg := scaleGraph inverse r z c g
  change ∃ v : graphSubgroup inverse r z, projectionHom inverse r z marked v = fun i => c * x i
  refine ⟨⟨sg.val, sg.property⟩, ?_⟩
  funext i
  change graphCoordinate (byteDiffusionHom inverse) (fun j => c * u.val j) (marked i) = c * x i
  have hs := graphCoordinate_scale inverse r z c g (marked i)
  change graphCoordinate (byteDiffusionHom inverse) (fun j => c * u.val j) (marked i) =
    c * graphCoordinate (byteDiffusionHom inverse) u.val (marked i) at hs
  rw [hs]
  have hui := congrFun hu i
  change graphCoordinate (byteDiffusionHom inverse) u.val (marked i) = x i at hui
  rw [hui]

def planeScale (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (c : Byte) (x : plane inverse r z marked) : plane inverse r z marked :=
  ⟨fun i => c * x.val i, plane_scale_mem inverse r z marked c x.val x.property⟩

theorem dual_scale_mem (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (c : Byte) (x : Fin 3 → Byte) (hx : x ∈ dualPlane inverse r z marked) :
    (fun i => c * x i) ∈ dualPlane inverse r z marked := by
  change ∀ y : plane inverse r z marked,
    (bytePairing.product (Fin 3)).value x y.val = 1 at hx
  change ∀ y : plane inverse r z marked,
    (bytePairing.product (Fin 3)).value (fun i => c * x i) y.val = 1
  intro y
  rw [ShortenedPlaneLinearity.pairing_scale_transfer]
  exact hx (planeScale inverse r z marked c y)

def dualScale (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (c : Byte) (x : dualPlane inverse r z marked) : dualPlane inverse r z marked :=
  ⟨fun i => c * x.val i, dual_scale_mem inverse r z marked c x.val x.property⟩

theorem dualCoordinateEquiv_scale (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (c : Byte) (x : dualPlane inverse r z marked) (i : Fin 3) :
    dualCoordinateEquiv inverse r z hplane marked hmarked hm i (dualScale inverse r z marked c x) =
      c * dualCoordinateEquiv inverse r z hplane marked hmarked hm i x := rfl

theorem dualParam_scale_one (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (c : Byte) :
    dualParam inverse r z hplane marked hmarked hm c =
      dualScale inverse r z marked c (dualParam inverse r z hplane marked hmarked hm 1) := by
  apply (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).injective
  change (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0)
      ((dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).symm c) =
    (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0)
      (dualScale inverse r z marked c ((dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).symm 1))
  rw [Equiv.apply_symm_apply, dualCoordinateEquiv_scale, Equiv.apply_symm_apply, _root_.mul_one]

def dualCoefficient (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) : Byte :=
  dualCoordinatePerm inverse r z hplane marked hmarked hm i 1

theorem dualCoordinatePerm_mul (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) (x : Byte) :
    dualCoordinatePerm inverse r z hplane marked hmarked hm i x =
      dualCoefficient inverse r z hplane marked hmarked hm i * x := by
  rw [← dualParam_coordinate, dualParam_scale_one]
  change x * (dualParam inverse r z hplane marked hmarked hm 1).val i = _
  rw [dualParam_coordinate]
  exact mul_comm _ _

theorem dualCoefficient_ne_zero (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    dualCoefficient inverse r z hplane marked hmarked hm i ≠ 0 := by
  intro h
  have hz := dualCoordinatePerm_zero inverse r z hplane marked hmarked hm i
  have he : dualCoordinatePerm inverse r z hplane marked hmarked hm i 1 =
      dualCoordinatePerm inverse r z hplane marked hmarked hm i 0 := h.trans hz.symm
  exact one_ne_zero ((dualCoordinatePerm inverse r z hplane marked hmarked hm i).injective he)

theorem dualCoordinatePerm_eq_mulLeft (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    dualCoordinatePerm inverse r z hplane marked hmarked hm i =
      Equiv.mulLeft₀ (dualCoefficient inverse r z hplane marked hmarked hm i)
        (dualCoefficient_ne_zero inverse r z hplane marked hmarked hm i) := by
  apply Equiv.ext
  intro x
  exact dualCoordinatePerm_mul inverse r z hplane marked hmarked hm i x

end AESConcrete.MixedMarkedPlaneLinearity
