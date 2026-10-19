import AESConcrete.ShortenedPlane

/-!
# Field-linear parameters of actual shortened-plane duals

The actual plane is the marked image of the physical AES byte matrix.
Its scalar closure follows by scaling the shortened graph. The actual
trace-character product pairing transfers a common scalar from its first
argument to its second; plane scalar closure therefore gives scalar closure
of its actual annihilator. The already proved coordinate equivalences then
force the dual line parameters to be multiplication by their value at one.

Constructive scope only. No frozen source is changed, and no plane-pair
ratio classification, Fourier-response identity, or word cap is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedPlaneLinearity
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedByteLinearity
open AESConcrete.ShortenedPlane

-- Actual byte-field coercions through range/annihilator definitions need
-- the same unfolding depth as the checked pointwise plane-response bridge.
set_option maxRecDepth 65536

/-- Scaling an actual graph witness proves closure of its marked plane. -/
theorem plane_scale_mem (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (c : Byte) (x : Fin 3 → Byte) (hx : x ∈ plane inverse e p) :
    (fun i => c * x i) ∈ plane inverse e p := by
  change ∃ u : graphSubgroup inverse p.val.1 p.val.2,
    projectionHom inverse p.val.1 p.val.2 e u = x at hx
  obtain ⟨u, hu⟩ := hx
  let g : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 := ⟨u.val, u.property⟩
  let sg := scaleGraph inverse p.val.1 p.val.2 c g
  change ∃ v : graphSubgroup inverse p.val.1 p.val.2,
    projectionHom inverse p.val.1 p.val.2 e v = fun i => c * x i
  refine ⟨⟨sg.val, sg.property⟩, ?_⟩
  funext i
  change byteDiffusionHom inverse (fun j => c * u.val j) (e i).val = c * x i
  rw [byteDiffusionHom_scale]
  -- Expose only the selected coordinate before applying scalar multiplication.
  -- Higher-order expected-type inference here unfolds the physical AES field.
  have hui := congrFun hu i
  change byteDiffusionHom inverse u.val (e i).val = x i at hui
  change c * byteDiffusionHom inverse u.val (e i).val = c * x i
  rw [hui]

def planeScale (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (c : Byte) (x : plane inverse e p) : plane inverse e p :=
  ⟨fun i => c * x.val i, plane_scale_mem inverse e p c x.val x.property⟩

/-- A common byte-field scalar transfers across the actual trace pairing.
No claim that every additive pairing has this property is used. -/
theorem pairing_scale_transfer (c : Byte) (x y : Fin 3 → Byte) :
    (bytePairing.product (Fin 3)).value (fun i => c * x i) y =
      (bytePairing.product (Fin 3)).value x (fun i => c * y i) := by
  change (∏ i : Fin 3, byteCharacter ((c * x i) * y i)) =
    ∏ i : Fin 3, byteCharacter (x i * (c * y i))
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- The annihilator used by the actual Fourier response is scalar closed. -/
theorem dual_scale_mem (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (c : Byte) (x : Fin 3 → Byte) (hx : x ∈ dualPlane inverse e p) :
    (fun i => c * x i) ∈ dualPlane inverse e p := by
  change ∀ y : plane inverse e p,
    (bytePairing.product (Fin 3)).value x y.val = 1 at hx
  change ∀ y : plane inverse e p,
    (bytePairing.product (Fin 3)).value (fun i => c * x i) y.val = 1
  intro y
  rw [pairing_scale_transfer]
  exact hx (planeScale inverse e p c y)

def dualScale (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (c : Byte) (x : dualPlane inverse e p) : dualPlane inverse e p :=
  ⟨fun i => c * x.val i, dual_scale_mem inverse e p c x.val x.property⟩

theorem dualCoordinateEquiv_apply (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (i : Fin 3) (x : dualPlane inverse e p) :
    dualCoordinateEquiv inverse out hout e p i x = x.val i := rfl

theorem dualCoordinateEquiv_scale (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (c : Byte) (x : dualPlane inverse e p) (i : Fin 3) :
    dualCoordinateEquiv inverse out hout e p i (dualScale inverse e p c x) =
      c * dualCoordinateEquiv inverse out hout e p i x := rfl

/-- The actual dual point with reference coordinate c is c times the
actual dual point with reference coordinate one. -/
theorem dualParam_scale_one (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (c : Byte) :
    dualParam inverse out hout e p c =
      dualScale inverse e p c (dualParam inverse out hout e p 1) := by
  apply (dualCoordinateEquiv inverse out hout e p 0).injective
  change (dualCoordinateEquiv inverse out hout e p 0)
      ((dualCoordinateEquiv inverse out hout e p 0).symm c) =
    (dualCoordinateEquiv inverse out hout e p 0)
      (dualScale inverse e p c ((dualCoordinateEquiv inverse out hout e p 0).symm 1))
  rw [Equiv.apply_symm_apply, dualCoordinateEquiv_scale, Equiv.apply_symm_apply, mul_one]

def dualCoefficient (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (i : Fin 3) : Byte :=
  dualCoordinatePerm inverse out hout e p i 1

theorem dualCoordinatePerm_mul (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (i : Fin 3) (x : Byte) :
    dualCoordinatePerm inverse out hout e p i x = dualCoefficient inverse out hout e p i * x := by
  rw [← dualParam_coordinate, dualParam_scale_one]
  change x * (dualParam inverse out hout e p 1).val i = _
  rw [dualParam_coordinate]
  exact mul_comm _ _

theorem dualCoefficient_ne_zero (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (i : Fin 3) : dualCoefficient inverse out hout e p i ≠ 0 := by
  intro h
  have hz := dualCoordinatePerm_zero inverse out hout e p i
  have he : dualCoordinatePerm inverse out hout e p i 1 =
      dualCoordinatePerm inverse out hout e p i 0 := h.trans hz.symm
  exact one_ne_zero ((dualCoordinatePerm inverse out hout e p i).injective he)

theorem dualCoordinatePerm_eq_mulLeft (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (i : Fin 3) :
    dualCoordinatePerm inverse out hout e p i =
      Equiv.mulLeft₀ (dualCoefficient inverse out hout e p i)
        (dualCoefficient_ne_zero inverse out hout e p i) := by
  apply Equiv.ext
  intro x
  exact dualCoordinatePerm_mul inverse out hout e p i x

end AESConcrete.ShortenedPlaneLinearity
