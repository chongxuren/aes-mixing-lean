import AESConcrete.ShortenedLineGeometry
import AESMixing.DualInformation

/-!
# Actual shortened planes and their dual line parameters

The two-zero AES graph projects to an actual additive subgroup of three
marked output bytes. Every pair of marked coordinates is an information set,
by the existing shortened MDS graph theorem. Dual information-set transfer
therefore makes each coordinate of its character annihilator bijective.
This supplies the actual dual line and its three zero-preserving coordinate
permutations, without assuming a dual-code slope table or a Fourier identity.

Constructive scope only. Generic Fourier-response transport is separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedPlane
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)

attribute [local instance] Classical.propDecidable

def graphSubgroup (inverse : Bool) (r z : Fin 16) : AddSubgroup (Fin 4 → Byte) where
  carrier := {x | graphZeroConditions (byteDiffusionHom inverse) r z x}
  zero_mem' := by constructor <;> intro i _ <;> simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      rw [map_add]
      change byteDiffusionHom inverse x i + byteDiffusionHom inverse y i = 0
      rw [hx.1 i hi, hy.1 i hi, zero_add]
    · intro i hi
      change x i + y i = 0
      rw [hx.2 i hi, hy.2 i hi, zero_add]
  neg_mem' := by
    intro x hx
    constructor
    · intro i hi
      rw [map_neg]
      change -byteDiffusionHom inverse x i = 0
      rw [hx.1 i hi, neg_zero]
    · intro i hi
      change -x i = 0
      rw [hx.2 i hi, neg_zero]

def projectionHom (inverse : Bool) (r z : Fin 16) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) : graphSubgroup inverse r z →+ (Fin 3 → Byte) where
  toFun x := fun i => byteDiffusionHom inverse x.val (e i).val
  map_zero' := by funext i; simp
  map_add' x y := by
    funext i
    change byteDiffusionHom inverse (x.val+y.val) (e i).val = _
    rw [map_add]
    rfl

/-- The actual marked-output image of the two-zero shortened graph. -/
def plane (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) : AddSubgroup (Fin 3 → Byte) :=
  (projectionHom inverse p.val.1 p.val.2 e).range

instance planeFintype (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) : Fintype (plane inverse e p) := Fintype.ofFinite _

theorem projection_injective (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    Function.Injective (projectionHom inverse p.val.1 p.val.2 e) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply mds_graph_zero_high (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    (maskUnion p.val.1 out) p.val.2
  · rw [maskUnion_size _ _ p.property.1]
    have hp := p.property.2
    omega
  · constructor
    · intro i hi
      rw [map_sub]
      change byteDiffusionHom inverse x.val i - byteDiffusionHom inverse y.val i = 0
      apply sub_eq_zero.mpr
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · rw [x.property.1 i hi, y.property.1 i hi]
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        have hv : (e j).val = i := congrArg Subtype.val hj
        have hh := congrFun hxy j
        change byteDiffusionHom inverse x.val (e j).val =
          byteDiffusionHom inverse y.val (e j).val at hh
        simpa only [hv] using hh
    · intro i hi
      change x.val i - y.val i = 0
      rw [x.property.2 i hi, y.property.2 i hi, sub_self]

def planeGraphEquiv (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 ≃ plane inverse e p :=
  Equiv.ofBijective (projectionHom inverse p.val.1 p.val.2 e).rangeRestrict
    ⟨fun x y h => projection_injective inverse out hout e p (congrArg Subtype.val h),
      (projectionHom inverse p.val.1 p.val.2 e).rangeRestrict_surjective⟩

theorem planeGraphEquiv_apply (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) (i : Fin 3) :
    (planeGraphEquiv inverse out hout e p x).val i = byteDiffusionHom inverse x.val (e i).val := rfl

theorem plane_card (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    Fintype.card (plane inverse e p) = 65536 := by
  rw [← Fintype.card_congr (planeGraphEquiv inverse out hout e p),
    plane_choice_cardinality (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) out p]
  norm_num [BinaryWord.card]

def pairMask {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out) (j : Fin 3) : Fin 16 :=
  maskIntersection out (maskComplement (singletonMask (e j).val))

private theorem erase_one_size : ∀ (out : Fin 16) (k : Fin 4),
    maskSize out = 3 → maskBit out k = true →
      maskSize (maskIntersection out (maskComplement (singletonMask k))) = 2 := by decide

theorem pairMask_size (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (j : Fin 3) : maskSize (pairMask e j) = 2 :=
  erase_one_size out (e j).val hout (e j).property

theorem pairMask_bit {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out) (j : Fin 3) (k : Fin 4) :
    maskBit (pairMask e j) k = true ↔ maskBit out k = true ∧ k ≠ (e j).val := by
  rw [pairMask, maskIntersection_bit, Bool.and_eq_true, maskComplement_bit]
  have hs := singletonMask_bit (e j).val k
  cases h : maskBit (singletonMask (e j).val) k <;> simp_all

def pairIndexEquiv {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out) (j : Fin 3) :
    {i : Fin 3 // i ≠ j} ≃ MaskCoordinates (pairMask e j) where
  toFun i := ⟨(e i.val).val, (pairMask_bit e j _).mpr
    ⟨(e i.val).property, fun h => i.property (e.injective (Subtype.ext h))⟩⟩
  invFun k := ⟨e.symm ⟨k.val, ((pairMask_bit e j k.val).mp k.property).1⟩, by
    intro h
    have hv := congrArg (fun i => (e i).val) h
    simp only [Equiv.apply_symm_apply] at hv
    exact ((pairMask_bit e j k.val).mp k.property).2 hv⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv k := by
    apply Subtype.ext
    change (e (e.symm ⟨k.val, ((pairMask_bit e j k.val).mp k.property).1⟩)).val = k.val
    exact congrArg Subtype.val (e.apply_symm_apply _)

theorem graph_pair_restriction_bijective (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (j : Fin 3) :
    Function.Bijective (fun x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 =>
      fun i : {i : Fin 3 // i ≠ j} => byteDiffusionHom inverse x.val (e i.val).val) := by
  have hdisj : MaskDisjoint p.val.1 (pairMask e j) := by
    intro k hk hp
    exact p.property.1 k hk ((pairMask_bit e j k).mp hp).1
  have hsize : maskSize p.val.1 + maskSize p.val.2 + maskSize (pairMask e j) + maskSize 0 = 4 := by
    rw [p.property.2, pairMask_size out hout e j, show maskSize 0 = 0 by decide]
  have hb := shortened_projection_bijective (byteDiffusionHom inverse)
    (byteDiffusionHom_zeroMDS inverse) p.val.1 p.val.2 (pairMask e j) 0
    hdisj (mask_disjoint_empty _) hsize
  let a := pairIndexEquiv e j
  constructor
  · intro x y hxy
    apply hb.1
    apply Prod.ext
    · funext k
      have h := congrFun hxy (a.symm k)
      have hk : (e (a.symm k).val).val = k.val := congrArg Subtype.val (a.apply_symm_apply k)
      change byteDiffusionHom inverse x.val k.val = byteDiffusionHom inverse y.val k.val
      simpa only [hk] using h
    · funext k
      exact (empty_mask_coordinate k).elim
  · intro v
    obtain ⟨x, hx⟩ := hb.2 ((fun k => v (a.symm k)), fun _ => 0)
    refine ⟨x, ?_⟩
    funext i
    have h := congrFun (congrArg Prod.fst hx) (a i)
    change byteDiffusionHom inverse x.val (e i.val).val = v (a.symm (a i)) at h
    simpa only [Equiv.symm_apply_apply] using h

theorem plane_pair_restriction_bijective (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (j : Fin 3) :
    Function.Bijective (subgroupRestriction (plane inverse e p) (fun i => i ≠ j)) := by
  apply (Function.Bijective.of_comp_iff _ (planeGraphEquiv inverse out hout e p).bijective).mp
  exact graph_pair_restriction_bijective inverse out hout e p j

def dualPlane (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) : AddSubgroup (Fin 3 → Byte) :=
  (bytePairing.product (Fin 3)).annihilator (plane inverse e p)

theorem dual_coordinate_bijective (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (j : Fin 3) :
    Function.Bijective (fun x : dualPlane inverse e p => x.val j) := by
  have hb := dual_restriction_bijective bytePairing (plane inverse e p) (fun i => i ≠ j)
    (plane_pair_restriction_bijective inverse out hout e p j)
  constructor
  · intro x y hxy
    apply hb.1
    funext k
    have hk : k.val = j := not_ne_iff.mp k.property
    simpa only [subgroupRestriction, hk] using hxy
  · intro v
    obtain ⟨x, hx⟩ := hb.2 (fun _ => v)
    refine ⟨x, ?_⟩
    exact congrFun hx ⟨j, by simp⟩

def dualCoordinateEquiv (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (j : Fin 3) :
    dualPlane inverse e p ≃ Byte :=
  Equiv.ofBijective (fun x => x.val j) (dual_coordinate_bijective inverse out hout e p j)

theorem dual_card (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    Fintype.card (dualPlane inverse e p) = 256 := by
  rw [Fintype.card_congr (dualCoordinateEquiv inverse out hout e p 0)]
  norm_num [BinaryWord.card]

def dualParam (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    Byte ≃ dualPlane inverse e p :=
  (dualCoordinateEquiv inverse out hout e p 0).symm

def dualCoordinatePerm (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (i : Fin 3) : Equiv.Perm Byte :=
  (dualParam inverse out hout e p).trans (dualCoordinateEquiv inverse out hout e p i)

theorem dualParam_coordinate (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (x : Byte) (i : Fin 3) :
    (dualParam inverse out hout e p x).val i = dualCoordinatePerm inverse out hout e p i x := rfl

theorem dualParam_zero (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    dualParam inverse out hout e p 0 = 0 := by
  apply (dualCoordinateEquiv inverse out hout e p 0).injective
  rw [dualParam, Equiv.apply_symm_apply]
  rfl

theorem dualCoordinatePerm_zero (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (i : Fin 3) :
    dualCoordinatePerm inverse out hout e p i 0 = 0 := by
  rw [← dualParam_coordinate, dualParam_zero]
  rfl

end AESConcrete.ShortenedPlane
