import AESConcrete.MixedMarkedPairGeometry
import AESConcrete.ActualMarkedCodeDual
import AESConcrete.PlaneFourierResponse

/-!
# Actual planes on arbitrary mixed physical marked triples

The image is constructed from the raw two-zero physical graph. Every
pair of selected physical coordinates is an information set, so each
coordinate of the actual trace annihilator is bijective. No physical
input is renamed as an output and no dual-line parameter is assumed.
Constructive mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPlane
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedCoordinates
open AESConcrete.ActualMarkedCodeMoment (selected_projection_injective selected_projection_bijective)
open AESConcrete.ShortenedPlane (graphSubgroup)

abbrev Byte := BinaryWord 8
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def projectionHom (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition) :
    graphSubgroup inverse r z →+ (Fin 3 → Byte) where
  toFun x := markedGraph (byteDiffusionHom inverse) r z marked x
  map_zero' := by
    funext i
    exact graphCoordinate_zero (byteDiffusionHom inverse) (marked i)
  map_add' x y := by
    funext i
    change graphCoordinate (byteDiffusionHom inverse) (x.val+y.val) (marked i) =
      graphCoordinate (byteDiffusionHom inverse) x.val (marked i) +
        graphCoordinate (byteDiffusionHom inverse) y.val (marked i)
    cases marked i <;> simp [graphCoordinate, map_add]

def plane (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition) :
    AddSubgroup (Fin 3 → Byte) := (projectionHom inverse r z marked).range

instance planeFintype (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition) :
    Fintype (plane inverse r z marked) := Fintype.ofFinite _

theorem projection_injective (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    Function.Injective (projectionHom inverse r z marked) := by
  exact selected_projection_injective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z marked hmarked hm (by simp only [Fintype.card_fin]; omega)

def planeGraphEquiv (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    ShortenedGraph (byteDiffusionHom inverse) r z ≃ plane inverse r z marked :=
  Equiv.ofBijective (projectionHom inverse r z marked).rangeRestrict
    ⟨fun _ _ h => projection_injective inverse r z hplane marked hmarked hm (congrArg Subtype.val h),
      (projectionHom inverse r z marked).rangeRestrict_surjective⟩

theorem planeGraphEquiv_apply (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (x : ShortenedGraph (byteDiffusionHom inverse) r z) (i : Fin 3) :
    (planeGraphEquiv inverse r z hplane marked hmarked hm x).val i =
      graphCoordinate (byteDiffusionHom inverse) x.val (marked i) := rfl

theorem plane_card (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    Fintype.card (plane inverse r z marked) = 65536 := by
  rw [← Fintype.card_congr (planeGraphEquiv inverse r z hplane marked hmarked hm),
    mds_graph_zero_count _ (byteDiffusionHom_zeroMDS inverse), hplane]
  norm_num [BinaryWord.card]

private theorem other_two_card (j : Fin 3) : Fintype.card {i : Fin 3 // i ≠ j} = 2 := by
  fin_cases j <;> decide

theorem graph_pair_restriction_bijective (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (j : Fin 3) :
    Function.Bijective (fun x : ShortenedGraph (byteDiffusionHom inverse) r z =>
      fun i : {i : Fin 3 // i ≠ j} => graphCoordinate (byteDiffusionHom inverse) x.val (marked i.val)) := by
  apply selected_projection_bijective _ (byteDiffusionHom_zeroMDS inverse) r z
    (fun i : {i : Fin 3 // i ≠ j} => marked i.val)
    (hmarked.comp Subtype.val_injective) (fun i => hm i.val)
  rw [other_two_card, hplane]

theorem plane_pair_restriction_bijective (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (j : Fin 3) :
    Function.Bijective (subgroupRestriction (plane inverse r z marked) (fun i => i ≠ j)) := by
  apply (Function.Bijective.of_comp_iff _
    (planeGraphEquiv inverse r z hplane marked hmarked hm).bijective).mp
  exact graph_pair_restriction_bijective inverse r z hplane marked hmarked hm j

def dualPlane (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition) :
    AddSubgroup (Fin 3 → Byte) := PlaneFourierResponse.byteDual (plane inverse r z marked)

theorem dual_coordinate_bijective (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (j : Fin 3) :
    Function.Bijective (fun x : dualPlane inverse r z marked => x.val j) := by
  have hb := dual_restriction_bijective bytePairing (plane inverse r z marked) (fun i => i ≠ j)
    (plane_pair_restriction_bijective inverse r z hplane marked hmarked hm j)
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

def dualCoordinateEquiv (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (j : Fin 3) :
    dualPlane inverse r z marked ≃ Byte :=
  Equiv.ofBijective (fun x => x.val j) (dual_coordinate_bijective inverse r z hplane marked hmarked hm j)

def dualParam (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    Byte ≃ dualPlane inverse r z marked :=
  (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).symm

def dualCoordinatePerm (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) : Equiv.Perm Byte :=
  (dualParam inverse r z hplane marked hmarked hm).trans
    (dualCoordinateEquiv inverse r z hplane marked hmarked hm i)

theorem dualParam_coordinate (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (x : Byte) (i : Fin 3) :
    (dualParam inverse r z hplane marked hmarked hm x).val i =
      dualCoordinatePerm inverse r z hplane marked hmarked hm i x := rfl

theorem dualParam_zero (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    dualParam inverse r z hplane marked hmarked hm 0 = 0 := by
  apply (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).injective
  rw [dualParam, Equiv.apply_symm_apply]
  rfl

theorem dualCoordinatePerm_zero (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    dualCoordinatePerm inverse r z hplane marked hmarked hm i 0 = 0 := by
  rw [← dualParam_coordinate, dualParam_zero]
  rfl

end AESConcrete.MixedMarkedPlane
