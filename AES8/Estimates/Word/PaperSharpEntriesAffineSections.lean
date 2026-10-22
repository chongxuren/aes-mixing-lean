import AESConcrete.MDSFiveFactorEntry
import AESConcrete.ShortenedByteLinearity

/-!
# Actual scalar-affine coordinates on five-factor byte sections

Draft diagnostic module. The affine identity below strengthens the existing
additive MDS coordinate permutations using actual F256 diffusion scaling.
It supplies geometry only; it assumes or concludes no 14/q or 27/q cap.
The fixed ordinary semantic pair predicate passed a separate C++ pilot;
its Lean certificate remains an independent obligation. Constructive only.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesAffineSections
open AESMixing
open AESConcrete.ShortenedLineResponse (Byte byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.MDSFiveFactorEntry
open AESConcrete.ShortenedByteLinearity (scaleGraph graphCoordinate_scale)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Addition stays inside the actual shortened physical graph. -/
def addGraph (inverse : Bool) (r z : Fin 16)
    (x y : ShortenedGraph (byteDiffusionHom inverse) r z) :
    ShortenedGraph (byteDiffusionHom inverse) r z :=
  ⟨fun i => x.val i + y.val i, by
    constructor
    · intro i hi
      have h := congrFun ((byteDiffusionHom inverse).map_add x.val y.val) i
      change byteDiffusionHom inverse (x.val + y.val) i = 0
      rw [h]
      simp only [Pi.add_apply, x.property.1 i hi, y.property.1 i hi, add_zero]
    · intro i hi
      simp only [x.property.2 i hi, y.property.2 i hi, add_zero]⟩

theorem graphCoordinate_add (inverse : Bool) (r z : Fin 16)
    (x y : ShortenedGraph (byteDiffusionHom inverse) r z) (p : GraphPosition) :
    graphCoordinate (byteDiffusionHom inverse) (addGraph inverse r z x y).val p =
      graphCoordinate (byteDiffusionHom inverse) x.val p +
        graphCoordinate (byteDiffusionHom inverse) y.val p := by
  cases p with
  | inl i => exact congrFun ((byteDiffusionHom inverse).map_add x.val y.val) i
  | inr i => rfl

theorem section_reference (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (a : I → Byte) (v : Byte) :
    graphCoordinate (byteDiffusionHom inverse)
      (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z idx hsize a v).val (idx (Sum.inr 0)).val = v := by
  exact congrArg Prod.snd
    ((projectionEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z idx hsize 0).apply_symm_apply (a,v))

/-- Every section is its actual offset plus a scalar multiple of the
zero-fixed section's unit point. No arbitrary additive permutation is used. -/
theorem sectionSource_affine (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (a : I → Byte) (v : Byte) :
    sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z idx hsize a v =
      addGraph inverse r z
        (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z idx hsize a 0)
        (scaleGraph inverse r z v
          (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
            r z idx hsize (fun _ => 0) 1)) := by
  apply (projectionEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z idx hsize 0).injective
  rw [sectionSource, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    change a i = graphCoordinate (byteDiffusionHom inverse) _ (idx (Sum.inl i)).val
    rw [graphCoordinate_add, graphCoordinate_scale, section_fixed, section_fixed]
    simp only [mul_zero, add_zero]
  · change v = graphCoordinate (byteDiffusionHom inverse) _ (idx (Sum.inr 0)).val
    rw [graphCoordinate_add, graphCoordinate_scale, section_reference, section_reference]
    simp only [mul_one, zero_add]

def sectionSlope (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (k : Fin 5) : Byte :=
  graphCoordinate (byteDiffusionHom inverse)
    (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z idx hsize (fun _ => 0) 1).val (idx (Sum.inr k)).val

def sectionOffset (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (a : I → Byte) (k : Fin 5) : Byte :=
  graphCoordinate (byteDiffusionHom inverse)
    (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z idx hsize a 0).val (idx (Sum.inr k)).val

theorem section_coordinate_affine (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (a : I → Byte) (k : Fin 5) (v : Byte) :
    graphCoordinate (byteDiffusionHom inverse)
      (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z idx hsize a v).val (idx (Sum.inr k)).val =
      sectionSlope inverse r z idx hsize k * v +
        sectionOffset inverse r z idx hsize a k := by
  rw [sectionSource_affine, graphCoordinate_add, graphCoordinate_scale]
  change sectionOffset inverse r z idx hsize a k +
    v * sectionSlope inverse r z idx hsize k = _
  rw [mul_comm v, add_comm]

/-- MDS bijectivity rules out zero slope for every remaining physical leg. -/
theorem sectionSlope_ne_zero (inverse : Bool) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : AES.maskSize r + AES.maskSize z + Fintype.card I + 1 = 4)
    (k : Fin 5) : sectionSlope inverse r z idx hsize k ≠ 0 := by
  intro hz
  have hinj := (section_coordinate_bijective (byteDiffusionHom inverse)
    (byteDiffusionHom_zeroMDS inverse) r z idx hsize (fun _ => 0) k).injective
  have he := hinj (a₁ := (0 : Byte)) (a₂ := (1 : Byte)) (by
    dsimp only
    rw [section_coordinate_affine, section_coordinate_affine, hz]
    simp only [zero_mul])
  exact zero_ne_one he

end AES8.PaperSharpEntriesAffineSections
