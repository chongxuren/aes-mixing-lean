import AESConcrete.ShortenedLineResponse

/-!
# Field-linear parameters for actual AES byte shortenings

The generic graph-to-line result gives coordinate permutations. For actual
forward/inverse AES byte diffusion the physical field-matrix formula supplies
scalar compatibility. It follows that every derived coordinate permutation is
multiplication by its actual nonzero value at one. No coefficient table or
line/plane intersection classification is assumed. Constructive scope only.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedByteLinearity
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse

theorem byteDiffusionHom_scale (inverse : Bool) (c : Byte) (x : Fin 4 → Byte) :
    byteDiffusionHom inverse (fun i => c * x i) =
      fun i => c * byteDiffusionHom inverse x i := by
  simp only [byteDiffusionHom_apply, byteDiffusionOrientation_apply]
  funext i
  change (∑ j, gramMixing inverse i j * (c * x j)) =
    c * ∑ j, gramMixing inverse i j * x j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def scaleGraph (inverse : Bool) (r z : Fin 16) (c : Byte)
    (x : ShortenedGraph (byteDiffusionHom inverse) r z) :
    ShortenedGraph (byteDiffusionHom inverse) r z :=
  ⟨fun i => c * x.val i, by
    constructor
    · intro i hi
      rw [byteDiffusionHom_scale]
      simp only [x.property.1 i hi, mul_zero]
    · intro i hi
      simp only [x.property.2 i hi, mul_zero]⟩

theorem graphCoordinate_scale (inverse : Bool) (r z : Fin 16) (c : Byte)
    (x : ShortenedGraph (byteDiffusionHom inverse) r z) (p : GraphPosition) :
    graphCoordinate (byteDiffusionHom inverse) (scaleGraph inverse r z c x).val p =
      c * graphCoordinate (byteDiffusionHom inverse) x.val p := by
  cases p with
  | inl i => exact congrFun (byteDiffusionHom_scale inverse c x.val) i
  | inr i => rfl

theorem coordinateEquiv_scale (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p)
    (c : Byte) (x : ShortenedGraph (byteDiffusionHom inverse) r z) :
    coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z hshort p hp (scaleGraph inverse r z c x) =
      c * coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z hshort p hp x := by
  rw [coordinateEquiv_apply, coordinateEquiv_apply]
  exact graphCoordinate_scale inverse r z c x p

/-- The actual inverse parameter map is scalar multiplication of the
graph point whose reference coordinate is one. -/
theorem coordinateEquiv_symm_scale_one (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p)
    (c : Byte) :
    (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort p hp).symm c =
        scaleGraph inverse r z c
          ((coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
            r z hshort p hp).symm 1) := by
  apply (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z hshort p hp).injective
  rw [Equiv.apply_symm_apply, coordinateEquiv_scale, Equiv.apply_symm_apply, mul_one]

def lineCoefficient (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) : Byte :=
  lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z hshort marked hm i 1

theorem lineCoordinatePerm_mul (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) (x : Byte) :
    lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm i x = lineCoefficient inverse r z hshort marked hm i * x := by
  unfold lineCoefficient
  rw [lineCoordinatePerm_apply, coordinateEquiv_symm_scale_one,
    graphCoordinate_scale, ← lineCoordinatePerm_apply]
  exact mul_comm _ _

theorem lineCoefficient_ne_zero (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    lineCoefficient inverse r z hshort marked hm i ≠ 0 := by
  intro h
  have hz := lineCoordinatePerm_zero (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z hshort marked hm i
  have he : lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm i 1 =
    lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm i 0 := h.trans hz.symm
  exact one_ne_zero
    ((lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm i).injective he)

theorem lineCoordinatePerm_eq_mulLeft (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm i =
        Equiv.mulLeft₀ (lineCoefficient inverse r z hshort marked hm i)
          (lineCoefficient_ne_zero inverse r z hshort marked hm i) := by
  apply Equiv.ext
  intro x
  exact lineCoordinatePerm_mul inverse r z hshort marked hm i x

end AESConcrete.ShortenedByteLinearity
