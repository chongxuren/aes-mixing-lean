import AESMixing.GraphExpansion
import AESMixing.ProjectedIncidence

/-! The actual marked-coordinate channel subject to the unmarked nonzero
restrictions is a signed sum of shortened incidence matrices. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable
open AES
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def restrictedGraphIncidence (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (s : Finset GraphPosition) (out inp : Fin 16)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) : ℝ :=
  ∑ x : Fin 4 → V,
    (if graphZeroConditions L r z x ∧ (∀ j ∈ s, graphCoordinate L x j ≠ 0)
      then 1 else 0) *
    (if restrictCoordinates out (L x) = y ∧ restrictCoordinates inp x = w then 1 else 0)

theorem restrictedGraphIncidence_expansion
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (out inp : Fin 16)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    restrictedGraphIncidence L r z s out inp y w =
      ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
        incidenceMultiplicity
          (shortenedOutput L (maskUnion r (outputPositionMask t))
            (maskUnion z (inputPositionMask t)) out)
          (shortenedInput L (maskUnion r (outputPositionMask t))
            (maskUnion z (inputPositionMask t)) inp) y w := by
  exact graph_nonzero_expansion L r z s
    (fun x => if restrictCoordinates out (L x) = y ∧ restrictCoordinates inp x = w then 1 else 0)

theorem restrictedGraphIncidence_action_expansion
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (out inp : Fin 16)
    (f : (MaskCoordinates inp → V) → ℝ) (y : MaskCoordinates out → V) :
    action (restrictedGraphIncidence L r z s out inp) f y =
      ∑ t ∈ s.powerset, (-1 : ℝ)^t.card * action
        (incidenceMultiplicity
          (shortenedOutput L (maskUnion r (outputPositionMask t))
            (maskUnion z (inputPositionMask t)) out)
          (shortenedInput L (maskUnion r (outputPositionMask t))
            (maskUnion z (inputPositionMask t)) inp)) f y := by
  unfold action
  simp_rw [restrictedGraphIncidence_expansion, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem restrictedGraphIncidence_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (out inp : Fin 16)
    (f : (MaskCoordinates inp → V) → ℝ) (g : (MaskCoordinates out → V) → ℝ) :
    (∑ y, g y * action (restrictedGraphIncidence L r z s out inp) f y) =
      ∑ x : Fin 4 → V,
        (if graphZeroConditions L r z x ∧ (∀ j ∈ s, graphCoordinate L x j ≠ 0)
          then 1 else 0) * (g (restrictCoordinates out (L x)) * f (restrictCoordinates inp x)) := by
  let p := fun x => graphZeroConditions L r z x ∧ (∀ j ∈ s, graphCoordinate L x j ≠ 0)
  let o : {x : Fin 4 → V // p x} → (MaskCoordinates out → V) :=
    fun x => restrictCoordinates out (L x.val)
  let i : {x : Fin 4 → V // p x} → (MaskCoordinates inp → V) :=
    fun x => restrictCoordinates inp x.val
  have he : restrictedGraphIncidence L r z s out inp = incidenceMultiplicity o i := by
    funext y w
    exact indicator_weight_subtype p (fun x =>
      if restrictCoordinates out (L x) = y ∧ restrictCoordinates inp x = w then 1 else 0)
  rw [he, incidenceMultiplicity_bilinear]
  exact (indicator_weight_subtype p (fun x =>
    g (restrictCoordinates out (L x)) * f (restrictCoordinates inp x))).symm

end AESMixing
