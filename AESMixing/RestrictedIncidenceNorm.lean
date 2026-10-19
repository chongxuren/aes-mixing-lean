import AESMixing.RestrictedIncidence
import AESMixing.IncidenceNorm

/-! Sum the surviving shortened-graph norms after exact inclusion-exclusion.
This is the operator estimate before support normalization and grouping by
support sizes; its input may have arbitrary correlations. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskSize)

theorem action_finset_linear {A B J : Type*} [Fintype B] [DecidableEq J]
    (K : A → B → ℝ) (s : Finset J) (c : J → ℝ) (f : J → B → ℝ) (y : A) :
    action K (fun x => ∑ j ∈ s, c j * f j x) y =
      ∑ j ∈ s, c j * action K (f j) y := by
  unfold action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

def shorteningNormSum (m : ℝ) (r z : Fin 16) (s : Finset GraphPosition)
    (out inp : Fin 16) : ℝ :=
  ∑ t ∈ s.powerset, incidenceNormCoefficient m
    (maskSize (maskUnion r (outputPositionMask t)) +
      maskSize (maskUnion z (inputPositionMask t))) (maskSize out) (maskSize inp)

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem restricted_incidence_l2
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16) (s : Finset GraphPosition)
    (hdisjoint : ∀ t ∈ s.powerset,
      MaskDisjoint (maskUnion r (outputPositionMask t)) out ∧
      MaskDisjoint (maskUnion z (inputPositionMask t)) inp)
    (k : MaskCoordinates inp) (f : (MaskCoordinates inp → V) → ℝ) :
    l2 (markedResidual out (action (restrictedGraphIncidence L r z s out inp)
      (markedResidual inp f))) ≤
      shorteningNormSum (Fintype.card V) r z s out inp * l2 f := by
  let A (t : Finset GraphPosition) := incidenceMultiplicity
    (shortenedOutput L (maskUnion r (outputPositionMask t))
      (maskUnion z (inputPositionMask t)) out)
    (shortenedInput L (maskUnion r (outputPositionMask t))
      (maskUnion z (inputPositionMask t)) inp)
  have hex : markedResidual out (action (restrictedGraphIncidence L r z s out inp)
      (markedResidual inp f)) =
      fun y => ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
        markedResidual out (action (A t) (markedResidual inp f)) y := by
    funext y
    unfold markedResidual
    have hinner := funext (restrictedGraphIncidence_action_expansion L r z s out inp
      (action (productProjection 0 (fun _ => true)) f))
    rw [hinner]
    exact action_finset_linear _ _ _ _ y
  rw [hex]
  calc
    _ ≤ ∑ t ∈ s.powerset, l2 (fun y => (-1 : ℝ)^t.card *
        markedResidual out (action (A t) (markedResidual inp f)) y) :=
      l2_finset_sum_le _ _
    _ ≤ ∑ t ∈ s.powerset, incidenceNormCoefficient (Fintype.card V)
        (maskSize (maskUnion r (outputPositionMask t)) +
          maskSize (maskUnion z (inputPositionMask t))) (maskSize out) (maskSize inp) * l2 f := by
      apply Finset.sum_le_sum
      intro t ht
      rw [l2_scale]
      simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact projected_incidence_l2 L hL hn _ _ out inp
        (hdisjoint t ht).1 (hdisjoint t ht).2 k f
    _ = _ := (Finset.sum_mul _ _ _).symm

end AESMixing
