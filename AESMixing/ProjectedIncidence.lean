import AESMixing.IncidenceCancellation
import AESMixing.ResidualCoordinates

/-! Actual residual projections on both marked sides of a shortened graph.
The zero-dimensional and uniform-marginal terms vanish as operators. All
other terms satisfy the row/column incidence estimate after projection. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def markedResidual (s : Fin 16) (f : (MaskCoordinates s → V) → ℝ) :
    (MaskCoordinates s → V) → ℝ :=
  action (productProjection 0 (fun _ => true)) f

theorem markedResidual_zero (s : Fin 16) (k : MaskCoordinates s)
    (f : (MaskCoordinates s → V) → ℝ) : markedResidual s f 0 = 0 :=
  productProjection_marked_zero 0 (fun _ => true) k rfl f 0 rfl

theorem markedResidual_sum (hn : 1 < Fintype.card V) (s : Fin 16)
    (k : MaskCoordinates s) (f : (MaskCoordinates s → V) → ℝ) :
    (∑ x, markedResidual s f x) = 0 :=
  productProjection_marked_sum 0 hn (fun _ => true) k rfl f

theorem markedResidual_energy (hn : 1 < Fintype.card V) (s : Fin 16)
    (f : (MaskCoordinates s → V) → ℝ) :
    (∑ x, markedResidual s f x^2) ≤ ∑ x, f x^2 :=
  productProjection_energy_le 0 hn (fun _ => true) f

theorem markedResidual_inner (s : Fin 16) (f g : (MaskCoordinates s → V) → ℝ) :
    (∑ x, markedResidual s f x * g x) = ∑ x, f x * markedResidual s g x :=
  productProjection_inner 0 (fun _ => true) f g

theorem projected_incidence_high_dimension
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (ht : maskSize r+maskSize z+maskSize out+maskSize inp ≤ 4)
    (k : MaskCoordinates inp) (f : (MaskCoordinates inp → V) → ℝ) :
    action (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp))
      (markedResidual inp f) = 0 :=
  shortened_incidence_zero_sum L hL r z out inp hr hz ht _
    (markedResidual_sum hn inp k f)

theorem projected_incidence_zero_dimension
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (ht : 4 ≤ maskSize r+maskSize z)
    (k : MaskCoordinates inp) (f : (MaskCoordinates inp → V) → ℝ) :
    action (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp))
      (markedResidual inp f) = 0 :=
  shortened_incidence_zero_dimension L hL r z out inp ht _
    (markedResidual_zero inp k f)

theorem projected_incidence_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) :
    (∑ y, markedResidual out (action
      (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp))
      (markedResidual inp f)) y^2) ≤
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+maskSize out)) *
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+maskSize inp)) * ∑ x, f x^2 := by
  calc
    _ ≤ ∑ y, action (incidenceMultiplicity
        (shortenedOutput L r z out) (shortenedInput L r z inp))
        (markedResidual inp f) y^2 := markedResidual_energy hn out _
    _ ≤ _ := (shortened_incidence_energy L hL r z out inp hr hz _).trans
      (mul_le_mul_of_nonneg_left (markedResidual_energy hn inp f) (by positivity))

end AESMixing
