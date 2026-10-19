import AESMixing.MarkedPrescriptions

/-! Uniform marked marginals annihilate every zero-sum input. This is
the cancellation of sufficiently high-dimensional shortenings in the
paper's residual incidence expansion. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem shortened_incidence_constant
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (ht : maskSize r+maskSize z+maskSize out+maskSize inp ≤ 4)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp) y w =
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+maskSize out+maskSize inp)) := by
  rw [incidenceMultiplicity_pair_card]
  change (Fintype.card {x : ShortenedGraph L r z //
    shortenedProjection L r z out inp x = (y,w)} : ℝ) = _
  rw [shortened_projection_fiber_uniform L hL r z out inp hr hz ht y w, Nat.cast_pow]

theorem shortened_incidence_zero_sum
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (ht : maskSize r+maskSize z+maskSize out+maskSize inp ≤ 4)
    (f : (MaskCoordinates inp → V) → ℝ) (hf : (∑ x, f x) = 0) :
    action (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp)) f = 0 :=
  constant_kernel_zero_sum _ _ (shortened_incidence_constant L hL r z out inp hr hz ht) f hf

theorem shortened_incidence_zero_dimension
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (ht : 4 ≤ maskSize r + maskSize z)
    (f : (MaskCoordinates inp → V) → ℝ) (hf : f 0 = 0) :
    action (incidenceMultiplicity (shortenedOutput L r z out) (shortenedInput L r z inp)) f = 0 := by
  funext y
  rw [incidenceMultiplicity_action]
  apply Finset.sum_eq_zero
  intro x _
  have hx : x.val = 0 := mds_graph_zero_high L hL r z ht x.val x.property
  have hi : shortenedInput L r z inp x = 0 := by
    funext j
    simp only [shortenedInput, hx, Pi.zero_apply]
  simp [hi, hf]

end AESMixing
