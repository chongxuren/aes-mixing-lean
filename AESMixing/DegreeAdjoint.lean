import AESMixing.DegreeProjectionBounds
import AESMixing.DegreeKernel

/-! Reversing an invertible diffusion interchanges its degree blocks and
preserves their norm bounds. The proof uses finite inner products and
Cauchy--Schwarz, so no spectral theorem is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem adjoint_energy_le {V W : Type*} [Fintype V] [Fintype W]
    (A : (V → ℝ) → W → ℝ) (B : (W → ℝ) → V → ℝ) (c : ℝ)
    (hadj : ∀ f g, (∑ y, A f y * g y) = ∑ x, f x * B g x)
    (hbound : ∀ f, (∑ y, A f y ^ 2) ≤ c^2 * ∑ x, f x ^ 2)
    (g : W → ℝ) : (∑ x, B g x ^ 2) ≤ c^2 * ∑ y, g y ^ 2 := by
  have he : (∑ y, A (B g) y * g y) = ∑ x, B g x ^ 2 := by
    simpa only [pow_two] using hadj (B g) g
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A (B g)) g
  rw [he] at hcs
  have hg : 0 ≤ ∑ y, g y ^ 2 := Finset.sum_nonneg (fun y _ => sq_nonneg (g y))
  have hb : 0 ≤ ∑ x, B g x ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg (B g x))
  have hm := mul_le_mul_of_nonneg_right (hbound (B g)) hg
  by_cases hz : (∑ x, B g x ^ 2) = 0
  · rw [hz]
    exact mul_nonneg (sq_nonneg c) hg
  · have hp : 0 < ∑ x, B g x ^ 2 := lt_of_le_of_ne hb (Ne.symm hz)
    nlinarith

theorem degreeComponent_inner {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (j : Fin 5) (f g : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x * g x) =
      ∑ x, f x * degreeComponent z j g x := by
  simp_rw [← degreeKernel_action]
  simp only [action, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [degreeKernel_symmetric z j y x]
  ring

def degreeTransfer {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (i j : Fin 5) (e : Equiv.Perm (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  degreeComponent z i (fun y => degreeComponent z j f (e.symm y))

theorem degreeTransfer_adjoint {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (i j : Fin 5) (e : Equiv.Perm (Fin 4 → V))
    (f g : (Fin 4 → V) → ℝ) :
    (∑ y, degreeTransfer z i j e f y * g y) =
      ∑ x, f x * degreeTransfer z j i e.symm g x := by
  unfold degreeTransfer
  rw [degreeComponent_inner]
  calc
    (∑ y, degreeComponent z j f (e.symm y) * degreeComponent z i g y) =
        ∑ x, degreeComponent z j f x * degreeComponent z i g (e x) := by
      simpa only [e.symm_apply_apply] using
        (Equiv.sum_comp e (fun y =>
          degreeComponent z j f (e.symm y) * degreeComponent z i g y)).symm
    _ = ∑ x, f x * degreeComponent z j (fun y => degreeComponent z i g (e y)) x :=
      degreeComponent_inner z j f _

theorem degreeTransfer_reverse_bound {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (i j : Fin 5) (e : Equiv.Perm (Fin 4 → V)) (c : ℝ)
    (hbound : ∀ f, (∑ y, degreeTransfer z i j e f y ^ 2) ≤ c^2 * ∑ x, f x ^ 2)
    (g : (Fin 4 → V) → ℝ) :
    (∑ x, degreeTransfer z j i e.symm g x ^ 2) ≤ c^2 * ∑ y, g y ^ 2 :=
  adjoint_energy_le _ _ c (degreeTransfer_adjoint z i j e) hbound g

end AESMixing
