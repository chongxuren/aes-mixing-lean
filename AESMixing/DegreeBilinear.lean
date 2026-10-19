import AESMixing.DegreeAdjoint
import AESMixing.L2Sums

/-! A bilinear estimate between two degree spaces implies the energy
bound for the actual degree-transfer operator, with the projected input
norm retained. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem degreeTransfer_energy_of_bilinear {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (i j : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ f g : (Fin 4 → V) → ℝ,
      |∑ x, degreeComponent z i g (e x)*degreeComponent z j f x| ≤
        c*l2 (degreeComponent z j f)*l2 (degreeComponent z i g))
    (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeTransfer z i j e f x^2) ≤ c^2 * ∑ x, degreeComponent z j f x^2 := by
  let g := degreeTransfer z i j e f
  have he : (∑ x, degreeComponent z i g (e x)*degreeComponent z j f x) =
      ∑ y, g y^2 := by
    calc
      _ = ∑ y, degreeComponent z i g y*degreeComponent z j f (e.symm y) := by
        simpa only [e.symm_apply_apply] using Equiv.sum_comp e
          (fun y => degreeComponent z i g y*degreeComponent z j f (e.symm y))
      _ = ∑ y, g y*degreeComponent z i (fun x => degreeComponent z j f (e.symm x)) y :=
        degreeComponent_inner z i g _
      _ = _ := by simp only [g,degreeTransfer,pow_two]
  have hp : l2 (degreeComponent z i g) ≤ l2 g := by
    have hbound := degreeComponent_energy_le z hn i g
    simpa only [one_mul] using l2_le_of_energy (degreeComponent z i g) g 1 (by norm_num)
      (by simpa only [one_pow,one_mul] using hbound)
  have hb := h f g
  rw [he,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),← l2_sq g] at hb
  have hg := l2_nonneg g
  have hfg := l2_nonneg (degreeComponent z j f)
  have ht := hb.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hc hfg))
  have hnorm : l2 g ≤ c*l2 (degreeComponent z j f) := by
    by_cases hz : l2 g = 0
    · rw [hz]
      exact mul_nonneg hc hfg
    · have hg' : 0 < l2 g := lt_of_le_of_ne hg (Ne.symm hz)
      exact le_of_mul_le_mul_right (by simpa only [pow_two] using ht) hg'
  have hsq := (sq_le_sq₀ hg (mul_nonneg hc hfg)).mpr hnorm
  simpa only [mul_pow,l2_sq,g] using hsq

end AESMixing
