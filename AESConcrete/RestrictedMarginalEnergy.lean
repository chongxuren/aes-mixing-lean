import AESMixing.Convolution
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Energy of an unnormalized restricted marginal

Each fixed section of a source split is a bijection onto the observed
coordinates. A dominated nonnegative source therefore has a marginal
dominated by a scaled mixture of reindexed source densities. Weighted
Cauchy--Schwarz bounds the mixture energy. Domination is used only before
any signed channel; no signed-response monotonicity is asserted.

Actual MDS information sets and the source-density domination are separate
caller obligations. Constructive mathematics only; no attacks, manuscript
or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.RestrictedMarginalEnergy
open AESMixing

variable {S U Y C : Type*} [Fintype S] [Fintype U] [Fintype Y] [Fintype C]
  [DecidableEq Y]

/-- No event probability is divided out. -/
def marginal (coord : C → Y) (g : C → ℝ) (y : Y) : ℝ :=
  ∑ c : C, if coord c = y then g c else 0

def sectionMixture (E : S → U ≃ Y) (lambda : S → ℝ) (f : U → ℝ) (y : Y) : ℝ :=
  ∑ s : S, lambda s * f ((E s).symm y)

/-- The section equivalences identify exactly one source point per section. -/
theorem marginal_eq_section_sum (e : C ≃ S × U) (coord : C → Y)
    (E : S → U ≃ Y) (hcoord : ∀ s u, coord (e.symm (s,u)) = E s u)
    (g : C → ℝ) (y : Y) :
    marginal coord g y = ∑ s : S, g (e.symm (s, (E s).symm y)) := by
  classical
  unfold marginal
  calc
    _ = ∑ p : S × U, if coord (e.symm p) = y then g (e.symm p) else 0 :=
      (Equiv.sum_comp e.symm (fun c : C => if coord c = y then g c else 0)).symm
    _ = ∑ s : S, ∑ u : U, if E s u = y then g (e.symm (s,u)) else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [hcoord]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      have heq (u : U) : E s u = y ↔ u = (E s).symm y := by
        constructor
        · intro h
          exact (E s).injective (h.trans ((E s).apply_symm_apply y).symm)
        · rintro rfl
          exact (E s).apply_symm_apply y
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem marginal_nonneg (coord : C → Y) (g : C → ℝ) (hg : ∀ c, 0 ≤ g c) (y : Y) :
    0 ≤ marginal coord g y := by
  unfold marginal
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact hg c
  · exact le_rfl

/-- Exact source domination implies nonnegative-marginal domination only. -/
theorem marginal_le_scaled_mixture (e : C ≃ S × U) (coord : C → Y)
    (E : S → U ≃ Y) (hcoord : ∀ s u, coord (e.symm (s,u)) = E s u)
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale : ℝ)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) (y : Y) :
    marginal coord g y ≤ scale * sectionMixture E lambda f y := by
  rw [marginal_eq_section_sum e coord E hcoord]
  calc
    _ ≤ ∑ s : S, scale * lambda s * f ((E s).symm y) := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [Equiv.apply_symm_apply] using hdom (e.symm (s, (E s).symm y))
    _ = _ := by
      unfold sectionMixture
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Every reindexing has the same energy; the mixture weights have mass one.
The density f may be signed in this intermediate theorem. -/
theorem mixture_energy_le (E : S → U ≃ Y) (lambda : S → ℝ) (f : U → ℝ) (rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf : (∑ u : U, f u^2) ≤ rho) :
    (∑ y : Y, sectionMixture E lambda f y ^ 2) ≤ rho := by
  have he (s : S) : (∑ y : Y, f ((E s).symm y)^2) = ∑ u : U, f u^2 :=
    Equiv.sum_comp (E s).symm (fun u : U => f u^2)
  calc
    _ ≤ ∑ s : S, lambda s * ∑ y : Y, f ((E s).symm y)^2 :=
      AESMixing.mixture_energy lambda (fun s y => f ((E s).symm y)) hlambda hmass
    _ = ∑ s : S, lambda s * ∑ u : U, f u^2 := by simp_rw [he]
    _ = (∑ s : S, lambda s) * ∑ u : U, f u^2 := (Finset.sum_mul _ _ _).symm
    _ = ∑ u : U, f u^2 := by rw [hmass, one_mul]
    _ ≤ rho := hf

/-- The j<d restricted-source branch, before applying any signed channel. -/
theorem restricted_marginal_energy_le (e : C ≃ S × U) (coord : C → Y)
    (E : S → U ≃ Y) (hcoord : ∀ s u, coord (e.symm (s,u)) = E s u)
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u : U, f u^2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y : Y, marginal coord g y ^ 2) ≤ scale^2 * rho := by
  have hm (y : Y) : 0 ≤ sectionMixture E lambda f y := by
    unfold sectionMixture
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hlambda s) (hf_nonneg _))
  have hp (y : Y) : marginal coord g y ^ 2 ≤ (scale * sectionMixture E lambda f y)^2 :=
    (sq_le_sq₀ (marginal_nonneg coord g hg y) (mul_nonneg hscale (hm y))).mpr
      (marginal_le_scaled_mixture e coord E hcoord lambda f g scale hdom y)
  calc
    _ ≤ ∑ y : Y, (scale * sectionMixture E lambda f y)^2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = scale^2 * ∑ y : Y, sectionMixture E lambda f y ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ scale^2 * rho := mul_le_mul_of_nonneg_left
      (mixture_energy_le E lambda f rho hlambda hmass hf) (sq_nonneg scale)

/-- Convenience interface when the caller has section bijectivity directly. -/
theorem restricted_marginal_energy_le_of_bijective (e : C ≃ S × U) (coord : C → Y)
    (hsection : ∀ s : S, Function.Bijective (fun u : U => coord (e.symm (s,u))))
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u : U, f u^2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y : Y, marginal coord g y ^ 2) ≤ scale^2 * rho := by
  let E : S → U ≃ Y := fun s => Equiv.ofBijective
    (fun u : U => coord (e.symm (s,u))) (hsection s)
  exact restricted_marginal_energy_le e coord E (fun _ _ => rfl)
    lambda f g scale rho hlambda hmass hf_nonneg hf hscale hg hdom

end AESConcrete.RestrictedMarginalEnergy
