import AESConcrete.RestrictedProductDensity
import AESMixing.Finite

/-!
# Finite Cauchy--Schwarz mass bounds with normalized section weights

The two parametrizations refer to the same finite source. In the section
bound, only the independent outer product law is normalized: the source
being bounded is never conditioned on its event. These generic lemmas are
the finite-algebra part of `lem:marginals` (a), independent of MDS and AES.

The Cauchy--Schwarz argument follows the generic `paired_mass_le` and
`section_paired_mass_le` in the preserved legacy `RestrictedZeroEvents`.
This leaf avoids importing that module's concrete AES instantiations.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedZeroAlgebra

variable {D X Y : Type*} [Fintype D] [Fintype X] [Fintype Y]

/-- Equal collision budgets on two information sets bound their joint mass. -/
theorem paired_mass_le (e : D ≃ X) (f : D ≃ Y) (a : X → ℝ) (b : Y → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (ha : (∑ x : X, a x ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R) :
    (∑ c : D, a (e c) * b (f c)) ≤ R := by
  have ha' : (∑ c : D, a (e c) ^ 2) ≤ R := by
    rw [e.sum_comp (fun x => a x ^ 2)]
    exact ha
  have hb' : (∑ c : D, b (f c) ^ 2) ≤ R := by
    rw [f.sum_comp (fun y => b y ^ 2)]
    exact hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun c : D => a (e c)) (fun c : D => b (f c))
  have hp : (∑ c : D, a (e c) ^ 2) * (∑ c : D, b (f c) ^ 2) ≤ R ^ 2 := by
    have h := mul_le_mul ha' hb'
      (Finset.sum_nonneg (fun c _ => sq_nonneg (b (f c)))) hR
    nlinarith
  have habs : |∑ c : D, a (e c) * b (f c)| ≤ R :=
    (sq_le_sq₀ (abs_nonneg _) hR).mp (by
      simpa only [sq_abs] using hcs.trans hp)
  exact (le_abs_self _).trans habs

/-- Omitted probability factors are paid by an explicit nonnegative scale. -/
theorem dominated_paired_mass_le (e : D ≃ X) (f : D ≃ Y)
    (a : X → ℝ) (b : Y → ℝ) (g : D → ℝ) (scale R : ℝ)
    (hscale : 0 ≤ scale) (hR : 0 ≤ R)
    (ha : (∑ x : X, a x ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R)
    (hdom : ∀ c, g c ≤ scale * a (e c) * b (f c)) :
    (∑ c : D, g c) ≤ scale * R := by
  calc
    _ ≤ ∑ c : D, scale * a (e c) * b (f c) :=
      Finset.sum_le_sum (fun c _ => hdom c)
    _ = scale * ∑ c : D, a (e c) * b (f c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (paired_mass_le e f a b R hR ha hb) hscale

/-- Parametrizations sharing their first coordinate give a bijection on every
section. No conditional-law premise is imposed. -/
theorem section_bijective {D S U Y : Type*}
    (e : D ≃ S × U) (f : D ≃ S × Y)
    (hfirst : ∀ c, (f c).1 = (e c).1) (s : S) :
    Function.Bijective (fun u => (f (e.symm (s, u))).2) := by
  constructor
  · intro u v h
    have he : f (e.symm (s, u)) = f (e.symm (s, v)) := by
      apply Prod.ext
      · simp only [hfirst, Equiv.apply_symm_apply]
      · exact h
    have hc := f.injective he
    have hp := congrArg e hc
    simpa only [Equiv.apply_symm_apply, Prod.mk.injEq, true_and] using hp
  · intro y
    let c := f.symm (s, y)
    have hs : (e c).1 = s := by
      rw [← hfirst]
      exact congrArg Prod.fst (f.apply_symm_apply (s, y))
    refine ⟨(e c).2, ?_⟩
    have he : e.symm (s, (e c).2) = c := by
      apply e.injective
      rw [Equiv.apply_symm_apply, ← hs]
    change (f (e.symm (s, (e c).2))).2 = y
    rw [he]
    exact congrArg Prod.snd (f.apply_symm_apply (s, y))

/-- Cauchy--Schwarz on each section, averaged with the original normalized
outer law. The unnormalized event density `g` is only dominated. -/
theorem section_paired_mass_le {D S U Y : Type*}
    [Fintype D] [Fintype S] [Fintype U] [Fintype Y]
    (e : D ≃ S × U) (f : D ≃ S × Y)
    (hfirst : ∀ c, (f c).1 = (e c).1)
    (lambda : S → ℝ) (a : U → ℝ) (b : Y → ℝ) (g : D → ℝ) (R : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hR : 0 ≤ R) (ha : (∑ u : U, a u ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R)
    (hdom : ∀ c, g c ≤ lambda (e c).1 * a (e c).2 * b (f c).2) :
    (∑ c : D, g c) ≤ R := by
  let E : S → U ≃ Y := fun s => Equiv.ofBijective
    (fun u => (f (e.symm (s, u))).2) (section_bijective e f hfirst s)
  have hs (s : S) : (∑ u : U, a u * b ((f (e.symm (s, u))).2)) ≤ R :=
    paired_mass_le (Equiv.refl U) (E s) a b R hR ha hb
  calc
    _ = ∑ p : S × U, g (e.symm p) := (e.symm.sum_comp g).symm
    _ = ∑ s : S, ∑ u : U, g (e.symm (s, u)) := Fintype.sum_prod_type _
    _ ≤ ∑ s : S, lambda s * ∑ u : U, a u * b ((f (e.symm (s, u))).2) := by
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ ∑ u : U, lambda s * a u * b ((f (e.symm (s, u))).2) := by
          apply Finset.sum_le_sum
          intro u _
          simpa only [Equiv.apply_symm_apply] using hdom (e.symm (s, u))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
    _ ≤ ∑ s : S, lambda s * R := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hs s) (hlambda s))
    _ = R := by rw [← Finset.sum_mul, hmass, one_mul]

end AES8.PaperRestrictedZeroAlgebra
