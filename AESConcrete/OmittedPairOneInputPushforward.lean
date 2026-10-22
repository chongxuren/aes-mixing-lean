import AESConcrete.InvariantSubspaceEnergy

/-!
# Finite pushforward through an explicitly parametrized fiber

Generic finite-fiber helper. An equivalence S = U x X whose second coordinate
is E gives exact fibers, an exact finite-pushforward formula and an energy
INEQUALITY with factor |U|. E need not be injective. The amplitude is
arbitrary, joint and signed. No AES response bound or desired-bound premise is
assumed here.

Constructive fixed AES10/14/16 work only.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedPairOneInputPushforward
open AESConcrete.InvariantSubspaceEnergy (zeroExtend)

attribute [local instance] Classical.propDecidable

variable {S U X : Type*} [Fintype S] [Fintype U] [Fintype X]

/-- Exact fiber coordinates, without an injectivity assertion about E. -/
def fiberEquiv (E : S → X) (e : S ≃ U × X)
    (hE : ∀ s, (e s).2 = E s) (x : X) : {s : S // E s = x} ≃ U where
  toFun s := (e s.val).1
  invFun u := ⟨e.symm (u, x),
    ((hE (e.symm (u, x))).symm.trans
      (congrArg Prod.snd (e.apply_symm_apply (u, x))))⟩
  left_inv s := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact ((hE s.val).trans s.property).symm
  right_inv u := congrArg Prod.fst (e.apply_symm_apply (u, x))

theorem fiber_card (E : S → X) (e : S ≃ U × X)
    (hE : ∀ s, (e s).2 = E s) (x : X) :
    Fintype.card {s : S // E s = x} = Fintype.card U :=
  Fintype.card_congr (fiberEquiv E e hE x)

/-- Each actual finite fiber is summed once, with the original signed amplitude. -/
theorem pushforward_eq_sum (E : S → X) (e : S ≃ U × X)
    (hE : ∀ s, (e s).2 = E s) (mu : S → ℝ) (x : X) :
    zeroExtend E mu x = ∑ u : U, mu (e.symm (u, x)) := by
  classical
  unfold zeroExtend
  calc
    (∑ s : S, if E s = x then mu s else 0) =
        ∑ p : U × X, if p.2 = x then mu (e.symm p) else 0 := by
      rw [← e.sum_comp
        (fun p : U × X => if p.2 = x then mu (e.symm p) else 0)]
      apply Finset.sum_congr rfl
      intro s _
      rw [hE s, e.symm_apply_apply]
    _ = ∑ u : U, mu (e.symm (u, x)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      simp

/-- Summing every section recovers the entire source energy exactly. -/
theorem section_energy (e : S ≃ U × X) (mu : S → ℝ) :
    (∑ x : X, ∑ u : U, mu (e.symm (u, x)) ^ 2) = ∑ s : S, mu s ^ 2 := by
  calc
    (∑ x : X, ∑ u : U, mu (e.symm (u, x)) ^ 2) =
        ∑ u : U, ∑ x : X, mu (e.symm (u, x)) ^ 2 := Finset.sum_comm
    _ = ∑ p : U × X, mu (e.symm p) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ s : S, mu s ^ 2 := e.symm.sum_comp (fun s => mu s ^ 2)

/-- Cauchy--Schwarz costs the actual fiber size, not the entire source size.
This is deliberately an inequality; injective zero-extension energy is unused. -/
theorem pushforward_energy_le (E : S → X) (e : S ≃ U × X)
    (hE : ∀ s, (e s).2 = E s) (mu : S → ℝ) :
    (∑ x : X, zeroExtend E mu x ^ 2) ≤
      (Fintype.card U : ℝ) * ∑ s : S, mu s ^ 2 := by
  classical
  simp_rw [pushforward_eq_sum E e hE mu]
  calc
    (∑ x : X, (∑ u : U, mu (e.symm (u, x))) ^ 2) ≤
        ∑ x : X, (Fintype.card U : ℝ) *
          ∑ u : U, mu (e.symm (u, x)) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : U => (1 : ℝ)) (fun u => mu (e.symm (u, x)))
    _ = (Fintype.card U : ℝ) * ∑ s : S, mu s ^ 2 := by
      rw [← Finset.mul_sum, section_energy e mu]

end AESConcrete.OmittedPairOneInputPushforward
