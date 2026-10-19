import AESMixing.AESPairing
import AESMixing.PairingFourier
import AESMixing.CoordinateTensor

/-! Tensor Fourier conjugation and the response identity for a code and its dual. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem sqrt_nat_power (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x^n) = (Real.sqrt x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem productPairing_fourier {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Fintype V] (B : CharacterPairing V) :
    pairingFourier (B.product I) = coordinateKernel (fun _ : I => pairingFourier B) := by
  funext x y
  unfold pairingFourier coordinateKernel CharacterPairing.product
  simp only [Fintype.card_fun, Nat.cast_pow, sqrt_nat_power _ (Nat.cast_nonneg _),
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

def fourierConjugate {X : Type*} [AddCommGroup X] [Fintype X]
    (B : CharacterPairing X) (T : X → X → ℝ) : X → X → ℝ :=
  kernelCompose (pairingFourier B) (kernelCompose T (pairingFourier B))

theorem fourierConjugate_energy {X : Type*} [AddCommGroup X] [Fintype X]
    (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0) (T : X → X → ℝ) (f : X → ℝ) :
    (∑ y, action (fourierConjugate B T) (action (pairingFourier B) f) y^2) =
      ∑ y, action T f y^2 := by
  unfold fourierConjugate
  rw [kernelCompose_action, kernelCompose_action, pairingFourier_twice B hchar]
  exact pairingFourier_energy B hchar (action T f)

theorem coordinate_fourierConjugate {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Fintype V] (B : CharacterPairing V) (T : V → V → ℝ) :
    fourierConjugate (B.product I) (coordinateKernel (fun _ : I => T)) =
      coordinateKernel (fun _ : I => fourierConjugate B T) := by
  unfold fourierConjugate
  rw [productPairing_fourier, coordinateKernel_compose, coordinateKernel_compose]

theorem code_dual_response_energy {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Fintype V] (B : CharacterPairing V)
    (hchar : ∀ x : V, x+x = 0) (T : V → V → ℝ)
    (C : AddSubgroup (I → V)) [Fintype C] :
    (∑ y, action (coordinateKernel (fun _ : I => T)) (unitSubgroupIndicator C) y^2) =
      ∑ y, action (coordinateKernel (fun _ : I => fourierConjugate B T))
        (unitSubgroupIndicator ((B.product I).annihilator C)) y^2 := by
  have hp : ∀ x : I → V, x+x = 0 := by
    intro x
    funext i
    exact hchar (x i)
  have he := fourierConjugate_energy (B.product I) hp (coordinateKernel (fun _ : I => T))
    (unitSubgroupIndicator C)
  rw [pairingFourier_subgroup, coordinate_fourierConjugate] at he
  exact he.symm

end AESMixing
