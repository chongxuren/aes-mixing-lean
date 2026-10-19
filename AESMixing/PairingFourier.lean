import AESMixing.CharacterSubgroup
import AESMixing.KernelAlgebra

/-! Normalized finite Fourier transform and the exact code/dual-code identity. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable

variable {X : Type*} [AddCommGroup X] [Fintype X]

def pairingFourier (B : CharacterPairing X) (y x : X) : ℝ :=
  B.value y x / Real.sqrt (Fintype.card X)

theorem pairing_value_gram (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (x y : X) : gram B.value x y = if x = y then (Fintype.card X : ℝ) else 0 := by
  classical
  have he : x+y = 0 ↔ x = y := by
    constructor
    · intro h
      calc
        x = x+(y+y) := by rw [hchar, add_zero]
        _ = y := by rw [← add_assoc, h, zero_add]
    · rintro rfl
      exact hchar _
  unfold gram
  simp_rw [← B.add_right]
  rw [B.full_sum]
  simp only [he]

theorem pairingFourier_gram (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (x y : X) : gram (pairingFourier B) x y = if x = y then 1 else 0 := by
  classical
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold gram pairingFourier
  simp_rw [div_mul_div_comm, ← pow_two]
  rw [← Finset.sum_div, Real.sq_sqrt (Nat.cast_nonneg _)]
  change gram B.value x y / Fintype.card X = _
  rw [pairing_value_gram B hchar]
  split_ifs <;> simp [hn]

theorem pairingFourier_symmetric (B : CharacterPairing X) (x y : X) :
    pairingFourier B x y = pairingFourier B y x := by
  unfold pairingFourier
  rw [B.symmetric]

theorem pairingFourier_energy (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (f : X → ℝ) : (∑ y, action (pairingFourier B) f y^2) = ∑ x, f x^2 := by
  classical
  unfold action
  rw [gram_quadratic]
  simp_rw [pairingFourier_gram B hchar, mul_ite, mul_zero]
  simp [pow_two]

theorem pairingFourier_twice (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (f : X → ℝ) : action (pairingFourier B) (action (pairingFourier B) f) = f := by
  classical
  rw [← kernelCompose_action]
  have he : kernelCompose (pairingFourier B) (pairingFourier B) = identityKernel := by
    funext x y
    unfold kernelCompose
    simp_rw [pairingFourier_symmetric B x]
    change gram (pairingFourier B) x y = _
    exact pairingFourier_gram B hchar x y
  rw [he, identityKernel_action]

def unitSubgroupIndicator (C : AddSubgroup X) [Fintype C] (x : X) : ℝ :=
  if x ∈ C then 1 / Real.sqrt (Fintype.card C) else 0

theorem pairingFourier_subgroup_coefficient (B : CharacterPairing X)
    (C : AddSubgroup X) [Fintype C] (w : X) :
    action (pairingFourier B) (unitSubgroupIndicator C) w =
      if w ∈ B.annihilator C then
        (Fintype.card C : ℝ) / (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card C)) else 0 := by
  classical
  have hsum : (∑ x : X, if x ∈ C then B.value w x else 0) = ∑ c : C, B.value w c.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  calc
    _ = (∑ x : X, if x ∈ C then B.value w x else 0) /
        (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card C)) := by
      unfold action pairingFourier unitSubgroupIndicator
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ C <;> simp [hx, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by
      rw [hsum, B.subgroup_sum C w]
      split_ifs <;> simp

theorem pairingFourier_subgroup (B : CharacterPairing X)
    (C : AddSubgroup X) [Fintype C] :
    action (pairingFourier B) (unitSubgroupIndicator C) =
      unitSubgroupIndicator (B.annihilator C) := by
  classical
  have hc : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcpos : (0 : ℝ) ≤ Fintype.card C := Nat.cast_nonneg _
  have hdpos : (0 : ℝ) ≤ Fintype.card (B.annihilator C) := Nat.cast_nonneg _
  have hcard : (Fintype.card (B.annihilator C) : ℝ) * Fintype.card C = Fintype.card X := by
    exact_mod_cast B.annihilator_card C
  have hscale : (Fintype.card C : ℝ) /
      (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card C)) =
        1 / Real.sqrt (Fintype.card (B.annihilator C)) := by
    rw [← hcard, Real.sqrt_mul hdpos, mul_assoc, ← pow_two, Real.sq_sqrt hcpos]
    field_simp
  funext w
  rw [pairingFourier_subgroup_coefficient, hscale]
  rfl

end AESMixing
