import AESMixing.FourierGram
import AESMixing.DualInformation

/-! Both code-moment branches as bounds on the actual normalized subgroup
indicator. The information-set maps explicitly identify their coordinates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable

theorem subgroup_action_formula {X : Type*} [AddCommGroup X] [Fintype X]
    (K : X → X → ℝ) (C : AddSubgroup X) [Fintype C] (y : X) :
    action K (unitSubgroupIndicator C) y =
      (∑ c : C, K y c.val) / Real.sqrt (Fintype.card C) := by
  have hsum : (∑ x : X, if x ∈ C then K y x else 0) = ∑ c : C, K y c.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hsum, Finset.sum_div]
  unfold action unitSubgroupIndicator
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ C <;> simp [hx, div_eq_mul_inv]

variable {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V]

theorem subgroup_codeResponse (T : V → V → ℝ)
    (C : AddSubgroup (CodePosition I J → V)) [Fintype C]
    (e f : C ≃ (I → V)) (rest : C → J → V)
    (hc : ∀ c : C, codeCoordinates e f rest c = c.val) :
    action (coordinateKernel (fun _ : CodePosition I J => T)) (unitSubgroupIndicator C) =
      codeResponse T e f rest := by
  funext y
  rw [subgroup_action_formula]
  unfold codeResponse
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  unfold codeKernel
  rw [hc c]
  rfl

theorem subgroup_code_moment_low (T : V → V → ℝ)
    (C : AddSubgroup (CodePosition I J → V)) [Fintype C]
    (e f : C ≃ (I → V)) (rest : C → J → V)
    (hc : ∀ c : C, codeCoordinates e f rest c = c.val)
    (delta : ℝ) (hd : 0 ≤ delta) (hdiag : ∀ x, gram T x x ≤ delta) :
    (∑ y, action (coordinateKernel (fun _ : CodePosition I J => T))
      (unitSubgroupIndicator C) y^2) ≤
      ((∑ xy : V × V, gram T xy.1 xy.2^2)^Fintype.card I *
        delta^Fintype.card J) / (Fintype.card V : ℝ)^Fintype.card I := by
  rw [subgroup_codeResponse T C e f rest hc]
  have he := low_code_response_bound T e f rest delta hd hdiag
  rw [Fintype.card_congr e, Fintype.card_fun, Nat.cast_pow] at he
  exact he

theorem subgroup_code_moment_dual (B : CharacterPairing V)
    (hchar : ∀ x : V, x+x = 0) (T : V → V → ℝ)
    (C : AddSubgroup (CodePosition I J → V)) [Fintype C]
    (e f : ((B.product (CodePosition I J)).annihilator C) ≃ (I → V))
    (rest : ((B.product (CodePosition I J)).annihilator C) → J → V)
    (hc : ∀ c, codeCoordinates e f rest c = c.val)
    (delta : ℝ) (hd : 0 ≤ delta)
    (hdiag : ∀ x, gram (fourierConjugate B T) x x ≤ delta) :
    (∑ y, action (coordinateKernel (fun _ : CodePosition I J => T))
      (unitSubgroupIndicator C) y^2) ≤
      ((∑ xy : V × V, gram T xy.1 xy.2^2)^Fintype.card I *
        delta^Fintype.card J) / (Fintype.card V : ℝ)^Fintype.card I := by
  rw [code_dual_response_energy B hchar]
  have he := subgroup_code_moment_low (fourierConjugate B T) _ e f rest hc delta hd hdiag
  rw [fourierConjugate_gram_moment B hchar] at he
  exact he

end AESMixing
