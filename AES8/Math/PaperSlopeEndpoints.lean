import AES8.Math.PaperSlopeFrameInput
import AESConcrete.WordFourierDiffusion
import AESMixing.DegreeComposition
import AESMixing.PointedProducts

/-! Removing the two endpoint activity columns after positive-degree
projection. Only a zero-preserving permutation is needed; no MDS bound or
input coefficient restriction is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeEndpoints
open AESMixing WordActivityFrame
open AESMixing.AES (maskBit)
open PaperSlopeFrameInput
open PaperSlopeCoincidenceMatrix PaperSlopeMetricComparison PaperSlopeMask
open AESConcrete.WordFourierDiffusion
set_option autoImplicit false
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] [Zero V]

theorem degree_zero_delta (hV : 1 < Fintype.card V) :
    degreeComponent (0 : V) 0 (fun x : Fin 4 → V => identityKernel x 0) =
      fun x => identityKernel x 0 := by
  rw [← degreeKernel_action]
  funext y
  have h := (degree_zero_pointed (0 : V) hV).zero_column y
  change degreeKernel 0 0 y (0 : Fin 4 → V) = (if y = 0 then 1 else 0) at h
  simpa [action, identityKernel] using h

theorem degree_zero_constant (hV : 1 < Fintype.card V) (c : ℝ) :
    degreeComponent (0 : V) 0 (fun _ : Fin 4 → V => c) = fun _ => c := by
  rw [← degreeKernel_action]
  funext y
  change (∑ x, degreeKernel 0 0 y x * c) = c
  rw [← Finset.sum_mul, (degree_zero_pointed (0 : V) hV).row_sum, one_mul]

theorem degree_two_delta (hV : 1 < Fintype.card V) :
    degreeComponent (0 : V) 2 (fun x : Fin 4 → V => identityKernel x 0) = 0 := by
  conv_lhs => rw [← degree_zero_delta hV]
  rw [degreeComponent_compose 0 hV, if_neg (by decide : (2 : Fin 5) ≠ 0)]

theorem degree_two_constant (hV : 1 < Fintype.card V) (c : ℝ) :
    degreeComponent (0 : V) 2 (fun _ : Fin 4 → V => c) = 0 := by
  conv_lhs => rw [← degree_zero_constant hV c]
  rw [degreeComponent_compose 0 hV, if_neg (by decide : (2 : Fin 5) ≠ 0)]

theorem frame_empty (x : Fin 4 → V) :
    frameColumn 0 (maskBit (0 : Fin 16)) x = identityKernel x 0 := by
  have hm : maskBit (0 : Fin 16) = fun _ => false := by decide
  simp only [frameColumn, hm, wordFrame, Bool.false_eq_true, if_false, identityKernel]
  rw [product_indicator]
  simp only [← funext_iff]
  rfl

theorem frame_full (x : Fin 4 → V) :
    frameColumn 0 (maskBit (15 : Fin 16)) x = (xi V)^4 := by
  have hm : maskBit (15 : Fin 16) = fun _ => true := by decide
  simp [frameColumn, hm, wordFrame]

omit [Fintype V] [DecidableEq V] in
theorem inverse_zero_iff (e : Equiv.Perm (Fin 4 → V)) (he : e 0 = 0)
    (y : Fin 4 → V) : e.symm y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have hh := congrArg e h
    simpa only [e.apply_symm_apply, he] using hh
  · intro h
    calc
      e.symm y = e.symm (e 0) := congrArg e.symm (h.trans he.symm)
      _ = 0 := e.symm_apply_apply 0

def projectedColumn (e : Equiv.Perm (Fin 4 → V)) (A : Fin 16) : (Fin 4 → V) → ℝ :=
  degreeComponent 0 2 (fun y => frameColumn 0 (maskBit A) (e.symm y))

theorem projected_empty (hV : 1 < Fintype.card V)
    (e : Equiv.Perm (Fin 4 → V)) (he : e 0 = 0) : projectedColumn e 0 = 0 := by
  unfold projectedColumn
  simp_rw [frame_empty, identityKernel, inverse_zero_iff e he]
  exact degree_two_delta hV

theorem projected_full (hV : 1 < Fintype.card V)
    (e : Equiv.Perm (Fin 4 → V)) : projectedColumn e 15 = 0 := by
  unfold projectedColumn
  simp_rw [frame_full]
  exact degree_two_constant hV _

theorem projected_synthesis (e : Equiv.Perm (Fin 4 → V))
    (u : Fin 16 → ℝ) (y : Fin 4 → V) :
    degreeComponent 0 2 (fun x => ∑ A : Fin 16,
      frameColumn 0 (maskBit A) (e.symm x) * u A) y =
      ∑ A : Fin 16, projectedColumn e A y * u A := by
  simp only [projectedColumn, ← degreeKernel_action, action, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem projected_synthesis_interior (hV : 1 < Fintype.card V)
    (e : Equiv.Perm (Fin 4 → V)) (he : e 0 = 0)
    (u : Fin 16 → ℝ) (y : Fin 4 → V) :
    degreeComponent 0 2 (fun x => ∑ A : Fin 16,
      frameColumn 0 (maskBit A) (e.symm x) * u A) y =
      ∑ A : Interior, projectedColumn e (mask A.val) y * u (mask A.val) := by
  rw [projected_synthesis, AESConcrete.ActivityEffectiveMetric.sum_split,
    projected_empty hV e he, projected_full hV e]
  simp only [Pi.zero_apply, zero_mul, zero_add]
  symm
  exact Equiv.sum_comp interiorEquiv
    (fun A : AESConcrete.ActivityEffectiveMetric.Interior => projectedColumn e A.val y * u A.val)

end AES8.PaperSlopeEndpoints
