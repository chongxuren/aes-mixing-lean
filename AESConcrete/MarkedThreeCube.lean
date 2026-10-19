import AESConcrete.SurvivorCubeNumbers
import AESConcrete.FrameHamming
import AESConcrete.MarkedThreeNumbers

/-!
# Signed three-mark coefficient costs and exact finite aggregate

The distance-one coefficient is negative and therefore uses the lower
containment endpoint. All other off-diagonal cases use absolute estimates.
This module evaluates only the Boolean coefficient sum. Actual overlap
estimates must be supplied separately before it can bound an AES block.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MarkedThreeCube
open SurvivorRelabel FrameHamming

attribute [local instance] Classical.propDecidable
local instance (priority := 10000) (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)
set_option maxRecDepth 100000

theorem distance_cons (n : ℕ) (b c : Bool) (s t : Fin n → Bool) :
    distance (Fin.cons b s) (Fin.cons c t) = (if b ≠ c then 1 else 0) + distance s t := by
  simp only [distance_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem distance_zero (s t : Fin 0 → Bool) : distance s t = 0 := by
  simp [distance]

def pairCost : ℕ → ℝ
  | 0 => ByteLineBounds.a3
  | 1 => -(1/16)*(ContainmentCodeBounds.z3-ContainmentCodeBounds.h3)
  | 2 => (1/16)^2*LineOverlap.eta1
  | 3 => (1/16)^3*MixedCodeBounds.f3
  | 4 => (1/16)^4*LineOverlap.eta2
  | 5 => (1/16)^5*ByteLineBounds.b3
  | _ => 0

def pairEstimate (d : ℕ) (b : ℝ) : Prop :=
  match d with
  | 0 => b ≤ ByteLineBounds.a3
  | 1 => ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 ≤ b
  | 2 => |b| ≤ LineOverlap.eta1
  | 3 => |b| ≤ MixedCodeBounds.f3
  | 4 => |b| ≤ LineOverlap.eta2
  | 5 => |b| ≤ ByteLineBounds.b3
  | _ => False

theorem coefficient_mul_le_cost (d : ℕ) (hd : d ≤ 5) (b : ℝ)
    (h : pairEstimate d b) : (-(1/16 : ℝ))^d * b ≤ pairCost d := by
  interval_cases d <;> norm_num [pairEstimate, pairCost] at h ⊢
  · exact h
  · linarith
  · have h' := (abs_le.mp h).2; linarith
  · have h' := (abs_le.mp h).1; linarith
  · have h' := (abs_le.mp h).2; linarith
  · have h' := (abs_le.mp h).1; linarith

def signedCubeBound (I : Type*) [Fintype I] : ℝ :=
  (256/255 : ℝ)^Fintype.card I *
    ∑ s : I → Bool, if cubeSurvives 3 s then
      (∑ t : I → Bool, if cubeSurvives 3 t then pairCost (distance s t) else 0)
    else 0

theorem signedCubeBound_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) : signedCubeBound I = signedCubeBound J := by
  have hrow (s : J → Bool) :
      (∑ t : I → Bool, if cubeSurvives 3 t then
        pairCost (distance (cubeReindex e s) t) else 0) =
      ∑ t : J → Bool, if cubeSurvives 3 t then pairCost (distance s t) else 0 := by
    rw [← (cubeReindex e).sum_comp]
    simp only [cubeReindex, Equiv.coe_fn_mk, cubeSurvives_comp, distance_comp]
  unfold signedCubeBound
  rw [Fintype.card_congr e]
  congr 1
  rw [← (cubeReindex e).sum_comp]
  simp only [cubeSurvives_reindex, hrow]

theorem signedCubeBound_fin_five :
    signedCubeBound (Fin 5) = MarkedThreeNumbers.groupedBound := by
  norm_num [signedCubeBound, cubeSurvives, SurvivorCubeNumbers.falseCount_cons, SurvivorCubeNumbers.falseCount_zero,
    SurvivorCubeNumbers.sum_cube_succ 0, SurvivorCubeNumbers.sum_cube_succ 1,
    SurvivorCubeNumbers.sum_cube_succ 2, SurvivorCubeNumbers.sum_cube_succ 3,
    SurvivorCubeNumbers.sum_cube_succ 4, SurvivorCubeNumbers.sum_cube_zero,
    distance_cons, distance_zero, Fin.sum_univ_succ, pairCost,
    MarkedThreeNumbers.groupedBound, ByteLineBounds.a3, ByteLineBounds.cubeBound,
    ByteGramResources.cubeNumerator, ByteLineBounds.b3, ByteLineBounds.mixedCubeBound,
    LineOverlap.eta1, LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3, MixedCodeBounds.f3]

end AESConcrete.MarkedThreeCube
