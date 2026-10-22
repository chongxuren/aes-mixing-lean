import AES8.Math.PaperSymbolicMDS
import AES8.Math.PaperSymbolicSlopeTable
import AES8.Math.PaperSymbolicWitness

noncomputable section
namespace AES8.PaperSymbolicShortening
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable PaperSymbolicMDS
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

def evaluatedWitness (a : F) (pair : Bool) (k : Fin 20) : Fin 4 → F :=
  fun i => aeval a (witness pair k i)

theorem eval_graphWord (a : F) (x : Fin 4 → P) (i : Fin 8) :
    aeval a (graphWord (X : P) x i) =
      graphWord a (fun j => aeval a (x j)) i := by
  simp only [graphWord, Matrix.mulVec, dotProduct, map_sum, map_mul,
    eval_graphMatrix]

theorem evaluatedWitness_zero (a : F) (pair : Bool) (k : Fin 20)
    (i : Fin 8) (hi : i ∈ zeros pair k) :
    graphWord a (evaluatedWitness a pair k) i = 0 := by
  unfold evaluatedWitness
  rw [← eval_graphWord, witness_zero pair k i hi, map_zero]

theorem evaluatedWitness_first (a : F) (pair : Bool) (k : Fin 20) :
    graphWord a (evaluatedWitness a pair k) 4 = aeval a (raw pair k).2 := by
  unfold evaluatedWitness
  rw [← eval_graphWord, witness_first]

theorem evaluatedWitness_second (a : F) (pair : Bool) (k : Fin 20) :
    graphWord a (evaluatedWitness a pair k) (secondMark pair) = aeval a (raw pair k).1 := by
  unfold evaluatedWitness
  rw [← eval_graphWord, witness_second]

def Shortened (a : F) (pair : Bool) (k : Fin 20) (x : Fin 4 → F) : Prop :=
  ∀ i ∈ zeros pair k, graphWord a x i = 0

theorem denominator_ne_zero (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (k : Fin 20) : aeval a (raw pair k).2 ≠ 0 :=
  PaperAlgebraicSpecialization.eval_ne_zero a _ (raw_bounds pair k).2.1
    (by have := (raw_bounds pair k).2.2.2; omega)

theorem shortened_eq_scaled_witness (a : F)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (pair : Bool) (k : Fin 20)
    (x : Fin 4 → F) (hx : Shortened a pair k x) :
    x = (graphWord a x 4 / aeval a (raw pair k).2) • evaluatedWitness a pair k := by
  apply sub_eq_zero.mp
  apply graph_zero_of_four a ha (insert 4 (zeros pair k)) (first_zero_set_card pair k)
  intro i hi
  simp only [graphWord, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rcases Finset.mem_insert.mp hi with rfl | hi
  · change graphWord a x 4 - _ * graphWord a (evaluatedWitness a pair k) 4 = 0
    rw [evaluatedWitness_first, div_mul_cancel₀ _ (denominator_ne_zero a ha pair k)]
    exact sub_self _
  · change graphWord a x i - _ * graphWord a (evaluatedWitness a pair k) i = 0
    rw [hx i hi, evaluatedWitness_zero a pair k i hi, mul_zero, sub_self]

/-- Literal marked image of the graph with all other unmarked coordinates
fixed to zero; its equation uses precisely the table's slope convention. -/
theorem shortened_marked_image (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (k : Fin 20) (z w : F) :
    (∃ x, Shortened a pair k x ∧ graphWord a x 4 = z ∧
      graphWord a x (secondMark pair) = w) ↔ w = slope a pair k * z := by
  constructor
  · rintro ⟨x,hx,rfl,rfl⟩
    have he := congrArg (fun y => graphWord a y (secondMark pair))
      (shortened_eq_scaled_witness a ha pair k x hx)
    simp only [graphWord, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at he
    change graphWord a x (secondMark pair) =
      (graphWord a x 4 / _) * graphWord a (evaluatedWitness a pair k) (secondMark pair) at he
    rw [evaluatedWitness_second] at he
    rw [he, slope]
    ring
  · intro hw
    refine ⟨(z / aeval a (raw pair k).2) • evaluatedWitness a pair k, ?_, ?_, ?_⟩
    · intro i hi
      simp only [graphWord, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      change _ * graphWord a (evaluatedWitness a pair k) i = 0
      rw [evaluatedWitness_zero a pair k i hi, mul_zero]
    · simp only [graphWord, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      change _ * graphWord a (evaluatedWitness a pair k) 4 = z
      rw [evaluatedWitness_first, div_mul_cancel₀ _ (denominator_ne_zero a ha pair k)]
    · simp only [graphWord, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      change _ * graphWord a (evaluatedWitness a pair k) (secondMark pair) = w
      rw [evaluatedWitness_second, hw, slope]
      ring

end AES8.PaperSymbolicShortening
