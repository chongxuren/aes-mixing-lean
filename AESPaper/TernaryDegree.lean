import AESPaper.TernaryTensor
import AESMixing.FiveDegree

/-!
# Exact residual-degree grouping of the J/Z/R decomposition

The residual mask marks precisely those ternary labels equal to two.
Summing J and Z at every unmarked coordinate recovers the original activity
projection. Hence grouping ternary patterns by their number of R labels is
exactly the existing five-degree decomposition, not a new profile or a
degree that counts Z factors. Orthogonality supplies the exact energy sums.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.TernaryDegree
open AESMixing
open AESPaper.UniformBias (piece)
open AESPaper.TernaryTensor (tensorProjection tensorChannel)

/-- Bias labels do not count toward residual degree. -/
def residualMask {I : Type*} (a : I → Fin 3) : I → Bool :=
  fun i => decide (a i = 2)

section GenericMask
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- A false residual bit consists of both J and Z, while a true bit is R. -/
theorem piece_group_by_residual (z : V) (b : Bool) (y x : V) :
    (∑ s : Fin 3, if decide (s=2) = b then piece z s y x else 0) =
      degreePiece z b y x := by
  cases b <;>
    simp [Fin.sum_univ_succ, UniformBias.piece, UniformBias.biasKernel, degreePiece] <;> ring

theorem tensorProjection_group_mask (z : V) (b : I → Bool) (y x : I → V) :
    (∑ a : I → Fin 3, if residualMask a = b then tensorProjection z a y x else 0) =
      productProjection z b y x := by
  have hterm (a : I → Fin 3) :
      (if residualMask a = b then tensorProjection z a y x else 0) =
        ∏ i, if decide (a i=2) = b i then piece z (a i) (y i) (x i) else 0 := by
    by_cases hab : residualMask a = b
    · rw [if_pos hab]
      unfold tensorProjection
      apply Finset.prod_congr rfl
      intro i _
      rw [if_pos (show decide (a i=2) = b i from congrFun hab i)]
    · rw [if_neg hab]
      symm
      have hw : ∃ i, decide (a i=2) ≠ b i := by
        by_contra h
        push Not at h
        exact hab (funext h)
      obtain ⟨i,hi⟩ := hw
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
  simp_rw [hterm]
  rw [← Fintype.prod_sum
    (fun i (s : Fin 3) => if decide (s=2) = b i then piece z s (y i) (x i) else 0)]
  simp only [piece_group_by_residual, productProjection]

/-- The binary projection is exactly a grouping of ternary output projections. -/
theorem productProjection_grouped (z : V) (b : I → Bool) (f : (I → V) → ℝ) :
    action (productProjection z b) f =
      groupedFamily residualMask (fun a : I → Fin 3 => action (tensorProjection z a) f) b := by
  funext y
  have hk (x : I → V) : productProjection z b y x =
      ∑ a : I → Fin 3, if residualMask a=b then tensorProjection z a y x else 0 :=
    (tensorProjection_group_mask z b y x).symm
  change (∑ x, productProjection z b y x * f x) =
    ∑ a : I → Fin 3, if residualMask a=b then
      (∑ x, tensorProjection z a y x * f x) else 0
  simp_rw [hk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : residualMask a=b <;>
    simp only [ha, if_true, if_false, zero_mul, Finset.sum_const_zero]

end GenericMask

/-- Regrouping by a composite label does not change any vector component. -/
theorem groupedFamily_comp {A B C X : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype X] [DecidableEq B] [DecidableEq C]
    (g : A → B) (h : B → C) (f : A → X → ℝ) (c : C) :
    groupedFamily h (fun b => groupedFamily g f b) c =
      groupedFamily (fun a => h (g a)) f c := by
  funext x
  simp only [groupedFamily]
  have hterm (b : B) :
      (if h b=c then (∑ a : A, if g a=b then f a x else 0) else 0) =
        ∑ a : A, if g a=b then (if h b=c then f a x else 0) else 0 := by
    by_cases hb : h b=c <;> simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The existing five-degree index applied to precisely the R positions. -/
def residualIndex (a : Fin 4 → Fin 3) : Fin 5 := degreeIndex (residualMask a)

theorem residualIndex_val (a : Fin 4 → Fin 3) :
    (residualIndex a).val = (Finset.univ.filter (fun i : Fin 4 => a i=2)).card := by
  simp only [residualIndex, degreeIndex, residualDegree, residualMask, decide_eq_true_eq]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This is the original degreeComponent, with every ternary pattern retained. -/
theorem degreeComponent_eq_grouped (z : V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j f =
      groupedFamily residualIndex
        (fun a : Fin 4 → Fin 3 => action (tensorProjection z a) f) j := by
  unfold degreeComponent
  simp_rw [productProjection_grouped z]
  exact groupedFamily_comp residualMask degreeIndex
    (fun a : Fin 4 → Fin 3 => action (tensorProjection z a) f) j

theorem degree_energy (z : V) (hn : 1 < Fintype.card V) (j : Fin 5)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z j f y ^ 2) =
      ∑ a : Fin 4 → Fin 3, if residualIndex a=j then
        (∑ y, action (tensorProjection z a) f y ^ 2) else 0 := by
  rw [degreeComponent_eq_grouped]
  exact groupedFamily_energy residualIndex _
    (fun a b hab => TernaryTensor.tensorProjection_orthogonal z hn a b hab f f) j

theorem degree_channel (D : Fin 4 → V → V → ℝ) (z : V)
    (h : ∀ i, PointedBistochastic (D i) z) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j (action (coordinateKernel D) f) =
      groupedFamily residualIndex
        (fun a : Fin 4 → Fin 3 => action (tensorChannel D z a) f) j := by
  rw [degreeComponent_eq_grouped]
  simp only [TernaryTensor.project_channel D z h]

/-- Exact orthogonal energy sum, grouped by R count rather than Z count. -/
theorem degree_channel_energy (D : Fin 4 → V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (h : ∀ i, PointedBistochastic (D i) z)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z j (action (coordinateKernel D) f) y ^ 2) =
      ∑ a : Fin 4 → Fin 3, if residualIndex a=j then
        (∑ y, action (tensorChannel D z a) f y ^ 2) else 0 := by
  rw [degree_energy z hn j (action (coordinateKernel D) f)]
  simp only [TernaryTensor.project_channel D z h]

end AESPaper.TernaryDegree
