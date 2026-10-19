import AESConcrete.WordMomentAssembly

/-!
# Orthogonal assembly of physical marked-position Hilbert--Schmidt bounds

The sixteen input and sixteen output patterns are the actual product
projections. Their squared HS norms add within each degree block. Only
their quantitative bounds remain premises of the final table reduction.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MarkedDegreeHilbertSchmidt
open AESMixing
open HilbertSchmidtEnergy (hs hs_sq hs_nonneg hs_transpose)
open DegreeHilbertSchmidt (block)

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

theorem compose_assoc {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C]
    (K : D → C → ℝ) (L : C → B → ℝ) (M : B → A → ℝ) :
    kernelCompose (kernelCompose K L) M = kernelCompose K (kernelCompose L M) := by
  classical
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action]

def patternBlock (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (a b : Fin 4 → Bool) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (productProjection z a) (kernelCompose K (productProjection z b))

theorem left_degree_hs (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → X → ℝ) (i : Fin 5) :
    hs (kernelCompose (degreeKernel z i) K)^2 =
      ∑ a : Fin 4 → Bool, if degreeIndex a = i then
        hs (kernelCompose (productProjection z a) K)^2 else 0 := by
  rw [hs_sq, Finset.sum_comm]
  change (∑ x, ∑ y, action (degreeKernel z i) (fun v => K v x) y^2) = _
  simp_rw [degreeKernel_action, degreeComponent_energy z hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degreeIndex a = i
  · simp only [ha, if_true, hs_sq]
    rw [Finset.sum_comm]
    rfl
  · simp only [ha, if_false, Finset.sum_const_zero]

theorem transpose_compose {Y : Type*} [Fintype Y]
    (A : X → Y → ℝ) (B : Y → (Fin 4 → V) → ℝ) :
    (fun x y => kernelCompose A B y x) =
      kernelCompose (fun x y => B y x) (fun x y => A y x) := by
  funext x y
  simp only [kernelCompose, mul_comm]

theorem right_degree_hs (z : V) (hn : 1 < Fintype.card V)
    (K : X → (Fin 4 → V) → ℝ) (j : Fin 5) :
    hs (kernelCompose K (degreeKernel z j))^2 =
      ∑ b : Fin 4 → Bool, if degreeIndex b = j then
        hs (kernelCompose K (productProjection z b))^2 else 0 := by
  have ht : (fun x y => degreeKernel z j y x) = degreeKernel z j :=
    funext (fun x => funext (fun y => degreeKernel_symmetric z j y x))
  rw [← hs_transpose (kernelCompose K (degreeKernel z j)), transpose_compose, ht,
    left_degree_hs z hn]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : degreeIndex b = j
  · simp only [hb, if_true]
    have hp : (fun x y => productProjection z b y x) = productProjection z b :=
      funext (fun x => funext (fun y => productProjection_symmetric z b y x))
    rw [← hs_transpose (kernelCompose K (productProjection z b)), transpose_compose, hp]
  · simp only [hb, if_false]

theorem pattern_block_pythagoras (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) :
    hs (block z K i j)^2 = ∑ a : Fin 4 → Bool, ∑ b : Fin 4 → Bool,
      if degreeIndex a = i ∧ degreeIndex b = j then hs (patternBlock z K a b)^2 else 0 := by
  rw [block, left_degree_hs z hn]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degreeIndex a = i
  · simp only [ha, if_true, true_and]
    rw [← compose_assoc, right_degree_hs z hn]
    apply Finset.sum_congr rfl
    intro b _
    simp only [patternBlock, compose_assoc]
  · simp only [ha, if_false, false_and, Finset.sum_const_zero]

set_option maxRecDepth 100000 in
theorem pattern_count (i : Fin 5) :
    (∑ a : Fin 4 → Bool, if degreeIndex a = i then 1 else 0) = Nat.choose 4 i.val := by
  fin_cases i <;> decide

theorem pattern_count_real (i : Fin 5) :
    (∑ a : Fin 4 → Bool, if degreeIndex a = i then (1:ℝ) else 0) = Nat.choose 4 i.val := by
  exact_mod_cast pattern_count i

theorem degree_hs_sq_le (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) (c : ℝ)
    (h : ∀ a b, degreeIndex a = i → degreeIndex b = j →
      hs (patternBlock z K a b)^2 ≤ c) :
    hs (block z K i j)^2 ≤ (Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val * c := by
  rw [pattern_block_pythagoras z hn]
  calc
    _ ≤ ∑ a : Fin 4 → Bool, ∑ b : Fin 4 → Bool,
        if degreeIndex a = i ∧ degreeIndex b = j then c else 0 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases hab : degreeIndex a = i ∧ degreeIndex b = j
      · simpa only [hab.1, hab.2, and_self, if_true] using h a b hab.1 hab.2
      · simp only [hab, if_false, le_refl]
    _ = _ := by
      have hi (a b : Fin 4 → Bool) :
          (if degreeIndex a = i ∧ degreeIndex b = j then c else 0) =
          (if degreeIndex a = i then (1:ℝ) else 0) *
            (if degreeIndex b = j then (1:ℝ) else 0) * c := by
        by_cases ha : degreeIndex a = i <;> by_cases hb : degreeIndex b = j <;> simp [ha,hb]
      simp_rw [hi, ← Finset.sum_mul, ← Finset.mul_sum, pattern_count_real]
      rw [← Finset.sum_mul, pattern_count_real]

theorem degree_table_of_pattern_bounds
    (left right : ByteOrientations.Orientation) (inverse : Bool)
    (h : ∀ a b : Fin 4 → Bool,
      hs (patternBlock 0 (WordMomentAssembly.residual left right inverse) a b)^2 ≤
        WordMomentNumbers.markedCap ((degreeIndex a).val + (degreeIndex b).val) /
          4294967296) :
    WordMomentAssembly.HasDegreeHSBounds left right inverse := by
  intro i j
  have hb := degree_hs_sq_le (0 : BinaryWord 8) (by norm_num [BinaryWord.card])
    (WordMomentAssembly.residual left right inverse) i j
    (WordMomentNumbers.markedCap (i.val+j.val)/4294967296)
    (fun a b ha hb => by simpa only [ha,hb] using h a b)
  have hc := div_le_div_of_nonneg_right (WordMomentNumbers.marked_to_degree i j)
    (by norm_num : (0:ℝ) ≤ 4294967296)
  have hsq : hs (block 0 (WordMomentAssembly.residual left right inverse) i j)^2 ≤
      (WordMomentNumbers.hs i j / 65536)^2 := by
    calc
      _ ≤ (Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val *
          (WordMomentNumbers.markedCap (i.val+j.val)/4294967296) := hb
      _ = ((Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val *
          WordMomentNumbers.markedCap (i.val+j.val))/4294967296 := by ring
      _ ≤ WordMomentNumbers.hs i j ^ 2 / 4294967296 := hc
      _ = _ := by ring
  exact (sq_le_sq₀ (hs_nonneg _) (div_nonneg (WordMomentNumbers.hs_nonneg i j)
    (by norm_num))).mp hsq

end AESConcrete.MarkedDegreeHilbertSchmidt
