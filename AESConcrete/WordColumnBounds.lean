import AESMixing.SuperboxStationarity
import AESMixing.Product

/-!
Concrete column-centering identities for the finite AES word channel.

This module keeps the exact centering step separate from a full word-column
collision estimate. In particular, it does not assume or claim the unproved
sharp full-column bound 17/(15q). The actual AES word theorem below has only
the nonzero-column condition. Its byte and first-substitution specializations
also have no quantitative AES hypothesis. The old AESMixing source is an
imported read-only dependency; all new results have distinct names here.

The research scope is constructive: finite kernel identities and correctness
bounds only, with no cryptanalytic attack or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete
open AESMixing

section FiniteCentering

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact energy of a nonzero column of the local activity projection. -/
theorem activity_column_energy_exact (z : V) (hn : 1 < Fintype.card V)
    (a : V) (ha : a ≠ z) :
    (∑ b, activityMatrix z b a ^ 2) = 1 / (Fintype.card V - 1 : ℝ) := by
  let c : ℝ := 1 / (Fintype.card V - 1 : ℝ)
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (Fintype.card V - 1 : ℝ) ≠ 0 := by linarith
  have hp (b : V) : activityMatrix z b a ^ 2 =
      c ^ 2 - if b = z then c ^ 2 else 0 := by
    by_cases hb : b = z
    · subst b
      simp [activityMatrix, ha]
    · simp [activityMatrix, hb, ha, c]
  calc
    (∑ b, activityMatrix z b a ^ 2) =
        (Fintype.card V : ℝ) * c ^ 2 - c ^ 2 := by
      simp_rw [hp]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = 1 / (Fintype.card V - 1 : ℝ) := by
      dsimp [c]
      field_simp [hd] <;> ring

/-- Exact column-energy subtraction, independent of a contraction estimate. -/
theorem pointed_residual_column_energy_exact {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (hn : 1 < Fintype.card V)
    (a : V) (ha : a ≠ z) :
    (∑ b, residualMatrix D z b a ^ 2) =
      (∑ b, D b a ^ 2) - 1 / (Fintype.card V - 1 : ℝ) := by
  let c : ℝ := 1 / (Fintype.card V - 1 : ℝ)
  have hp (b : V) : D b a * activityMatrix z b a = D b a * c := by
    by_cases hb : b = z
    · subst b
      rw [h.zero_row, if_neg ha]
      simp
    · simp [activityMatrix, hb, ha, c]
  have hcross : (∑ b, D b a * activityMatrix z b a) = c := by
    simp_rw [hp]
    rw [← Finset.sum_mul, h.column_sum, one_mul]
  have hsquare (b : V) : residualMatrix D z b a ^ 2 =
      D b a ^ 2 + activityMatrix z b a ^ 2 -
        2 * (D b a * activityMatrix z b a) := by
    unfold residualMatrix
    ring
  simp_rw [hsquare]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hcross, activity_column_energy_exact z hn a ha]
  dsimp [c]
  ring

/-- Both fixed-point directions vanish in the actual residual kernel. -/
theorem pointed_residual_zero_row {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (a : V) : residualMatrix D z z a = 0 := by
  simp [residualMatrix, activityMatrix, h.zero_row]

theorem pointed_residual_zero_column {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (b : V) : residualMatrix D z b z = 0 := by
  by_cases hb : b = z <;> simp [residualMatrix, activityMatrix, h.zero_column, hb]

/-- Applying the residual kernel always gives a centered nonzero-word vector. -/
theorem pointed_residual_action_centered {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (hn : 1 < Fintype.card V) (f : V → ℝ) :
    action (residualMatrix D z) f z = 0 ∧
      (∑ b, action (residualMatrix D z) f b) = 0 := by
  rw [residualMatrix_action h]
  exact ⟨(h.action_zero _).trans (wordResidual_at_zero z f),
    (h.action_sum _).trans (wordResidual_sum z f hn)⟩

/-- The residual channel kills an activity input: the R A block is zero. -/
theorem pointed_residual_activity_zero {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (hn : 1 < Fintype.card V) :
    kernelCompose (residualMatrix D z) (activityMatrix z) = 0 := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action]
  change action (D - activityMatrix z) (wordAverage z f) =
    action (0 : V → V → ℝ) f
  rw [kernel_action_sub, h.action_average, activityMatrix_action,
    wordAverage_idempotent z f hn, sub_self]
  funext b
  simp [action]

/-- The activity output of the residual channel is zero: the A R block is zero. -/
theorem pointed_activity_residual_zero {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (hn : 1 < Fintype.card V) :
    kernelCompose (activityMatrix z) (residualMatrix D z) = 0 := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action]
  have hc := pointed_residual_action_centered h hn f
  have hav : wordAverage z (action (residualMatrix D z) f) = 0 := by
    funext b
    simp only [wordAverage, nonzeroMean, hc.1, hc.2, sub_self, zero_div,
      ite_self, Pi.zero_apply]
  rw [hav]
  funext b
  simp [action]

end FiniteCentering

namespace AES
open AESMixing.AES

/-- No state enumeration is used to establish the finite word-space size. -/
theorem word_card_exact : Fintype.card Word = 4294967296 := by
  norm_num [Word, BinaryWord.card, Fintype.card_fun]

theorem word_card_gt_one : 1 < Fintype.card Word := by
  rw [word_card_exact]
  norm_num

/-- Exact energy subtraction for the actual SubBytes--MixColumns--SubBytes
word channel. A separate full-column estimate must supply the sharp δ bound. -/
theorem word_residual_column_energy_exact (a : Word) (ha : a ≠ 0) :
    (∑ b, residualMatrix wordSuperboxKernel 0 b a ^ 2) =
      (∑ b, wordSuperboxKernel b a ^ 2) - (1 : ℝ) / 4294967295 := by
  have h := pointed_residual_column_energy_exact word_superbox_pointed
    word_card_gt_one a ha
  have hc : (Fintype.card Word - 1 : ℝ) = 4294967295 := by
    rw [word_card_exact]
    norm_num
  simpa only [hc] using h

theorem word_residual_zero_row (a : Word) :
    residualMatrix wordSuperboxKernel 0 0 a = 0 :=
  pointed_residual_zero_row word_superbox_pointed a

theorem word_residual_zero_column (b : Word) :
    residualMatrix wordSuperboxKernel 0 b 0 = 0 :=
  pointed_residual_zero_column word_superbox_pointed b

theorem word_residual_activity_zero :
    kernelCompose (residualMatrix wordSuperboxKernel 0) (activityMatrix 0) = 0 :=
  pointed_residual_activity_zero word_superbox_pointed word_card_gt_one

theorem word_activity_residual_zero :
    kernelCompose (activityMatrix 0) (residualMatrix wordSuperboxKernel 0) = 0 :=
  pointed_activity_residual_zero word_superbox_pointed word_card_gt_one

/-- The byte residual has an exact, rather than assumed, column energy. -/
theorem byte_residual_column_energy_exact (a : BinaryWord 8) (ha : a ≠ 0) :
    (∑ b, residualMatrix aesByteChannel 0 b a ^ 2) = (8383 : ℝ) / 2088960 := by
  rw [pointed_residual_column_energy_exact aes_byte_resources.pointed
    (by norm_num [BinaryWord.card]) a ha, aes_byte_collision_column a ha]
  norm_num [BinaryWord.card]

/-- The nonzero and zero byte columns give the complete first-layer collision
profile. This is a tensor identity, not an independence assumption on a law. -/
theorem byte_column_energy_complete (a : BinaryWord 8) :
    (∑ b, aesByteChannel b a ^ 2) = if a = 0 then 1 else (65 : ℝ) / 8192 := by
  by_cases ha : a = 0
  · subst a
    have hp (b : BinaryWord 8) : aesByteChannel b 0 ^ 2 =
        if b = 0 then 1 else 0 := by
      rw [aes_byte_resources.zero_column]
      split_ifs <;> norm_num
    simp only [hp]
    simp
  · rw [if_neg ha]
    exact aes_byte_collision_column a ha

/-- Exact four-byte column collision before the word diffusion and second
substitution. The remaining smoothing step is not claimed in this theorem. -/
theorem word_first_substitution_column_energy_exact (a : Word) :
    (∑ b, substitutionKernel aesByteChannel b a ^ 2) =
      ∏ i : Fin 4, if a i = 0 then 1 else (65 : ℝ) / 8192 := by
  change (∑ b : Fin 4 → BinaryWord 8,
    (∏ i, aesByteChannel (b i) (a i)) ^ 2) = _
  have hproduct : (∑ b : Fin 4 → BinaryWord 8,
      (∏ i, aesByteChannel (b i) (a i)) ^ 2) =
      ∏ i : Fin 4, ∑ b : BinaryWord 8, aesByteChannel b (a i) ^ 2 :=
    product_column_energy (fun (i : Fin 4) (b : BinaryWord 8) =>
      aesByteChannel b (a i))
  rw [hproduct]
  apply Finset.prod_congr rfl
  intro i _
  exact byte_column_energy_complete (a i)

end AES
end AESConcrete
