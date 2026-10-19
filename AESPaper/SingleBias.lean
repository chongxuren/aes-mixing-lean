import AESPaper.UniformBias
import AESPaper.ConvolutionAtom

/-!
# The four single-Z activity terms for actual several-source inputs
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.SingleBias
open AESMixing AESConcrete
open AESPaper.StartingWord (q)
open AESPaper.UniformBias
open AESConcrete.RestrictedMarginalEnergy (marginal)

def Z : AES.Word → AES.Word → ℝ := biasKernel (0 : AES.Word)

theorem bias_action_formula (f : AES.Word → ℝ) (hm : (∑ x, f x) = 1) (y : AES.Word) :
    action Z f y = (q*f 0-1)/(q*(q-1)) * (if y=0 then q-1 else -1) := by
  have h := congrFun (biasKernel_action (0 : AES.Word) f) y
  change action Z f y = _ at h
  rw [h]
  by_cases hy : y=0
  all_goals simp only [Pi.sub_apply, wordAverage, nonzeroMean, hm,
    ← StartingWord.q_eq_word_card, hy, if_true, if_false]
  all_goals field_simp [show q ≠ 0 by norm_num [q], show q-1 ≠ 0 by norm_num [q]] <;> ring

theorem bias_vector_energy :
    (∑ y : AES.Word, (if y=0 then q-1 else (-1 : ℝ))^2) = q*(q-1) := by
  have hp (y : AES.Word) : (if y=0 then q-1 else (-1 : ℝ))^2 =
      1 + if y=0 then (q-1)^2-1 else 0 := by
    by_cases hy : y=0 <;> simp [hy]
  simp only [hp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← StartingWord.q_eq_word_card]
  ring

/-- Exact counting-measure formula; the input need not be nonnegative. -/
theorem bias_energy (f : AES.Word → ℝ) (hm : (∑ x, f x) = 1) :
    (∑ y, action Z f y ^ 2) = (q*f 0-1)^2/(q*(q-1)) := by
  simp only [bias_action_formula f hm, mul_pow, ← Finset.mul_sum]
  rw [bias_vector_energy]
  field_simp [show q ≠ 0 by norm_num [q], show q-1 ≠ 0 by norm_num [q]]

theorem bias_energy_le (f : AES.Word → ℝ) (hm : (∑ x, f x) = 1)
    (hz : 0 ≤ f 0) (hp : f 0 ≤ 2/q) :
    (∑ y, action Z f y ^ 2) ≤ 1/(q*(q-1)) := by
  rw [bias_energy f hm]
  have h0 : 0 ≤ q*f 0 := mul_nonneg (by norm_num [q]) hz
  have h2 : q*f 0 ≤ 2 := by
    calc
      q*f 0 ≤ q*(2/q) := mul_le_mul_of_nonneg_left hp (by norm_num [q])
      _ = 2 := by norm_num [q]
  apply div_le_div_of_nonneg_right _ (by norm_num [q])
  nlinarith

def kernel (c : Fin 4) (y x : AES.WordState) : ℝ :=
  ∏ i, if i=c then Z (y i) (x i) else 1/q

theorem kernel_eq (c : Fin 4) (y x : AES.WordState) :
    kernel c y x = (1/q)^3 * Z (y c) (x c) := by
  fin_cases c <;> simp [kernel, Fin.prod_univ_four] <;> norm_num [q] <;> ring

theorem action_eq (c : Fin 4) (f : AES.WordState → ℝ) (y : AES.WordState) :
    action (kernel c) f y = (1/q)^3 *
      action Z (marginal (fun x : AES.WordState => x c) f) (y c) := by
  change (∑ x, kernel c y x * f x) = (1/q)^3 *
    (∑ v, Z (y c) v * marginal (fun x : AES.WordState => x c) f v)
  rw [SingleResidualJ.sum_marginal]
  simp only [kernel_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem energy_eq (c : Fin 4) (f : AES.WordState → ℝ) :
    (∑ y, action (kernel c) f y ^ 2) = (1/q)^3 *
      ∑ v, action Z (marginal (fun x : AES.WordState => x c) f) v ^ 2 := by
  simp only [action_eq, mul_pow, ← Finset.mul_sum]
  rw [SingleResidualJ.coordinate_energy]
  ring_nf
  norm_num [q]

open AESPaper.ManySourceLaw AESPaper.ManySourceBounds

theorem actual_scaled_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b) (c : Fin 4) :
    q^5 * (∑ y, action (kernel c) (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) y ^ 2) ≤
      q/(q-1) := by
  rw [energy_eq]
  have h := bias_energy_le _ (ConvolutionAtom.actual_marginal_mass b c)
    (ConvolutionAtom.actual_marginal_nonnegative b c 0)
    (ConvolutionAtom.actual_zero_probability_lt b hb c).le
  calc
    _ = (q^5 * (1/q)^3) *
      (∑ v, action Z (wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c) v ^ 2) := by
        unfold wordMarginal
        ring
    _ ≤ (q^5 * (1/q)^3) * (1/(q*(q-1))) :=
      mul_le_mul_of_nonneg_left h (by norm_num [q])
    _ = q/(q-1) := by norm_num [q]

/-- Sum of the four literal single-bias terms, before multiple-zero biases. -/
theorem actual_total_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ c : Fin 4, ∑ y,
      action (kernel c) (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) y ^ 2) <
        1000001/250000 := by
  calc
    _ = ∑ c : Fin 4, q^5 * (∑ y,
      action (kernel c) (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) y ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _ : Fin 4, q/(q-1) :=
      Finset.sum_le_sum (fun c _ => actual_scaled_energy_le b hb c)
    _ < 1000001/250000 := by norm_num [q]

end AESPaper.SingleBias
