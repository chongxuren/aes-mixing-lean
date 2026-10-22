import AESConcrete.GraphColumnEnergy
import AESConcrete.NonzeroUniformGraphCap
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Signed singleton-source graph energy on three retained channels

The analytic estimate has one operator-energy factor and two column-energy
factors. Its input amplitude is an arbitrary signed function. The omitted
nonzero-uniform weight is charged once, in the source energy; no unit-code
indicator or code-cardinality normalization is introduced. Actual singleton
support geometry, physical coordinate reindexing and support aggregation are
separate obligations supplied by a later specialization.

Independent retained uniform keys, whitening, omitted final MixColumns,
ordered-distinct pairs and fixed 10/14/16 remain fixed.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SingletonResidualCore
open AESMixing
open AESConcrete.GraphColumnEnergy (graphKernel graphKernel_weighted_energy)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)

set_option maxRecDepth 100000

section WeightedGraph
variable {V W Y Z : Type*} [Fintype W] [Fintype Y] [Fintype Z]

/-- Signed amplitudes are retained throughout. The pointwise omitted-weight
cap is applied only to its square after the graph-kernel energy estimate. -/
theorem weighted_graph_energy
    (B : Y → V → ℝ) (A : Z → W → ℝ) (g : W → V)
    (r b gamma : ℝ) (hb : 0 ≤ b)
    (hA : ∀ f : W → ℝ,
      (∑ y, action A f y ^ 2) ≤ r ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ b)
    (weight mu : W → ℝ) (hweight : ∀ x, weight x ^ 2 ≤ gamma) :
    (∑ y, action (graphKernel B A g) (fun x => weight x * mu x) y ^ 2) ≤
      r ^ 2 * b * gamma * ∑ x, mu x ^ 2 := by
  calc
    _ ≤ r ^ 2 * ∑ x, (weight x * mu x) ^ 2 * ∑ y, B y (g x) ^ 2 :=
      graphKernel_weighted_energy B A g r hA (fun x => weight x * mu x)
    _ ≤ r ^ 2 * ∑ x, (gamma * mu x ^ 2) * b := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
      apply Finset.sum_le_sum
      intro x _
      calc
        _ ≤ (weight x * mu x) ^ 2 * b :=
          mul_le_mul_of_nonneg_left (hB (g x)) (sq_nonneg _)
        _ ≤ (gamma * mu x ^ 2) * b := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hweight x) (sq_nonneg (mu x))) hb
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end WeightedGraph

section TwoColumns
variable {V Y Z : Type*} [Fintype Y] [Fintype Z]

/-- Two retained dependent coordinates are treated as a single joint graph
value. Their two genuine column energies multiply. -/
theorem tensor_two_column_energy
    (B : Y → V → ℝ) (C : Z → V → ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ k)
    (hC : ∀ v, (∑ z, C z v ^ 2) ≤ k) (v : V × V) :
    (∑ y, tensorKernel B C y v ^ 2) ≤ k ^ 2 := by
  simp only [tensorKernel, Fintype.sum_prod_type, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simpa only [pow_two] using mul_le_mul (hB v.1) (hC v.2)
    (Finset.sum_nonneg (fun z _ => sq_nonneg (C z v.2))) hk

end TwoColumns

/-- The same actual word residual on every retained physical coordinate. -/
abbrev wordResidual : AES.Word → AES.Word → ℝ :=
  residualMatrix AES.wordSuperboxKernel 0

/-- Rectangular retained response: the last output is the free coordinate;
the first pair consists of the other two retained physical coordinates. -/
def wordTripleGraphKernel (g : AES.Word → AES.Word × AES.Word) :
    ((AES.Word × AES.Word) × AES.Word) → AES.Word → ℝ :=
  graphKernel (tensorKernel wordResidual wordResidual) wordResidual g

/-- Uniform pointwise squared cap, including the zero source value. -/
theorem nonzeroUniform_word_sq_le (x : AES.Word) :
    nonzeroUniform x ^ 2 ≤ 1 / (q - 1) := by
  have hc : (Fintype.card AES.Word : ℝ) = q := by rw [AES.word_card]; rfl
  have hn : supportConstant false x ^ 2 ≤ (1 : ℝ) := by
    by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]
  unfold nonzeroUniform
  rw [div_pow, hc, Real.sq_sqrt (le_of_lt q_sub_one_pos)]
  exact div_le_div_of_nonneg_right hn (le_of_lt q_sub_one_pos)

/-- The zero source contributes exactly zero through the omitted weight.
This identity does not divide by a source value or assume it is nonzero. -/
theorem nonzeroUniform_word_zero : nonzeroUniform (0 : AES.Word) = 0 := by
  simp [nonzeroUniform, supportConstant, identityKernel]

/-- A retained zero source column independently kills the zero-point term. -/
theorem wordTripleGraphKernel_zero
    (g : AES.Word → AES.Word × AES.Word)
    (y : (AES.Word × AES.Word) × AES.Word) :
    wordTripleGraphKernel g y 0 = 0 := by
  simp only [wordTripleGraphKernel, graphKernel, wordResidual,
    AES.word_residual_zero_column, mul_zero]

/-- The exact signed graph estimate needed by the `(3,4)`/`(1,1)` route.
The maps may depend jointly on the free source value. No nonzero-source,
independence, positivity or normalization premise is imposed on the amplitude. -/
theorem word_weighted_graph_energy
    (g : AES.Word → AES.Word × AES.Word) (omitted : AES.Word → AES.Word)
    (mu : AES.Word → ℝ) :
    (∑ y, action (wordTripleGraphKernel g)
      (fun x => nonzeroUniform (omitted x) * mu x) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2 / (q - 1)) * ∑ x, mu x ^ 2 := by
  have hA : ∀ f : AES.Word → ℝ,
      (∑ y, action wordResidual f y ^ 2) ≤ rho ^ 2 * ∑ x, f x ^ 2 := by
    intro f
    simpa only [wordResidual, rho] using
      SharpDampedWordNorm.word_superbox_residual_energy f
  have hcolumn : ∀ v : AES.Word, (∑ y, wordResidual y v ^ 2) ≤ kappa := by
    intro v
    simpa only [wordResidual, kappa] using
      (AllColumnBound.actual_word_residual_column_energy_lt v).le
  have hB := tensor_two_column_energy wordResidual wordResidual kappa
    kappa_nonneg hcolumn hcolumn
  have he := weighted_graph_energy (tensorKernel wordResidual wordResidual)
    wordResidual g rho (kappa ^ 2) (1 / (q - 1)) (sq_nonneg _) hA hB
    (fun x => nonzeroUniform (omitted x)) mu
    (fun x => nonzeroUniform_word_sq_le (omitted x))
  change (∑ y, action (wordTripleGraphKernel g)
    (fun x => nonzeroUniform (omitted x) * mu x) y ^ 2) ≤ _ at he
  exact he.trans_eq (by ring)

section Reindexing
variable {Y : Type*} [Fintype Y]

/-- A response identity and a genuine output equivalence suffice to apply
the signed estimate. This interface keeps geometric identification separate
from the analytic bound, while preserving the exact counting energy. -/
theorem word_response_energy
    (out : Y ≃ ((AES.Word × AES.Word) × AES.Word))
    (g : AES.Word → AES.Word × AES.Word) (omitted : AES.Word → AES.Word)
    (mu : AES.Word → ℝ) (response : Y → ℝ)
    (hresponse : ∀ y, response y = action (wordTripleGraphKernel g)
      (fun x => nonzeroUniform (omitted x) * mu x) (out y)) :
    (∑ y, response y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2 / (q - 1)) * ∑ x, mu x ^ 2 := by
  simp_rw [hresponse]
  rw [out.sum_comp (fun y => action (wordTripleGraphKernel g)
    (fun x => nonzeroUniform (omitted x) * mu x) y ^ 2)]
  exact word_weighted_graph_energy g omitted mu

/-- Rectangular kernel formulation for an actual one-dimensional source
parameterized by a bijective retained coordinate. No source norm is lost. -/
theorem word_reindexed_graph_energy {C : Type*} [Fintype C]
    (source : C ≃ AES.Word) (out : Y ≃ ((AES.Word × AES.Word) × AES.Word))
    (g : AES.Word → AES.Word × AES.Word) (omitted : AES.Word → AES.Word)
    (K : Y → C → ℝ)
    (hK : ∀ y c, K y c = nonzeroUniform (omitted (source c)) *
      wordTripleGraphKernel g (out y) (source c)) (mu : C → ℝ) :
    (∑ y, action K mu y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2 / (q - 1)) * ∑ c, mu c ^ 2 := by
  have ha (y : Y) : action K mu y = action (wordTripleGraphKernel g)
      (fun x => nonzeroUniform (omitted x) * mu (source.symm x)) (out y) := by
    unfold action
    calc
      _ = ∑ c : C, wordTripleGraphKernel g (out y) (source c) *
          (nonzeroUniform (omitted (source c)) * mu c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hK]
        ring
      _ = _ := by
        simpa only [source.symm_apply_apply] using source.sum_comp
          (fun x => wordTripleGraphKernel g (out y) x *
            (nonzeroUniform (omitted x) * mu (source.symm x)))
  have he := word_response_energy out g omitted (fun x => mu (source.symm x))
    (action K mu) ha
  rw [source.symm.sum_comp (fun c => mu c ^ 2)] at he
  exact he

end Reindexing
end AESConcrete.SingletonResidualCore
