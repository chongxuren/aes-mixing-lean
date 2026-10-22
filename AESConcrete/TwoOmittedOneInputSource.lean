import AESConcrete.TwoOmittedOneInputGeometry
import AESConcrete.TwoOmittedOneInputScalar
import AESConcrete.TripleResponse

/-!
# Exact original signed source and one-input-uniform split for (10,12)

One arbitrary signed joint h on the original J tuple is used, including h(0).
The full normalized source is exactly multiUniform at the original masks and
has energy H. Only W expands its input U; output-event restrictions retain G
unchanged. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputSource
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputScalar (D d)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.MultiUniformExpansion (multiUniform normalizedLeg)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

-- Top-level universe-polymorphic helpers are permitted; no local Type* have is used.
theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

def psi (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ)
    (x : AES.WordState) : ℝ := h (residualTuple pIn x)

def normalizedSource (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  multiUniform pIn.val.val.2 pIn.val.val.1 h

theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h = multiUniform pIn.val.val.2 pIn.val.val.1 h := rfl

theorem normalizedSource_energy (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ r, h r ^ 2 :=
  MultiUniformExpansion.multiUniform_energy AES.word_card_gt_one _ _ h

theorem normalizedSource_eq (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    normalizedSource pIn h x = psi pIn h x * nonzeroUniform (x (inputUniform pIn).val) := by
  unfold normalizedSource multiUniform coordinateEmbedding
  rw [counting_prod_instances (X := OtherCoordinates pIn.val.val.1) _ inferInstance]
  have hleg (i : InputOther pIn) :
      normalizedLeg (maskBit pIn.val.val.2 i.val) (x i.val) = nonzeroUniform (x i.val) := by
    simp [normalizedLeg, input_inactive_not pIn i.val]
  simp_rw [hleg]
  have hp : (∏ i : InputOther pIn, nonzeroUniform (x i.val)) =
      nonzeroUniform (x (inputUniform pIn).val) := by
    have he := (inputOtherEquiv pIn).symm.prod_comp
      (fun i : InputOther pIn => nonzeroUniform (x i.val))
    simpa [Fin.prod_univ_succ, inputUniform] using he.symm
  rw [hp]
  rfl

theorem psi_zero (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    psi pIn h 0 = h 0 := rfl

theorem full_psi_energy (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, psi pIn h x ^ 2) = ActivityCodeScalar.q * ∑ r, h r ^ 2 := by
  have hcard : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
    rw [AES.word_card]
    norm_num [ActivityCodeScalar.q]
  have he := (residualUniformEquiv pIn).sum_comp
    (fun uv : (Residual pIn → AES.Word) × AES.Word => h uv.1 ^ 2)
  change (∑ x : AES.WordState, psi pIn h x ^ 2) =
      ∑ uv : (Residual pIn → AES.Word) × AES.Word, h uv.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Rewrite the scalar directly; do not run congr through the physical equivalence.
  rw [← Finset.mul_sum, hcard]

theorem nonzeroUniform_eq (x : AES.Word) :
    nonzeroUniform x = (1 - if x = 0 then 1 else 0) / d := by
  -- AES.word_card is already imported; this source needs no Fourier-energy module.
  have hcard : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
    -- Rewrite the word cardinal before arithmetic can unfold the byte tuple type.
    rw [AES.word_card]
    norm_num [ActivityCodeScalar.q]
  rw [nonzeroUniform, hcard]
  by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx, d, D]

theorem nonzeroUniform_sq_le (x : AES.Word) : nonzeroUniform x ^ 2 ≤ 1 / D := by
  rw [nonzeroUniform_eq]
  by_cases hx : x = 0
  · simp only [if_pos hx, sub_self, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact div_nonneg (by norm_num) TwoOmittedOneInputScalar.D_pos.le
  · simp only [if_neg hx, sub_zero, div_pow, one_pow, TwoOmittedOneInputScalar.d_sq]
    exact le_rfl

def rawResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (psi pIn h) (stateKernel pOut)

def inputZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (psi pIn h) (stateKernel pOut)
    (fun x => x (inputUniform pIn).val)

def inputWeightedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (normalizedSource pIn h) (stateKernel pOut)

/-- Bare A0-Au over the one original input normalizer; no cancellation assumed. -/
theorem inputWeightedResponse_eq_split (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y - inputZeroResponse pOut pIn h y) / d := by
  funext y
  unfold inputWeightedResponse rawResponse inputZeroResponse
    WeightedResponse.rawResponse WeightedResponse.zeroResponse
  have hsummand (x : AES.WordState) :
      normalizedSource pIn h x * stateKernel pOut y x =
        (psi pIn h x * stateKernel pOut y x -
          (if x (inputUniform pIn).val = 0 then psi pIn h x * stateKernel pOut y x else 0)) / d := by
    rw [normalizedSource_eq, nonzeroUniform_eq]
    by_cases hx : x (inputUniform pIn).val = 0 <;> simp [hx] <;> ring
  simp_rw [hsummand]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

end AESConcrete.TwoOmittedOneInputSource
