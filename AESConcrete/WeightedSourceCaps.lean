import AESConcrete.TwoActiveMinorResponse
import AESConcrete.TwoActivePlaneEnergy
import AESConcrete.TwoActiveLineEnergy
import AESConcrete.TwoActiveShortenedGeometry

/-!
# Weighted two-active selected-piece energy

The actual retained plane and three actual zero lines are bounded separately.
Their four signed responses are then combined with the exact three-weight
normalization. The original signed residual amplitude, including its value at
zero, is shared throughout, and every reindexing preserves counting measure.

This module supplies a selected-piece candidate only. Physical input/output
aggregation, frozen-certificate comparison and inventory admission are separate
obligations. Constructive mathematics only; no attacks. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs and
the fixed 10/14/16 target remain unchanged. No compilation, independent review,
accepted cap or manuscript change is asserted by source authoring alone.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedSourceCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoActiveSource
open AESConcrete.TwoActiveGeometry
open AESConcrete.TwoActiveMinorResponse
open AESConcrete.TwoActiveLineEnergy
open AESConcrete.TwoActiveShortenedGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_sub_one_pos s_pos s_sq)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- The selected-piece energy coefficient; no physical multiplicity is included. -/
def pieceSquaredBound : ℝ := rho ^ 2 * kappa * (s + 3) ^ 2 / (q - 1) ^ 3

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := by
  unfold pieceSquaredBound
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg (s + 3)))
    (pow_nonneg (le_of_lt q_sub_one_pos) 3)

theorem retained_card (pOut : SelectedSupport 2 4) :
    Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

/-- A retained physical label is different from either enumerated omitted label. -/
theorem retained_ne_omitted (pOut : SelectedSupport 2 4)
    (k : Fin 2) (i : Retained pOut) : i.val ≠ omittedLabel pOut k := by
  intro he
  have ho : AES.maskBit pOut.val.val.1 (omittedLabel pOut k) ≠ true :=
    ((omittedEquiv pOut).symm k).property
  exact ho (he ▸ i.property)

/-- The raw plane is exactly the retained-coordinate Fourier-plane response.
This conversion only changes the order of two scalar factors. -/
theorem raw_plane_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤
      (rho ^ 2 * kappa * q) * ∑ u, h u ^ 2 := by
  have hcurve (uv : AES.Word × AES.Word) :
      (retainedEquiv pOut pIn).toEquiv uv = curve pOut pIn uv := rfl
  have heq : WeightedResponse.rawResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) =
      TwoActivePlaneEnergy.planeResponse (retainedEquiv pOut pIn).toEquiv
        (residualMatrix AES.wordSuperboxKernel 0) h := by
    funext y
    unfold WeightedResponse.rawResponse TwoActivePlaneEnergy.planeResponse residualKernel
    simp_rw [hcurve]
    apply Finset.sum_congr rfl
    intro uv _
    ring
  rw [heq]
  exact TwoActivePlaneEnergy.retained_planeResponse_energy pOut pIn h

/-- The source-uniform zero response is the actual residual source axis.
The sum over the original uniform coordinate collapses exactly to its zero. -/
theorem source_zero_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) Prod.snd y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retained_card]; norm_num)
  let j : Retained pOut := Classical.choice inferInstance
  have hprojection : Function.Bijective
      (fun u : AES.Word => curve pOut pIn (u, 0) j) :=
    residual_axis_coordinate_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS pIn j.val
  have hb := word_curve_energy_of_bijective (retained_card pOut) j
    (fun u : AES.Word => curve pOut pIn (u, 0)) h hprojection
  have heq : WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) Prod.snd =
      curveResponse (residualMatrix AES.wordSuperboxKernel 0)
        (fun u : AES.Word => curve pOut pIn (u, 0)) h := by
    funext y
    unfold WeightedResponse.zeroResponse curveResponse
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    simp [residualKernel]
  rw [heq]
  simpa only [UniformGraphScalar.rho, UniformGraphScalar.kappa] using hb

/-- Each omitted-output zero response is an actual shortened line. Its
retained projection and its original residual source value are both bijective,
so neither graph energy nor input energy incurs a cardinality factor. -/
theorem omitted_zero_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (k : Fin 2) (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn k) y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  classical
  let i : Fin 4 := omittedLabel pOut k
  let C := zeroLine wordMixAddEquiv.toAddMonoidHom pIn i
  let curveC : C → Retained pOut → AES.Word := fun uv => curve pOut pIn uv.val
  let μ : C → ℝ := fun uv => h uv.val.1
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retained_card]; norm_num)
  let j : Retained pOut := Classical.choice inferInstance
  have hprojection : Function.Bijective (fun uv : C => curveC uv j) :=
    word_zeroLine_output_bijective pIn i j.val (retained_ne_omitted pOut k j)
  let e : C ≃ AES.Word := Equiv.ofBijective (fun uv : C => uv.val.1)
    (word_zeroLine_residual_bijective pIn i)
  have hμ : (∑ uv : C, μ uv ^ 2) = ∑ u : AES.Word, h u ^ 2 :=
    e.sum_comp (fun u => h u ^ 2)
  have hb := word_curve_energy_of_bijective (retained_card pOut) j curveC μ hprojection
  have heq : WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn k) =
      curveResponse (residualMatrix AES.wordSuperboxKernel 0) curveC μ := by
    funext y
    exact zeroResponse_eq_curve (residualMatrix AES.wordSuperboxKernel 0)
      (curve pOut pIn) (fun uv : AES.Word × AES.Word => h uv.1)
      (omittedValue pOut pIn k) y
  rw [heq]
  rw [hμ] at hb
  simpa only [UniformGraphScalar.rho, UniformGraphScalar.kappa] using hb

/-- The actual three-weight response receives the candidate coefficient.
Its four signed terms share one amplitude and are combined before squaring. -/
theorem response_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (h : AES.Word → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  let a : ℝ := rho * Real.sqrt kappa
  have ha : 0 ≤ a := mul_nonneg rho_nonneg (Real.sqrt_nonneg kappa)
  have ha_sq : a ^ 2 = rho ^ 2 * kappa := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt kappa_nonneg]
  have hA :
      (∑ y, WeightedResponse.rawResponse (fun uv : AES.Word × AES.Word => h uv.1)
        (residualKernel pOut pIn) y ^ 2) ≤ (s * a) ^ 2 * ∑ u, h u ^ 2 :=
    (raw_plane_energy pOut pIn h).trans_eq (by rw [mul_pow, ha_sq, s_sq]; ring)
  have hB :
      (∑ y, WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
        (residualKernel pOut pIn) Prod.snd y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (source_zero_energy pOut pIn h).trans_eq (by rw [ha_sq])
  have hC :
      (∑ y, WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
        (residualKernel pOut pIn) (omittedValue pOut pIn 0) y ^ 2) ≤
        a ^ 2 * ∑ u, h u ^ 2 :=
    (omitted_zero_energy pOut pIn 0 h).trans_eq (by rw [ha_sq])
  have hD :
      (∑ y, WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
        (residualKernel pOut pIn) (omittedValue pOut pIn 1) y ^ 2) ≤
        a ^ 2 * ∑ u, h u ^ 2 :=
    (omitted_zero_energy pOut pIn 1 h).trans_eq (by rw [ha_sq])
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := pairwise_zero_kernel pOut pIn
  have hn : 1 ≤ Fintype.card AES.Word := le_of_lt AES.word_card_gt_one
  have hb := WeightedResponse.weightedResponse_common_energy_le hn
    (fun uv : AES.Word × AES.Word => h uv.1) (residualKernel pOut pIn)
    Prod.snd (omittedValue pOut pIn 0) (omittedValue pOut pIn 1) h
    h₀₁ h₀₂ h₁₂ s a (le_of_lt s_pos) ha hA hB hC hD
  change (∑ y, response pOut pIn h y ^ 2) ≤ _ at hb
  have hcard : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  simpa only [ha_sq, hcard, pieceSquaredBound] using hb

/-- Actual selected-step energy on the `(1,2)` source, with its original
source energy. This theorem has no physical support multiplicity. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, hsource, henergy, hoff⟩ := word_source_representation pIn f
  calc
    _ = ∑ y, response pOut pIn h y ^ 2 :=
      selectedStep_energy_eq pOut pIn _ h hsource hoff
    _ ≤ pieceSquaredBound * ∑ u, h u ^ 2 := response_energy pOut pIn h
    _ = _ := by rw [henergy]

end AESConcrete.WeightedSourceCaps
