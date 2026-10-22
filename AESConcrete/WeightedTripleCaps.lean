import AESConcrete.ThreeActiveMinorResponse
import AESConcrete.ThreeActiveFourierEnergy
import AESConcrete.ThreeActiveLineEnergy

/-!
# Actual weighted triple-source selected-piece energy

The same arbitrary signed residual-pair amplitude occurs in the full source,
both planes and the surviving intersection line. The latter receives only
restriction subenergy, never an unjustified equality. Triangle aggregation
precedes the exact coefficient comparison. Candidate until compilation and
independent review; constructive mathematics only, no attacks.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.WeightedTripleCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeActiveSource
open AESConcrete.ThreeActiveGeometry
open AESConcrete.ThreeActiveMinorResponse
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s s_sq s_pos q_sub_one_pos)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

def pieceSquaredBound : ℝ := rho ^ 4 * kappa * (s + 2 + 1 / 28) ^ 2 / (q - 1) ^ 2

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := by
  unfold pieceSquaredBound
  exact div_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg rho_nonneg 4) kappa_nonneg) (sq_nonneg _))
    (sq_nonneg _)

/-- Exact source restriction before any energy estimate. -/
private theorem conditional_response_eq {S I V : Type*}
    [Fintype S] [Fintype I] [Fintype V] (P : S → Prop) [DecidablePred P]
    (T : V → V → ℝ) (c : S → I → V) (h : S → ℝ) (y : I → V) :
    (∑ x, if P x then h x * (∏ i, T (y i) (c x i)) else 0) =
      IndexedTripleEnergy.response T (fun x : {x // P x} => c x.val)
        (fun x => h x.val) y := by
  rw [← Finset.sum_filter]
  calc
    _ = ∑ x : {x // P x}, h x.val * (∏ i, T (y i) (c x.val i)) :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      unfold IndexedTripleEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Raw retained-triple Fourier energy includes exactly one word fiber. -/
theorem raw_full_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤ (rho ^ 4 * kappa * q) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) = ThreeActiveFourierEnergy.fullResponse
        (retainedEquiv pOut pIn).toEquiv (residualMatrix AES.wordSuperboxKernel 0) h := by
    funext y
    unfold WeightedResponse.rawResponse ThreeActiveFourierEnergy.fullResponse
    apply Finset.sum_congr rfl
    intro uv _
    change h uv.1 * (∏ i, residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn uv i)) = _
    have hc : (retainedEquiv pOut pIn).toEquiv uv = curve pOut pIn uv := rfl
    rw [hc]
    ring
  rw [heq]
  exact ThreeActiveFourierEnergy.retained_fullResponse_energy pOut pIn h

theorem source_zero_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.vPlane (V := AES.Word) pIn => curve pOut pIn uv.val)
        (fun uv => h uv.val.1) := by
    funext y
    exact conditional_response_eq (fun uv : SourceDomain pIn => uv.2 = 0)
      _ (curve pOut pIn) (fun uv => h uv.1) y
  rw [heq]
  exact ThreeActivePlaneEnergy.retained_vPlane_energy pOut pIn h

theorem omitted_zero_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.zeroPlane wordMixAddEquiv.toAddMonoidHom
          pIn (omittedLabel pOut) => curve pOut pIn uv.val) (fun uv => h uv.val.1) := by
    funext y
    exact conditional_response_eq (fun uv : SourceDomain pIn => omittedValue pOut pIn uv = 0)
      _ (curve pOut pIn) (fun uv => h uv.1) y
  rw [heq]
  exact ThreeActivePlaneEnergy.retained_zeroPlane_energy pOut pIn h

/-- The intersection survives; its injective residual restriction costs no
more than the full original joint energy. -/
theorem intersection_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd (omittedValue pOut pIn) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have heq : TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd (omittedValue pOut pIn) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.intersectionLine wordMixAddEquiv.toAddMonoidHom
          pIn (omittedLabel pOut) => curve pOut pIn uv.val) (fun uv => h uv.val.1) := by
    funext y
    exact conditional_response_eq
      (fun uv : SourceDomain pIn => uv.2 = 0 ∧ omittedValue pOut pIn uv = 0)
      _ (curve pOut pIn) (fun uv => h uv.1) y
  rw [heq]
  exact ThreeActiveLineEnergy.retained_intersectionLine_energy pOut pIn h

/-- Rational safe replacement for the smaller line norm coefficient. -/
theorem line_squared_safe : rho ^ 2 * kappa ^ 2 ≤ rho ^ 4 * kappa / 28 ^ 2 := by
  norm_num [rho, kappa, q]

theorem response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  let a : ℝ := rho ^ 2 * Real.sqrt kappa
  have ha : 0 ≤ a := mul_nonneg (sq_nonneg rho) (Real.sqrt_nonneg kappa)
  have ha_sq : a ^ 2 = rho ^ 4 * kappa := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt kappa_nonneg]
    ring
  have hA : (∑ y, WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤ (s * a) ^ 2 * ∑ u, h u ^ 2 :=
    (raw_full_energy pOut pIn h).trans_eq (by rw [mul_pow, ha_sq, s_sq]; ring)
  have hB : (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (source_zero_energy pOut pIn h).trans_eq (by rw [ha_sq])
  have hC : (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (omitted_zero_energy pOut pIn h).trans_eq (by rw [ha_sq])
  have hD : (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) Prod.snd (omittedValue pOut pIn) y ^ 2) ≤
      (a / 28) ^ 2 * ∑ u, h u ^ 2 := by
    apply (intersection_energy pOut pIn h).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun u _ => sq_nonneg (h u)))
    rw [div_pow, ha_sq]
    exact line_squared_safe
  have hb := TripleResponse.weightedResponse_energy_le
    (le_of_lt AES.word_card_gt_one) (fun uv : SourceDomain pIn => h uv.1)
    (residualKernel pOut pIn) Prod.snd (omittedValue pOut pIn) h
    (s * a) a a (a / 28) (mul_nonneg (le_of_lt s_pos) ha) ha ha
    (div_nonneg ha (by norm_num)) hA hB hC hD
  change (∑ y, response pOut pIn h y ^ 2) ≤ _ at hb
  have hcard : (Fintype.card AES.Word : ℝ) = q := by rw [AES.word_card]; norm_num [q]
  rw [hcard] at hb
  have hcoef : (s * a + a + a + a / 28) ^ 2 / (q - 1) ^ 2 = pieceSquaredBound := by
    calc
      _ = a ^ 2 * (s + 2 + 1 / 28) ^ 2 / (q - 1) ^ 2 := by ring
      _ = _ := by rw [ha_sq]; rfl
  rw [hcoef] at hb
  exact hb

/-- Return to the actual selected-step energy with its original input energy. -/
theorem selected_piece_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, hsource, henergy, hoff⟩ := word_source_representation pIn f
  calc
    _ = ∑ y, response pOut pIn h y ^ 2 := selectedStep_energy_eq pOut pIn _ h hsource hoff
    _ ≤ pieceSquaredBound * ∑ u, h u ^ 2 := response_energy pOut pIn h
    _ = _ := by rw [henergy]

end AESConcrete.WeightedTripleCaps
