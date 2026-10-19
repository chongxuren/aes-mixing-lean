import AESPaper.SignedBiasExpansion
import AESPaper.RestrictedResponseL2

/-!
# Actual mixed response bound before the J/Z output factors
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.SignedResponseBounds
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (residual)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESConcrete.RestrictedMarginalEnergy (marginal)

def weightedResponse (b : AES.State) (out : Fin 16) (S : Finset (Fin 4)) :
    (MaskCoordinates out → AES.Word) → ℝ :=
  action (coordinateKernel (fun _ : MaskCoordinates out => residual))
    (marginal (fun x (i : MaskCoordinates out) => x i.val)
      (fun x : AES.WordState => BiasStartup.inputLaw b x * BiasTensorEnergy.basisProduct 0 S x))

theorem response_expansion (b : AES.State) (out : Fin 16) (S : Finset (Fin 4)) :
    weightedResponse b out S = fun y => ∑ D ∈ S.powerset,
      SignedBiasExpansion.signedCoefficient (V := AES.Word) S D *
        RestrictedResponseL2.setResponse b D out y := by
  funext y
  exact SignedBiasExpansion.weighted_response_expansion (0 : AES.Word) S
    (fun x (i : MaskCoordinates out) => x i.val) (BiasStartup.inputLaw b)
    (coordinateKernel (fun _ : MaskCoordinates out => residual)) y

theorem coefficient_abs (S D : Finset (Fin 4)) :
    |SignedBiasExpansion.signedCoefficient (V := AES.Word) S D| = q^D.card := by
  have h := SignedBiasExpansion.signedCoefficient_abs (V := AES.Word) S D
  simpa only [← StartingWord.q_eq_word_card] using h

theorem subset_weight_sum (S : Finset (Fin 4)) :
    (∑ D ∈ S.powerset, (20 : ℝ)^D.card) = 21^S.card := by
  have h := Finset.prod_add (fun _ : Fin 4 => (20 : ℝ)) (fun _ => (1 : ℝ)) S
  norm_num [Finset.prod_const] at h
  exact h.symm

/-- Scalar cancellation of the q^|D| from each zero-indicator coefficient. -/
theorem cancel_indicator_weight (k j : ℕ) :
    q^k * ((6/5 : ℝ)^2*20^k*nu/(q^k*Real.sqrt (q^j))) =
      ((6/5 : ℝ)^2*nu/Real.sqrt (q^j))*20^k := by
  have hs : Real.sqrt (q^j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2
    (pow_pos ResponseScalarBounds.q_positive j))
  field_simp [ResponseScalarBounds.q_ne_zero, hs]
  <;> ring

/-- Every nonempty residual set has the same single-contraction bound after
summing signed zero restrictions, regardless of the number of bias positions. -/
theorem weightedResponse_norm_le (b : AES.State) (hb : 0 < activeSourceCount b)
    (out : Fin 16) (S : Finset (Fin 4))
    (hdis : ∀ i ∈ S, maskBit out i=false) (hj : 0 < maskSize out) :
    l2 (weightedResponse b out S) ≤
      (6/5 : ℝ)^2 * nu * 21^S.card / Real.sqrt (q^maskSize out) := by
  rw [response_expansion]
  calc
    _ ≤ ∑ D ∈ S.powerset, l2 (fun y =>
        SignedBiasExpansion.signedCoefficient (V := AES.Word) S D *
          RestrictedResponseL2.setResponse b D out y) := l2_finset_sum_le _ _
    _ = ∑ D ∈ S.powerset, q^D.card * l2 (RestrictedResponseL2.setResponse b D out) := by
      simp only [l2_scale, coefficient_abs]
    _ ≤ ∑ D ∈ S.powerset, ((6/5 : ℝ)^2*nu/Real.sqrt (q^maskSize out))*20^D.card := by
      apply Finset.sum_le_sum
      intro D hD
      have hsub := Finset.mem_powerset.mp hD
      calc
        _ ≤ q^D.card * ((6/5 : ℝ)^2*20^D.card*nu /
            (q^D.card*Real.sqrt (q^maskSize out))) :=
          mul_le_mul_of_nonneg_left
            (RestrictedResponseL2.setResponse_norm_le b hb D out
              (fun i hi => hdis i (hsub hi)) hj)
            (pow_nonneg ResponseScalarBounds.q_positive.le _)
        _ = _ := cancel_indicator_weight _ _
    _ = _ := by rw [← Finset.mul_sum, subset_weight_sum]; ring

end AESPaper.SignedResponseBounds
