import AESPaper.MixedTensorEnergy
import AESPaper.SignedResponseBounds

/-!
# Actual mixed tensor terms after summing uniform and bias outputs
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators
namespace AESPaper.MixedTermBounds
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (residual)
open AESPaper.ManySourceBounds (activeSourceCount)

theorem q_gt_one : 1 < q := by norm_num [q]

theorem denominator_eq (out : Fin 16) (S : Finset (Fin 4)) :
    MixedTensorEnergy.denominator (V := AES.Word) out S =
      q^(4-maskSize out)*(q-1)^S.card := by
  simp only [MixedTensorEnergy.denominator, ← StartingWord.q_eq_word_card]

theorem mixed_scalar_eq (j z : ℕ) (hj : j ≤ 4) :
    (((6/5 : ℝ)^2*nu*21^z/Real.sqrt (q^j))^2) /
      (q^(4-j)*(q-1)^z) =
      (6/5 : ℝ)^4*nu^2*(441/(q-1))^z/q^4 := by
  have hq : q ≠ 0 := ResponseScalarBounds.q_ne_zero
  have hQ : q-1 ≠ 0 := ne_of_gt (sub_pos.mpr q_gt_one)
  have hp : q^j*q^(4-j) = q^4 := by rw [← pow_add, Nat.add_sub_of_le hj]
  have h21 : ((21 : ℝ)^z)^2 = (441 : ℝ)^z := by
    rw [← pow_mul, Nat.mul_comm z 2, pow_mul]
    norm_num
  simp only [div_pow, mul_pow, Real.sq_sqrt (pow_nonneg ResponseScalarBounds.q_positive.le j), h21]
  rw [← hp]
  field_simp [hq, hQ]
  <;> ring

/-- Named function equality keeps concrete AES sum instances opaque when
the generic mixed-energy identity is specialized. -/
theorem weighted_response_eq (b : AES.State) (out : Fin 16)
    (S : Finset (Fin 4)) :
    action (coordinateKernel (fun _ : MaskCoordinates out => residual))
      (MixedTensorEnergy.weightedMarginal (0 : AES.Word) out S (BiasStartup.inputLaw b)) =
      SignedResponseBounds.weightedResponse b out S := rfl

/-- Every literal mixed term with a nonempty residual mask has this bound.
The bias set may be empty, although that case has a sharper two-contraction
bound when both the source and residual counts are at least two. -/
theorem mixed_energy_le (b : AES.State) (hb : 0 < activeSourceCount b)
    (out : Fin 16) (S : Finset (Fin 4)) (hd : MixedTensorEnergy.Disjoint out S)
    (hj : 0 < maskSize out) :
    (∑ y, action (MixedTensorEnergy.kernel (0 : AES.Word) out S residual)
      (BiasStartup.inputLaw b) y ^ 2) ≤
      (6/5 : ℝ)^4*nu^2*(441/(q-1))^S.card/q^4 := by
  rw [MixedTensorEnergy.energy_eq _ AES.word_card_gt_one out S hd residual,
    denominator_eq, weighted_response_eq]
  have hn := SignedResponseBounds.weightedResponse_norm_le b hb out S hd hj
  have hC : 0 ≤ (6/5 : ℝ)^2*nu*21^S.card/Real.sqrt (q^maskSize out) := by
    have hnu := WordDamping.nu_nonnegative
    positivity
  have hs := (sq_le_sq₀ (l2_nonneg _) hC).2 hn
  rw [l2_sq] at hs
  calc
    _ ≤ ((6/5 : ℝ)^2*nu*21^S.card/Real.sqrt (q^maskSize out))^2 /
        (q^(4-maskSize out)*(q-1)^S.card) :=
      div_le_div_of_nonneg_right hs (mul_nonneg
        (pow_nonneg ResponseScalarBounds.q_positive.le _)
        (pow_nonneg (sub_nonneg.mpr q_gt_one.le) _))
    _ = _ := mixed_scalar_eq _ _ (ResponseMaskSelection.maskSize_le_four out)

theorem empty_weighted_response (b : AES.State) (out : Fin 16) :
    SignedResponseBounds.weightedResponse b out ∅ =
      RestrictedResponseL2.setResponse b ∅ out := by
  unfold SignedResponseBounds.weightedResponse RestrictedResponseL2.setResponse
    RestrictedResponseL2.setMarginal
  apply congrArg (fun f : (MaskCoordinates out → AES.Word) → ℝ =>
    action (coordinateKernel (fun _ : MaskCoordinates out => residual)) f)
  apply congrArg (fun f : AES.WordState → ℝ =>
    RestrictedMarginalEnergy.marginal
      (fun (x : AES.WordState) (i : MaskCoordinates out) => x i.val) f)
  funext x
  have he : ∀ i ∈ (∅ : Finset (Fin 4)), x i = 0 := by
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  rw [if_pos he]
  simp only [BiasTensorEnergy.basisProduct, Finset.notMem_empty, if_false,
    Finset.prod_const_one, mul_one]

theorem pure_scalar_eq (j : ℕ) (hj : j ≤ 4) :
    (((6/5 : ℝ)^2*nu^2/Real.sqrt (q^j))^2) / q^(4-j) =
      (6/5 : ℝ)^4*nu^4/q^4 := by
  have hp : q^j*q^(4-j) = q^4 := by rw [← pow_add, Nat.add_sub_of_le hj]
  simp only [div_pow, mul_pow, Real.sq_sqrt (pow_nonneg ResponseScalarBounds.q_positive.le j)]
  rw [← hp]
  field_simp [ResponseScalarBounds.q_ne_zero]
  <;> ring

/-- The pure residual term pays two contractions when both counts are at least two. -/
theorem pure_residual_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (out : Fin 16) (hj : 2 ≤ maskSize out) :
    (∑ y, action (MixedTensorEnergy.kernel (0 : AES.Word) out ∅ residual)
      (BiasStartup.inputLaw b) y ^ 2) ≤ (6/5 : ℝ)^4*nu^4/q^4 := by
  have hd : MixedTensorEnergy.Disjoint out ∅ := by intro i hi; simp at hi
  rw [MixedTensorEnergy.energy_eq _ AES.word_card_gt_one out ∅ hd residual,
    denominator_eq, weighted_response_eq]
  simp only [Finset.card_empty, pow_zero, mul_one]
  have hn := RestrictedResponseL2.empty_response_norm_le b hb out hj
  have he := empty_weighted_response b out
  rw [← he] at hn
  have hC : 0 ≤ (6/5 : ℝ)^2*nu^2/Real.sqrt (q^maskSize out) := by positivity
  have hs := (sq_le_sq₀ (l2_nonneg _) hC).2 hn
  rw [l2_sq] at hs
  calc
    _ ≤ ((6/5 : ℝ)^2*nu^2/Real.sqrt (q^maskSize out))^2 / q^(4-maskSize out) :=
      div_le_div_of_nonneg_right hs (pow_nonneg ResponseScalarBounds.q_positive.le _)
    _ = _ := pure_scalar_eq _ (ResponseMaskSelection.maskSize_le_four out)

end AESPaper.MixedTermBounds
