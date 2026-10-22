import AESConcrete.ActivityCodeGeometry
import AESConcrete.ActivityCodeScalar
import AESConcrete.MixedCodeMoment
import AESConcrete.WordFourierVariants
import AESConcrete.ActualMarkedCodeDual
import AESConcrete.UniformSelectionCounting

/-!
# Word code moments for the activity-only Boolean expansion

The source in each term is the actual normalized image subgroup indicator.
Its two physical information sets are restrictions of that same subgroup;
the dimension-three branch uses its whole-word trace-character annihilator.
The Gram moment and ordinary/Fourier column resources are supplied by the
actual word residual. The common signed scalar is restored through the exact
energy identity in `ActivityCodeGeometry`, before Boolean aggregation.

Constructive mathematics only; no attacks, workloads, manuscript or frozen
source edits. Independent uniform retained keys, whitening, omitted final
MixColumns, ordered-distinct pairs and 10/14/16 stay fixed. Compilation and
independent review are required before accepting any new physical cap.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityCodeMoment
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityCodeGeometry
open AESConcrete.ActivityCodeScalar
open AESConcrete.MultiUniformExpansion
open AESConcrete.UniformSelectionCounting
open AESConcrete.WordFourierCore (wordConjugate)
-- Qualify the actual whole-word pairing: AESMixing also exports this name.
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.ActualMarkedCodeDual
  (selectionRange selectionEquiv selection_complement_card
    dual_projection_bijective_of_complement)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- Translate a physical predicate to the existing mask information-set API.
The change of labels leaves every actual word coordinate unchanged. -/
theorem wordCode_predicate_restriction_bijective (U : Fin 16) (p : Fin 4 → Prop)
    (hsize : Fintype.card {i : Fin 4 // p i} = maskSize U) :
    Function.Bijective (subgroupRestriction (wordCode U) p) := by
  let m : Fin 16 := maskBitsEquiv.symm (fun i => decide (p i))
  have hm (i : Fin 4) : maskBit m i = decide (p i) :=
    congrFun (maskBitsEquiv.apply_symm_apply (fun i => decide (p i))) i
  let e : MaskCoordinates m ≃ {i : Fin 4 // p i} :=
    Equiv.subtypeEquivRight (fun i => by rw [hm]; simp)
  have hcard : maskSize m = maskSize U := by
    rw [← maskCoordinates_card m, Fintype.card_congr e]
    exact hsize
  have hc := wordCode_restriction_bijective U m hcard
  have hr : Function.Bijective
      (fun g : MaskCoordinates m → AES.Word => fun i : {i : Fin 4 // p i} => g (e.symm i)) :=
    (Equiv.arrowCongr e (Equiv.refl AES.Word)).bijective
  have h := hr.comp hc
  change Function.Bijective (subgroupRestriction (wordCode U) p) at h
  exact h

/-- Any injective labels of the right size give an actual primal information set. -/
theorem wordCode_projection_bijective {A : Type*} [Fintype A]
    (U : Fin 16) (p : A → Fin 4) (hp : Function.Injective p)
    (hsize : Fintype.card A = maskSize U) :
    Function.Bijective (fun c : wordCode U => fun a : A => c.val (p a)) := by
  let e := selectionEquiv p hp
  have hc := wordCode_predicate_restriction_bijective U (selectionRange p)
    ((Fintype.card_congr e).symm.trans hsize)
  have hr : Function.Bijective
      (fun g : {i : Fin 4 // selectionRange p i} → AES.Word => fun a : A => g (e a)) :=
    (Equiv.arrowCongr e.symm (Equiv.refl AES.Word)).bijective
  have h := hr.comp hc
  change Function.Bijective (fun c : wordCode U => fun a : A => c.val (p a)) at h
  exact h

/-- Complementary primal restrictions prove the actual annihilator restrictions. -/
theorem wordCode_dual_projection_bijective {A : Type*} [Fintype A]
    (U : Fin 16) (p : A → Fin 4) (hp : Function.Injective p)
    (hsize : 4 - Fintype.card A = maskSize U) :
    Function.Bijective (fun c :
      (AESConcrete.WordFourierCore.wordPairing.product (Fin 4)).annihilator (wordCode U) =>
      fun a : A => c.val (p a)) := by
  apply dual_projection_bijective_of_complement
    AESConcrete.WordFourierCore.wordPairing (wordCode U) p hp
  apply wordCode_predicate_restriction_bijective U (fun i => ¬ selectionRange p i)
  have hcard := selection_complement_card p hp
  simp only [Fintype.card_fin] at hcard
  -- Nat.card removes dependence on the inferred subtype Fintype instance.
  simpa only [← Nat.card_eq_fintype_card] using hcard.trans hsize

private theorem word_gram_moment_le :
    (∑ ab : AES.Word × AES.Word,
      gram (residualMatrix AES.wordSuperboxKernel 0) ab.1 ab.2 ^ 2) ≤
      (300 / q : ℝ) ^ 2 := by
  have h := (WordFourierVariants.variant_gram_moment_lt false false).le
  simpa only [WordFourierVariants.variant, WordFourierVariants.baseResidual,
    Bool.false_eq_true, if_false, gram, Fintype.sum_prod_type, q] using h

private theorem word_column_le (a : AES.Word) :
    gram (residualMatrix AES.wordSuperboxKernel 0) a a ≤ 2 / (15 * q) := by
  rw [gram_diagonal]
  have h := (WordFourierVariants.variant_column_energy_lt false false a).le
  simpa only [WordFourierVariants.variant, WordFourierVariants.baseResidual,
    Bool.false_eq_true, if_false, q] using h

private theorem word_fourier_column_le (a : AES.Word) :
    gram (fourierConjugate AESConcrete.WordFourierCore.wordPairing
      (residualMatrix AES.wordSuperboxKernel 0)) a a ≤
      2 / (15 * q) := by
  rw [gram_diagonal]
  have h := (WordFourierVariants.variant_column_energy_lt false true a).le
  simpa only [WordFourierVariants.variant, WordFourierVariants.baseResidual,
    Bool.false_eq_true, if_false, if_true, wordConjugate, q] using h

/-- The primal moment bound with the actual two disjoint physical restrictions. -/
theorem wordCode_primal_energy {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : Fin 16) (idx : CodePosition I J ≃ Fin 4)
    (hsize : Fintype.card I = maskSize U) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      (((300 / q : ℝ) ^ 2) / q) ^ Fintype.card I *
        (2 / (15 * q)) ^ Fintype.card J := by
  have he := wordCode_projection_bijective U (fun i : I => idx (Sum.inl i))
    (fun _ _ h => Sum.inl.inj (idx.injective h)) hsize
  have hf := wordCode_projection_bijective U (fun i : I => idx (Sum.inr (Sum.inl i)))
    (fun _ _ h => Sum.inl.inj (Sum.inr.inj (idx.injective h))) hsize
  have hb := MixedCodeMoment.subgroup_energy_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0) (wordCode U) idx he hf
    ((300 / q : ℝ) ^ 2) (2 / (15 * q)) (sq_nonneg _) (by norm_num [q])
    (fun _ => word_gram_moment_le) (fun _ => word_column_le)
  have hq : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  simpa only [residualTensor, hq] using hb

/-- Whole-word Fourier duality changes kernels in place and preserves leg order. -/
theorem wordCode_dual_energy {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : Fin 16) (idx : CodePosition I J ≃ Fin 4)
    (hsize : 4 - Fintype.card I = maskSize U) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      (((300 / q : ℝ) ^ 2) / q) ^ Fintype.card I *
        (2 / (15 * q)) ^ Fintype.card J := by
  have he := wordCode_dual_projection_bijective U (fun i : I => idx (Sum.inl i))
    (fun _ _ h => Sum.inl.inj (idx.injective h)) hsize
  have hf := wordCode_dual_projection_bijective U (fun i : I => idx (Sum.inr (Sum.inl i)))
    (fun _ _ h => Sum.inl.inj (Sum.inr.inj (idx.injective h))) hsize
  have hb := MixedCodeMoment.subgroup_energy_dual_le
    AESConcrete.WordFourierCore.wordPairing word_add_self
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0) (wordCode U) idx he hf
    ((300 / q : ℝ) ^ 2) (2 / (15 * q)) (sq_nonneg _) (by norm_num [q])
    (fun _ => word_gram_moment_le) (fun _ => word_fourier_column_le)
  have hq : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  simpa only [residualTensor, hq] using hb

-- Cardinality chooses physical labels only. The actual MDS restriction
-- lemmas above, rather than this equivalence, prove the information sets.
private def oneDimSplit : CodePosition (Fin 1) (Fin 2) ≃ Fin 4 :=
  Fintype.equivOfCardEq (by simp only [CodePosition, Fintype.card_sum, Fintype.card_fin])

private def twoDimSplit : CodePosition (Fin 2) (Fin 0) ≃ Fin 4 :=
  Fintype.equivOfCardEq (by simp only [CodePosition, Fintype.card_sum, Fintype.card_fin])

theorem wordCode_one_energy (U : Fin 16) (hs : maskSize U = 1) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      termNorm (maskSize U) ^ 2 := by
  have hb := wordCode_primal_energy U oneDimSplit
    (by simpa only [Fintype.card_fin] using hs.symm)
  exact hb.trans_eq (by rw [hs]; norm_num [termNorm, q, s])

theorem wordCode_two_energy (U : Fin 16) (hs : maskSize U = 2) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      termNorm (maskSize U) ^ 2 := by
  have hb := wordCode_primal_energy U twoDimSplit
    (by simpa only [Fintype.card_fin] using hs.symm)
  exact hb.trans_eq (by rw [hs]; norm_num [termNorm, q, s])

theorem wordCode_three_energy (U : Fin 16) (hs : maskSize U = 3) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      termNorm (maskSize U) ^ 2 := by
  have hb := wordCode_dual_energy U oneDimSplit
    (by simpa only [Fintype.card_fin] using hs.symm)
  exact hb.trans_eq (by rw [hs]; norm_num [termNorm, q, s])

/-- The two endpoints vanish by channel identities; all positive branches
retain their own exact moment envelope. -/
theorem wordCode_activity_energy (U : Fin 16) :
    (∑ y, action residualTensor (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      termNorm (maskSize U) ^ 2 := by
  have hU := AESMixing.maskSize_le_four U
  have hcases : maskSize U = 0 ∨ maskSize U = 1 ∨ maskSize U = 2 ∨
      maskSize U = 3 ∨ maskSize U = 4 := by omega
  rcases hcases with hs | hs | hs | hs | hs
  · have hz := wordCode_zero_action U hs
    change action residualTensor (unitSubgroupIndicator (wordCode U)) = 0 at hz
    rw [hz, hs, termNorm_zero]
    simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, le_refl]
  · exact wordCode_one_energy U hs
  · exact wordCode_two_energy U hs
  · exact wordCode_three_energy U hs
  · have hz := wordCode_full_action U hs
    change action residualTensor (unitSubgroupIndicator (wordCode U)) = 0 at hz
    rw [hz, hs, termNorm_four]
    simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, le_refl]

/-- The scalar on the singleton residual domain remains arbitrary and signed.
The actual normalized code energy receives its square exactly once. -/
theorem word_expansionTerm_activity_energy (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r 0 σ h) y ^ 2) ≤
      termNorm (maskSize (selectionMask r 0 σ)) ^ 2 * ∑ w, h w ^ 2 := by
  rw [word_expansionTerm_energy_eq]
  exact mul_le_mul_of_nonneg_right
    (wordCode_activity_energy (selectionMask r 0 σ))
    (Finset.sum_nonneg (fun w _ => sq_nonneg (h w)))

private theorem word_sqrt_card : Real.sqrt (Fintype.card AES.Word : ℝ) = s := by
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num [s]

/-- Heterogeneous Boolean aggregation with the exact odd denominator powers.
Support multiplicity is deliberately left to the physical aggregation layer. -/
theorem word_multiUniform_activity_energy (r : Fin 16)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (multiUniform r 0 h) y ^ 2) ≤
      (numerator (Fintype.card (UniformPositions r 0)) ^ 2 /
        (q - 1) ^ Fintype.card (UniformPositions r 0)) * ∑ w, h w ^ 2 := by
  have hn : 1 < Fintype.card AES.Word := by rw [AES.word_card]; norm_num
  have he := multiUniform_action_energy residualStepKernel hn r 0 h
    (fun σ => termNorm (maskSize (selectionMask r 0 σ)))
    (fun _ => termNorm_nonneg _)
    (fun σ => word_expansionTerm_activity_energy r σ h)
  rw [expansion_weighted_sum_by_size hn r 0 termNorm, word_sqrt_card] at he
  have hs : (Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^
      Fintype.card (UniformPositions r 0)) ^ 2 =
        (q - 1) ^ Fintype.card (UniformPositions r 0) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      Real.sq_sqrt (by rw [AES.word_card]; norm_num)]
    rw [AES.word_card]
    rfl
  rw [div_pow, hs] at he
  simpa only [numerator] using he

end AESConcrete.ActivityCodeMoment
