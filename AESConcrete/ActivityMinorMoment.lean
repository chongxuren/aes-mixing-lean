import AESConcrete.ActivityMinorGeometry
import AESConcrete.ActivityMinorContraction

/-!
# Word residual moments on shorter physical coordinate sets

The input is a unit indicator of the actual subgroup on the retained coordinates.
Information-set hypotheses refer to restrictions of that subgroup. The dual
branch uses its whole-word character annihilator and conjugates each kernel in
place. Geometry supplies the hypotheses separately; no physical leg is reversed.

Constructive mathematics only; no attacks. Independent retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and 10/14/16 stay fixed.
These moment lemmas alone add no physical step cap or full-round theorem.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityMinorMoment
open AESMixing
open AESConcrete.ActivityMinorGeometry (HasInformationSets wordMinor wordMinor_information_sets)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.WordFourierCore (wordConjugate)
open AESConcrete.ActualMarkedCodeDual
  (selectionRange selectionEquiv selection_complement_card
    dual_projection_bijective_of_complement)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- The same actual residual kernel on each retained physical coordinate. -/
def wordResidualTensor (K : Type*) [Fintype K] : (K → AES.Word) → (K → AES.Word) → ℝ :=
  coordinateKernel (fun _ : K => residualMatrix AES.wordSuperboxKernel 0)

private theorem word_card_real : (Fintype.card AES.Word : ℝ) = q := by
  rw [AES.word_card]
  norm_num [q]

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
      (residualMatrix AES.wordSuperboxKernel 0)) a a ≤ 2 / (15 * q) := by
  rw [gram_diagonal]
  have h := (WordFourierVariants.variant_column_energy_lt false true a).le
  simpa only [WordFourierVariants.variant, WordFourierVariants.baseResidual,
    Bool.false_eq_true, if_false, if_true, wordConjugate, q] using h

section Information
variable {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A]

omit [DecidableEq K] in
theorem projection_bijective (C : AddSubgroup (K → AES.Word)) (d : ℕ)
    (hC : HasInformationSets C d) (p : A → K) (hp : Function.Injective p)
    (hsize : Fintype.card A = d) :
    Function.Bijective (fun c : C => fun a : A => c.val (p a)) := by
  exact ActivityMinorGeometry.projection_bijective_of_information_sets C d hC p hp hsize

theorem dual_projection_bijective (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (d : ℕ) (hC : HasInformationSets C d)
    (p : A → K) (hp : Function.Injective p)
    (hsize : Fintype.card K - Fintype.card A = d) :
    Function.Bijective (fun c :
      (AESConcrete.WordFourierCore.wordPairing.product K).annihilator C =>
      fun a : A => c.val (p a)) := by
  apply dual_projection_bijective_of_complement
    AESConcrete.WordFourierCore.wordPairing C p hp
  apply hC (fun k => ¬ selectionRange p k)
  simpa only [← Nat.card_eq_fintype_card] using
    (selection_complement_card p hp).trans hsize

end Information

section Moment
variable {K I J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem primal_energy (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (idx : CodePosition I J ≃ K)
    (hC : HasInformationSets C (Fintype.card I)) :
    (∑ y, action (wordResidualTensor K) (unitSubgroupIndicator C) y ^ 2) ≤
      (((300 / q : ℝ) ^ 2) / q) ^ Fintype.card I *
        (2 / (15 * q)) ^ Fintype.card J := by
  have he := projection_bijective C _ hC (fun i : I => idx (Sum.inl i))
    (fun _ _ h => Sum.inl.inj (idx.injective h)) rfl
  have hf := projection_bijective C _ hC (fun i : I => idx (Sum.inr (Sum.inl i)))
    (fun _ _ h => Sum.inl.inj (Sum.inr.inj (idx.injective h))) rfl
  have hb := MixedCodeMoment.subgroup_energy_le
    (fun _ : K => residualMatrix AES.wordSuperboxKernel 0) C idx he hf
    ((300 / q : ℝ) ^ 2) (2 / (15 * q)) (sq_nonneg _) (by norm_num [q])
    (fun _ => word_gram_moment_le) (fun _ => word_column_le)
  simpa only [wordResidualTensor, word_card_real] using hb

theorem dual_energy (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (idx : CodePosition I J ≃ K)
    (hC : HasInformationSets C (Fintype.card K - Fintype.card I)) :
    (∑ y, action (wordResidualTensor K) (unitSubgroupIndicator C) y ^ 2) ≤
      (((300 / q : ℝ) ^ 2) / q) ^ Fintype.card I *
        (2 / (15 * q)) ^ Fintype.card J := by
  have he := dual_projection_bijective C _ hC (fun i : I => idx (Sum.inl i))
    (fun _ _ h => Sum.inl.inj (idx.injective h)) rfl
  have hf := dual_projection_bijective C _ hC (fun i : I => idx (Sum.inr (Sum.inl i)))
    (fun _ _ h => Sum.inl.inj (Sum.inr.inj (idx.injective h))) rfl
  have hb := MixedCodeMoment.subgroup_energy_dual_le
    AESConcrete.WordFourierCore.wordPairing word_add_self
    (fun _ : K => residualMatrix AES.wordSuperboxKernel 0) C idx he hf
    ((300 / q : ℝ) ^ 2) (2 / (15 * q)) (sq_nonneg _) (by norm_num [q])
    (fun _ => word_gram_moment_le) (fun _ => word_fourier_column_le)
  simpa only [wordResidualTensor, word_card_real] using hb

end Moment

section ShortLengths
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem two_coordinate_energy (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (hK : Fintype.card K = 2) (hC : HasInformationSets C 1) :
    (∑ y, action (wordResidualTensor K) (unitSubgroupIndicator C) y ^ 2) ≤
      90000 / q ^ 3 := by
  let idx : CodePosition (Fin 1) (Fin 0) ≃ K :=
    Fintype.equivOfCardEq (by simp only [CodePosition, Fintype.card_sum,
      Fintype.card_fin, hK])
  have hb := primal_energy C idx hC
  exact hb.trans_eq (by norm_num [q])

theorem three_coordinate_primal_energy (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (hK : Fintype.card K = 3) (hC : HasInformationSets C 1) :
    (∑ y, action (wordResidualTensor K) (unitSubgroupIndicator C) y ^ 2) ≤
      12000 / q ^ 4 := by
  let idx : CodePosition (Fin 1) (Fin 1) ≃ K :=
    Fintype.equivOfCardEq (by simp only [CodePosition, Fintype.card_sum,
      Fintype.card_fin, hK])
  have hb := primal_energy C idx hC
  exact hb.trans_eq (by norm_num [q])

theorem three_coordinate_dual_energy (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (hK : Fintype.card K = 3) (hC : HasInformationSets C 2) :
    (∑ y, action (wordResidualTensor K) (unitSubgroupIndicator C) y ^ 2) ≤
      12000 / q ^ 4 := by
  let idx : CodePosition (Fin 1) (Fin 1) ≃ K :=
    Fintype.equivOfCardEq (by simp only [CodePosition, Fintype.card_sum,
      Fintype.card_fin, hK])
  have hc : HasInformationSets C (Fintype.card K - Fintype.card (Fin 1)) := by
    simpa only [hK, Fintype.card_fin] using hC
  have hb := dual_energy C idx hc
  exact hb.trans_eq (by norm_num [q])

/-- The exact length-two moment bound on an actual shortened/punctured word code. -/
theorem wordMinor_two_coordinate_energy (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hZ : Fintype.card {j : Fin 4 // Z j} ≤ AES.maskSize U)
    (hL : Fintype.card {j : Fin 4 // L j} = 2)
    (hd : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 1) :
    (∑ y, action (wordResidualTensor {j : Fin 4 // L j})
      (unitSubgroupIndicator (wordMinor U Z L)) y ^ 2) ≤ 90000 / q ^ 3 := by
  apply two_coordinate_energy (wordMinor U Z L) hL
  simpa only [hd] using wordMinor_information_sets U Z L hZL hZ

/-- Both nontrivial dimensions on three retained physical legs share one
squared coefficient, so subsequent sums need no rounded square roots. -/
theorem wordMinor_three_coordinate_energy (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hZ : Fintype.card {j : Fin 4 // Z j} ≤ AES.maskSize U)
    (hL : Fintype.card {j : Fin 4 // L j} = 3)
    (hd : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 1 ∨
      AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 2) :
    (∑ y, action (wordResidualTensor {j : Fin 4 // L j})
      (unitSubgroupIndicator (wordMinor U Z L)) y ^ 2) ≤ 12000 / q ^ 4 := by
  rcases hd with hd | hd
  · apply three_coordinate_primal_energy (wordMinor U Z L) hL
    simpa only [hd] using wordMinor_information_sets U Z L hZL hZ
  · apply three_coordinate_dual_energy (wordMinor U Z L) hL
    simpa only [hd] using wordMinor_information_sets U Z L hZL hZ

end ShortLengths
section ActualContraction
open AESConcrete.ActivityMinorGeometry
open AESConcrete.ActivityMinorContraction
open AESConcrete.ActivityCodeGeometry (wordCode wordCode_card)
open AESConcrete.ActivityCodeScalar (s)

private theorem word_sqrt_card : Real.sqrt (Fintype.card AES.Word : ℝ) = s := by
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num [s]

/-- Actual-word specialization discharges the injectivity and both cardinality
premises of the zero/full-uniform contraction. -/
theorem wordCode_zeroUniform_response (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hZ : Fintype.card {j : Fin 4 // Z j} ≤ AES.maskSize U)
    (hL : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} ≤
      Fintype.card {j : Fin 4 // L j}) (y : {j : Fin 4 // L j} → AES.Word) :
    minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight L Z) (unitSubgroupIndicator (wordCode U)) y =
      (1 / s ^ (Fintype.card {j : Fin 4 // Z j} + uniformCount L Z)) *
        action (wordResidualTensor {j : Fin 4 // L j})
          (unitSubgroupIndicator (wordMinor U Z L)) y := by
  have hC : Fintype.card (wordCode U) = Fintype.card AES.Word ^ AES.maskSize U := by
    rw [wordCode_card, AES.word_card]
    norm_num
  have hD : Fintype.card (wordMinor U Z L) =
      Fintype.card AES.Word ^ (AES.maskSize U - Fintype.card {j : Fin 4 // Z j}) := by
    rw [wordMinor_card U Z L hZL hZ hL, AES.word_card]
    norm_num
  have hb := unitSubgroup_zeroUniform_response_of_cards (wordCode U) L Z
    (fun j hLj hZj => hZL j hZj hLj) (wordMinor_source_injective U Z L hZL hZ hL)
    (AES.maskSize U) (Fintype.card {j : Fin 4 // Z j}) hZ hC hD
    (fun _ => residualMatrix AES.wordSuperboxKernel 0) y
  simpa only [word_sqrt_card, wordResidualTensor] using hb

/-- Two retained residual legs of the actual word code after exact omitted
zero/full-uniform contraction. The squared normalization is charged once. -/
theorem wordCode_two_coordinate_contraction_energy (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hZ : Fintype.card {j : Fin 4 // Z j} ≤ AES.maskSize U)
    (hL : Fintype.card {j : Fin 4 // L j} = 2)
    (hd : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 1) :
    (∑ y, minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight L Z) (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      (1 / s ^ (Fintype.card {j : Fin 4 // Z j} + uniformCount L Z)) ^ 2 *
        (90000 / q ^ 3) := by
  have hn := wordCode_zeroUniform_response U Z L hZL hZ (by rw [hd, hL]; omega)
  simp_rw [hn, mul_pow]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (wordMinor_two_coordinate_energy U Z L hZL hZ hL hd)
    (sq_nonneg _)

/-- Three retained residual legs share the same exact squared moment for
both nontrivial minor dimensions; no independent square-root rounding. -/
theorem wordCode_three_coordinate_contraction_energy (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hZ : Fintype.card {j : Fin 4 // Z j} ≤ AES.maskSize U)
    (hL : Fintype.card {j : Fin 4 // L j} = 3)
    (hd : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 1 ∨
      AES.maskSize U - Fintype.card {j : Fin 4 // Z j} = 2) :
    (∑ y, minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight L Z) (unitSubgroupIndicator (wordCode U)) y ^ 2) ≤
      (1 / s ^ (Fintype.card {j : Fin 4 // Z j} + uniformCount L Z)) ^ 2 *
        (12000 / q ^ 4) := by
  have hle : AES.maskSize U - Fintype.card {j : Fin 4 // Z j} ≤
      Fintype.card {j : Fin 4 // L j} := by rw [hL]; omega
  have hn := wordCode_zeroUniform_response U Z L hZL hZ hle
  simp_rw [hn, mul_pow]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (wordMinor_three_coordinate_energy U Z L hZL hZ hL hd)
    (sq_nonneg _)

/-- Once the retained projection is full, exact uniform fibers give a
zero response. This includes noninjective puncturing without applying the
injective normalization theorem. -/
theorem wordCode_zeroUniform_high_zero (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hdim : Fintype.card {j : Fin 4 // Z j} + Fintype.card {j : Fin 4 // L j} ≤
      AES.maskSize U) (k : {j : Fin 4 // L j}) :
    minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight L Z) (unitSubgroupIndicator (wordCode U)) = 0 := by
  apply unitSubgroup_zeroUniform_response_of_surjective (wordCode U) L Z
    (fun j hLj hZj => hZL j hZj hLj)
    (wordMinor_source_surjective U Z L hZL hdim) _ k
  intro y
  unfold residualMatrix
  rw [Finset.sum_sub_distrib, AES.word_superbox_pointed.row_sum,
    (activityMatrix_pointed (0 : AES.Word) AES.word_card_gt_one).row_sum]
  norm_num

/-- Enough pinned zero coordinates force the original codeword to zero;
any retained actual residual zero column then kills the contraction. -/
theorem wordCode_zeroUniform_low_zero (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hdim : AES.maskSize U ≤ Fintype.card {j : Fin 4 // Z j})
    (k : {j : Fin 4 // L j}) :
    minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight L Z) (unitSubgroupIndicator (wordCode U)) = 0 := by
  apply unitSubgroup_zeroUniform_response_of_zero_source (wordCode U) L Z
    (fun j hLj hZj => hZL j hZj hLj)
    (zeroSubgroup_mem_iff_eq_zero_of_le (wordCode U) (AES.maskSize U)
      (wordCode_information_sets U) Z hdim) _ k
  exact AES.word_residual_zero_column

end ActualContraction
end AESConcrete.ActivityMinorMoment
