import AESConcrete.ActivityMinorCounting

/-!
# Selected physical activity-minor energy bounds

Every signed omitted-leg term is bounded using its actual contracted word code.
The zero-dimensional and full-dimensional endpoints vanish exactly. All other
terms share a single square root of the retained-length moment, before the
triangle inequality is squared once. No Boolean-term orthogonality is used.
Constructive mathematics only; no attacks. The independent retained-key model,
whitening, omitted final MixColumns, ordered-distinct pairs and fixed 10/14/16
target remain unchanged. No new inventory entry is accepted by this source.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityMinorTermBounds
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction
open AESConcrete.ActivityMinorCounting
open AESConcrete.ActivityMinorEnvelope
open AESConcrete.UniformSelectionCounting
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ActivityCodeScalar (q s)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- A true-count term receives the common moment exactly on the surviving
minor dimensions. This auxiliary definition carries no rounding. -/
def choiceNorm (d t u : ℕ) : ℝ :=
  if 4 - d - u < t ∧ t < 4 - u then Real.sqrt (moment d) / s ^ (4 - d) else 0

theorem choiceNorm_nonneg (d t u : ℕ) : 0 ≤ choiceNorm d t u := by
  unfold choiceNorm s
  split_ifs <;> positivity

private theorem selectedRetained_nonempty (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (p : SelectedSupport d a) :
    Nonempty {i : Fin 4 // selectedRetained d a p i} := by
  have hp : 0 < Fintype.card {i : Fin 4 // selectedRetained d a p i} := by
    rw [selectedRetained_card]
    omega
  have hu : 0 < (Finset.univ :
      Finset {i : Fin 4 // selectedRetained d a p i}).card := by simpa using hp
  obtain ⟨i, _⟩ := Finset.card_pos.mp hu
  exact ⟨i⟩

/-- Actual contraction bound for each choice, including both exact endpoints. -/
theorem selected_choice_energy (d a : Fin 5) (hd : d.val = 2 ∨ d.val = 3)
    (p : SelectedSupport d a) (U : Fin 16)
    (σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool) :
    (∑ y, minorResponse (selectedRetained d a p)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (zeroUniformWeight (selectedRetained d a p)
        (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ))
      (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) y ^ 2) ≤
      choiceNorm d.val (AES.maskSize U) (selectionSize σ).val ^ 2 := by
  let L := selectedRetained d a p
  let Z := choiceZeros L (selectedZeros d a p) σ
  have hdisj : ∀ i, Z i → ¬ L i := by
    intro i hz hl
    exact choiceZeros_disjoint L (selectedZeros d a p) (selected_disjoint d a p) σ i hl hz
  have hcL : Fintype.card {i : Fin 4 // L i} = d.val := selectedRetained_card d a p
  have hcZ : Fintype.card {i : Fin 4 // Z i} =
      4 - d.val - (selectionSize σ).val := choiceZeros_card d a p σ
  have hn : Fintype.card {i : Fin 4 // Z i} + uniformCount L Z = 4 - d.val :=
    choice_normalization d a p σ
  have hu := choiceSize_le d a p σ
  have hadd : (4 - d.val - (selectionSize σ).val) + d.val =
      4 - (selectionSize σ).val := by omega
  obtain ⟨k⟩ := selectedRetained_nonempty d a hd p
  change (∑ y, minorResponse L _ (zeroUniformWeight L Z) _ y ^ 2) ≤ _
  by_cases hs : 4 - d.val - (selectionSize σ).val < AES.maskSize U ∧
      AES.maskSize U < 4 - (selectionSize σ).val
  · have hZ : Fintype.card {i : Fin 4 // Z i} ≤ AES.maskSize U := by omega
    have he : (∑ y, minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
        (zeroUniformWeight L Z) (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) y ^ 2) ≤
        (1 / s ^ (4 - d.val)) ^ 2 * moment d.val := by
      rcases hd with hd | hd
      · have hdim : AES.maskSize U - Fintype.card {i : Fin 4 // Z i} = 1 := by omega
        have hb := ActivityMinorMoment.wordCode_two_coordinate_contraction_energy U Z L
          hdisj hZ (hcL.trans hd) hdim
        rw [hn] at hb
        simpa [moment, hd] using hb
      · have hdim : AES.maskSize U - Fintype.card {i : Fin 4 // Z i} = 1 ∨
            AES.maskSize U - Fintype.card {i : Fin 4 // Z i} = 2 := by omega
        have hb := ActivityMinorMoment.wordCode_three_coordinate_contraction_energy U Z L
          hdisj hZ (hcL.trans hd) hdim
        rw [hn] at hb
        simpa only [moment, hd, show (3 : ℕ) ≠ 2 by omega, if_false] using hb
    refine he.trans_eq ?_
    simp only [choiceNorm, if_pos hs, div_pow, one_pow, Real.sq_sqrt (moment_nonneg _)]
    ring
  · have hz : minorResponse L (fun _ => residualMatrix AES.wordSuperboxKernel 0)
        (zeroUniformWeight L Z) (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) = 0 := by
      by_cases hl : AES.maskSize U ≤ Fintype.card {i : Fin 4 // Z i}
      · exact ActivityMinorMoment.wordCode_zeroUniform_low_zero U Z L hdisj hl k
      · apply ActivityMinorMoment.wordCode_zeroUniform_high_zero U Z L hdisj _ k
        omega
    rw [hz]
    simp only [Pi.zero_apply, zero_pow (by omega : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, choiceNorm, if_neg hs, le_refl]

/-- The entire arbitrary signed omitted expansion has the exactly grouped
common norm cap. The source is the unit indicator of the actual word code. -/
theorem selected_unitCode_l2 (d a : Fin 5) (hd : d.val = 2 ∨ d.val = 3)
    (p : SelectedSupport d a) (U : Fin 16) :
    l2 (minorResponse (selectedRetained d a p)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained d a p) (selectedZeros d a p))
      (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U))) ≤
        termNorm d.val a.val (AES.maskSize U) := by
  rw [minorResponse_nonzero_expansion AES.word_card_gt_one]
  calc
    _ ≤ ∑ σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool,
        l2 (fun y => choiceCoefficient (V := AES.Word) (selectedRetained d a p)
          (selectedZeros d a p) σ *
          minorResponse (selectedRetained d a p)
            (fun _ => residualMatrix AES.wordSuperboxKernel 0)
            (zeroUniformWeight (selectedRetained d a p)
              (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ))
            (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) y) := by
      exact l2_finset_sum_le Finset.univ
        (fun σ y => choiceCoefficient (V := AES.Word) (selectedRetained d a p)
          (selectedZeros d a p) σ *
          minorResponse (selectedRetained d a p)
            (fun _ => residualMatrix AES.wordSuperboxKernel 0)
            (zeroUniformWeight (selectedRetained d a p)
              (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ))
            (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) y)
    _ = ∑ σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool,
        |choiceCoefficient (V := AES.Word) (selectedRetained d a p) (selectedZeros d a p) σ| *
          l2 (minorResponse (selectedRetained d a p)
            (fun _ => residualMatrix AES.wordSuperboxKernel 0)
            (zeroUniformWeight (selectedRetained d a p)
              (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ))
            (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U))) := by
      simp_rw [l2_scale]
    _ ≤ ∑ σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool,
        |choiceCoefficient (V := AES.Word) (selectedRetained d a p) (selectedZeros d a p) σ| *
          choiceNorm d.val (AES.maskSize U) (selectionSize σ).val := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (sq_le_sq₀ (l2_nonneg _) (choiceNorm_nonneg _ _ _)).mp
      simpa only [l2_sq] using selected_choice_energy d a hd p U σ
    _ = termNorm d.val a.val (AES.maskSize U) := by
      unfold choiceNorm
      rw [selected_survivor_sum d a p (AES.maskSize U)
        (Real.sqrt (moment d.val) / s ^ (4 - d.val))]
      unfold termNorm
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Selected physical tensor energy before source-support aggregation.
The retained-length moment is shared and squared only after the triangle sum. -/
theorem selected_unitCode_energy (d a : Fin 5) (hd : d.val = 2 ∨ d.val = 3)
    (_hda : d ≤ a) (p : SelectedSupport d a) (U : Fin 16) :
    (∑ y, action (selectedWordTensor d a p)
      (unitSubgroupIndicator (ActivityCodeGeometry.wordCode U)) y ^ 2) ≤
        termNorm d.val a.val (AES.maskSize U) ^ 2 := by
  rw [selectedWordTensor_minor_energy]
  have hb := (sq_le_sq₀ (l2_nonneg _) (termNorm_nonneg d.val a.val (AES.maskSize U))).mpr
    (selected_unitCode_l2 d a hd p U)
  simpa only [l2_sq] using hb

end AESConcrete.ActivityMinorTermBounds
