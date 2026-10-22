import AESConcrete.ActivityMinorEnvelope
import AESConcrete.UniformSelectionCounting

/-!
# Physical coordinate counts in omitted-leg activity minors

Counting is on the original four coordinate labels. Boolean terms need not be
orthogonal. These identities preserve every absolute signed coefficient and
unit-vector normalization; they add no accepted cap. Constructive mathematics
only; no attacks. Independent retained keys, whitening, omitted final
MixColumns, ordered-distinct pairs and the fixed 10/14/16 target are unchanged.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityMinorCounting
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction
open AESConcrete.UniformSelectionCounting
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ActivityCodeScalar (q s)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- The marked subtype counts retained physical coordinates. -/
theorem selectedRetained_card (d a : Fin 5) (p : SelectedSupport d a) :
    Fintype.card {i : Fin 4 // selectedRetained d a p i} = d.val := by
  simpa only [← Nat.card_eq_fintype_card, selectedRetained] using
    (maskCoordinates_card p.val.val.1).trans p.val.property.2

/-- The inactive subtype counts the original zero coordinates. -/
theorem selectedZeros_card (d a : Fin 5) (p : SelectedSupport d a) :
    Fintype.card {i : Fin 4 // selectedZeros d a p i} = 4 - a.val := by
  have hc : AES.maskSize p.val.val.2 = 4 - a.val := by
    have h := p.property
    omega
  simpa only [← Nat.card_eq_fintype_card, selectedZeros] using
    (maskCoordinates_card p.val.val.2).trans hc

theorem selected_disjoint (d a : Fin 5) (p : SelectedSupport d a) :
    ∀ i, selectedRetained d a p i → ¬ selectedZeros d a p i := by
  intro i hi hz
  exact p.val.property.1 i hz hi

/-- Exactly the unmarked active coordinates receive Boolean choices. -/
theorem selected_uniform_card (d a : Fin 5) (p : SelectedSupport d a) :
    Fintype.card (UniformOmitted (selectedRetained d a p) (selectedZeros d a p)) =
      a.val - d.val := by
  have hc := MultiUniformExpansion.uniformPositions_card
    p.val.val.2 p.val.val.1 p.val.property.1
  have he : 4 - (AES.maskSize p.val.val.2 + AES.maskSize p.val.val.1) =
      a.val - d.val := by
    have h := p.property
    have hd := p.val.property.2
    omega
  simpa only [← Nat.card_eq_fintype_card, MultiUniformExpansion.UniformPositions,
    GeneralMDSGraphSupport.OtherCoordinates, UniformOmitted, selectedRetained, selectedZeros]
    using hc.trans he

section ChoiceCounting
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (L Z : J → Prop)

/-- True Boolean entries are precisely the remaining full-uniform positions. -/
private def choiceUniformEquiv (σ : UniformOmitted L Z → Bool) :
    UniformOmitted L (choiceZeros L Z σ) ≃
      {j : UniformOmitted L Z // σ j = true} where
  toFun j := by
    have hZ : ¬ Z j.val.val := fun h => j.property (Or.inl h)
    exact ⟨⟨j.val, hZ⟩, by
      cases hs : σ ⟨j.val, hZ⟩
      · exact (j.property (Or.inr ⟨j.val.property, hZ, hs⟩)).elim
      · rfl⟩
  invFun j := ⟨j.val.val, by
    rintro (hZ | ⟨hL, hZ, hs⟩)
    · exact j.val.property hZ
    · have he : (⟨⟨j.val.val.val, hL⟩, hZ⟩ : UniformOmitted L Z) = j.val := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [he, j.property] at hs
      exact Bool.noConfusion hs⟩
  left_inv j := by apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl

omit [DecidableEq J] in
/-- No alphabet-vector counting occurs in this identity. -/
theorem choice_uniformCount (σ : UniformOmitted L Z → Bool) :
    uniformCount L (choiceZeros L Z σ) = (selectionSize σ).val := by
  calc
    _ = Fintype.card (UniformOmitted L (choiceZeros L Z σ)) := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card {j : UniformOmitted L Z // σ j = true} :=
      Fintype.card_congr (choiceUniformEquiv L Z σ)
    _ = _ := by rw [Fintype.card_subtype]; rfl

private def omittedZerosEquiv (hdisj : ∀ j, L j → ¬ Z j) :
    {j : {j // ¬ L j} // Z j.val} ≃ {j : J // Z j} where
  toFun j := ⟨j.val.val, j.property⟩
  invFun j := ⟨⟨j.val, fun h => hdisj j.val h j.property⟩, j.property⟩
  left_inv j := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

omit [DecidableEq J] in
/-- Pinned zeros and full uniforms partition all omitted coordinates. -/
theorem zero_card_add_uniformCount (hdisj : ∀ j, L j → ¬ Z j) :
    Fintype.card {j : J // Z j} + uniformCount L Z =
      Fintype.card J - Fintype.card {j : J // L j} := by
  have hc := Fintype.card_subtype_compl (fun j : {j // ¬ L j} => Z j.val)
  have hz := Fintype.card_congr (omittedZerosEquiv L Z hdisj)
  have hle := Fintype.card_subtype_le (fun j : {j // ¬ L j} => Z j.val)
  have hu : uniformCount L Z =
      Fintype.card {j : {j // ¬ L j} // ¬ Z j.val} := by
    rw [Fintype.card_subtype]
    rfl
  rw [← hu, hz] at hc
  rw [hz] at hle
  rw [Fintype.card_subtype_compl L] at hc hle
  omega

end ChoiceCounting

attribute [local instance] Classical.propDecidable

/-- The common omitted-coordinate normalization is independent of the choice. -/
theorem choice_normalization (d a : Fin 5) (p : SelectedSupport d a)
    (σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool) :
    Fintype.card {i : Fin 4 //
        choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ i} +
      uniformCount (selectedRetained d a p)
        (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ) = 4 - d.val := by
  simpa only [Fintype.card_fin, selectedRetained_card] using
    zero_card_add_uniformCount (selectedRetained d a p)
      (choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ)
      (choiceZeros_disjoint _ _ (selected_disjoint d a p) σ)

/-- The expanded zero count uses the true Boolean count exactly once. -/
theorem choiceZeros_card (d a : Fin 5) (p : SelectedSupport d a)
    (σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool) :
    Fintype.card {i : Fin 4 //
      choiceZeros (selectedRetained d a p) (selectedZeros d a p) σ i} =
        4 - d.val - (selectionSize σ).val := by
  have h := choice_normalization d a p σ
  rw [choice_uniformCount] at h
  omega

theorem choiceSize_le (d a : Fin 5) (p : SelectedSupport d a)
    (σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool) :
    (selectionSize σ).val ≤ 4 - d.val := by
  have h := choice_normalization d a p σ
  rw [choice_uniformCount] at h
  omega

/-- Absolute omitted coefficients, grouped by their actual true count. -/
theorem choiceCoefficient_abs (d a : Fin 5) (p : SelectedSupport d a)
    (σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool) :
    |choiceCoefficient (V := AES.Word) (selectedRetained d a p) (selectedZeros d a p) σ| =
      s ^ (selectionSize σ).val / Real.sqrt (q - 1) ^ (a.val - d.val) := by
  have hd : 0 < Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) := by
    rw [AES.word_card]
    positivity
  unfold choiceCoefficient
  rw [Finset.abs_prod]
  have hf (j : UniformOmitted (selectedRetained d a p) (selectedZeros d a p)) :
      |(if σ j then Real.sqrt (Fintype.card AES.Word : ℝ) else -1) /
        Real.sqrt ((Fintype.card AES.Word : ℝ) - 1)| =
      (if σ j then Real.sqrt (Fintype.card AES.Word : ℝ) else 1) /
        Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) := by
    rw [abs_div, abs_of_pos hd]
    cases hj : σ j
    · simp only [Bool.false_eq_true, if_false, abs_neg, abs_one]
    · simp only [if_true, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp_rw [hf]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, mul_one]
  change Real.sqrt (Fintype.card AES.Word : ℝ) ^ (selectionSize σ).val /
      Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^
        Fintype.card (UniformOmitted (selectedRetained d a p) (selectedZeros d a p)) = _
  -- Rewrite only the denominator power: selectionSize has a dependent Fin range.
  have hpow :
      Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^
          Fintype.card (UniformOmitted (selectedRetained d a p) (selectedZeros d a p)) =
        Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^ (a.val - d.val) :=
    congrArg (fun n : ℕ => Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^ n)
      (selected_uniform_card d a p)
  rw [hpow, AES.word_card]
  have hs : Real.sqrt (4294967296 : ℝ) = s := by
    rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num [s]
  norm_num only [Nat.cast_ofNat] at *
  rw [hs]
  norm_num [q]

/-- Exact binomial regrouping retains each chosen full-uniform factor. -/
theorem selected_weighted_sum (d a : Fin 5) (p : SelectedSupport d a) (D : ℕ → ℝ) :
    (∑ σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool,
      |choiceCoefficient (V := AES.Word) (selectedRetained d a p) (selectedZeros d a p) σ| *
        D (selectionSize σ).val) =
      (∑ u : Fin (a.val - d.val + 1),
        (Nat.choose (a.val - d.val) u.val : ℝ) * s ^ u.val * D u.val) /
          Real.sqrt (q - 1) ^ (a.val - d.val) := by
  simp_rw [choiceCoefficient_abs]
  rw [selection_sum_by_size (fun u =>
    s ^ u.val / Real.sqrt (q - 1) ^ (a.val - d.val) * D u.val)]
  rw [selected_uniform_card]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A common survivor norm is factored once after exact Boolean grouping. -/
theorem selected_survivor_sum (d a : Fin 5) (p : SelectedSupport d a)
    (t : ℕ) (c : ℝ) :
    (∑ σ : UniformOmitted (selectedRetained d a p) (selectedZeros d a p) → Bool,
      |choiceCoefficient (V := AES.Word) (selectedRetained d a p) (selectedZeros d a p) σ| *
        (if 4 - d.val - (selectionSize σ).val < t ∧
            t < 4 - (selectionSize σ).val then c else 0)) =
      c / Real.sqrt (q - 1) ^ (a.val - d.val) *
        ActivityMinorEnvelope.omittedSum d.val a.val t := by
  rw [selected_weighted_sum d a p
    (fun u => if 4 - d.val - u < t ∧ t < 4 - u then c else 0)]
  unfold ActivityMinorEnvelope.omittedSum
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> ring

end AESConcrete.ActivityMinorCounting
