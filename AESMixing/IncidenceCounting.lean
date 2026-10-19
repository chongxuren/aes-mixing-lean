import AESMixing.SupportIncidenceBound
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! The inclusion-exclusion coefficient depends only on support sizes.
These counting identities connect the exact subset expansion to the
binomial expression used for the small comparison matrices. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)

theorem powerset_size_sum {J : Type*} [DecidableEq J]
    (s : Finset J) (f : ℕ → ℝ) :
    (∑ t ∈ s.powerset, f t.card) =
      ∑ n ∈ Finset.range (s.card+1), (s.card.choose n : ℝ)*f n := by
  rw [Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, nsmul_eq_mul]

set_option maxRecDepth 100000 in
theorem selected_position_count : ∀ t : Finset GraphPosition,
    maskSize (outputPositionMask t)+maskSize (inputPositionMask t) = t.card := by
  have hc : ∀ t : Finset GraphPosition,
      (Finset.univ.filter (fun i : Fin 4 => Sum.inl i ∈ t)).card +
        (Finset.univ.filter (fun i : Fin 4 => Sum.inr i ∈ t)).card = t.card := by decide
  intro t
  simpa only [maskSize, outputPositionMask_bit, inputPositionMask_bit] using hc t

set_option maxRecDepth 100000 in
theorem free_position_count : ∀ r marked : Fin 16, MaskDisjoint r marked →
    Fintype.card {i : Fin 4 // maskBit r i ≠ true ∧ maskBit marked i ≠ true} =
      4-(maskSize r+maskSize marked) := by decide

def unmarkedPositionEquiv (r z out inp : Fin 16) :
    {j : GraphPosition // j ∈ unmarkedGraphPositions r z out inp} ≃
      ({i : Fin 4 // maskBit r i ≠ true ∧ maskBit out i ≠ true} ⊕
       {i : Fin 4 // maskBit z i ≠ true ∧ maskBit inp i ≠ true}) where
  toFun j := by
    rcases j with ⟨j,hj⟩
    cases j with
    | inl i => exact Sum.inl ⟨i,(unmarkedGraphPositions_output r z out inp i).1 hj⟩
    | inr i => exact Sum.inr ⟨i,(unmarkedGraphPositions_input r z out inp i).1 hj⟩
  invFun j := match j with
    | Sum.inl i => ⟨Sum.inl i.val,(unmarkedGraphPositions_output r z out inp i.val).2 i.property⟩
    | Sum.inr i => ⟨Sum.inr i.val,(unmarkedGraphPositions_input r z out inp i.val).2 i.property⟩
  left_inv j := by rcases j with ⟨j,hj⟩; cases j <;> rfl
  right_inv j := by cases j <;> rfl

theorem unmarkedGraphPositions_card (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp) :
    (unmarkedGraphPositions r z out inp).card =
      (4-(maskSize r+maskSize out))+(4-(maskSize z+maskSize inp)) := by
  have h := Fintype.card_congr (unmarkedPositionEquiv r z out inp)
  simpa only [Fintype.card_coe, Fintype.card_sum,
    free_position_count r out hr, free_position_count z inp hz] using h

theorem unmarked_selected_disjoint (r z out inp : Fin 16)
    (t : Finset GraphPosition) (ht : t ∈ (unmarkedGraphPositions r z out inp).powerset) :
    MaskDisjoint r (outputPositionMask t) ∧ MaskDisjoint z (inputPositionMask t) := by
  have hsub := Finset.mem_powerset.mp ht
  constructor
  · intro i hir hit
    exact ((unmarkedGraphPositions_output r z out inp i).1
      (hsub ((outputPositionMask_bit t i).1 hit))).1 hir
  · intro i hiz hit
    exact ((unmarkedGraphPositions_input r z out inp i).1
      (hsub ((inputPositionMask_bit t i).1 hit))).1 hiz

theorem shortening_constraint_count (r z out inp : Fin 16)
    (t : Finset GraphPosition) (ht : t ∈ (unmarkedGraphPositions r z out inp).powerset) :
    maskSize (maskUnion r (outputPositionMask t)) +
      maskSize (maskUnion z (inputPositionMask t)) = maskSize r+maskSize z+t.card := by
  obtain ⟨hr,hz⟩ := unmarked_selected_disjoint r z out inp t ht
  rw [maskUnion_size r _ hr, maskUnion_size z _ hz]
  have h := selected_position_count t
  omega

theorem shorteningNormSum_by_size (m : ℝ) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp) :
    shorteningNormSum m r z (unmarkedGraphPositions r z out inp) out inp =
      ∑ n ∈ Finset.range ((4-(maskSize r+maskSize out))+(4-(maskSize z+maskSize inp))+1),
        (((4-(maskSize r+maskSize out))+(4-(maskSize z+maskSize inp))).choose n : ℝ) *
          incidenceNormCoefficient m (maskSize r+maskSize z+n) (maskSize out) (maskSize inp) := by
  unfold shorteningNormSum
  calc
    _ = ∑ t ∈ (unmarkedGraphPositions r z out inp).powerset,
        incidenceNormCoefficient m (maskSize r+maskSize z+t.card) (maskSize out) (maskSize inp) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [shortening_constraint_count r z out inp t ht]
    _ = _ := by
      have h := powerset_size_sum (unmarkedGraphPositions r z out inp)
        (fun n => incidenceNormCoefficient m (maskSize r+maskSize z+n) (maskSize out) (maskSize inp))
      rw [unmarkedGraphPositions_card r z out inp hr hz] at h
      exact h

theorem maskSize_le_four : ∀ r : Fin 16, maskSize r ≤ 4 := by decide

theorem disjoint_mask_size_le_four : ∀ r s : Fin 16, MaskDisjoint r s →
    maskSize r+maskSize s ≤ 4 := by decide

end AESMixing
