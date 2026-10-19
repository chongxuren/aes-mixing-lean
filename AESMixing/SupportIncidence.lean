import AESMixing.SupportEmbedding
import AESMixing.RestrictedIncidence

/-! Connect the support components on the original four coordinates to
the marked incidence channel. The bilinear identity is valid for arbitrary
joint functions on the marked coordinates, before residual projection. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit)
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

section Zero
variable [Zero V]

def supportCondition (r marked : Fin 16) (x : Fin 4 → V) : Prop :=
  (∀ i, maskBit r i = true → x i = 0) ∧
    (∀ i, maskBit r i ≠ true → maskBit marked i ≠ true → x i ≠ 0)

omit [Fintype V] in
theorem supportConstant_indicator (b : Bool) (x : V) :
    supportConstant b x = if (if b then x = 0 else x ≠ 0) then 1 else 0 := by
  cases b <;> by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

omit [Fintype V] in
theorem supportEmbedding_apply (r marked : Fin 16) (hr : MaskDisjoint r marked)
    (f : (MaskCoordinates marked → V) → ℝ) (x : Fin 4 → V) :
    supportEmbedding r marked f x =
      if supportCondition r marked x then f (restrictCoordinates marked x) else 0 := by
  have hc : (∀ i : {i : Fin 4 // maskBit marked i ≠ true},
      if maskBit r i.val then x i.val = 0 else x i.val ≠ 0) ↔ supportCondition r marked x := by
    constructor
    · intro h
      constructor
      · intro i hi
        have hh := h ⟨i,hr i hi⟩
        simpa only [hi, ite_true] using hh
      · intro i hi hm
        have hh := h ⟨i,hm⟩
        simpa [hi] using hh
    · rintro ⟨hz,hn⟩ i
      by_cases hi : maskBit r i.val = true
      · simpa only [hi, ite_true] using hz i.val hi
      · simpa [hi] using hn i.val hi i.property
  unfold supportEmbedding coordinateEmbedding
  simp_rw [supportConstant_indicator]
  rw [product_indicator]
  simp only [hc, mul_ite, mul_one, mul_zero]
  rfl

end Zero

def unmarkedGraphPositions (r z out inp : Fin 16) : Finset GraphPosition :=
  Finset.univ.filter (Sum.elim
    (fun i => maskBit r i ≠ true ∧ maskBit out i ≠ true)
    (fun i => maskBit z i ≠ true ∧ maskBit inp i ≠ true))

theorem unmarkedGraphPositions_output (r z out inp : Fin 16) (i : Fin 4) :
    Sum.inl i ∈ unmarkedGraphPositions r z out inp ↔
      maskBit r i ≠ true ∧ maskBit out i ≠ true := by
  simp [unmarkedGraphPositions]

theorem unmarkedGraphPositions_input (r z out inp : Fin 16) (i : Fin 4) :
    Sum.inr i ∈ unmarkedGraphPositions r z out inp ↔
      maskBit z i ≠ true ∧ maskBit inp i ≠ true := by
  simp [unmarkedGraphPositions]

theorem unmarked_shortening_disjoint (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (t : Finset GraphPosition) (ht : t ∈ (unmarkedGraphPositions r z out inp).powerset) :
    MaskDisjoint (maskUnion r (outputPositionMask t)) out ∧
      MaskDisjoint (maskUnion z (inputPositionMask t)) inp := by
  have hsub := Finset.mem_powerset.mp ht
  constructor
  · intro i hi hout
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact hr i hi hout
    · exact ((unmarkedGraphPositions_output r z out inp i).1
        (hsub ((outputPositionMask_bit t i).1 hi))).2 hout
  · intro i hi hinp
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact hz i hi hinp
    · exact ((unmarkedGraphPositions_input r z out inp i).1
        (hsub ((inputPositionMask_bit t i).1 hi))).2 hinp

section Additive
variable [AddCommGroup V]

omit [Fintype V] [DecidableEq V] in
theorem supportCondition_pair (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (x : Fin 4 → V) :
    (supportCondition r out (L x) ∧ supportCondition z inp x) ↔
      graphZeroConditions L r z x ∧
        ∀ j ∈ unmarkedGraphPositions r z out inp, graphCoordinate L x j ≠ 0 := by
  constructor
  · rintro ⟨⟨ho,hn⟩,⟨hi,hm⟩⟩
    refine ⟨⟨ho,hi⟩,?_⟩
    intro j hj
    cases j with
    | inl i =>
      obtain ⟨hr,hout⟩ := (unmarkedGraphPositions_output r z out inp i).1 hj
      exact hn i hr hout
    | inr i =>
      obtain ⟨hz,hinp⟩ := (unmarkedGraphPositions_input r z out inp i).1 hj
      exact hm i hz hinp
  · rintro ⟨⟨ho,hi⟩,hn⟩
    constructor
    · refine ⟨ho,?_⟩
      intro i hr hout
      exact hn (Sum.inl i) ((unmarkedGraphPositions_output r z out inp i).2 ⟨hr,hout⟩)
    · refine ⟨hi,?_⟩
      intro i hz hinp
      exact hn (Sum.inr i) ((unmarkedGraphPositions_input r z out inp i).2 ⟨hz,hinp⟩)

theorem supportEmbedding_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) (g : (MaskCoordinates out → V) → ℝ) :
    (∑ x : Fin 4 → V, supportEmbedding r out g (L x) * supportEmbedding z inp f x) =
      ∑ y, g y * action
        (restrictedGraphIncidence L r z (unmarkedGraphPositions r z out inp) out inp) f y := by
  rw [restrictedGraphIncidence_bilinear]
  apply Finset.sum_congr rfl
  intro x _
  rw [supportEmbedding_apply r out hr, supportEmbedding_apply z inp hz]
  simp only [← supportCondition_pair L r z out inp x]
  split_ifs <;> simp_all

end Additive
end AESMixing
