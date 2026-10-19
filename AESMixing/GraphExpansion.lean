import AESMixing.NonzeroExpansion
import AESMixing.ActivitySpan

/-! Inclusion-exclusion on the eight coordinates of an MDS graph, with
every summand identified with the previously defined shortened graph.
No counting or independence assumption enters this exact identity. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable
open AES

abbrev GraphPosition := Fin 4 ⊕ Fin 4

def outputPositionMask (s : Finset GraphPosition) : Fin 16 :=
  maskBitsEquiv.symm (fun i => decide (Sum.inl i ∈ s))

def inputPositionMask (s : Finset GraphPosition) : Fin 16 :=
  maskBitsEquiv.symm (fun i => decide (Sum.inr i ∈ s))

theorem outputPositionMask_bit (s : Finset GraphPosition) (i : Fin 4) :
    maskBit (outputPositionMask s) i = true ↔ Sum.inl i ∈ s := by
  have h := congrFun (maskBitsEquiv.apply_symm_apply
    (fun i => decide (Sum.inl i ∈ s))) i
  change maskBit (outputPositionMask s) i = decide (Sum.inl i ∈ s) at h
  simp only [h, decide_eq_true_eq]

theorem inputPositionMask_bit (s : Finset GraphPosition) (i : Fin 4) :
    maskBit (inputPositionMask s) i = true ↔ Sum.inr i ∈ s := by
  have h := congrFun (maskBitsEquiv.apply_symm_apply
    (fun i => decide (Sum.inr i ∈ s))) i
  change maskBit (inputPositionMask s) i = decide (Sum.inr i ∈ s) at h
  simp only [h, decide_eq_true_eq]

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def graphCoordinate (L : (Fin 4 → V) →+ (Fin 4 → V))
    (x : Fin 4 → V) : GraphPosition → V := Sum.elim (L x) x

omit [Fintype V] [DecidableEq V] in
theorem graphZeroConditions_union_positions
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (x : Fin 4 → V) :
    graphZeroConditions L (maskUnion r (outputPositionMask s))
      (maskUnion z (inputPositionMask s)) x ↔
      graphZeroConditions L r z x ∧ ∀ j ∈ s, graphCoordinate L x j = 0 := by
  constructor
  · rintro ⟨ho,hi⟩
    constructor
    · constructor
      · intro i h
        exact ho i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl h)
      · intro i h
        exact hi i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl h)
    · intro j hj
      cases j with
      | inl i =>
        exact ho i (by
          rw [maskUnion_bit, Bool.or_eq_true]
          exact Or.inr ((outputPositionMask_bit s i).2 hj))
      | inr i =>
        exact hi i (by
          rw [maskUnion_bit, Bool.or_eq_true]
          exact Or.inr ((inputPositionMask_bit s i).2 hj))
  · rintro ⟨⟨ho,hi⟩,hs⟩
    constructor
    · intro i h
      rw [maskUnion_bit, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ho i h
      · exact hs (Sum.inl i) ((outputPositionMask_bit s i).1 h)
    · intro i h
      rw [maskUnion_bit, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hi i h
      · exact hs (Sum.inr i) ((inputPositionMask_bit s i).1 h)

theorem indicator_weight_subtype {C : Type*} [Fintype C]
    (p : C → Prop) [DecidablePred p] (w : C → ℝ) :
    (∑ c, (if p c then (1 : ℝ) else 0) * w c) =
      ∑ c : {x // p x}, w c.val := by
  classical
  calc
    _ = ∑ c, if p c then w c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : p c <;> simp [h]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem shortened_graph_weight (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (w : (Fin 4 → V) → ℝ) :
    (∑ x, (if graphZeroConditions L r z x then (1 : ℝ) else 0) * w x) =
      ∑ x : ShortenedGraph L r z, w x.val :=
  indicator_weight_subtype _ w

theorem graph_nonzero_expansion (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (s : Finset GraphPosition) (w : (Fin 4 → V) → ℝ) :
    (∑ x, (if graphZeroConditions L r z x ∧
        (∀ j ∈ s, graphCoordinate L x j ≠ 0) then (1 : ℝ) else 0) * w x) =
      ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
        ∑ x : ShortenedGraph L (maskUnion r (outputPositionMask t))
          (maskUnion z (inputPositionMask t)), w x.val := by
  have h := nonzero_weighted_expansion s (fun j x => graphCoordinate L x j = 0)
    (fun x => (if graphZeroConditions L r z x then (1 : ℝ) else 0) * w x)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hz : graphZeroConditions L r z x <;> simp [hz]
  · apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [← shortened_graph_weight]
    apply Finset.sum_congr rfl
    intro x _
    simp only [graphZeroConditions_union_positions]
    split_ifs <;> simp_all

end AESMixing
