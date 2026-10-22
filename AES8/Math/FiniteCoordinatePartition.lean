import AESMixing.Product

/-!
# Splitting a finite coordinate tuple into a subset and its complement

The equivalence keeps literal physical coordinates. It is shared by source
factorization and output energy reindexing; it has no probabilistic premises.
-/

noncomputable section
open scoped BigOperators

namespace AES8.FiniteCoordinatePartition

variable {K V : Type*} [DecidableEq K]

/-- Restrict a tuple to a chosen subset and its relative complement. -/
def split (s t : Finset K) (hst : s ⊆ t) :
    (t → V) ≃ (s → V) × (↥(t \ s) → V) where
  toFun x := (fun i => x ⟨i.val, hst i.property⟩,
    fun i => x ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩)
  invFun x i := if hi : i.val ∈ s then x.1 ⟨i.val, hi⟩ else
    x.2 ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩
  left_inv x := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      simp only [dif_neg (Finset.mem_sdiff.mp i.property).2]

/-- Product factorization with no artificial coordinate ordering. -/
theorem prod_split (s t : Finset K) (hst : s ⊆ t) (f : K → ℝ) :
    (∏ i ∈ t, f i) = (∏ i : s, f i.val) * (∏ i : ↥(t \ s), f i.val) := by
  rw [Finset.prod_coe_sort s f, Finset.prod_coe_sort (t \ s) f, mul_comm]
  exact (Finset.prod_sdiff hst).symm

end AES8.FiniteCoordinatePartition
