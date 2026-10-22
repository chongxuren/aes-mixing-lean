import AES8.Math.WordActivityFrame

/-! Factor a finite frame product by disjoint marked and uniform coordinates.
This counting identity is independent of AES operator estimates. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFramePartition
set_option autoImplicit false

section FramePartition
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

/-- Write the literal outside frame product over all physical coordinates. -/
theorem frame_partition (M U : Finset K) (hd : Disjoint M U)
    (z : V) (c : K → V) :
    (∏ p : U, WordActivityFrame.wordFrame z true (c p.val)) *
      (∏ p : ↥((M ∪ U)ᶜ), WordActivityFrame.wordFrame z false (c p.val)) =
      ∏ p : K, if p ∈ M then 1 else
        WordActivityFrame.wordFrame z (decide (p ∈ U)) (c p) := by
  have hf : (Mᶜ.filter (fun p => p ∈ U)) = U := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_compl]
    constructor
    · exact And.right
    · intro hp
      exact ⟨fun hm => Finset.disjoint_left.mp hd hm hp, hp⟩
  have hz : (Mᶜ.filter (fun p => p ∉ U)) = (M ∪ U)ᶜ := by
    ext p
    simp
  have he : (∏ p : K, if p ∈ M then (1 : ℝ) else
      WordActivityFrame.wordFrame z (decide (p ∈ U)) (c p)) =
      ∏ p ∈ Mᶜ, WordActivityFrame.wordFrame z (decide (p ∈ U)) (c p) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    congr 1
    ext p
    simp
  rw [he]
  simp only [WordActivityFrame.wordFrame, if_true,
    Bool.false_eq_true, if_false, decide_eq_true_eq]
  rw [Finset.prod_ite, hf, hz, ← Finset.prod_coe_sort U,
    ← Finset.prod_coe_sort (M ∪ U)ᶜ]

end FramePartition

end AES8.PaperFramePartition
