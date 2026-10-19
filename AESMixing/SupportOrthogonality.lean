import AESMixing.SupportProduct

/-! Support components are orthogonal even when the sets of residual
positions differ. This permits regrouping by total residual degree. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem supportPiece_mixed_compose (z : V) (hn : 1 < Fintype.card V)
    (ma mb a b : Bool) :
    kernelCompose (supportPiece z ma a) (supportPiece z mb b) =
      if ma = mb ∧ a = b then supportPiece z ma a else 0 := by
  apply kernel_action_ext
  intro f
  cases ma <;> cases mb <;> cases a <;> cases b <;>
    simp only [supportPiece,ite_true,Bool.false_eq_true,Bool.true_eq_false,if_false,
      and_self,and_false,false_and,kernelCompose_action,zero_kernel_action,
      constantMatrix_action,zeroMatrix_action,residualProjection_action,wordResidual,
      wordAverage_sub,zeroPart_sub,wordAverage_idempotent z f hn,
      wordAverage_zeroPart,zeroPart_wordAverage,zeroPart_idempotent,
      wordAverage_zero,zeroPart_zero,sub_self,sub_zero]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem supportProduct_mixed_compose (z : V) (hn : 1 < Fintype.card V)
    (ma mb a b : I → Bool) :
    kernelCompose (supportProduct z ma a) (supportProduct z mb b) =
      if ma = mb ∧ a = b then supportProduct z ma a else 0 := by
  funext y x
  have he : kernelCompose (supportProduct z ma a) (supportProduct z mb b) y x =
      ∏ i, kernelCompose (supportPiece z (ma i) (a i))
        (supportPiece z (mb i) (b i)) (y i) (x i) := by
    unfold kernelCompose supportProduct
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => supportPiece z (ma i) (a i) (y i) v *
      supportPiece z (mb i) (b i) v (x i))).symm
  rw [he]
  simp_rw [supportPiece_mixed_compose z hn]
  by_cases hab : ma = mb ∧ a = b
  · obtain ⟨rfl,rfl⟩ := hab
    simp [supportProduct]
  · simp only [hab,if_false,Pi.zero_apply]
    have hw : ∃ i, ¬(ma i = mb i ∧ a i = b i) := by
      by_contra h
      push Not at h
      exact hab ⟨funext (fun i => (h i).1),funext (fun i => (h i).2)⟩
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem supportProduct_mixed_orthogonal (z : V) (hn : 1 < Fintype.card V)
    (ma mb a b : I → Bool) (hab : ¬(ma = mb ∧ a = b))
    (f g : (I → V) → ℝ) :
    (∑ y, action (supportProduct z ma a) f y *
      action (supportProduct z mb b) g y) = 0 := by
  rw [kernel_bilinear]
  have hc (x w : I → V) : (∑ y, supportProduct z ma a y x *
      supportProduct z mb b y w) = 0 := by
    simp_rw [supportProduct_symmetric z ma a _ x]
    change kernelCompose (supportProduct z ma a) (supportProduct z mb b) x w = 0
    rw [supportProduct_mixed_compose z hn,if_neg hab]
    rfl
  simp_rw [hc,mul_zero,Finset.sum_const_zero]

end AESMixing
