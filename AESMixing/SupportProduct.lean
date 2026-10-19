import AESMixing.SupportPieces

/-! Refine a fixed residual-coordinate projection by the zero/nonzero
support of its remaining coordinates. The refinement is an exact
orthogonal decomposition of arbitrary joint inputs. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def supportProduct (z : V) (marked inactive : I → Bool) (y x : I → V) : ℝ :=
  ∏ i, supportPiece z (marked i) (inactive i) (y i) (x i)

omit [DecidableEq I] in
theorem supportProduct_symmetric (z : V) (marked inactive : I → Bool) (x y : I → V) :
    supportProduct z marked inactive x y = supportProduct z marked inactive y x := by
  unfold supportProduct
  apply Finset.prod_congr rfl
  intro i _
  exact supportPiece_symmetric z (marked i) (inactive i) (x i) (y i)

theorem supportProduct_compose (z : V) (hn : 1 < Fintype.card V)
    (marked a b : I → Bool) :
    kernelCompose (supportProduct z marked a) (supportProduct z marked b) =
      if a = b then supportProduct z marked a else 0 := by
  funext y x
  have he : kernelCompose (supportProduct z marked a) (supportProduct z marked b) y x =
      ∏ i, kernelCompose (supportPiece z (marked i) (a i))
        (supportPiece z (marked i) (b i)) (y i) (x i) := by
    unfold kernelCompose supportProduct
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => supportPiece z (marked i) (a i) (y i) v *
      supportPiece z (marked i) (b i) v (x i))).symm
  rw [he]
  simp_rw [supportPiece_compose z hn]
  by_cases hab : a = b
  · subst b
    simp [supportProduct]
  · simp only [hab,if_false,Pi.zero_apply]
    have hw : ∃ i, a i ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem supportProduct_sum (z : V) (marked : I → Bool) (y x : I → V) :
    (∑ inactive : I → Bool, supportProduct z marked inactive y x) =
      productProjection z marked y x := by
  unfold supportProduct
  rw [← Fintype.prod_sum (fun i b => supportPiece z (marked i) b (y i) (x i))]
  simp only [supportPiece_sum,productProjection]

theorem supportProduct_decomposition (z : V) (marked : I → Bool) (f : (I → V) → ℝ) :
    (fun y => ∑ inactive : I → Bool, action (supportProduct z marked inactive) f y) =
      action (productProjection z marked) f := by
  funext y
  unfold action
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,supportProduct_sum]

theorem supportProduct_orthogonal (z : V) (hn : 1 < Fintype.card V)
    (marked a b : I → Bool) (hab : a ≠ b) (f g : (I → V) → ℝ) :
    (∑ y, action (supportProduct z marked a) f y *
      action (supportProduct z marked b) g y) = 0 := by
  rw [kernel_bilinear]
  have hc (x w : I → V) : (∑ y, supportProduct z marked a y x *
      supportProduct z marked b y w) = 0 := by
    simp_rw [supportProduct_symmetric z marked a _ x]
    change kernelCompose (supportProduct z marked a) (supportProduct z marked b) x w = 0
    rw [supportProduct_compose z hn,if_neg hab]
    rfl
  simp_rw [hc,mul_zero,Finset.sum_const_zero]

theorem supportProduct_pythagoras (z : V) (hn : 1 < Fintype.card V)
    (marked : I → Bool) (f : (I → V) → ℝ) :
    (∑ y, action (productProjection z marked) f y^2) =
      ∑ inactive : I → Bool, ∑ y, action (supportProduct z marked inactive) f y^2 := by
  have he := orthogonal_family_energy (fun inactive => action (supportProduct z marked inactive) f)
    (fun a b hab => supportProduct_orthogonal z hn marked a b hab f f)
  simpa only [congrFun (supportProduct_decomposition z marked f)] using he

end AESMixing
