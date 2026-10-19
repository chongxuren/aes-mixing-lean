import AESMixing.PointedProducts
import AESMixing.Markov

/-! Connect independently masked coordinate permutations to their product
difference kernel. This is an identity of the actual finite experiment,
not an assumption that the evolving difference law is a product. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V] [AddCommGroup V]

def coordinatePerm (s : I → Equiv.Perm V) : Equiv.Perm (I → V) :=
  Equiv.piCongrRight s

theorem differenceChannel_coordinates (s : I → Equiv.Perm V) (b a : I → V) :
    differenceChannel (coordinatePerm s) b a =
      ∏ i, differenceChannel (s i) (b i) (a i) := by
  have hp (x : I → V) :
      (if difference (coordinatePerm s) a x = b then (1 : ℝ) else 0) =
        ∏ i, if difference (s i) (a i) (x i) = b i then 1 else 0 := by
    rw [product_indicator]
    have he : difference (coordinatePerm s) a x = b ↔
        ∀ i, difference (s i) (a i) (x i) = b i := by
      exact funext_iff
    simp only [he]
  unfold differenceChannel
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun i x => if difference (s i) (a i) x = b i then (1 : ℝ) else 0)]
  rw [Finset.prod_div_distrib]
  simp only [Fintype.card_fun, Nat.cast_pow, Finset.prod_const, Finset.card_univ]

omit [Fintype I] [DecidableEq I] in
theorem differenceChannel_pointed (s : Equiv.Perm V) :
    PointedBistochastic (differenceChannel s) 0 :=
  ⟨differenceChannel_nonneg s, differenceChannel_zero_row s,
   differenceChannel_zero_column s, differenceChannel_column s, differenceChannel_row s⟩

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem difference_linearOutput (s : Equiv.Perm V) (L : V ≃+ V) (a x : V) :
    difference (s.trans L.toEquiv) a x = L (difference s a x) := by
  simp [difference, Equiv.trans_apply]

omit [Fintype I] [DecidableEq I] in
theorem differenceChannel_linearOutput (s : Equiv.Perm V) (L : V ≃+ V) (a b : V) :
    differenceChannel (s.trans L.toEquiv) b a = differenceChannel s (L.symm b) a := by
  have hp (x : V) : difference (s.trans L.toEquiv) a x = b ↔
      difference s a x = L.symm b := by
    rw [difference_linearOutput]
    exact L.toEquiv.apply_eq_iff_eq_symm_apply
  simp only [differenceChannel, hp]

end AESMixing
