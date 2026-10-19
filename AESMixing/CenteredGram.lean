import AESMixing.ActivityDomination

/-! Removing the two invariant word directions from a Gram calculation.
The correction is derived from the actual averaging projection. It cannot
be omitted when certifying the degree-zero diffusion block. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem wordAverage_inner (z : V) (hn : 1 < Fintype.card V) (f g : V → ℝ) :
    (∑ x, wordAverage z f x * wordAverage z g x) = f z * g z +
      ((∑ x, f x) - f z) * ((∑ x, g x) - g z) / (Fintype.card V - 1 : ℝ) := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (Fintype.card V - 1 : ℝ) ≠ 0 := by linarith
  have hp (x : V) : wordAverage z f x * wordAverage z g x =
      nonzeroMean z f * nonzeroMean z g +
        if x = z then f z * g z - nonzeroMean z f * nonzeroMean z g else 0 := by
    by_cases hx : x = z <;> simp [wordAverage, hx]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold nonzeroMean
  field_simp
  ring

theorem wordResidual_inner (z : V) (hn : 1 < Fintype.card V) (f g : V → ℝ) :
    (∑ x, wordResidual z f x * wordResidual z g x) =
      (∑ x, f x * g x) - ∑ x, wordAverage z f x * wordAverage z g x := by
  have hfg := activity_residual_orthogonal z f g hn
  have hgf := activity_residual_orthogonal z g f hn
  have hp (x : V) : f x * g x =
      wordAverage z f x * wordAverage z g x +
      wordAverage z f x * wordResidual z g x +
      wordAverage z g x * wordResidual z f x +
      wordResidual z f x * wordResidual z g x := by
    simp only [wordResidual, Pi.sub_apply]
    ring
  simp_rw [hp, Finset.sum_add_distrib]
  rw [hfg, hgf]
  ring

theorem wordAverage_same_statistics (z : V) (f g : V → ℝ)
    (hz : f z = g z) (hs : (∑ x, f x) = ∑ x, g x) :
    wordAverage z f = wordAverage z g := by
  funext x
  simp only [wordAverage, nonzeroMean, hz, hs]

theorem centered_gram_same_statistics {I : Type*}
    (z : V) (hn : 1 < Fintype.card V) (f g : I → V → ℝ)
    (hz : ∀ i, f i z = g i z)
    (hs : ∀ i, (∑ x, f i x) = ∑ x, g i x) (i j : I) :
    gram (fun x i => wordResidual z (f i) x) i j =
      gram (fun x i => f i x) i j -
      gram (fun x i => wordAverage z (g i) x) i j := by
  unfold gram
  rw [wordResidual_inner z hn]
  simp_rw [wordAverage_same_statistics z (f _) (g _) (hz _) (hs _)]

end AESMixing
