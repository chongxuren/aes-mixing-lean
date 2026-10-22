import AESConcrete.MultiUniformExpansion
import Mathlib.Data.Fintype.Powerset

/-!
# Boolean selection counts and exact normalized expansion weights

Counting takes place on the finite coordinate labels, never on alphabet
vectors. The geometric selection mask has exactly the Boolean selection's
degree; grouping by that degree gives the binomial formula for the weighted
norm sum. The signed expansion and its arbitrary joint residual remain in
`MultiUniformExpansion`.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and 10/14/16 stay fixed; the separate 10/12/14 target
is unchanged. This file asserts no physical cap, return bound, or complete AES
mixing theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.UniformSelectionCounting
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.MultiUniformExpansion

section BooleanCounting
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The number of true entries, with its natural finite range. -/
def selectionSize (σ : A → Bool) : Fin (Fintype.card A + 1) :=
  ⟨(Finset.univ.filter (fun i => σ i = true)).card, by
    have h : (Finset.univ.filter (fun i => σ i = true)).card ≤ Fintype.card A :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    omega⟩

/-- A fixed-size Boolean selection is precisely a subset of that size. -/
private def selectionFiberEquiv (t : Fin (Fintype.card A + 1)) :
    {σ : A → Bool // selectionSize σ = t} ≃
      {s : Finset A // s ∈ (Finset.univ : Finset A).powersetCard t.val} where
  toFun σ := ⟨Finset.univ.filter (fun i => σ.val i = true),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      exact congrArg Fin.val σ.property⟩⟩
  invFun s := ⟨fun i => decide (i ∈ s.val), by
    apply Fin.ext
    change (Finset.univ.filter (fun i => decide (i ∈ s.val) = true)).card = t.val
    have he : Finset.univ.filter (fun i => decide (i ∈ s.val) = true) = s.val := by
      ext i
      simp
    rw [he]
    exact (Finset.mem_powersetCard.mp s.property).2⟩
  left_inv σ := by
    apply Subtype.ext
    funext i
    change decide (i ∈ Finset.univ.filter (fun j => σ.val j = true)) = σ.val i
    cases hi : σ.val i <;> simp [hi]
  right_inv s := by
    apply Subtype.ext
    ext i
    simp

/-- Binomial counting of each Boolean-selection degree. -/
theorem selectionSize_fiber_card (t : Fin (Fintype.card A + 1)) :
    Fintype.card {σ : A → Bool // selectionSize σ = t} =
      Nat.choose (Fintype.card A) t.val := by
  rw [Fintype.card_congr (selectionFiberEquiv t), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]

/-- Any weight depending only on selection degree groups by binomial counts. -/
theorem selection_sum_by_size (w : Fin (Fintype.card A + 1) → ℝ) :
    (∑ σ : A → Bool, w (selectionSize σ)) =
      ∑ t : Fin (Fintype.card A + 1),
        (Nat.choose (Fintype.card A) t.val : ℝ) * w t := by
  rw [← Fintype.sum_fiberwise' (selectionSize (A := A)) w]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, selectionSize_fiber_card]

end BooleanCounting

section PhysicalMask

/-- A physical selected coordinate is exactly a true unmarked-active label. -/
private def selectionMaskCoordinatesEquiv (r E : Fin 16) (σ : Selection r E) :
    MaskCoordinates (selectionMask r E σ) ≃
      {i : UniformPositions r E // σ i = true} where
  toFun j := by
    have hE : maskBit E j.val ≠ true := by
      intro hE
      have hj := j.property
      rw [selectionMask_bit, dif_pos hE] at hj
      exact Bool.false_ne_true hj
    have hr : maskBit r j.val ≠ true := by
      intro hr
      have hj := j.property
      rw [selectionMask_bit, dif_neg hE, dif_pos hr] at hj
      exact Bool.false_ne_true hj
    exact ⟨⟨⟨j.val, hE⟩, hr⟩, by
      simpa only [selectionMask_bit, dif_neg hE, dif_neg hr] using j.property⟩
  invFun j := ⟨j.val.val.val, by
    rw [selectionMask_bit, dif_neg j.val.val.property, dif_neg j.val.property]
    exact j.property⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The Fourier/ordinary mask API and the finite Boolean count agree. -/
theorem selectionMask_size (r E : Fin 16) (σ : Selection r E) :
    maskSize (selectionMask r E σ) = (selectionSize σ).val := by
  calc
    _ = Fintype.card (MaskCoordinates (selectionMask r E σ)) :=
      (maskCoordinates_card _).symm
    _ = Fintype.card {i : UniformPositions r E // σ i = true} :=
      Fintype.card_congr (selectionMaskCoordinatesEquiv r E σ)
    _ = _ := by rw [Fintype.card_subtype]; rfl

end PhysicalMask

section NormalizedWeights
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

omit [AddCommGroup V] [DecidableEq V] in
/-- The absolute coefficient retains every unit normalization exactly.
Absolute values are used only for norm aggregation, not in the signed
pointwise expansion. -/
theorem expansionCoefficient_abs (hn : 1 < Fintype.card V)
    (r E : Fin 16) (σ : Selection r E) :
    |expansionCoefficient (V := V) r E σ| =
      Real.sqrt (Fintype.card V : ℝ) ^ (selectionSize σ).val /
        Real.sqrt ((Fintype.card V : ℝ) - 1) ^
          Fintype.card (UniformPositions r E) := by
  have hq : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < Real.sqrt ((Fintype.card V : ℝ) - 1) :=
    Real.sqrt_pos.2 (by linarith)
  unfold expansionCoefficient
  rw [Finset.abs_prod]
  have hfactor (i : UniformPositions r E) :
      |(if σ i then Real.sqrt (Fintype.card V : ℝ) else -1) /
        Real.sqrt ((Fintype.card V : ℝ) - 1)| =
      (if σ i then Real.sqrt (Fintype.card V : ℝ) else 1) /
        Real.sqrt ((Fintype.card V : ℝ) - 1) := by
    rw [abs_div, abs_of_pos hd]
    cases hi : σ i
    · simp only [Bool.false_eq_true, if_false, abs_neg, abs_one]
    · simp only [if_true, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp_rw [hfactor]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, mul_one]
  rfl

omit [AddCommGroup V] [DecidableEq V] in
/-- The complete weighted norm sum is a binomial sum on coordinate counts.
The denominator remains `sqrt(q-1)^k`; squaring later gives `(q-1)^k`
exactly, including odd `k`. The weight `D` may have either sign here. -/
theorem expansion_weighted_sum_by_size (hn : 1 < Fintype.card V)
    (r E : Fin 16) (D : ℕ → ℝ) :
    (∑ σ : Selection r E,
      |expansionCoefficient (V := V) r E σ| *
        D (maskSize (selectionMask r E σ))) =
    (∑ t : Fin (Fintype.card (UniformPositions r E) + 1),
      (Nat.choose (Fintype.card (UniformPositions r E)) t.val : ℝ) *
        Real.sqrt (Fintype.card V : ℝ) ^ t.val * D t.val) /
      Real.sqrt ((Fintype.card V : ℝ) - 1) ^
        Fintype.card (UniformPositions r E) := by
  simp_rw [expansionCoefficient_abs hn, selectionMask_size]
  rw [selection_sum_by_size (A := UniformPositions r E) (fun t =>
    Real.sqrt (Fintype.card V : ℝ) ^ t.val /
      Real.sqrt ((Fintype.card V : ℝ) - 1) ^
        Fintype.card (UniformPositions r E) * D t.val)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  ring

end NormalizedWeights
end AESConcrete.UniformSelectionCounting
