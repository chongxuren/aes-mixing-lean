import AESConcrete.WeightedDiagonalDominance

/-!
# Retaining a finite strict weighted Gram margin

This generic real-algebra leaf perturbs a strictly weighted diagonally
dominant matrix by a sufficiently small multiple of any symmetric matrix.
The positive perturbation is obtained from finitely many positive margins;
no numerical constant, optimization or enumeration is introduced.

Constructive proofs only. This is a candidate until a source-bound formal
diagnostic and independent review pass.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperStrictGramMargin
set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

def offWeight (M : I → I → ℝ) (w : I → ℝ) (i : I) : ℝ :=
  ∑ j : I, if i = j then 0 else |M i j| * w j

theorem offWeight_nonneg (M : I → I → ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (i : I) : 0 ≤ offWeight M w i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (abs_nonneg _) (hw j).le

theorem offWeight_sub_le (M H : I → I → ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (e : ℝ) (he : 0 ≤ e) (i : I) :
    offWeight (fun i j => M i j - e * H i j) w i ≤
      offWeight M w i + e * offWeight H w i := by
  unfold offWeight
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp only [hij, if_true, mul_zero, add_zero, le_refl]
  · simp only [hij, if_false]
    have h := abs_sub (M i j) (e * H i j)
    rw [abs_mul, abs_of_nonneg he] at h
    calc
      _ ≤ (|M i j| + e * |H i j|) * w j :=
        mul_le_mul_of_nonneg_right h (hw j).le
      _ = _ := by ring

/-- A finite family of positive real numbers has a common positive lower
bound. The empty family is allowed, so no nonempty-index premise is hidden. -/
theorem exists_positive_le (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ f i := by
  classical
  have hs : ∀ s : Finset I, ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨e, he, hs⟩ := ih
      refine ⟨min (f i) e, lt_min (hf i) he, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hs j hjs)
  obtain ⟨e, he, hs⟩ := hs Finset.univ
  exact ⟨e, he, fun i => hs i (Finset.mem_univ i)⟩

/-- Strict row margins imply nonnegative quadratic domination after a
uniform positive shift. The requested limit keeps the shifted scalar
positive in callers; the proof does not assume positivity of `H`. -/
theorem exists_positive_shift (M H : I → I → ℝ) (w : I → ℝ)
    (hM : ∀ i j, M i j = M j i) (hH : ∀ i j, H i j = H j i)
    (hw : ∀ i, 0 < w i)
    (hdom : ∀ i, 0 < M i i * w i - offWeight M w i)
    (limit : ℝ) (hlimit : 0 < limit) :
    ∃ e : ℝ, 0 < e ∧ e ≤ limit ∧ ∀ x : I → ℝ,
      0 ≤ ∑ i : I, ∑ j : I, x i * x j * (M i j - e * H i j) := by
  let slack : I → ℝ := fun i => M i i * w i - offWeight M w i
  let denom : I → ℝ := fun i => |H i i| * w i + offWeight H w i + 1
  have hd (i : I) : 0 < denom i := by
    have h0 := mul_nonneg (abs_nonneg (H i i)) (hw i).le
    have h1 := offWeight_nonneg H w hw i
    dsimp [denom]
    linarith
  obtain ⟨d, hdpos, hdsmall⟩ := exists_positive_le
    (fun i => slack i / denom i) (fun i => div_pos (hdom i) (hd i))
  let e : ℝ := min d limit
  have he : 0 < e := lt_min hdpos hlimit
  have hbudget (i : I) : e * denom i ≤ slack i := by
    exact (le_div_iff₀ (hd i)).mp ((min_le_left d limit).trans (hdsmall i))
  have hrow (i : I) : offWeight (fun i j => M i j - e * H i j) w i ≤
      (M i i - e * H i i) * w i := by
    have hs := offWeight_sub_le M H w hw e he.le i
    have hb := hbudget i
    have hh : H i i * w i ≤ |H i i| * w i :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (hw i).le
    have hh' := mul_le_mul_of_nonneg_left hh he.le
    dsimp [denom, slack] at hb
    nlinarith
  refine ⟨e, he, min_le_right d limit, ?_⟩
  intro x
  exact AESConcrete.WeightedDiagonalDominance.weighted_diagonal_nonneg
    (fun i j => M i j - e * H i j) w
    (fun i j => by rw [hM i j, hH i j]) hw hrow x

end AES8.PaperStrictGramMargin
