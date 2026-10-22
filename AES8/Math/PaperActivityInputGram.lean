import AES8.Math.WordActivityFrame
import AES8.Math.NormalizedSchur

/-! Generic scalar Gram control for arbitrary signed activity coefficients.
The elementary lower bound uses the exact off-diagonal row sum; it does not
claim the paper's sharper spectral lower bound `(1-xi)^n`.
Constructive proofs only; no attacks, numerical search or manuscript edits. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputGram
open AESMixing WordActivityFrame
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

variable {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]

/-- Symmetric row dominance controls the quadratic on signed coefficients. -/
theorem symmetric_quadratic_le (G : I → I → ℝ) (r : ℝ)
    (hsym : ∀ i j, G i j = G j i) (hpos : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, (∑ j, G i j) ≤ r) (c : I → ℝ) :
    (∑ i, ∑ j, c i * c j * G i j) ≤ r * ∑ i, c i ^ 2 := by
  have hp (i j : I) : c i * c j * G i j ≤
      (c i ^ 2 + c j ^ 2) / 2 * G i j :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (c i-c j)]) (hpos i j)
  calc
    _ ≤ ∑ i, ∑ j, (c i ^ 2 + c j ^ 2) / 2 * G i j :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = ∑ i, c i ^ 2 * ∑ j, G i j := by
      have he : (∑ i, ∑ j, c j ^ 2 * G i j) =
          ∑ i, ∑ j, c i ^ 2 * G i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym j i]
      simp_rw [add_div, add_mul, div_mul_eq_mul_div,
        Finset.sum_add_distrib, ← Finset.sum_div]
      rw [he]
      simp_rw [Finset.mul_sum]
      ring
    _ ≤ ∑ i, c i ^ 2 * r := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- An adjoint energy estimate transfers with its coefficient unchanged. -/
theorem energy_of_adjoint_energy (B : I → J → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hadj : ∀ v : I → ℝ,
      (∑ j, (∑ i, B i j * v i)^2) ≤ r * ∑ i, v i ^ 2)
    (c : J → ℝ) :
    (∑ i, action B c i ^ 2) ≤ r * ∑ j, c j ^ 2 := by
  let v : I → ℝ := action B c
  let e : ℝ := ∑ i, v i ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hid : (∑ j, c j * (∑ i, B i j * v i)) = e := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold e
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (∑ j, B i j * c j) * v i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = v i ^ 2 := by change v i * v i = v i ^ 2; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c
    (fun j => ∑ i, B i j * v i)
  rw [hid] at hcs
  have hh := mul_le_mul_of_nonneg_left (hadj v)
    (show 0 ≤ ∑ j, c j ^ 2 from Finset.sum_nonneg (fun j _ => sq_nonneg (c j)))
  change e ≤ _
  by_cases hz : e = 0
  · rw [hz]
    exact mul_nonneg hr (by positivity)
  · have hp : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    nlinarith

/-- A row-Gram certificate controls the original rectangular scalar matrix. -/
theorem energy_of_rowGram (B : I → J → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hgram : ∀ i k, 0 ≤ ∑ j, B i j * B k j)
    (hrow : ∀ i, (∑ k, ∑ j, B i j * B k j) ≤ r) (c : J → ℝ) :
    (∑ i, action B c i ^ 2) ≤ r * ∑ j, c j ^ 2 := by
  apply energy_of_adjoint_energy B r hr _ c
  intro v
  rw [gram_quadratic]
  exact symmetric_quadratic_le (fun i k => ∑ j, B i j * B k j) r
    (fun i k => by simp only [mul_comm]) hgram hrow v

section TensorFrame
variable {V N : Type*} [Fintype V] [DecidableEq V]
  [Fintype N] [DecidableEq N]

omit [DecidableEq V] [DecidableEq N] in
theorem metric_diagonal (s : N → Bool) : frameMetric V s s = 1 := by
  simp [frameMetric, wordMetric]

omit [DecidableEq V] [DecidableEq N] in
theorem metric_nonnegative (s t : N → Bool) : 0 ≤ frameMetric V s t := by
  apply Finset.prod_nonneg
  intro i _
  unfold wordMetric xi
  split_ifs <;> positivity

omit [DecidableEq V] [DecidableEq N] in
theorem metric_symmetric (s t : N → Bool) : frameMetric V s t = frameMetric V t s := by
  simp only [frameMetric, wordMetric_symmetric]

omit [DecidableEq V] in
/-- The exact tensor-Gram row sum follows by finite product/sum exchange. -/
theorem metric_row_sum (s : N → Bool) :
    (∑ t : N → Bool, frameMetric V s t) = (1 + xi V)^Fintype.card N := by
  unfold frameMetric
  rw [← Fintype.prod_sum]
  have h (i : N) : (∑ t : Bool, wordMetric V (s i) t) = 1 + xi V := by
    cases s i <;> simp [wordMetric, add_comm]
  simp_rw [h]
  simp

def offMetric (s t : N → Bool) : ℝ := if s = t then 0 else frameMetric V s t

omit [DecidableEq V] in
theorem offMetric_row_sum (s : N → Bool) :
    (∑ t : N → Bool, offMetric (V := V) s t) =
      (1 + xi V)^Fintype.card N - 1 := by
  have h (t : N → Bool) : offMetric (V := V) s t =
      frameMetric V s t - if s = t then 1 else 0 := by
    by_cases h : s = t <;> simp [offMetric, h, metric_diagonal]
  simp_rw [h, Finset.sum_sub_distrib]
  rw [metric_row_sum]
  simp

/-- An elementary diagonal-dominance lower bound on the genuine frame.
All signed coefficients and every off-diagonal correlation remain present. -/
theorem frame_energy_lower (z : V) (hV : 1 < Fintype.card V)
    (c : (N → Bool) → ℝ) :
    (2 - (1 + xi V)^Fintype.card N) * (∑ s, c s ^ 2) ≤
      ∑ x : N → V, (∑ s, frameColumn z s x * c s)^2 := by
  have hs := symmetric_quadratic_le (offMetric (V := V))
    ((1 + xi V)^Fintype.card N - 1)
    (fun s t => by simp only [offMetric, eq_comm, metric_symmetric])
    (fun s t => by unfold offMetric; split_ifs; norm_num; exact metric_nonnegative _ _)
    (fun s => (offMetric_row_sum s).le) (fun s => |c s|)
  have hentry (s t : N → Bool) :
      -(c s * c t * offMetric (V := V) s t) ≤
        |c s| * |c t| * offMetric (V := V) s t := by
    have hp : 0 ≤ offMetric (V := V) s t := by
      unfold offMetric; split_ifs; norm_num; exact metric_nonnegative _ _
    have ha := neg_le_abs (c s * c t)
    rw [abs_mul] at ha
    nlinarith
  have he := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hentry s t))
  simp only [sq_abs] at hs
  have hsplit : (∑ s, ∑ t, c s * c t * frameMetric V s t) =
      (∑ s, c s ^ 2) + ∑ s, ∑ t, c s * c t * offMetric (V := V) s t := by
    have h (s t : N → Bool) : c s * c t * frameMetric V s t =
        (if s = t then c s ^ 2 else 0) + c s * c t * offMetric (V := V) s t := by
      by_cases h : s = t <;> simp [offMetric, h, metric_diagonal, pow_two]
    simp_rw [h, Finset.sum_add_distrib]
    simp
  rw [frame_energy z hV, hsplit]
  simp only [Finset.sum_neg_distrib] at he
  nlinarith

end TensorFrame

end AES8.PaperActivityInputGram
