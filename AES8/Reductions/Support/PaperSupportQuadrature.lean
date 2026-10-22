import AES8.Reductions.Support.PaperSupportProjectionOutput

/-!
# Residual quadrature at every support size

The frozen paper f902bb94 combines all positive residual degrees before
applying the support-size Cauchy--Schwarz bound, at every support size.
The older output functional summed partial-support lengths separately.
This leaf proves the strengthened functional directly for the actual tensor
projections and the exact nonzero domain. It preserves the older interface
for historical consumers without equating the two functionals.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSupportQuadrature
open AESMixing AESPaper.RareActivity
open PaperSupportOutput (activeCell activeCount supportRadius supportWeight ambientRadius)
open PaperSupportProjection

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- Literal functional in equation (general-output), including its exact
all-active weight rather than an enlargement to one. -/
def psi (n q : ℕ) (p : PaperSupportOutput.Profile) : ℝ :=
  2 * (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * p 0 (t.val + 1)) +
    ∑ t : Fin n, supportWeight n q (t.val + 1) *
      Real.sqrt (∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1) ^ 2)

def rawOutput (n q : ℕ) (p : PaperSupportOutput.Profile) : ℝ :=
  2 * (∑ t : Fin (n - 1), supportRadius n q (t.val + 1) * p 0 (t.val + 1)) +
    ∑ t : Fin n, supportRadius n q (t.val + 1) *
      Real.sqrt (∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1) ^ 2)

theorem psi_mono (n q : ℕ) {p r : PaperSupportOutput.Profile}
    (hp : ∀ i t, 0 ≤ p i t) (hpr : ∀ i t, p i t ≤ r i t) :
    psi n q p ≤ psi n q r := by
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    exact Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_left (hpr _ _) (PaperSupportOutput.supportWeight_nonneg _ _ _))
  · apply Finset.sum_le_sum
    intro t _
    apply mul_le_mul_of_nonneg_left _ (PaperSupportOutput.supportWeight_nonneg _ _ _)
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum (fun i _ =>
      (sq_le_sq₀ (hp _ _) ((hp _ _).trans (hpr _ _))).mpr (hpr _ _))

theorem psi_scale (n q : ℕ) (a : ℝ) (p : PaperSupportOutput.Profile) (ha : 0 ≤ a) :
    psi n q (fun i t => a * p i t) = a * psi n q p := by
  have he (t : ℕ) : (∑ i : Fin t, (a * p (i.val + 1) t) ^ 2) =
      a ^ 2 * ∑ i : Fin t, p (i.val + 1) t ^ 2 := by
    simp only [mul_pow, Finset.mul_sum]
  have hs (t : ℕ) : Real.sqrt (∑ i : Fin t, (a * p (i.val + 1) t) ^ 2) =
      a * Real.sqrt (∑ i : Fin t, p (i.val + 1) t ^ 2) := by
    rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  unfold psi
  simp_rw [hs]
  simp only [mul_add, Finset.mul_sum]
  congr 1 <;> simp only [mul_left_comm, mul_assoc]

theorem normalization (n q : ℕ) (hq : 0 < q) (p : PaperSupportOutput.Profile) :
    ambientRadius n q * psi n q p = rawOutput n q p := by
  unfold psi rawOutput
  have hscale {k : ℕ} (v : Fin k → ℝ) :
      ambientRadius n q * (∑ t : Fin k, supportWeight n q (t.val + 1) * v t) =
        ∑ t : Fin k, supportRadius n q (t.val + 1) * v t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_assoc, PaperSupportOutput.radius_mul_weight n q _ hq]
  rw [mul_add, mul_left_comm, hscale, hscale]

theorem residual_support_l1 (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (t : ℕ) :
    l1 (fun x => ∑ i : Fin t, component z f (i.val + 1) t x) ≤
      supportRadius n (Fintype.card V) t *
        Real.sqrt (∑ i : Fin t, profile z f (i.val + 1) t ^ 2) := by
  have hs : ∀ x, x ∉ activeCell z t →
      (∑ i : Fin t, component z f (i.val + 1) t x) = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro i _
    exact component_supported z f _ _ x (by simpa only [PaperSupportOutput.mem_activeCell] using hx)
  have hc : ((activeCell (n := n) z t).card : ℝ) ≤
      supportRadius n (Fintype.card V) t ^ 2 := by
    rw [supportRadius, Real.sq_sqrt (by positivity)]
    exact_mod_cast (PaperSupportOutput.activeCell_card (n := n) z t).le
  have horth (i j : Fin t) (hij : i ≠ j) :
      (∑ x, component z f (i.val + 1) t x * component z f (j.val + 1) t x) = 0 := by
    apply component_orthogonal z hq f _ _ _ _
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg (fun p : ℕ × ℕ => p.1) he
    omega
  have h := PaperSupportOutput.l1_le_of_supported_card (activeCell z t)
    (fun x => ∑ i : Fin t, component z f (i.val + 1) t x)
    (supportRadius n (Fintype.card V) t) (Real.sqrt_nonneg _) hs hc
  rw [PaperSupportOutput.orthogonal_sum_l2 _ horth] at h
  exact h

theorem activity_l1 (hn : 1 ≤ n) (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (hf : f (fun _ => z) = 0) (hcenter : (∑ x, f x) = 0) :
    l1 (activity z f) ≤ 2 * ∑ t : Fin (n - 1),
      supportRadius n (Fintype.card V) (t.val + 1) * profile z f 0 (t.val + 1) := by
  have ha := PaperSupportOutput.constant_cell_cancellation_pairwise (activeCell z n)
    (activity z f) (activity_const z f) (activity_sum z hq f hcenter)
  have hout : (∑ x ∈ (activeCell z n)ᶜ, |activity z f x|) ≤
      ∑ t : Fin (n - 1), l1 (component z f 0 (t.val + 1)) := by
    calc
      _ ≤ ∑ x ∈ (activeCell z n)ᶜ, ∑ t : Fin (n - 1),
          |component z f 0 (t.val + 1) x| := by
        apply Finset.sum_le_sum
        intro x hx
        rw [activity_outside hn z f hf x (Finset.mem_compl.mp hx)]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin n → V, ∑ t : Fin (n - 1),
          |component z f 0 (t.val + 1) x| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      _ = _ := Finset.sum_comm
  have hc : (∑ t : Fin (n - 1), l1 (component z f 0 (t.val + 1))) ≤
      ∑ t : Fin (n - 1), supportRadius n (Fintype.card V) (t.val + 1) *
        profile z f 0 (t.val + 1) := by
    apply Finset.sum_le_sum
    intro t _
    exact PaperSupportOutput.component_l1 z (component z f)
      (component_supported z f) 0 (t.val + 1)
  linarith

theorem support_sensitive_distance (hn : 1 ≤ n) (z : V)
    (hq : 1 < Fintype.card V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (hcenter : (∑ x, f x) = 0) :
    l1 f / 2 ≤ ambientRadius n (Fintype.card V) / 2 *
      psi n (Fintype.card V) (profile z f) := by
  have ha := activity_l1 hn z hq f hf hcenter
  have hr : l1 (fun x => ∑ t : Fin n, ∑ i : Fin (t.val + 1),
      component z f (i.val + 1) (t.val + 1) x) ≤
      ∑ t : Fin n, supportRadius n (Fintype.card V) (t.val + 1) *
        Real.sqrt (∑ i : Fin (t.val + 1), profile z f (i.val + 1) (t.val + 1) ^ 2) :=
    (PaperSupportOutput.l1_sum_le _).trans
      (Finset.sum_le_sum (fun t _ => residual_support_l1 z hq f (t.val + 1)))
  have htri : l1 f ≤ l1 (activity z f) +
      l1 (fun x => ∑ t : Fin n, ∑ i : Fin (t.val + 1),
        component z f (i.val + 1) (t.val + 1) x) := by
    unfold l1
    calc
      _ ≤ ∑ x, (|activity z f x| + |∑ t : Fin n, ∑ i : Fin (t.val + 1),
          component z f (i.val + 1) (t.val + 1) x|) := by
        apply Finset.sum_le_sum
        intro x _
        rw [residual_decomposition z f hf x]
        exact abs_add_le _ _
      _ = _ := Finset.sum_add_distrib
  have h : l1 f ≤ rawOutput n (Fintype.card V) (profile z f) :=
    htri.trans (add_le_add ha hr)
  rw [← normalization n (Fintype.card V) (by omega)] at h
  linarith

/-- The exact current general-output lemma on its stated nonzero domain. -/
theorem support_sensitive_distance_nonzero (hn : 1 ≤ n) (z : V)
    (hq : 1 < Fintype.card V) (f : NonzeroState z n → ℝ)
    (hcenter : (∑ x, f x) = 0) :
    l1 f / 2 ≤ ambientRadius n (Fintype.card V) / 2 *
      psi n (Fintype.card V) (nonzeroProfile z f) := by
  have h := support_sensitive_distance hn z hq (zeroExtend z f) (zeroExtend_zero z f)
    ((zeroExtend_sum z f).trans hcenter)
  simpa only [zeroExtend_l1, profile_zeroExtend] using h

end AES8.PaperSupportQuadrature
