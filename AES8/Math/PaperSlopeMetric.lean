import AES8.Math.PaperKernelBounds

/-!
# Weighted row comparison in an inverse metric

The product `H * J` need not be symmetric. Two weighted Schur estimates
and completion of a square in `K` give its quadratic-form implication.
Only the defining metric properties are premises; the desired comparison
is proved. Zero entries of `J *ᵥ w` are permitted.
Constructive proof only; no cryptanalytic attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace AES8.PaperSlopeMetric
set_option autoImplicit false
variable {I : Type*} [Fintype I]

def quad (M : Matrix I I ℝ) (x : I → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

theorem dot_mulVec_symm (M : Matrix I I ℝ) (hsym : ∀ i j, M i j = M j i)
    (x y : I → ℝ) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym j i]
  ring

/-- The variable row-sum form of the symmetric Schur estimate. -/
theorem symmetric_quadratic_le_rows (M : Matrix I I ℝ)
    (hsym : ∀ i j, M i j = M j i) (hpos : ∀ i j, 0 ≤ M i j)
    (x : I → ℝ) : quad M x ≤ ∑ i, x i ^ 2 * (∑ j, M i j) := by
  have hp (i j : I) : x i * x j * M i j ≤
      (x i ^ 2 + x j ^ 2) / 2 * M i j :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (x i - x j)]) (hpos i j)
  calc
    _ = ∑ i, ∑ j, x i * x j * M i j := by
      simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, ∑ j, (x i ^ 2 + x j ^ 2) / 2 * M i j :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      have he : (∑ i, ∑ j, x j ^ 2 * M i j) =
          ∑ i, ∑ j, x i ^ 2 * M i j := by
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

/-- Nonnegative weights may vanish in this Schur estimate. -/
theorem weighted_quadratic_le (M : Matrix I I ℝ)
    (hsym : ∀ i j, M i j = M j i) (hpos : ∀ i j, 0 ≤ M i j)
    (u v : I → ℝ) (hv : ∀ i, 0 ≤ v i) :
    quad M (fun i => u i * v i) ≤ ∑ i, u i ^ 2 * v i * (M *ᵥ v) i := by
  let B : Matrix I I ℝ := fun i j => M i j * v i * v j
  have hBsym : ∀ i j, B i j = B j i := fun i j => by
    dsimp [B]; rw [hsym i j]; ring
  have hBpos : ∀ i j, 0 ≤ B i j := fun i j =>
    mul_nonneg (mul_nonneg (hpos i j) (hv i)) (hv j)
  have h := symmetric_quadratic_le_rows B hBsym hBpos u
  convert h using 1
  · simp only [quad, dotProduct, Matrix.mulVec, B, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Matrix.mulVec, dotProduct, B, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem complete_square [DecidableEq I] (K H : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i) (hKH : K * H = 1)
    (x y : I → ℝ) (t : ℝ) :
    quad K (x - t • (H *ᵥ y)) =
      quad K x - 2 * t * (x ⬝ᵥ y) + t ^ 2 * quad H y := by
  have hid : K *ᵥ (H *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
  have hcross : (H *ᵥ y) ⬝ᵥ (K *ᵥ x) = x ⬝ᵥ y := by
    rw [dot_mulVec_symm K hKsym, hid]
  simp only [quad, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    sub_dotProduct, smul_dotProduct, dotProduct_smul, hid, hcross]
  rw [dotProduct_comm (H *ᵥ y) y]
  ring

/-- A nonnegative symmetric comparison and an inverse metric turn the
positive-vector product bound into a quadratic-form bound. -/
theorem quadratic_le_of_product_rows [DecidableEq I] (K H J : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i) (hKpos : ∀ x : I → ℝ, 0 ≤ quad K x)
    (hKH : K * H = 1)
    (hHsym : ∀ i j, H i j = H j i) (hHpos : ∀ i j, 0 ≤ H i j)
    (hJsym : ∀ i j, J i j = J j i) (hJpos : ∀ i j, 0 ≤ J i j)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (r : ℝ) (hr : 0 < r)
    (hrow : ∀ i, ((H * J) *ᵥ w) i ≤ r * w i) (x : I → ℝ) :
    quad J x ≤ r * quad K x := by
  let u : I → ℝ := fun i => x i / w i
  let z : I → ℝ := J *ᵥ w
  let y : I → ℝ := fun i => u i * z i
  let Q : ℝ := ∑ i, u i ^ 2 * w i * z i
  have huz : ∀ i, u i * w i = x i := fun i => div_mul_cancel₀ _ (ne_of_gt (hw i))
  have hz : ∀ i, 0 ≤ z i := fun i => Finset.sum_nonneg
    (fun j _ => mul_nonneg (hJpos i j) (le_of_lt (hw j)))
  have hQ : quad J x ≤ Q := by
    simpa only [show (fun i => u i * w i) = x from funext huz] using
      weighted_quadratic_le J hJsym hJpos u w (fun i => le_of_lt (hw i))
  have hy : quad H y ≤ r * Q := by
    calc
      _ ≤ ∑ i, u i ^ 2 * z i * (H *ᵥ z) i :=
        weighted_quadratic_le H hHsym hHpos u z hz
      _ ≤ ∑ i, u i ^ 2 * z i * (r * w i) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by simpa only [z, Matrix.mulVec_mulVec] using hrow i)
          (mul_nonneg (sq_nonneg _) (hz i))
      _ = r * Q := by
        simp only [Q, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hxy : x ⬝ᵥ y = Q := by
    simp only [dotProduct, y, Q]
    apply Finset.sum_congr rfl
    intro i _
    rw [← huz i]
    ring
  have hs := hKpos (x - r⁻¹ • (H *ᵥ y))
  rw [complete_square K H hKsym hKH, hxy] at hs
  have hprod := mul_le_mul_of_nonneg_left hy (sq_nonneg r⁻¹)
  have hcancel : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
  have hmain : Q ≤ r * quad K x := by
    have hscale : 0 ≤ r * (quad K x - 2 * r⁻¹ * Q + r⁻¹ ^ 2 * quad H y) :=
      mul_nonneg (le_of_lt hr) hs
    have hscale' : r * (r⁻¹ ^ 2 * quad H y) ≤ Q := by
      calc
        _ ≤ r * (r⁻¹ ^ 2 * (r * Q)) := mul_le_mul_of_nonneg_left hprod (le_of_lt hr)
        _ = Q := by field_simp
    nlinarith [hcancel]
  exact hQ.trans hmain

/-- The scale remains outside the comparison form and the inverse metric. -/
theorem scaled_quadratic_le_of_product_rows [DecidableEq I] (K H J : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i) (hKpos : ∀ x : I → ℝ, 0 ≤ quad K x)
    (hKH : K * H = 1)
    (hHsym : ∀ i j, H i j = H j i) (hHpos : ∀ i j, 0 ≤ H i j)
    (hJsym : ∀ i j, J i j = J j i) (hJpos : ∀ i j, 0 ≤ J i j)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hrow : ∀ i, c * ((H * J) *ᵥ w) i ≤ r * w i) (x : I → ℝ) :
    c * quad J x ≤ r * quad K x := by
  have h := quadratic_le_of_product_rows K H (c • J) hKsym hKpos hKH hHsym hHpos
    (fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [hJsym i j])
    (fun i j => mul_nonneg hc (hJpos i j)) w hw r hr
    (fun i => by simpa only [Matrix.mul_smul, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul] using hrow i) x
  simpa only [quad, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using h

/-- A fixed smaller row bound gives the uniform strict form needed before
taking an operator norm. -/
theorem scaled_quadratic_lt_of_product_margin [DecidableEq I] (K H J : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i)
    (hKpos : ∀ x : I → ℝ, 0 ≤ quad K x)
    (hKstrict : ∀ x : I → ℝ, x ≠ 0 → 0 < quad K x)
    (hKH : K * H = 1)
    (hHsym : ∀ i j, H i j = H j i) (hHpos : ∀ i j, 0 ≤ H i j)
    (hJsym : ∀ i j, J i j = J j i) (hJpos : ∀ i j, 0 ≤ J i j)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (c a r : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a) (har : a < r)
    (hrow : ∀ i, c * ((H * J) *ᵥ w) i ≤ a * w i)
    (x : I → ℝ) (hx : x ≠ 0) : c * quad J x < r * quad K x :=
  lt_of_le_of_lt
    (scaled_quadratic_le_of_product_rows K H J hKsym hKpos hKH hHsym hHpos hJsym hJpos
      w hw c a hc ha hrow x)
    (mul_lt_mul_of_pos_right har (hKstrict x hx))

/-- Finitely many strict coordinate comparisons admit one uniform margin.
The new bound is positive even if some row values are zero. -/
theorem exists_product_margin (v w : I → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℝ) (hr : 0 < r) (hrow : ∀ i, v i < r * w i) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧ ∀ i, v i ≤ a * w i := by
  classical
  by_cases hI : Nonempty I
  · letI := hI
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i => v i / w i) Finset.univ_nonempty
    let b := max 0 (v j / w j)
    have hb : b < r := max_lt hr ((div_lt_iff₀ (hw j)).mpr (hrow j))
    refine ⟨(b+r)/2, by have := le_max_left 0 (v j/w j); dsimp [b] at *; linarith,
      by linarith, ?_⟩
    intro i
    apply (div_le_iff₀ (hw i)).mp
    exact (hj i (Finset.mem_univ i)).trans
      ((le_max_right 0 (v j/w j)).trans (by change b ≤ (b+r)/2; linarith))
  · exact ⟨r/2, by linarith, by linarith, fun i => (hI ⟨i⟩).elim⟩

/-- The strict row certificate supplies a single smaller scalar for every
input, which remains valid when an operator supremum is taken. -/
theorem exists_scaled_quadratic_margin [DecidableEq I] (K H J : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i) (hKpos : ∀ x : I → ℝ, 0 ≤ quad K x)
    (hKH : K * H = 1)
    (hHsym : ∀ i j, H i j = H j i) (hHpos : ∀ i j, 0 ≤ H i j)
    (hJsym : ∀ i j, J i j = J j i) (hJpos : ∀ i j, 0 ≤ J i j)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hrow : ∀ i, c * ((H * J) *ᵥ w) i < r * w i) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧ ∀ x : I → ℝ, c * quad J x ≤ a * quad K x := by
  obtain ⟨a, ha, har, hrowa⟩ := exists_product_margin
    (fun i => c * ((H * J) *ᵥ w) i) w hw r hr hrow
  exact ⟨a, ha, har, scaled_quadratic_le_of_product_rows K H J hKsym hKpos hKH
    hHsym hHpos hJsym hJpos w hw c a hc ha hrowa⟩

/-- Strict weighted product rows yield a strict metric quadratic bound.
No assertion about a nonsymmetric product's Euclidean norm is used. -/
theorem scaled_quadratic_lt_of_product_rows [DecidableEq I] (K H J : Matrix I I ℝ)
    (hKsym : ∀ i j, K i j = K j i)
    (hKpos : ∀ x : I → ℝ, 0 ≤ quad K x)
    (hKstrict : ∀ x : I → ℝ, x ≠ 0 → 0 < quad K x)
    (hKH : K * H = 1)
    (hHsym : ∀ i j, H i j = H j i) (hHpos : ∀ i j, 0 ≤ H i j)
    (hJsym : ∀ i j, J i j = J j i) (hJpos : ∀ i j, 0 ≤ J i j)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (hrow : ∀ i, c * ((H * J) *ᵥ w) i < r * w i)
    (x : I → ℝ) (hx : x ≠ 0) : c * quad J x < r * quad K x := by
  obtain ⟨a, ha, har, hrowa⟩ := exists_product_margin
    (fun i => c * ((H * J) *ᵥ w) i) w hw r hr hrow
  exact scaled_quadratic_lt_of_product_margin K H J hKsym hKpos hKstrict hKH
    hHsym hHpos hJsym hJpos w hw c a r hc ha har hrowa x hx

end AES8.PaperSlopeMetric
