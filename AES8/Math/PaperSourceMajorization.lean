import AES8.Math.Imports

/-!
# The source activity quadratic and its affine majorant

This is the exact symbolic two-step majorization used in Section 11 of the
frozen paper. The complementary mass stays `1 - ∑ i, p i`. The second step
requires nonnegative affine coefficients; no coordinate monotonicity of the
quadratic is assumed. Probability interpretation and concrete constants are
separate interfaces. Constructive mathematics only; no attacks.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperSourceMajorization

variable {I : Type*} [Fintype I]

/-- Weighted collision with the exact complementary mass. -/
def quadratic (w p : I → ℝ) : ℝ :=
  (1 - ∑ i, p i)^2 + ∑ i, w i * p i^2

/-- Affine upper envelope obtained by using each cap once. -/
def affineMajorant (w b p : I → ℝ) : ℝ :=
  1 + ∑ i, ((∑ j, b j) - 2 + w i * b i) * p i

/-- First displayed inequality in the paper. -/
theorem quadratic_le_affine (w b p : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hpb : ∀ i, p i ≤ b i) :
    quadratic w p ≤ affineMajorant w b p := by
  classical
  have hP : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
  have hPB : (∑ i, p i) ≤ ∑ i, b i := Finset.sum_le_sum (fun i _ => hpb i)
  have hsq : (∑ i, p i)^2 ≤ (∑ i, b i) * ∑ i, p i := by
    nlinarith [mul_le_mul_of_nonneg_right hPB hP]
  have hterms : (∑ i, w i * p i^2) ≤ ∑ i, (w i * b i) * p i := by
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hpb i) (mul_nonneg (hw i) (hp i))
    nlinarith
  have he : affineMajorant w b p =
      1 + ((∑ i, b i) - 2) * (∑ i, p i) + ∑ i, (w i * b i) * p i := by
    unfold affineMajorant
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [he]
  unfold quadratic
  nlinarith

/-- At the all-caps endpoint the majorant is exactly the quadratic. -/
theorem affine_at_caps (w b : I → ℝ) :
    affineMajorant w b b = quadratic w b := by
  unfold affineMajorant quadratic
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h : (∑ i, w i * b i * b i) = ∑ i, w i * b i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  ring

/-- Second displayed inequality: only the affine function is made monotone. -/
theorem affine_le_caps (w b p : I → ℝ) (hpb : ∀ i, p i ≤ b i)
    (hcoeff : ∀ i, 0 ≤ (∑ j, b j) - 2 + w i * b i) :
    affineMajorant w b p ≤ quadratic w b := by
  rw [← affine_at_caps]
  unfold affineMajorant
  exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (hpb i) (hcoeff i)))

/-- The paper's symbolic majorization, with the precise coefficient condition. -/
theorem quadratic_le_caps (w b p : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hpb : ∀ i, p i ≤ b i)
    (hcoeff : ∀ i, 0 ≤ (∑ j, b j) - 2 + w i * b i) :
    quadratic w p ≤ quadratic w b :=
  (quadratic_le_affine w b p hw hp hpb).trans (affine_le_caps w b p hpb hcoeff)

/-- The paper uses the stronger sufficient condition `2 ≤ wᵢ bᵢ`. -/
theorem quadratic_le_caps_of_weighted_cap (w b p : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hpb : ∀ i, p i ≤ b i)
    (hweighted : ∀ i, 2 ≤ w i * b i) :
    quadratic w p ≤ quadratic w b := by
  apply quadratic_le_caps w b p hw hp hpb
  have hB : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => (hp j).trans (hpb j))
  intro i
  linarith [hweighted i]

/-- Probability interpretation requires exact complementary mass, not a new
normalization of the restricted events. -/
theorem collision_with_complement (w b p : I → ℝ) (p0 : ℝ)
    (hmass : p0 + ∑ i, p i = 1)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hpb : ∀ i, p i ≤ b i)
    (hweighted : ∀ i, 2 ≤ w i * b i) :
    p0^2 + ∑ i, w i * p i^2 ≤ quadratic w b := by
  have hp0 : p0 = 1 - ∑ i, p i := by linarith
  rw [hp0]
  exact quadratic_le_caps_of_weighted_cap w b p hw hp hpb hweighted

/-- Exact algebra behind `Q^z (p^(z-1) rho) = Q rho (Q p)^(z-1)`. -/
theorem weighted_geometric_cap (Q p rho : ℝ) (z : ℕ) (hz : 0 < z) :
    Q^z * (p^(z-1) * rho) = Q * rho * (Q*p)^(z-1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : z ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ, mul_pow]
  ring

/-- A single base inequality proves positivity for every nonempty zero set. -/
theorem weighted_geometric_cap_gt_two (Q p rho : ℝ) (z : ℕ) (hz : 0 < z)
    (hbase : 2 < Q * rho) (hgrowth : 1 ≤ Q * p) :
    2 < Q^z * (p^(z-1) * rho) := by
  rw [weighted_geometric_cap Q p rho z hz]
  have hg : 1 ≤ (Q*p)^(z-1) := one_le_pow₀ hgrowth
  nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ Q*rho by linarith)]

end AES8.PaperSourceMajorization
