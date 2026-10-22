import AES8.Math.PaperKernelBounds
import AESMixing.L2Sums

/-!
# Unit-factor compression of finite kernels

Analysis and synthesis on a unit outside factor identify the projected full
operator with its smaller compressed kernel. Arbitrary joint inputs remain
allowed; no product-input hypothesis is introduced.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperTensorCompression
open AESMixing PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {X Y U W : Type*} [Fintype X] [Fintype Y] [Fintype U] [Fintype W]

def embed (a : U → ℝ) (f : X → ℝ) (p : X × U) : ℝ := f p.1 * a p.2

def collapse (a : U → ℝ) (f : X × U → ℝ) (x : X) : ℝ := ∑ u, a u * f (x,u)

def project (a : U → ℝ) (f : X × U → ℝ) := embed a (collapse a f)

def compressed (K : (Y × U) → (X × W) → ℝ) (a : U → ℝ) (b : W → ℝ)
    (y : Y) (x : X) : ℝ := ∑ u, ∑ v, a u * K (y,u) (x,v) * b v

theorem embed_energy (a : U → ℝ) (f : X → ℝ) :
    (∑ p, embed a f p ^ 2) = (∑ x, f x ^ 2) * ∑ u, a u ^ 2 := by
  simp only [embed, Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

theorem embed_l2 (a : U → ℝ) (ha : (∑ u, a u ^ 2) = 1) (f : X → ℝ) :
    l2 (embed a f) = l2 f := by
  apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  rw [l2_sq, l2_sq, embed_energy, ha, _root_.mul_one]

theorem collapse_embed (a : U → ℝ) (ha : (∑ u, a u ^ 2) = 1) (f : X → ℝ) :
    collapse a (embed a f) = f := by
  funext x
  unfold collapse embed
  calc
    _ = f x * ∑ u, a u ^ 2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ = _ := by rw [ha, _root_.mul_one]

theorem collapse_l2_le (a : U → ℝ) (ha : (∑ u, a u ^ 2) = 1)
    (f : X × U → ℝ) : l2 (collapse a f) ≤ l2 f := by
  apply (sq_le_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  rw [l2_sq, l2_sq, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro x _
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun u => f (x,u))
  simpa only [collapse, ha, one_mul] using h

theorem collapse_project (a : U → ℝ) (ha : (∑ u, a u ^ 2) = 1)
    (f : X × U → ℝ) : collapse a (project a f) = collapse a f :=
  collapse_embed a ha _

theorem project_l2 (a : U → ℝ) (ha : (∑ u, a u ^ 2) = 1)
    (f : X × U → ℝ) : l2 (project a f) = l2 (collapse a f) := embed_l2 a ha _

/-- Literal compressed action before norm estimates. -/
theorem compressed_action (K : (Y × U) → (X × W) → ℝ)
    (a : U → ℝ) (b : W → ℝ) (f : X → ℝ) :
    collapse a (kernelAction K (embed b f)) = kernelAction (compressed K a b) f := by
  funext y
  unfold collapse compressed kernelAction embed
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem projected_action (K : (Y × U) → (X × W) → ℝ)
    (a : U → ℝ) (b : W → ℝ) (f : X × W → ℝ) :
    project a (kernelAction K (project b f)) =
      embed a (kernelAction (compressed K a b) (collapse b f)) := by
  unfold project
  rw [compressed_action]

theorem l2_eq_norm {A : Type*} [Fintype A] (f : A → ℝ) :
    l2 f = ‖WithLp.toLp 2 f‖ := by
  apply (sq_eq_sq₀ (l2_nonneg _) (norm_nonneg _)).mp
  simp only [l2_sq, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- A compressed operator cap controls the actual projected full operator.
The input length is measured after projection, as needed for block assembly. -/
theorem projected_l2_le [DecidableEq X] (K : (Y × U) → (X × W) → ℝ)
    (a : U → ℝ) (b : W → ℝ) (ha : (∑ u, a u ^ 2) = 1)
    (hb : (∑ v, b v ^ 2) = 1) (c : ℝ)
    (hK : ‖kernelOperator (compressed K a b)‖ ≤ c) (f : X × W → ℝ) :
    l2 (project a (kernelAction K (project b f))) ≤ c * l2 (project b f) := by
  rw [projected_action, embed_l2 a ha, project_l2 b hb, l2_eq_norm, l2_eq_norm]
  let g : EuclideanSpace ℝ X := WithLp.toLp 2 (collapse b f)
  change ‖kernelOperator (compressed K a b) g‖ ≤ c * ‖g‖
  exact ((kernelOperator (compressed K a b)).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg g))

end AES8.PaperTensorCompression
