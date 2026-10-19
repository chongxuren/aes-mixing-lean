import AESMixing.CoordinateTensor
import Mathlib.Logic.Equiv.Prod

/-! Keep an arbitrary joint function on the marked coordinates and put
fixed unit vectors on the other coordinates. This is an isometric embedding;
in particular it does not require the marked function to be a product. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]

def coordinateEmbedding (p : I → Prop) [DecidablePred p]
    (a : {i // ¬p i} → V → ℝ) (f : ({i // p i} → V) → ℝ)
    (x : I → V) : ℝ :=
  f (fun i => x i.val) * ∏ i : {i // ¬p i}, a i (x i.val)

theorem coordinateEmbedding_energy (p : I → Prop) [DecidablePred p]
    (a : {i // ¬p i} → V → ℝ) (f : ({i // p i} → V) → ℝ) :
    (∑ x, coordinateEmbedding p a f x^2) =
      (∑ u, f u^2) * ∏ i : {i // ¬p i}, ∑ v, a i v^2 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => V)
  have he := e.sum_comp (fun uv => (f uv.1 * ∏ i, a i (uv.2 i))^2)
  change (∑ x, coordinateEmbedding p a f x^2) = _ at he
  rw [he, Fintype.sum_prod_type]
  have hinner (u : {i // p i} → V) :
      (∑ v : {i // ¬p i} → V, (f u * ∏ i, a i (v i))^2) =
        f u^2 * ∏ i, ∑ w, a i w^2 := by
    simp_rw [mul_pow, ← Finset.prod_pow]
    rw [← Finset.mul_sum]
    exact congrArg (f u^2 * ·) (Fintype.prod_sum (fun i w => a i w^2)).symm
  simp_rw [hinner]
  exact (Finset.sum_mul _ _ _).symm

theorem coordinateEmbedding_isometry (p : I → Prop) [DecidablePred p]
    (a : {i // ¬p i} → V → ℝ) (ha : ∀ i, (∑ v, a i v^2) = 1)
    (f : ({i // p i} → V) → ℝ) :
    (∑ x, coordinateEmbedding p a f x^2) = ∑ u, f u^2 := by
  rw [coordinateEmbedding_energy]
  simp only [ha, Finset.prod_const_one, mul_one]

end AESMixing
