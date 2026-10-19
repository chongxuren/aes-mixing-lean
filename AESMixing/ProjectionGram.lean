import AESMixing.FiveDegree

/-! Gram entries for the actual projected columns. These identities connect
small certificate matrices to concrete responses; they do not assume any of
the numerical diffusion bounds. Counting measure is used throughout. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem projection_gram {V : Type*} [Fintype V]
    (P : V → V → ℝ) (hs : ∀ x y, P x y = P y x)
    (hp : kernelCompose P P = P) (x y : V) :
    gram P x y = P x y := by
  unfold gram
  simp_rw [hs _ x]
  exact congrFun (congrFun hp x) y

theorem productProjection_gram {I V : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (a : I → Bool) (x y : I → V) :
    gram (productProjection z a) x y = productProjection z a x y := by
  apply projection_gram
  · exact productProjection_symmetric z a
  · rw [productProjection_compose z hn, if_pos rfl]

theorem projected_columns_gram {I V : Type*} [Fintype V]
    (P : V → V → ℝ) (hs : ∀ x y, P x y = P y x)
    (hp : kernelCompose P P = P) (B : V → I → ℝ) (i j : I) :
    gram (fun y a => action P (fun x => B x a) y) i j =
      ∑ x, ∑ y, B x i * B y j * P x y := by
  unfold gram
  rw [kernel_bilinear]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [show (∑ a, P a x * P a y) = P x y from projection_gram P hs hp x y]

/-- A column indexed by a finite set of graph points, with no assumed
independence among its output coordinates. -/
def responseColumn {C V : Type*} [Fintype C]
    (P : V → V → ℝ) (L : C → V) (y : V) : ℝ := ∑ c, P y (L c)

theorem responseColumn_gram {A B V : Type*}
    [Fintype A] [Fintype B] [Fintype V]
    (P : V → V → ℝ) (hs : ∀ x y, P x y = P y x)
    (hp : kernelCompose P P = P) (L : A → V) (R : B → V) :
    (∑ y, responseColumn P L y * responseColumn P R y) =
      ∑ a, ∑ b, P (L a) (R b) := by
  have he (y : V) : responseColumn P L y * responseColumn P R y =
      ∑ a, ∑ b, P y (L a) * P y (R b) := by
    simp only [responseColumn, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact projection_gram P hs hp (L a) (R b)

end AESMixing
