import AES8.Math.PaperActivityMinorTransport

/-! The two middle frame legs join through the retained residual coordinates.
This is a counting-kernel identity; no inverse metric or norm is inserted. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityFrameJoin
open AESMixing PaperActivityMinorTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

def outside (S : Finset J) (u : J → Bool) (x : J → V) : ℝ :=
  ∏ j : J, if j ∈ S then 1 else WordActivityFrame.wordFrame 0 (u j) (x j)

private theorem partition_product (S : Finset J) (T : S → ℝ) (w : J → ℝ) :
    (∏ j : J, if h : j ∈ S then T ⟨j,h⟩ else w j) =
      (∏ p : S, T p) * (∏ j : J, if j ∈ S then 1 else w j) := by
  have hl : (∏ j : J, if h : j ∈ S then T ⟨j,h⟩ else w j) =
      (∏ p : S, T p) * (∏ p : {j // j ∉ S}, w p.val) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro p _
      simp only [dif_pos p.property]
    · apply Finset.prod_congr (by ext; simp)
      intro p _
      simp only [dif_neg p.property]
  have hr : (∏ j : J, if j ∈ S then (1 : ℝ) else w j) =
      ∏ p : {j // j ∉ S}, w p.val := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)]
    calc
      _ = 1 * (∏ p : {j // j ∉ S}, w p.val) := by
        apply congrArg₂ (· * ·)
        · apply Finset.prod_eq_one
          intro p _
          exact if_pos p.property
        · apply Finset.prod_congr (by ext; simp)
          intro p _
          exact if_neg p.property
      _ = _ := one_mul _
  rw [hl, hr]

theorem analysis_split (S : Finset J) (u : J → Bool)
    (a : S → V) (x : J → V) :
    analysis S u a x =
      (∏ p : S, residualProjection 0 (a p) (x p.val)) * outside S u x :=
  partition_product S (fun p => residualProjection 0 (a p) (x p.val))
    (fun j => WordActivityFrame.wordFrame 0 (u j) (x j))

theorem residual_idempotent (hV : 1 < Fintype.card V) :
    kernelCompose (residualProjection (0 : V)) (residualProjection 0) =
      residualProjection 0 := by
  simpa only [degreePiece, if_true] using degreePiece_compose (0 : V) hV true true

/-- Every omitted physical position retains both actual frame factors. -/
theorem join (S : Finset J) (u v : J → Bool) (hV : 1 < Fintype.card V)
    (y x : J → V) :
    kernelCompose (synthesis S u) (analysis S v) y x =
      (∏ p : S, residualProjection 0 (y p.val) (x p.val)) *
        outside S u y * outside S v x := by
  change (∑ a : S → V, analysis S u a y * analysis S v a x) = _
  simp_rw [analysis_split]
  have he (a : S → V) :
      ((∏ p : S, residualProjection 0 (a p) (y p.val)) * outside S u y) *
        ((∏ p : S, residualProjection 0 (a p) (x p.val)) * outside S v x) =
      (∏ p : S, residualProjection 0 (y p.val) (a p) *
        residualProjection 0 (a p) (x p.val)) * (outside S u y * outside S v x) := by
    simp_rw [show ∀ p : S, residualProjection (0 : V) (a p) (y p.val) =
      residualProjection 0 (y p.val) (a p) from fun p => degreePiece_symmetric 0 true _ _]
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun (p : S) (a : V) =>
    residualProjection 0 (y p.val) a * residualProjection 0 a (x p.val))]
  have hp (p : S) :
      (∑ a : V, residualProjection 0 (y p.val) a * residualProjection 0 a (x p.val)) =
      residualProjection 0 (y p.val) (x p.val) :=
    congrFun (congrFun (residual_idempotent hV) (y p.val)) (x p.val)
  simp_rw [hp]
  ring

theorem join_coordinates (S : Finset J) (u v : J → Bool)
    (hV : 1 < Fintype.card V) (y x : J → V) :
    kernelCompose (synthesis S u) (analysis S v) y x =
      ∏ j : J, if j ∈ S then residualProjection 0 (y j) (x j)
        else WordActivityFrame.wordFrame 0 (u j) (y j) *
          WordActivityFrame.wordFrame 0 (v j) (x j) := by
  rw [join S u v hV]
  have he := partition_product S
    (fun p => residualProjection 0 (y p.val) (x p.val))
    (fun j => WordActivityFrame.wordFrame 0 (u j) (y j) *
      WordActivityFrame.wordFrame 0 (v j) (x j))
  simp only [Subtype.coe_mk, dite_eq_ite] at he
  rw [he]
  rw [mul_assoc]
  apply congrArg (fun a : ℝ => (∏ p : S, residualProjection 0 (y p.val) (x p.val)) * a)
  unfold outside
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ S <;> simp only [hj, if_true, if_false, one_mul]

/-- Explicit enumeration changes no counting coefficient. -/
def assignmentEquiv {m : ℕ} (S : Finset J) (e : S ≃ Fin m) :
    (Fin m → V) ≃ (S → V) where
  toFun a p := a (e p)
  invFun a k := a (e.symm k)
  left_inv a := by funext k; simp
  right_inv a := by funext p; simp

theorem join_reindexed {m : ℕ} (S : Finset J) (e : S ≃ Fin m)
    (u v : J → Bool) :
    kernelCompose (fun y (a : Fin m → V) => synthesis S u y (fun p => a (e p)))
      (fun a x => analysis S v (fun p => a (e p)) x) =
      kernelCompose (synthesis S u) (analysis S v) := by
  funext y x
  exact (assignmentEquiv (V := V) S e).sum_comp
    (fun a => synthesis S u y a * analysis S v a x)

end AES8.PaperActivityFrameJoin
