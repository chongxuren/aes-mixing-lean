import AES8.Reductions.Support.PaperSupportCompression
import AES8.Math.PaperCompressedExpansion

/-!
# Outside-frame expansion for literal support masks

Only constant-nonzero coordinates are expanded. Prescribed zero coordinates
remain zero in every summand, and residual projections stay inside the block.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportOutside
open AESMixing PaperSupportProjection PaperSupportCoordinates
open PaperActivityExpansion WordActivityFrame PaperKernelBounds PaperTensorCompression
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

abbrev Active (p : Label n) := {k : Outside p // p.2 k.val = false}
abbrev Inactive (p : Label n) := {k : Outside p // ¬ p.2 k.val = false}

def zeroFactor (z : V) (p : Label n) (x : Outside p → V) : ℝ :=
  ∏ k : Inactive p, wordFrame z false (x k.val)

def frameOutside (z : V) (p : Label n) (s : Finset (Active p))
    (x : Outside p → V) : ℝ :=
  frameProduct z s (fun k => x k.val) * zeroFactor z p x

theorem outside_factorization (z : V) (p : Label n) (x : Outside p → V) :
    outsideUnit z p x =
      (∏ k : Active p, nonzeroUnit z (x k.val)) * zeroFactor z p x := by
  unfold outsideUnit
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k : Outside p => p.2 k.val = false)]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    simp only [k.property, Bool.false_eq_true, if_false]
  · unfold zeroFactor
    apply Finset.prod_congr rfl
    intro k _
    have hk : p.2 k.val.val = true := by
      have hk0 := k.property
      cases he : p.2 k.val.val <;> simp_all
    simp only [hk, if_true]

theorem outside_expansion (z : V) (hq : 1 < Fintype.card V)
    (p : Label n) (x : Outside p → V) :
    outsideUnit z p x = ∑ s : Finset (Active p),
      coefficient (V := V) s * frameOutside z p s x := by
  rw [outside_factorization, product_expansion z hq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp only [frameOutside]
  ring

def frameKernel (z : V) (K : (Fin n → V) → (Fin n → V) → ℝ)
    (p q : Label n) (s : Finset (Active p)) (t : Finset (Active q)) :=
  kernelCompose (residualKernel z p) (kernelCompose
    (compressed (PaperSupportCompression.coordinateKernel K p q)
      (frameOutside z p s) (frameOutside z q t)) (residualKernel z q))

theorem block_expansion (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n) :
    kernelOperator (PaperSupportCompression.blockKernel z K p q) =
      ∑ s : Finset (Active p), ∑ t : Finset (Active q),
        (coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameKernel z K p q s t) := by
  unfold PaperSupportCompression.blockKernel
  have hp : outsideUnit z p = fun x => ∑ s : Finset (Active p),
      coefficient (V := V) s * frameOutside z p s x :=
    funext (outside_expansion z hq p)
  have hq' : outsideUnit z q = fun x => ∑ t : Finset (Active q),
      coefficient (V := V) t * frameOutside z q t x :=
    funext (outside_expansion z hq q)
  rw [hp, hq']
  exact PaperCompressedExpansion.sandwich_expansion _ _ _ _ _ _ _

/-- Literal fixed-position support bound, before grouping physical masks. -/
theorem block_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n)
    (G : ℕ → ℕ → ℝ)
    (hG : ∀ (s : Finset (Active p)) (t : Finset (Active q)),
      ‖kernelOperator (frameKernel z K p q s t)‖ ≤ G s.card t.card) :
    ‖kernelOperator (PaperSupportCompression.blockKernel z K p q)‖ ≤
      Real.sqrt (eta V) ^ (Fintype.card (Active p) + Fintype.card (Active q)) *
        supportSum (Fintype.card (Active p)) (Fintype.card (Active q)) (xi V) G := by
  rw [← absolute_sum_eq (I := Active p) (J := Active q) G,
    block_expansion z hq K p q]
  calc
    _ ≤ ∑ s : Finset (Active p), ‖∑ t : Finset (Active q),
        (coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameKernel z K p q s t)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset (Active p), ∑ t : Finset (Active q),
        ‖(coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameKernel z K p q s t)‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_coefficient, abs_coefficient]
      exact mul_le_mul_of_nonneg_left (hG s t) (by
        unfold absoluteCoefficient xi
        positivity)

/-- The number of expanded coordinates is support size minus residual degree. -/
theorem active_card (p : Label n) (hp : Valid p) :
    Fintype.card (Active p) = supportCount p.2 - residualCount p.1 := by
  let S := {k : Fin n // p.2 k = false}
  let ea : Active p ≃ {k : S // ¬ p.1 k.val = true} :=
    { toFun := fun k => ⟨⟨k.val.val, k.property⟩, k.val.property⟩
      invFun := fun k => ⟨⟨k.val.val, k.property⟩, k.val.property⟩
      left_inv := by intro k; rfl
      right_inv := by intro k; rfl }
  let er : {k : S // p.1 k.val = true} ≃ Residual p :=
    { toFun := fun k => ⟨k.val.val, k.property⟩
      invFun := fun k => ⟨⟨k.val, hp k.val k.property⟩, k.property⟩
      left_inv := by intro k; rfl
      right_inv := by intro k; rfl }
  rw [Fintype.card_congr ea, Fintype.card_subtype_compl, Fintype.card_congr er]
  simp only [S, Residual, Fintype.card_subtype, supportCount, residualCount]

end AES8.PaperSupportOutside
