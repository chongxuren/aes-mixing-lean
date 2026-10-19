import AESMixing.Tensor
import AESMixing.ChannelProjection

/-! Tensor products of four kernels, acting on arbitrary joint input vectors.
The product bound is an operator theorem, not an independence assumption. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def tensorKernel {α β γ δ : Type*} (A : α → β → ℝ) (B : γ → δ → ℝ)
    (y : α × γ) (x : β × δ) : ℝ := A y.1 x.1 * B y.2 x.2

theorem tensorKernel_action {α β γ δ : Type*} [Fintype β] [Fintype δ]
    (A : α → β → ℝ) (B : γ → δ → ℝ) (f : β × δ → ℝ) :
    action (tensorKernel A B) f = productAction A B f := by
  funext y
  simp only [action, tensorKernel, productAction, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

theorem tensorKernel_energy {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : α → β → ℝ) (B : γ → δ → ℝ) (a b : ℝ)
    (hA : ∀ f, (∑ y, action A f y^2) ≤ a^2 * ∑ x, f x^2)
    (hB : ∀ f, (∑ y, action B f y^2) ≤ b^2 * ∑ x, f x^2)
    (f : β × δ → ℝ) :
    (∑ y, action (tensorKernel A B) f y^2) ≤ (a*b)^2 * ∑ x, f x^2 := by
  rw [tensorKernel_action, mul_pow]
  exact product_operator_energy A B a b hA hB f

abbrev PairFour (V : Type*) := (V × V) × (V × V)

def tensorFour {V : Type*} (A B C D : V → V → ℝ) : PairFour V → PairFour V → ℝ :=
  tensorKernel (tensorKernel A B) (tensorKernel C D)

theorem tensorFour_energy {V : Type*} [Fintype V]
    (A B C D : V → V → ℝ) (a b c d : ℝ)
    (hA : ∀ f, (∑ y, action A f y^2) ≤ a^2 * ∑ x, f x^2)
    (hB : ∀ f, (∑ y, action B f y^2) ≤ b^2 * ∑ x, f x^2)
    (hC : ∀ f, (∑ y, action C f y^2) ≤ c^2 * ∑ x, f x^2)
    (hD : ∀ f, (∑ y, action D f y^2) ≤ d^2 * ∑ x, f x^2)
    (f : PairFour V → ℝ) :
    (∑ y, action (tensorFour A B C D) f y^2) ≤
      (a*b*(c*d))^2 * ∑ x, f x^2 :=
  tensorKernel_energy _ _ (a*b) (c*d)
    (tensorKernel_energy A B a b hA hB)
    (tensorKernel_energy C D c d hC hD) f

theorem activityMatrix_energy {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (f : V → ℝ) :
    (∑ y, action (activityMatrix z) f y^2) ≤ (1 : ℝ)^2 * ∑ x, f x^2 := by
  rw [activityMatrix_action, one_pow, one_mul]
  have he := activity_residual_pythagoras z f hn
  have hp : 0 ≤ ∑ x, wordResidual z f x^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

def bytePiece (D : BinaryWord 8 → BinaryWord 8 → ℝ) (residual : Bool) :=
  if residual then residualMatrix D 0 else activityMatrix (0 : BinaryWord 8)

def bytePieceBound (residual : Bool) : ℝ := if residual then 9/128 else 1

theorem bytePiece_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ} (h : ByteResources D)
    (residual : Bool) (f : BinaryWord 8 → ℝ) :
    (∑ y, action (bytePiece D residual) f y^2) ≤ bytePieceBound residual^2 * ∑ x, f x^2 := by
  cases residual
  · exact activityMatrix_energy 0 (by norm_num [BinaryWord.card]) f
  · exact h.residual_matrix_energy f

theorem four_byte_piece_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ} (h : ByteResources D)
    (a b c d : Bool) (f : PairFour (BinaryWord 8) → ℝ) :
    (∑ y, action (tensorFour (bytePiece D a) (bytePiece D b) (bytePiece D c) (bytePiece D d)) f y^2) ≤
      (bytePieceBound a * bytePieceBound b * (bytePieceBound c * bytePieceBound d))^2 * ∑ x, f x^2 :=
  tensorFour_energy _ _ _ _ _ _ _ _
    (bytePiece_energy h a) (bytePiece_energy h b) (bytePiece_energy h c) (bytePiece_energy h d) f

/-- Fully residual four-byte operator, for every joint real input vector. -/
theorem four_byte_residual_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (f : PairFour (BinaryWord 8) → ℝ) :
    (∑ y, action (tensorFour (residualMatrix D 0) (residualMatrix D 0)
      (residualMatrix D 0) (residualMatrix D 0)) f y^2) ≤
        (9/128 : ℝ)^8 * ∑ x, f x^2 := by
  have he := four_byte_piece_energy h true true true true f
  norm_num only [bytePiece, bytePieceBound, Bool.true_eq, if_true] at he
  convert he using 1
  ring

end AESMixing
