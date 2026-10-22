import AES8.Math.PaperKernelBounds

/-!
# Nonnegative matrix bounds through coordinate groups

Group labels need not be injective or surjective. The group matrix bounds
the full sum into each group, so composition does not introduce a group-size
factor. This is the symbolic reduction used by the degree-two slope criterion.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperGroupedMatrix
set_option autoImplicit false
variable {I J K G H L : Type*}
variable [Fintype I] [Fintype J] [Fintype K]
variable [Fintype G] [Fintype H] [Fintype L]
variable [DecidableEq G] [DecidableEq H] [DecidableEq L]

def action (M : Matrix I J ℝ) (x : J → ℝ) (i : I) : ℝ := ∑ j, M i j * x j

def GroupBound (M : Matrix I J ℝ) (out : I → G) (inp : J → H)
    (B : Matrix G H ℝ) : Prop :=
  ∀ i h, (∑ j, if inp j = h then M i j else 0) ≤ B (out i) h

theorem action_grouped (M : Matrix I J ℝ) (inp : J → H) (w : H → ℝ) (i : I) :
    action M (fun j => w (inp j)) i =
      ∑ h, (∑ j, if inp j = h then M i j else 0) * w h := by
  unfold action
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem action_le_of_groupBound (M : Matrix I J ℝ) (out : I → G) (inp : J → H)
    (B : Matrix G H ℝ) (hB : GroupBound M out inp B)
    (w : H → ℝ) (hw : ∀ h, 0 ≤ w h) (i : I) :
    action M (fun j => w (inp j)) i ≤ action B w (out i) := by
  rw [action_grouped]
  exact Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_right (hB i h) (hw h))

theorem action_mono (M : Matrix I J ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x y : J → ℝ) (hxy : ∀ j, x j ≤ y j) (i : I) :
    action M x i ≤ action M y i :=
  Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hM i j))

theorem action_nonneg (M : Matrix I J ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (x : J → ℝ) (hx : ∀ j, 0 ≤ x j) (i : I) : 0 ≤ action M x i :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hx j))

theorem action_mul (A : Matrix I J ℝ) (B : Matrix J K ℝ) (x : K → ℝ) (i : I) :
    action (A * B) x i = action A (action B x) i := by
  simp only [action, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Group row bounds compose before taking weighted row sums. -/
theorem product_action_le (A : Matrix I J ℝ) (B : Matrix J K ℝ)
    (out : I → G) (middle : J → H) (inp : K → L)
    (Ag : Matrix G H ℝ) (Bg : Matrix H L ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hBg : ∀ h l, 0 ≤ Bg h l)
    (hAg : GroupBound A out middle Ag) (hBgBound : GroupBound B middle inp Bg)
    (w : L → ℝ) (hw : ∀ l, 0 ≤ w l) (i : I) :
    action (A * B) (fun k => w (inp k)) i ≤ action (Ag * Bg) w (out i) := by
  rw [action_mul, action_mul]
  apply le_trans (action_mono A hA _ _
    (fun j => action_le_of_groupBound B middle inp Bg hBgBound w hw j) i)
  exact action_le_of_groupBound A out middle Ag hAg (action Bg w)
    (action_nonneg Bg hBg w hw) i

/-- A strict group comparison gives a strict weighted row bound for every
original coordinate. The weights remain the original group weights. -/
theorem scaled_product_action_lt (A : Matrix I J ℝ) (B : Matrix J I ℝ)
    (out : I → G) (middle : J → H) (Ag : Matrix G H ℝ) (Bg : Matrix H G ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hBg : ∀ h g, 0 ≤ Bg h g)
    (hAg : GroupBound A out middle Ag) (hBgBound : GroupBound B middle out Bg)
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (c r : ℝ) (hc : 0 ≤ c)
    (hstrict : ∀ g, c * action (Ag * Bg) w g < r * w g) (i : I) :
    c * action (A * B) (fun j => w (out j)) i < r * w (out i) := by
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (product_action_le A B out middle out Ag Bg hA hBg hAg hBgBound w hw i) hc)
    (hstrict (out i))

end AES8.PaperGroupedMatrix
