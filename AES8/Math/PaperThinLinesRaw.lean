import AES8.Math.PaperThinHolderAffine
import AES8.Math.PaperFiberKernelPower

/-!
# Raw absolute kernels on two three/four-coordinate lines

This leaf derives rows, columns and the total kernel sum from the local
second/fourth moments. Coordinate equivalences are only parametrizations;
the actual affine-MDS and outside-fiber endpoint is in `PaperThinLines`.
Counting measure, real or complex local entries; constructive work only.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperThinLines

variable {𝕜 V L R : Type*} [RCLike 𝕜] [Fintype V] [Fintype L] [Fintype R]

/-- The manuscript's uniform local resources, with their signs explicit. -/
structure EntryMoments {n : ℕ} (T : Fin n → V → V → 𝕜) (δ τ r s : ℝ) : Prop where
  delta_nonneg : 0 ≤ δ
  tau_nonneg : 0 ≤ τ
  rowScale_nonneg : 0 ≤ r
  totalScale_nonneg : 0 ≤ s
  row_second : ∀ j a, (∑ b, ‖T j a b‖ ^ 2) ≤ δ
  col_second : ∀ j b, (∑ a, ‖T j a b‖ ^ 2) ≤ δ
  total_second : ∀ j, (∑ a, ∑ b, ‖T j a b‖ ^ 2) ≤ τ
  row_fourth : ∀ j a, (∑ b, ‖T j a b‖ ^ 4) ≤ r ^ 2 * δ
  col_fourth : ∀ j b, (∑ a, ‖T j a b‖ ^ 4) ≤ r ^ 2 * δ
  total_fourth : ∀ j, (∑ a, ∑ b, ‖T j a b‖ ^ 4) ≤ s ^ 2 * τ

/-- The literal restricted product kernel. -/
def lineKernel {n : ℕ} (T : Fin n → V → V → 𝕜)
    (left : L → Fin n → V) (right : R → Fin n → V) (x : L) (y : R) : 𝕜 :=
  ∏ j, T j (left x j) (right y j)

/-- The nonnegative raw kernel used in `lem:lines`. -/
def absoluteKernel {n : ℕ} (T : Fin n → V → V → 𝕜)
    (left : L → Fin n → V) (right : R → Fin n → V) (x : L) (y : R) : ℝ :=
  ∏ j, ‖T j (left x j) (right y j)‖

theorem absoluteKernel_nonneg {n : ℕ} (T : Fin n → V → V → 𝕜)
    (left : L → Fin n → V) (right : R → Fin n → V) (x : L) (y : R) :
    0 ≤ absoluteKernel T left right x y :=
  Finset.prod_nonneg (fun _ _ => norm_nonneg _)

theorem norm_lineKernel {n : ℕ} (T : Fin n → V → V → 𝕜)
    (left : L → Fin n → V) (right : R → Fin n → V) (x : L) (y : R) :
    ‖lineKernel T left right x y‖ = absoluteKernel T left right x y := by
  simp only [lineKernel, absoluteKernel, norm_prod]

/-- No desired row/column/total cap is an input here: all three are derived
from local moments and bijectivity of each physical line coordinate. -/
theorem raw_bounds (n : ℕ) (hn : n = 3 ∨ n = 4)
    (T : Fin n → V → V → 𝕜) (eL : Fin n → L ≃ V) (eR : Fin n → R ≃ V)
    (δ τ r s : ℝ) (h : EntryMoments T δ τ r s) :
    (∀ x, (∑ y, absoluteKernel T (fun x j => eL j x) (fun y j => eR j y) x y)
      ≤ δ * r ^ (n - 2)) ∧
    (∀ y, (∑ x, absoluteKernel T (fun x j => eL j x) (fun y j => eR j y) x y)
      ≤ δ * r ^ (n - 2)) ∧
    ((∑ x, ∑ y, absoluteKernel T (fun x j => eL j x) (fun y j => eR j y) x y)
      ≤ τ * s ^ (n - 2)) := by
  rcases hn with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      have hb := PaperThinHolder.three_transport eR
        (fun j b => ‖T j (eL j x) b‖) δ r h.delta_nonneg h.rowScale_nonneg
        (fun j => h.row_second j _) (fun j => h.row_fourth j _)
      simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc] using hb
    · intro y
      have hb := PaperThinHolder.three_transport eL
        (fun j a => ‖T j a (eR j y)‖) δ r h.delta_nonneg h.rowScale_nonneg
        (fun j => h.col_second j _) (fun j => h.col_fourth j _)
      simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc] using hb
    · have hb := PaperThinHolder.three_transport
        (fun j => Equiv.prodCongr (eL j) (eR j))
        (fun j z => ‖T j z.1 z.2‖) τ s h.tau_nonneg h.totalScale_nonneg
        (by intro j; simpa only [Fintype.sum_prod_type] using h.total_second j)
        (by intro j; simpa only [Fintype.sum_prod_type] using h.total_fourth j)
      simpa [absoluteKernel, Fin.prod_univ_succ, Fintype.sum_prod_type, mul_assoc] using hb
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      have hb := PaperThinHolder.four_transport eR
        (fun j b => ‖T j (eL j x) b‖) δ r h.delta_nonneg
        (fun j => h.row_fourth j _)
      simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc] using hb
    · intro y
      have hb := PaperThinHolder.four_transport eL
        (fun j a => ‖T j a (eR j y)‖) δ r h.delta_nonneg
        (fun j => h.col_fourth j _)
      simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc] using hb
    · have hb := PaperThinHolder.four_transport
        (fun j => Equiv.prodCongr (eL j) (eR j))
        (fun j z => ‖T j z.1 z.2‖) τ s h.tau_nonneg
        (by intro j; simpa only [Fintype.sum_prod_type] using h.total_fourth j)
      simpa [absoluteKernel, Fin.prod_univ_succ, Fintype.sum_prod_type, mul_assoc] using hb

end AES8.PaperThinLines
