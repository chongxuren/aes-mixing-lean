import AES8.Math.PaperFiniteOrthonormalCompression
import AES8.Math.PaperActivityExpansion

/-! Lossless rectangular compression of kernels indexed by Boolean subsets.
The size columns and binomial multiplicities are proved here. No spectral
radius or norm correspondence is an input. Constructive mathematics only.
Paper binding: 1906c42e047dabe7dcb66393cdb9658a2a7bd800,
12-word-resources.tex:424--454. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetSizeCompression
open PaperKernelBounds PaperFiniteOrthonormalCompression
set_option autoImplicit false
set_option maxHeartbeats 2400000

section Rectangular
variable {I J X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

/-- Separate orthonormal columns on the two sides of a rectangular matrix. -/
def rectLift (U : J → Y → ℝ) (V : I → X → ℝ)
    (A : Matrix J I ℝ) (y : Y) (x : X) : ℝ :=
  ∑ a : J, ∑ b : I, U a y * A a b * V b x

theorem rect_lift_action (U : J → Y → ℝ) (V : I → X → ℝ)
    (A : Matrix J I ℝ) (f : X → ℝ) :
    kernelAction (rectLift U V A) f = synthesize U (A.mulVec (analyze V f)) := by
  funext y
  simp only [kernelAction, rectLift, synthesize, Matrix.mulVec, dotProduct,
    analyze, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Rectangular norm correspondence, derived from synthesis isometry and
analysis contraction on each side, including empty ambient index types. -/
theorem rect_lift_norm (U : J → Y → ℝ) (V : I → X → ℝ)
    (hU : ∀ a b, (∑ y, U a y * U b y) = if a = b then 1 else 0)
    (hV : ∀ a b, (∑ x, V a x * V b x) = if a = b then 1 else 0)
    (A : Matrix J I ℝ) :
    ‖kernelOperator (rectLift U V A)‖ = ‖kernelOperator A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖WithLp.toLp 2 (kernelAction (rectLift U V A) (fun x => f x))‖ ≤ _
    rw [rect_lift_action, synthesis_norm hU]
    have hb := (kernelOperator A).le_opNorm (WithLp.toLp 2 (analyze V (fun x => f x)))
    exact hb.trans (mul_le_mul_of_nonneg_left (analysis_norm_le hV (fun x => f x))
      (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have hb := (kernelOperator (rectLift U V A)).le_opNorm
      (WithLp.toLp 2 (synthesize V (fun a => v a)))
    change ‖WithLp.toLp 2 (kernelAction (rectLift U V A)
      (synthesize V (fun a => v a)))‖ ≤ _ at hb
    rw [rect_lift_action, analyze_synthesize hV, synthesis_norm hU,
      synthesis_norm hV] at hb
    exact hb
end Rectangular

/-- A subset's size is a legitimate coordinate from zero to `a`. -/
def sizeIndex {a : ℕ} (s : Finset (Fin a)) : Fin (a+1) :=
  ⟨s.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ s)⟩

def sizeScale (a : ℕ) (i : Fin (a+1)) : ℝ :=
  Real.sqrt (Nat.choose a i.val : ℝ)

theorem sizeScale_pos (a : ℕ) (i : Fin (a+1)) : 0 < sizeScale a i := by
  exact Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)))

theorem sizeScale_sq (a : ℕ) (i : Fin (a+1)) :
    sizeScale a i ^ 2 = (Nat.choose a i.val : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

/-- Normalized indicator of one size class. -/
def sizeColumn (a : ℕ) (i : Fin (a+1)) (s : Finset (Fin a)) : ℝ :=
  if i = sizeIndex s then (sizeScale a i)⁻¹ else 0

theorem size_columns_orthonormal (a : ℕ) (i j : Fin (a+1)) :
    (∑ s : Finset (Fin a), sizeColumn a i s * sizeColumn a j s) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hs : sizeScale a i ≠ 0 := ne_of_gt (sizeScale_pos a i)
    calc
      _ = ∑ s : Finset (Fin a),
          (if s.card = i.val then (sizeScale a i)⁻¹ ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases h : s.card = i.val
        · have he : i = sizeIndex s := Fin.ext h.symm
          simp [sizeColumn, he, h, pow_two]
        · have he : i ≠ sizeIndex s := by
            intro he
            exact h (congrArg Fin.val he).symm
          simp [sizeColumn, he, h]
      _ = (Nat.choose a i.val : ℝ) * (sizeScale a i)⁻¹ ^ 2 := by
        rw [PaperActivityExpansion.sum_by_card (I := Fin a)
          (fun k => if k = i.val then (sizeScale a i)⁻¹ ^ 2 else 0)]
        rw [Finset.sum_eq_single i.val]
        · simp
        · intro k _ hk
          simp [hk]
        · intro hi
          exact (hi (Finset.mem_range.mpr (by simpa using i.isLt))).elim
      _ = 1 := by rw [← sizeScale_sq a i]; field_simp
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hi : i = sizeIndex s
    · have hj : j ≠ sizeIndex s := by
        intro hj
        exact hij (hi.trans hj.symm)
      simp [sizeColumn, hi, hj]
    · simp [sizeColumn, hi]

/-- The literal subset array from the paper. -/
def subsetKernel (a b : ℕ) (f : ℕ → ℝ)
    (s : Finset (Fin a)) (t : Finset (Fin b)) : ℝ := f (s.card+t.card)

/-- Size coordinates, with the exact binomial weights. -/
def compressed (a b : ℕ) (f : ℕ → ℝ) : Matrix (Fin (a+1)) (Fin (b+1)) ℝ :=
  fun i j => sizeScale a i * sizeScale b j * f (i.val+j.val)

theorem compressed_entry (a b : ℕ) (f : ℕ → ℝ)
    (i : Fin (a+1)) (j : Fin (b+1)) :
    compressed a b f i j =
      Real.sqrt ((Nat.choose a i.val : ℝ) * (Nat.choose b j.val : ℝ)) *
        f (i.val+j.val) := by
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  rfl

/-- Exact matrix factorization `K = E_a Khat E_b*`. -/
theorem subset_factorization (a b : ℕ) (f : ℕ → ℝ) :
    subsetKernel a b f = rectLift (sizeColumn a) (sizeColumn b) (compressed a b f) := by
  funext s t
  simp only [rectLift, sizeColumn]
  rw [Finset.sum_eq_single (sizeIndex s)]
  · rw [Finset.sum_eq_single (sizeIndex t)]
    · simp only [ite_true, compressed, subsetKernel]
      change f (s.card+t.card) = (sizeScale a (sizeIndex s))⁻¹ *
        (sizeScale a (sizeIndex s) * sizeScale b (sizeIndex t) * f (s.card+t.card)) *
          (sizeScale b (sizeIndex t))⁻¹
      symm
      calc
        _ = ((sizeScale a (sizeIndex s))⁻¹ * sizeScale a (sizeIndex s)) *
          (sizeScale b (sizeIndex t) * (sizeScale b (sizeIndex t))⁻¹) *
            f (s.card+t.card) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt (sizeScale_pos a (sizeIndex s))),
          mul_inv_cancel₀ (ne_of_gt (sizeScale_pos b (sizeIndex t)))]; ring
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- Lossless compression for every pair of Boolean subset spaces and every
real-valued size function; signed entries and rectangular arrays are allowed. -/
theorem subset_norm (a b : ℕ) (f : ℕ → ℝ) :
    ‖kernelOperator (subsetKernel a b f)‖ = ‖kernelOperator (compressed a b f)‖ := by
  rw [subset_factorization]
  exact rect_lift_norm (sizeColumn a) (sizeColumn b)
    (size_columns_orthonormal a) (size_columns_orthonormal b) (compressed a b f)

end AES8.PaperSubsetSizeCompression
