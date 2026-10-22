import AES8.Math.WordActivityFrame
import AES8.Math.PaperKernelLinear
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Exact outside activity expansion

Each constant-nonzero unit vector is expanded into the zero and full-uniform
unit frame. The two outside sides of an arbitrary kernel are expanded before
absolute values and operator norms are taken. The middle activity metric is
not part of this module.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityExpansion
open WordActivityFrame PaperKernelBounds PaperKernelLinear
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {V I J X Y : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X] [DecidableEq X] [Fintype Y]

/-- Unit constant-nonzero vector for an arbitrary finite alphabet. -/
def nonzeroUnit (z : V) (x : V) : ℝ :=
  (if x = z then 0 else 1) / Real.sqrt (q V - 1)

def coefficient (s : Finset I) : ℝ :=
  Real.sqrt (eta V) ^ Fintype.card I * (-xi V) ^ (Fintype.card I - s.card)

def frameProduct (z : V) (s : Finset I) (x : I → V) : ℝ :=
  (∏ i ∈ s, wordFrame z true (x i)) * ∏ i ∈ Finset.univ \ s, wordFrame z false (x i)

theorem sqrt_eta (hq : 1 < Fintype.card V) :
    Real.sqrt (eta V) = Real.sqrt (q V) / Real.sqrt (q V - 1) := by
  rw [eta, Real.sqrt_div (q_pos hq).le]

theorem nonzeroUnit_expansion (z : V) (hq : 1 < Fintype.card V) (x : V) :
    nonzeroUnit z x = Real.sqrt (eta V) *
      (wordFrame z true x + (-xi V) * wordFrame z false x) := by
  have hs : Real.sqrt (q V) ≠ 0 := (Real.sqrt_pos.mpr (q_pos hq)).ne'
  rw [sqrt_eta hq]
  by_cases hx : x = z
  · simp [nonzeroUnit, wordFrame, AESMixing.identityKernel, xi, hx]
  · simp [nonzeroUnit, wordFrame, AESMixing.identityKernel, xi, hx]
    field_simp

theorem product_expansion (z : V) (hq : 1 < Fintype.card V) (x : I → V) :
    (∏ i, nonzeroUnit z (x i)) =
      ∑ s : Finset I, coefficient (V := V) s * frameProduct z s x := by
  simp_rw [nonzeroUnit_expansion z hq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_add, Finset.mul_sum]
  have hall : (Finset.univ : Finset I).powerset = Finset.univ := by ext; simp
  rw [hall]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hc : ((Finset.univ : Finset I) \ s).card = Fintype.card I - s.card := by
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [hc]
  unfold coefficient frameProduct
  ring

/-- Actual contraction on both omitted coordinate families. -/
def slice (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (a : (I → V) → ℝ) (b : (J → V) → ℝ) (y : Y) (x : X) : ℝ :=
  ∑ u, ∑ v, a u * K (y,u) (x,v) * b v

def nonzeroSlice (K : (Y × (I → V)) → (X × (J → V)) → ℝ) (z : V) :=
  slice K (fun u => ∏ i, nonzeroUnit z (u i)) (fun v => ∏ j, nonzeroUnit z (v j))

def frameSlice (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (s : Finset I) (t : Finset J) := slice K (frameProduct z s) (frameProduct z t)

theorem slice_expansion (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (hq : 1 < Fintype.card V) (y : Y) (x : X) :
    nonzeroSlice K z y x =
      ∑ s : Finset I, ∑ t : Finset J,
        (coefficient (V := V) s * coefficient (V := V) t) * frameSlice K z s t y x := by
  unfold nonzeroSlice slice
  simp_rw [product_expansion z hq, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (J → V)))
    (t := (Finset.univ : Finset (Finset I)))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (I → V)))
    (t := (Finset.univ : Finset (Finset I)))]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (J → V)))
    (t := (Finset.univ : Finset (Finset J)))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (I → V)))
    (t := (Finset.univ : Finset (Finset J)))]
  apply Finset.sum_congr rfl
  intro t _
  unfold frameSlice slice
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact matrix identity before the triangle inequality. -/
theorem operator_expansion (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (hq : 1 < Fintype.card V) :
    kernelOperator (nonzeroSlice K z) =
      ∑ s : Finset I, ∑ t : Finset J,
        (coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameSlice K z s t) := by
  have he : nonzeroSlice K z = fun y x =>
      ∑ s : Finset I, ∑ t : Finset J,
        (coefficient (V := V) s * coefficient (V := V) t) * frameSlice K z s t y x :=
    funext (fun y => funext (fun x => slice_expansion K z hq y x))
  rw [he, operator_sum]
  simp_rw [operator_sum, operator_smul]

def absoluteCoefficient (s : Finset I) : ℝ :=
  Real.sqrt (eta V) ^ Fintype.card I * xi V ^ (Fintype.card I - s.card)

theorem abs_coefficient (s : Finset I) :
    |coefficient (V := V) s| = absoluteCoefficient (V := V) s := by
  have hx : 0 ≤ xi V := by unfold xi; positivity
  simp only [coefficient, absoluteCoefficient, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hx]

/-- Norm bound for the literal two-sided activity contraction. -/
theorem norm_le (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (hq : 1 < Fintype.card V) (G : ℕ → ℕ → ℝ)
    (hG : ∀ (s : Finset I) (t : Finset J),
      ‖kernelOperator (frameSlice K z s t)‖ ≤ G s.card t.card) :
    ‖kernelOperator (nonzeroSlice K z)‖ ≤
      ∑ s : Finset I, ∑ t : Finset J,
        absoluteCoefficient (V := V) s * absoluteCoefficient (V := V) t * G s.card t.card := by
  rw [operator_expansion K z hq]
  calc
    _ ≤ ∑ s : Finset I, ‖∑ t : Finset J,
        (coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameSlice K z s t)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset I, ∑ t : Finset J,
        ‖(coefficient (V := V) s * coefficient (V := V) t) •
          kernelOperator (frameSlice K z s t)‖ :=
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

/-- Regrouping by subset size gives the exact binomial multiplicity. -/
theorem sum_by_card (f : ℕ → ℝ) :
    (∑ s : Finset I, f s.card) =
      ∑ k ∈ Finset.range (Fintype.card I + 1), (Nat.choose (Fintype.card I) k : ℝ) * f k := by
  have hu : (Finset.univ : Finset I).powerset = Finset.univ := by ext; simp
  rw [← hu, Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, Finset.card_univ, nsmul_eq_mul]

/-- Exact nonnegative double binomial sum from the paper. -/
def supportSum (n m : ℕ) (xi : ℝ) (G : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (m+1),
    (Nat.choose n a : ℝ) * (Nat.choose m b : ℝ) * xi ^ (n-a) * xi ^ (m-b) * G a b

theorem absolute_sum_eq (G : ℕ → ℕ → ℝ) :
    (∑ s : Finset I, ∑ t : Finset J,
      absoluteCoefficient (V := V) s * absoluteCoefficient (V := V) t * G s.card t.card) =
    Real.sqrt (eta V) ^ (Fintype.card I + Fintype.card J) *
      supportSum (Fintype.card I) (Fintype.card J) (xi V) G := by
  unfold absoluteCoefficient
  rw [sum_by_card (fun a => ∑ t : Finset J,
    (Real.sqrt (eta V) ^ Fintype.card I * xi V ^ (Fintype.card I-a)) *
    (Real.sqrt (eta V) ^ Fintype.card J * xi V ^ (Fintype.card J-t.card)) * G a t.card)]
  unfold supportSum
  rw [pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_by_card (I := J) (fun b =>
    (Real.sqrt (eta V) ^ Fintype.card I * xi V ^ (Fintype.card I-a)) *
    (Real.sqrt (eta V) ^ Fintype.card J * xi V ^ (Fintype.card J-b)) * G a b)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Outside constant-nonzero activity factors have exactly the binomial
loss, with all signs retained until the norm estimate. -/
theorem norm_le_supportSum (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (hq : 1 < Fintype.card V) (G : ℕ → ℕ → ℝ)
    (hG : ∀ (s : Finset I) (t : Finset J),
      ‖kernelOperator (frameSlice K z s t)‖ ≤ G s.card t.card) :
    ‖kernelOperator (nonzeroSlice K z)‖ ≤
      Real.sqrt (eta V) ^ (Fintype.card I + Fintype.card J) *
        supportSum (Fintype.card I) (Fintype.card J) (xi V) G := by
  have h := norm_le K z hq G hG
  rw [absolute_sum_eq] at h
  exact h

end AES8.PaperActivityExpansion
