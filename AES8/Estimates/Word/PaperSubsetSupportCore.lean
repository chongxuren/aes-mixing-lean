import AES8.Math.PaperSubsetFrameChange
import AES8.Math.PaperActivityArrayBlocks
import AES8.Math.PaperKernelComposition
import AESMixing.ByteResidualConcrete

/-! Exact equivalence between the live normalized support comparison and the
printed subset-array route. No historical incidence witness is used below.
Support labels are compressed by their exact multiplicities; the resulting
small matrices factor through the paper's subset arrays and frame changes.
Paper binding: 1906c42e047dabe7dcb66393cdb9658a2a7bd800,
12-word-resources.tex:383--497. Constructive build-only source candidate. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetSupportBridge
open AESMixing PaperKernelBounds PaperSubsetSizeCompression PaperSubsetArrayNorms
open PaperSubsetFrameChange PaperActivityArrayBlocks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def supportScale (i : Fin 5) (a : Fin (5-i.val)) : ℝ :=
  Real.sqrt (Nat.choose 4 i.val : ℝ) * Real.sqrt (Nat.choose (4-i.val) a.val : ℝ)

theorem supportScale_pos (i : Fin 5) (a : Fin (5-i.val)) : 0 < supportScale i a := by
  apply mul_pos <;> apply Real.sqrt_pos.2 <;> apply Nat.cast_pos.mpr
  · exact Nat.choose_pos (by omega)
  · exact Nat.choose_pos (by omega)

theorem supportScale_sq (i : Fin 5) (a : Fin (5-i.val)) :
    supportScale i a ^ 2 = (Nat.choose 4 i.val * Nat.choose (4-i.val) a.val : ℕ) := by
  simp only [supportScale, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]

def supportColumn (i : Fin 5) (a : Fin (5-i.val)) (p : SupportIndex i.val) : ℝ :=
  if a = supportIndexSize p then (supportScale i a)⁻¹ else 0

theorem support_columns_orthonormal (i : Fin 5) (a b : Fin (5-i.val)) :
    (∑ p, supportColumn i a p * supportColumn i b p) = if a=b then 1 else 0 := by
  by_cases hab : a=b
  · subst b
    simp only [ite_true]
    calc
      _ = ∑ p : SupportIndex i.val,
          if a=supportIndexSize p then (supportScale i a)⁻¹^2 else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases h : a=supportIndexSize p <;> simp [supportColumn, h, pow_two]
      _ = (Nat.choose 4 i.val * Nat.choose (4-i.val) a.val : ℕ) *
          (supportScale i a)⁻¹^2 := by
        rw [supportIndex_sum_by_size i
          (fun b => if a=b then (supportScale i a)⁻¹^2 else 0)]
        simp [mul_ite]
      _ = 1 := by
        rw [← supportScale_sq i a]
        field_simp [ne_of_gt (supportScale_pos i a)]
  · simp only [hab, ite_false]
    apply Finset.sum_eq_zero
    intro p _
    by_cases ha : a=supportIndexSize p
    · have hb : b≠supportIndexSize p := fun hb => hab (ha.trans hb.symm)
      simp [supportColumn, ha, hb]
    · simp [supportColumn, ha]

def supportCompressed (i j : Fin 5) : Matrix (Fin (5-i.val)) (Fin (5-j.val)) ℝ :=
  fun a b => supportScale i a * Real.sqrt (1/255^a.val) *
    (incidenceSupportRaw i.val j.val (a.val+i.val) (b.val+j.val) : ℝ) *
      Real.sqrt (1/255^b.val) * supportScale j b

theorem support_factorization (i j : Fin 5) :
    supportIncidenceComparison i j =
      rectLift (supportColumn i) (supportColumn j) (supportCompressed i j) := by
  funext p q
  simp only [rectLift, supportColumn]
  rw [Finset.sum_eq_single (supportIndexSize p)]
  · rw [Finset.sum_eq_single (supportIndexSize q)]
    · simp only [ite_true, supportCompressed, supportIncidenceComparison, supportDiagonal]
      field_simp [ne_of_gt (supportScale_pos i (supportIndexSize p)),
        ne_of_gt (supportScale_pos j (supportIndexSize q))]
      <;> ring
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha; simp [ha]
  · simp

theorem support_norm (i j : Fin 5) :
    ‖kernelOperator (supportIncidenceComparison i j)‖ =
      ‖kernelOperator (supportCompressed i j)‖ := by
  rw [support_factorization]
  exact rect_lift_norm _ _ (support_columns_orthonormal i)
    (support_columns_orthonormal j) _

theorem sqrt_nat_power (x : ℝ) (hx : 0≤x) (n : ℕ) :
    Real.sqrt (x^n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem diagonal_sqrt (a : ℕ) : Real.sqrt (1/(255:ℝ)^a) =
    Real.sqrt 255 ^ a / (255:ℝ)^a := by
  have hp : 0 < Real.sqrt (255:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤255)
  have hpow : (Real.sqrt (255:ℝ)^a)^2 = (255:ℝ)^a := by
    rw [← pow_mul, Nat.mul_comm a 2, pow_mul, hs]
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1), Real.sqrt_one,
    sqrt_nat_power _ (by norm_num)]
  apply (div_eq_div_iff (ne_of_gt (pow_pos hp a)) (by positivity)).mpr
  nlinarith only [hpow]

def middle11 : Matrix (Fin 4) (Fin 4) ℝ := fun a b => matrix11 a b / 4096
def middle12 : Matrix (Fin 4) (Fin 3) ℝ := fun a b => matrix12 a b / 256
def middle22 : Matrix (Fin 3) (Fin 3) ℝ := matrix22 (1/16) (1/256)


end AES8.PaperSubsetSupportBridge
