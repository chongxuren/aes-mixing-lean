import AESMixing.ActivitySpan
import AESMixing.WordMDS
import AESMixing.L2Sums
import AESConcrete.InverseFrameEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual 32-bit word activity frame

`AES.Word` is `Fin 4 → BinaryWord 8`, of cardinality 2^32. Its normalized
uniform vector has value 1/65536. The byte constants 256 and 1/16 do not occur
in this word frame. The two columns are normalized, but are not orthogonal.

The generic row-quadratic theorem imported from `InverseFrameEnergy` is used
only as a theorem about arbitrary finite real arrays; none of that module's
byte-frame constants are instantiated here. All four project imports occur
in the operator-20261017 archive's `current-closure.json`, with source hashes
checked while drafting. See the adjacent notes for exact bindings.

Conditioning is proved from the exact Gram inverse and its absolute row sum.
The coefficients are arbitrary signed real numbers. There is no probability,
mass, independence, or assumed conditioning premise.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordActivityFrame
open AESMixing
open AESMixing.AES (maskBit maskSize)

section GenericConditioning

variable {S X : Type*} [Fintype S] [DecidableEq S] [Fintype X]

/-- A bilinear synthesis identity in counting measure. -/
theorem synthesis_bilinear (A : X → S → ℝ) (c d : S → ℝ) :
    (∑ x, action A c x * action A d x) =
      ∑ s, c s * action (gram A) d s := by
  rw [kernel_bilinear]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ t, c s * d t * gram A s t) = c s * action (gram A) d s
  rw [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- An exact symmetric inverse, bounded by absolute row sums, controls a
signed scalar quadratic. This specializes the frozen generic row theorem. -/
theorem symmetric_quadratic_le_row_sum (B : S → S → ℝ) (R : ℝ)
    (hsym : ∀ s t, B s t = B t s)
    (hrow : ∀ s, (∑ t, |B s t|) ≤ R) (c : S → ℝ) :
    (∑ s, c s * action B c s) ≤ R * ∑ s, c s ^ 2 := by
  have h := AESConcrete.InverseFrameEnergy.quadratic_le_rows
    (S := S) (Y := Unit) 1 (by norm_num) B hsym
    (fun s _ => c s) (fun s => c s ^ 2)
    (fun s => by simp [AESConcrete.InverseFrameEnergy.energy])
  calc
    (∑ s, c s * action B c s) =
        ∑ s, ∑ t, B s t *
          AESConcrete.InverseFrameEnergy.inner (fun _ : Unit => c s)
            (fun _ : Unit => c t) := by
      simp only [action, Finset.mul_sum, AESConcrete.InverseFrameEnergy.inner,
        Fintype.sum_unique]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, c s ^ 2 * ∑ t, |B s t| := by simpa only [one_mul] using h
    _ ≤ ∑ s, c s ^ 2 * R := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg (c s))
    _ = R * ∑ s, c s ^ 2 := by rw [← Finset.sum_mul]; ring

/-- Finite-coordinate conditioning from an actual inverse of an actual Gram.
The inverse equation and its row bound are algebraic interfaces, not an
assumed lower singular-value bound. Both are discharged for the word frame
below. No sign or normalization requirement is imposed on `c`. -/
theorem coefficient_energy_le_of_inverse_gram
    (A : X → S → ℝ) (B : S → S → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hsym : ∀ s t, B s t = B t s)
    (hinv : ∀ s t, (∑ u, gram A s u * B u t) = if s = t then 1 else 0)
    (hrow : ∀ s, (∑ t, |B s t|) ≤ R) (c : S → ℝ) :
    (∑ s, c s ^ 2) ≤ R * ∑ x, action A c x ^ 2 := by
  let d : S → ℝ := action B c
  have hcomp : kernelCompose (gram A) B = identityKernel := by
    funext s t
    exact hinv s t
  have hdual : action (gram A) d = c := by
    change action (gram A) (action B c) = c
    rw [← kernelCompose_action, hcomp, identityKernel_action]
  have hpair : (∑ x, action A c x * action A d x) = ∑ s, c s ^ 2 := by
    rw [synthesis_bilinear, hdual]
    simp only [pow_two]
  have hd : (∑ x, action A d x ^ 2) ≤ R * ∑ s, c s ^ 2 := by
    calc
      (∑ x, action A d x ^ 2) = ∑ s, d s * c s := by
        simpa only [← pow_two, hdual] using synthesis_bilinear A d d
      _ = ∑ s, c s * action B c s := by
        apply Finset.sum_congr rfl
        intro s _
        exact mul_comm _ _
      _ ≤ R * ∑ s, c s ^ 2 := symmetric_quadratic_le_row_sum B R hsym hrow c
  have hphys : 0 ≤ ∑ x, action A c x ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hcoeff : 0 ≤ ∑ s, c s ^ 2 :=
    Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (action A c) (action A d)
  rw [hpair] at hcs
  have hmain : (∑ s, c s ^ 2) ^ 2 ≤
      (∑ x, action A c x ^ 2) * (R * ∑ s, c s ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hd hphys)
  by_cases hz : (∑ s, c s ^ 2) = 0
  · rw [hz]
    exact mul_nonneg hR hphys
  · have hpos : 0 < ∑ s, c s ^ 2 := lt_of_le_of_ne hcoeff (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := ∑ s, c s ^ 2) _ hpos
    nlinarith [hmain]

end GenericConditioning

/-- The actual word columns: delta at zero and the normalized uniform word. -/
def wordFrame (s : Bool) (x : AES.Word) : ℝ :=
  if s then 1 / 65536 else identityKernel x 0

def wordMetric (s t : Bool) : ℝ := if s = t then 1 else 1 / 65536

/-- The off-diagonal signs are essential; this is the exact inverse metric. -/
def wordInverse (s t : Bool) : ℝ :=
  (4294967296 / 4294967295) * if s = t then 1 else -(1 / 65536)

theorem wordMetric_symmetric (s t : Bool) : wordMetric s t = wordMetric t s := by
  simp [wordMetric, eq_comm]

theorem wordInverse_symmetric (s t : Bool) : wordInverse s t = wordInverse t s := by
  simp [wordInverse, eq_comm]

theorem word_gram (s t : Bool) :
    (∑ x : AES.Word, wordFrame s x * wordFrame t x) = wordMetric s t := by
  cases s <;> cases t <;>
    simp [wordFrame, wordMetric, identityKernel, BinaryWord.card] <;> norm_num

theorem word_inverse (s t : Bool) :
    (∑ u : Bool, wordMetric s u * wordInverse u t) = if s = t then 1 else 0 := by
  cases s <;> cases t <;> norm_num [wordMetric, wordInverse]

theorem word_projection (x y : AES.Word) :
    activityMatrix 0 x y =
      ∑ s : Bool, ∑ t : Bool, wordFrame s x * wordInverse s t * wordFrame t y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    norm_num [wordFrame, wordInverse, activityMatrix, identityKernel, hx, hy,
      BinaryWord.card]

theorem wordInverse_abs_row (s : Bool) :
    (∑ t : Bool, |wordInverse s t|) = 65536 / 65535 := by
  cases s <;> norm_num [wordInverse]

section TensorFrame

variable {I : Type*} [Fintype I] [DecidableEq I]

def frameColumn (s : I → Bool) (x : I → AES.Word) : ℝ :=
  ∏ i, wordFrame (s i) (x i)

def frameMetric (s t : I → Bool) : ℝ := ∏ i, wordMetric (s i) (t i)
def frameInverse (s t : I → Bool) : ℝ := ∏ i, wordInverse (s i) (t i)

def synthesize (c : (I → Bool) → ℝ) (x : I → AES.Word) : ℝ :=
  ∑ s, frameColumn s x * c s

theorem frameMetric_symmetric (s t : I → Bool) : frameMetric s t = frameMetric t s := by
  unfold frameMetric
  apply Finset.prod_congr rfl
  intro i _
  exact wordMetric_symmetric _ _

theorem frameInverse_symmetric (s t : I → Bool) :
    frameInverse s t = frameInverse t s := by
  unfold frameInverse
  apply Finset.prod_congr rfl
  intro i _
  exact wordInverse_symmetric _ _

theorem frame_gram (s t : I → Bool) :
    (∑ x : I → AES.Word, frameColumn s x * frameColumn t x) = frameMetric s t := by
  unfold frameColumn frameMetric
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => wordFrame (s i) x * wordFrame (t i) x)]
  simp_rw [word_gram]

theorem frame_inverse (s t : I → Bool) :
    (∑ u : I → Bool, frameMetric s u * frameInverse u t) =
      if s = t then 1 else 0 := by
  unfold frameMetric frameInverse
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => wordMetric (s i) u * wordInverse u (t i))]
  simp_rw [word_inverse]
  rw [product_indicator]
  simp only [funext_iff]

/-- Reconstruction of the actual orthogonal activity projection. -/
theorem frame_projection (x y : I → AES.Word) :
    (∏ i, activityMatrix 0 (x i) (y i)) =
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameColumn s x * frameInverse s t * frameColumn t y := by
  simp_rw [word_projection]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [frameColumn, frameInverse, Finset.prod_mul_distrib]

/-- Physical energy is the Gram quadratic, for every signed coefficient array. -/
theorem frame_energy (c : (I → Bool) → ℝ) :
    (∑ x : I → AES.Word, synthesize c x ^ 2) =
      ∑ s : I → Bool, ∑ t : I → Bool, c s * c t * frameMetric s t := by
  unfold synthesize
  rw [gram_quadratic]
  simp only [gram, frame_gram]

/-- Exact inverse row sum, including all negative inverse entries in absolute
value. The formula also holds for an empty coordinate type. -/
theorem frameInverse_abs_row (s : I → Bool) :
    (∑ t : I → Bool, |frameInverse s t|) =
      (65536 / 65535 : ℝ) ^ Fintype.card I := by
  unfold frameInverse
  simp_rw [Finset.abs_prod]
  rw [← Fintype.prod_sum (fun i t => |wordInverse (s i) t|)]
  simp_rw [wordInverse_abs_row]
  simp only [Finset.prod_const, Finset.card_univ]

/-- Coefficient energy is controlled by the actual physical energy; the
conditioning hypothesis is proved by the preceding exact frame algebra. -/
theorem frame_coefficient_energy (c : (I → Bool) → ℝ) :
    (∑ s : I → Bool, c s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ x : I → AES.Word, synthesize c x ^ 2 := by
  apply coefficient_energy_le_of_inverse_gram
    (fun x s => frameColumn s x) frameInverse
    ((65536 / 65535 : ℝ) ^ Fintype.card I) (by positivity)
    frameInverse_symmetric
  · intro s t
    simpa only [gram, frame_gram] using frame_inverse s t
  · intro s
    exact (frameInverse_abs_row s).le

/-- The equivalent lower Gram bound used for activity-frame synthesis. -/
theorem frame_energy_lower (c : (I → Bool) → ℝ) :
    (1 - 1 / 65536 : ℝ) ^ Fintype.card I * (∑ s : I → Bool, c s ^ 2) ≤
      ∑ x : I → AES.Word, synthesize c x ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (frame_coefficient_energy c)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 1 / 65536) (Fintype.card I))
  have hcancel : (1 - 1 / 65536 : ℝ) ^ Fintype.card I *
      (65536 / 65535 : ℝ) ^ Fintype.card I = 1 := by
    rw [← mul_pow]
    norm_num
  simpa only [← mul_assoc, hcancel, one_mul] using h

/-- Residual coordinates may remain as an arbitrary additional finite index.
No factorization of the jointly indexed coefficient array is required. -/
theorem frame_coefficient_family_energy {Y : Type*} [Fintype Y]
    (c : Y → (I → Bool) → ℝ) :
    (∑ y, ∑ s : I → Bool, c y s ^ 2) ≤
      (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ y, ∑ x : I → AES.Word, synthesize (c y) x ^ 2 := by
  calc
    _ ≤ ∑ y, (65536 / 65535 : ℝ) ^ Fintype.card I *
        ∑ x : I → AES.Word, synthesize (c y) x ^ 2 :=
      Finset.sum_le_sum (fun y _ => frame_coefficient_energy (c y))
    _ = _ := (Finset.mul_sum _ _ _).symm

end TensorFrame

/-- Square-root form of the exact inverse norm factor. -/
def conditioningFactor (n : ℕ) : ℝ := ((Real.sqrt (1 - 1 / 65536 : ℝ))⁻¹) ^ n

theorem conditioningFactor_nonneg (n : ℕ) : 0 ≤ conditioningFactor n := by
  unfold conditioningFactor
  positivity

theorem conditioningFactor_sq (n : ℕ) :
    conditioningFactor n ^ 2 = (65536 / 65535 : ℝ) ^ n := by
  unfold conditioningFactor
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - 1 / 65536)]
  norm_num

/-- The factor is exactly the paper's `(1-q^(-1/2))^(-n/2)`. -/
theorem conditioningFactor_eq_rpow (n : ℕ) :
    conditioningFactor n = (1 - 1 / 65536 : ℝ) ^ (-(n : ℝ) / 2) := by
  rw [Real.rpow_div_two_eq_sqrt (-(n : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 - 1 / 65536),
    Real.rpow_neg (Real.sqrt_nonneg _) (n : ℝ), Real.rpow_natCast]
  exact inv_pow _ _

/-- Conditioning on the image of the actual word synthesis map, in the
counting-measure norm used throughout the project. -/
theorem frame_coefficient_norm {I : Type*} [Fintype I] [DecidableEq I]
    (c : (I → Bool) → ℝ) :
    l2 c ≤ (1 - 1 / 65536 : ℝ) ^ (-(Fintype.card I : ℝ) / 2) *
      l2 (synthesize c) := by
  rw [← conditioningFactor_eq_rpow]
  apply l2_le_of_energy c (synthesize c) (conditioningFactor (Fintype.card I))
    (conditioningFactor_nonneg _)
  rw [conditioningFactor_sq]
  exact frame_coefficient_energy c

/-- A change to the outer word alphabet is reflected in the normalized
activity-column denominator. -/
theorem wordFrame_basis (s : Bool) (x : AES.Word) :
    wordFrame s x = activityBasisFactor s x / (if s then 65536 else 1) := by
  cases s <;> simp [wordFrame, activityBasisFactor]

theorem frameColumn_activity (a : Fin 16) (x : Fin 4 → AES.Word) :
    frameColumn (maskBit a) x = activityColumn a x / (65536 : ℝ) ^ maskSize a := by
  unfold frameColumn
  simp_rw [wordFrame_basis]
  rw [Finset.prod_div_distrib, activity_basis_product]
  congr 1
  simp [Finset.prod_ite, maskSize]

/-- The actual four-word degree-zero projector is reconstructed by this frame. -/
theorem degree_zero_projection (x y : Fin 4 → AES.Word) :
    degreeKernel 0 0 x y = ∑ s : Fin 4 → Bool, ∑ t : Fin 4 → Bool,
      frameColumn s x * frameInverse s t * frameColumn t y := by
  rw [degreeKernel_zero]
  change (∏ i, activityMatrix 0 (x i) (y i)) = _
  exact frame_projection x y

end AESPaper.WordActivityFrame
