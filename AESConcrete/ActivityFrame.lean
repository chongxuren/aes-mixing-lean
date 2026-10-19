import AESMixing.ActivitySpan

/-!
# Normalized activity frame and its actual projection

The two byte columns are delta at zero and the constant 1/16. They are
normalized but not orthogonal. The inverse metric, including its negative
cross term, is needed when contracting an output activity coordinate.
Constructive mathematics only; no attacks or manuscript changes.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityFrame
open AESMixing AESMixing.AES

variable {V : Type*} [Zero V] [DecidableEq V]

def byteFrame (s : Bool) (x : V) : ℝ :=
  if s then 1 / 16 else identityKernel x 0

def byteMetric (s t : Bool) : ℝ := if s = t then 1 else 1 / 16

def byteInverse (s t : Bool) : ℝ :=
  (256 / 255) * if s = t then 1 else -(1 / 16)

theorem byteMetric_symmetric (s t : Bool) : byteMetric s t = byteMetric t s := by
  simp [byteMetric, eq_comm]

theorem byteInverse_symmetric (s t : Bool) : byteInverse s t = byteInverse t s := by
  simp [byteInverse, eq_comm]

theorem byte_inverse (s t : Bool) :
    (∑ u : Bool, byteMetric s u * byteInverse u t) = if s = t then 1 else 0 := by
  cases s <;> cases t <;> norm_num [byteMetric, byteInverse]

variable [Fintype V]

theorem byte_gram (hV : Fintype.card V = 256) (s t : Bool) :
    (∑ x : V, byteFrame s x * byteFrame t x) = byteMetric s t := by
  cases s <;> cases t <;> simp [byteFrame, byteMetric, identityKernel, hV]
  <;> norm_num

theorem byte_projection (hV : Fintype.card V = 256) (x y : V) :
    activityMatrix 0 x y =
      ∑ s : Bool, ∑ t : Bool, byteFrame s x * byteInverse s t * byteFrame t y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    norm_num [byteFrame, byteInverse, activityMatrix, identityKernel, hx, hy, hV]

variable {I : Type*} [Fintype I] [DecidableEq I]

def frameColumn (s : I → Bool) (x : I → V) : ℝ := ∏ i, byteFrame (s i) (x i)
def frameMetric (s t : I → Bool) : ℝ := ∏ i, byteMetric (s i) (t i)
def frameInverse (s t : I → Bool) : ℝ := ∏ i, byteInverse (s i) (t i)

theorem frame_gram (hV : Fintype.card V = 256) (s t : I → Bool) :
    (∑ x : I → V, frameColumn s x * frameColumn t x) = frameMetric s t := by
  unfold frameColumn frameMetric
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => byteFrame (s i) x * byteFrame (t i) x)]
  simp_rw [byte_gram hV]

theorem frame_inverse (s t : I → Bool) :
    (∑ u : I → Bool, frameMetric s u * frameInverse u t) = if s = t then 1 else 0 := by
  unfold frameMetric frameInverse
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => byteMetric (s i) u * byteInverse u (t i))]
  simp_rw [byte_inverse]
  rw [product_indicator]
  simp only [funext_iff]

/-- Tensor reconstruction of the actual activity projection. -/
theorem frame_projection (hV : Fintype.card V = 256) (x y : I → V) :
    (∏ i, activityMatrix 0 (x i) (y i)) =
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameColumn s x * frameInverse s t * frameColumn t y := by
  simp_rw [byte_projection hV]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [frameColumn, frameInverse, Finset.prod_mul_distrib]

/-- The domain norm is the frame metric quadratic, not the coefficient norm. -/
theorem frame_energy (hV : Fintype.card V = 256) (c : (I → Bool) → ℝ) :
    (∑ x : I → V, (∑ s : I → Bool, frameColumn s x * c s)^2) =
      ∑ s : I → Bool, ∑ t : I → Bool, c s * c t * frameMetric s t := by
  rw [gram_quadratic]
  simp only [gram, frame_gram hV]

omit [Fintype V] in
theorem byteFrame_basis (s : Bool) (x : V) :
    byteFrame s x = activityBasisFactor s x / (if s then 16 else 1) := by
  cases s <;> simp [byteFrame, activityBasisFactor]

theorem frameColumn_activity (a : Fin 16) (x : Fin 4 → V) :
    frameColumn (maskBit a) x = activityColumn a x / (16 : ℝ)^maskSize a := by
  unfold frameColumn
  simp_rw [byteFrame_basis]
  rw [Finset.prod_div_distrib, activity_basis_product]
  congr 1
  simp [Finset.prod_ite, maskSize]

/-- The four-byte degree-zero kernel uses the same normalized frame. -/
theorem degree_zero_projection (hV : Fintype.card V = 256) (x y : Fin 4 → V) :
    degreeKernel 0 0 x y = ∑ s : Fin 4 → Bool, ∑ t : Fin 4 → Bool,
      frameColumn s x * frameInverse s t * frameColumn t y := by
  rw [degreeKernel_zero]
  change (∏ i, activityMatrix 0 (x i) (y i)) = _
  exact frame_projection hV x y

end AESConcrete.ActivityFrame
