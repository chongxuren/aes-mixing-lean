import AESConcrete.ActivityFrameContraction
import AESConcrete.ShortenedLineResponse
import AESMixing.PointedProducts

/-!
# Activity contractions are normalized shortened-graph sums

This is an exact kernel identity, with the input support mask complemented
and the last output zero constraint present precisely for the delta frame
choice. It identifies the /256 line normalization. Identification of this
kernel expression with the full centered degree-three word block is separate.
Constructive mathematics only; no attacks or manuscript changes.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityGraphContraction
open AESMixing AESMixing.AES
open AESConcrete.ActivityFrame AESConcrete.ActivityFrameContraction
open AESConcrete.ShortenedLineResponse

/-- The input support uses unrestricted coordinates, including zero. -/
def inputZeroMask (a : Fin 16) : Fin 16 :=
  maskComplement a

def outputZeroMask (r : Fin 4) (b : Bool) : Fin 16 := if b then 0 else singletonMask r

theorem inputZeroMask_bit (a : Fin 16) (i : Fin 4) :
    maskBit (inputZeroMask a) i = !(maskBit a i) :=
  maskComplement_bit a i

set_option maxRecDepth 100000 in
theorem constraint_balance : ∀ (a : Fin 16) (r : Fin 4) (b : Bool),
    maskSize (outputZeroMask r b) + maskSize (inputZeroMask a) +
      (maskSize a + if b then 1 else 0) = 5 := by decide

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem graph_conditions (L : (Fin 4 → V) →+ (Fin 4 → V))
    (a : Fin 16) (r : Fin 4) (b : Bool) (x : Fin 4 → V) :
    graphZeroConditions L (outputZeroMask r b) (inputZeroMask a) x ↔
      maskProjection a x = x ∧ (b = true ∨ L x r = 0) := by
  have hi : (∀ i, maskBit (inputZeroMask a) i = true → x i = 0) ↔
      maskProjection a x = x := by
    have hb (i : Fin 4) : maskBit (inputZeroMask a) i = true ↔ maskBit a i ≠ true := by
      rw [inputZeroMask_bit]
      cases maskBit a i <;> decide
    simp_rw [hb, maskProjection_fixed_iff]
  cases b
  · change ((∀ i, maskBit (singletonMask r) i = true → L x i = 0) ∧ _) ↔ _
    simp only [singletonMask_bit, forall_eq, Bool.false_eq_true, false_or]
    rw [hi]
    exact and_comm
  · change ((∀ i, maskBit 0 i = true → L x i = 0) ∧ _) ↔ _
    have he : ∀ i : Fin 4, maskBit 0 i ≠ true := by decide
    simpa [he] using hi

theorem frame_weight (L : (Fin 4 → V) →+ (Fin 4 → V))
    (a : Fin 16) (r : Fin 4) (b : Bool) (x : Fin 4 → V) :
    byteFrame b (L x r) * frameColumn (maskBit a) x =
      (if graphZeroConditions L (outputZeroMask r b) (inputZeroMask a) x then 1 else 0) /
        (16 : ℝ)^(maskSize a + if b then 1 else 0) := by
  rw [frameColumn_activity]
  simp only [graph_conditions]
  by_cases hx : maskProjection a x = x <;> by_cases hz : L x r = 0 <;>
    cases b <;> simp [byteFrame, identityKernel, activityColumn, hx, hz, pow_succ] <;> ring

theorem byteFrame_activity (hV : Fintype.card V = 256) (b : Bool) (v : V) :
    (∑ x : V, byteFrame b x * activityMatrix 0 x v) = byteFrame b v := by
  cases b
  · simp only [byteFrame, Bool.false_eq_true, if_false, identityKernel,
      ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [activityMatrix]
  · simp only [byteFrame, if_true, ← Finset.mul_sum]
    rw [(activityMatrix_pointed (0 : V) (by omega)).column_sum]
    ring

/-- The graph response before contracting its one activity output. -/
def graphResponse (L : (Fin 4 → V) →+ (Fin 4 → V)) (a : Fin 16)
    (r : Fin 4) (marked : Fin 3 → GraphPosition) (T : Fin 3 → V → V → ℝ)
    (y : Fin 3 → V) (v : V) : ℝ :=
  ∑ x : Fin 4 → V, (∏ i, T i (y i) (graphCoordinate L x (marked i))) *
    activityMatrix 0 v (L x r) * frameColumn (maskBit a) x

/-- Exact input/output frame contraction as a shortened-graph sum. -/
theorem graphResponse_contraction (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (a : Fin 16)
    (r : Fin 4) (b : Bool) (marked : Fin 3 → GraphPosition)
    (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    contraction (graphResponse L a r marked T y) b =
      shortenedResponse L (outputZeroMask r b) (inputZeroMask a) marked T y /
        (16 : ℝ)^(maskSize a + if b then 1 else 0) := by
  unfold contraction graphResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hp (x : Fin 4 → V) :
      (∑ v : V, byteFrame b v * ((∏ i, T i (y i) (graphCoordinate L x (marked i))) *
        activityMatrix 0 v (L x r) * frameColumn (maskBit a) x)) =
      (byteFrame b (L x r) * frameColumn (maskBit a) x) *
        ∏ i, T i (y i) (graphCoordinate L x (marked i)) := by
    calc
      _ = (∑ v : V, byteFrame b v * activityMatrix 0 v (L x r)) *
        frameColumn (maskBit a) x * ∏ i, T i (y i) (graphCoordinate L x (marked i)) := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          ring
      _ = _ := by rw [byteFrame_activity hV]
  simp_rw [hp, frame_weight, div_mul_eq_mul_div]
  rw [← Finset.sum_div, shortened_graph_weight]
  rfl

/-- The remaining output is already in the actual activity range. -/
theorem graphResponse_activity (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (a : Fin 16)
    (r : Fin 4) (marked : Fin 3 → GraphPosition)
    (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    action (activityMatrix 0) (graphResponse L a r marked T y) =
      graphResponse L a r marked T y := by
  funext v
  unfold action graphResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (∏ i, T i (y i) (graphCoordinate L x (marked i))) *
      kernelCompose (activityMatrix 0) (activityMatrix 0) v (L x r) *
      frameColumn (maskBit a) x := by
        simp only [kernelCompose, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        ring
    _ = _ := by rw [activityMatrix_idempotent (0 : V) (by omega)]

/-- Exact fixed-triple Gram identity before geometric interval estimates.
All correlations in the three marked outputs remain in the inner sum. -/
theorem graphResponse_inner (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (a a' : Fin 16)
    (r : Fin 4) (marked : Fin 3 → GraphPosition)
    (T : Fin 3 → V → V → ℝ) :
    (∑ y : Fin 3 → V, ∑ v : V,
      graphResponse L a r marked T y v * graphResponse L a' r marked T y v) =
      ∑ b : Bool, ∑ c : Bool, byteInverse b c *
        ∑ y : Fin 3 → V,
          (shortenedResponse L (outputZeroMask r b) (inputZeroMask a) marked T y /
            (16 : ℝ)^(maskSize a + if b then 1 else 0)) *
          (shortenedResponse L (outputZeroMask r c) (inputZeroMask a') marked T y /
            (16 : ℝ)^(maskSize a' + if c then 1 else 0)) := by
  have h := projected_tensor_inner hV
    (graphResponse L a r marked T) (graphResponse L a' r marked T)
  simp_rw [graphResponse_activity hV, graphResponse_contraction hV] at h
  exact h

/-- At activity weight two the graph contraction is exactly the source
line response. Its denominator is 256 rather than sqrt(256). -/
theorem line_contraction (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a : Fin 16)
    (r : Fin 4) (b : Bool)
    (hshort : maskSize (outputZeroMask r b) + maskSize (inputZeroMask a) = 3)
    (hweight : maskSize a + (if b then 1 else 0) = 2)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining (outputZeroMask r b) (inputZeroMask a) (marked i))
    (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    contraction (graphResponse L a r marked T y) b =
      DampedLineGram.lineResponse T
        (lineCoordinatePerm L hL _ _ hshort marked hm) y := by
  rw [graphResponse_contraction hV, shortened_response_eq_card_line L hL _ _ hshort marked hm,
    hweight, hV]
  norm_num

/-- The two zero-mask sizes are computed from the activity choices, so the
line-cardinality hypothesis need not be supplied independently. -/
theorem line_contraction_of_weight (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a : Fin 16)
    (r : Fin 4) (b : Bool)
    (hweight : maskSize a + (if b then 1 else 0) = 2)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining (outputZeroMask r b) (inputZeroMask a) (marked i))
    (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    contraction (graphResponse L a r marked T y) b =
      DampedLineGram.lineResponse T
        (lineCoordinatePerm L hL _ _
          (by have hc := constraint_balance a r b; omega) marked hm) y :=
  line_contraction hV L hL a r b _ hweight marked hm T y

/-- Concrete damped energy of every weight-two graph contraction, with
actual forward or inverse AES diffusion and actual byte residual legs. -/
theorem actual_line_contraction_energy (inverse : Bool) (a : Fin 16)
    (r : Fin 4) (b : Bool)
    (hweight : maskSize a + (if b then 1 else 0) = 2)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining (outputZeroMask r b) (inputZeroMask a) (marked i))
    (o : Fin 3 → ByteOrientations.Orientation) (s : Fin 3 → Bool) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → BinaryWord 8,
      contraction (graphResponse (byteDiffusionHom inverse) a r marked
        (fun i => ByteLineBounds.leg (o i) (s i)) y) b ^ 2) ≤ ByteLineBounds.a3 := by
  simp_rw [line_contraction_of_weight (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) a r b hweight marked hm]
  exact ByteLineBounds.actual_line_energy_bound o s _

end AESConcrete.ActivityGraphContraction
