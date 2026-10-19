import AESConcrete.ActivityGraphContraction
import AESConcrete.ShortenedPlaneResponse

/-!
# Actual plane contractions and low-activity vanishing

Activity weight three produces exactly the actual two-zero plane response,
with divisor 4096. Activity weights zero and one vanish because four or
more physical graph zeros force the graph point to zero. These identities
concern the checked graph-response kernel; full centered-word identification
and the four-triple operator assembly remain separate obligations.
Constructive proof work only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityPlaneContraction
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityFrameContraction
open AESConcrete.ActivityGraphContraction
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ShortenedPlane
open AESConcrete.ShortenedPlaneResponse
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteLineBounds (leg residual)

set_option maxRecDepth 65536

/-- A complementary physical output coordinate gives the required disjointness. -/
theorem output_mask_disjoint (out : Fin 16) (r : Fin 4)
    (hr : maskBit out r ≠ true) (b : Bool) :
    MaskDisjoint (outputZeroMask r b) out := by
  cases b
  · intro i hi ho
    have hir := (singletonMask_bit r i).mp hi
    subst i
    exact hr ho
  · intro i hi _
    exact Bool.false_ne_true ((empty_mask_bit i).symm.trans hi)

/-- The plane shortening is derived from the actual activity labels. -/
def activityPlaneChoice (out a : Fin 16) (r : Fin 4) (b : Bool)
    (hdisj : MaskDisjoint (outputZeroMask r b) out)
    (hweight : maskSize a + (if b then 1 else 0) = 3) : ShorteningChoice out 2 :=
  ⟨(outputZeroMask r b, inputZeroMask a), hdisj, by
    change maskSize (outputZeroMask r b) + maskSize (inputZeroMask a) = 2
    have h := constraint_balance a r b
    omega⟩

/-- Injectivity of the actual plane projection removes no multiplicity factor. -/
theorem normalized_plane_eq_shortened (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedPlaneResponse inverse e p T y =
      shortenedResponse (byteDiffusionHom inverse) p.val.1 p.val.2
        (markedPositions e) T y / 4096 := by
  have hinj : Function.Injective
      (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)) := by
    intro x z hxz
    have h : (⟨x.val, x.property⟩ : graphSubgroup inverse p.val.1 p.val.2) =
        ⟨z.val, z.property⟩ := projection_injective inverse out hout e p hxz
    exact Subtype.ext (congrArg Subtype.val h)
  unfold normalizedPlaneResponse
  rw [action_codeIndicator _ _ hinj]
  rfl

/-- Weight-three graph contractions are actual plane responses, pointwise. -/
theorem plane_contraction_of_weight (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hdisj : MaskDisjoint (outputZeroMask r b) out)
    (hweight : maskSize a + (if b then 1 else 0) = 3)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    contraction (graphResponse (byteDiffusionHom inverse) a r (markedPositions e) T y) b =
      normalizedPlaneResponse inverse e (activityPlaneChoice out a r b hdisj hweight) T y := by
  rw [graphResponse_contraction (by norm_num [BinaryWord.card]),
    normalized_plane_eq_shortened inverse out hout e]
  simp only [activityPlaneChoice, hweight]
  norm_num

theorem actual_plane_contraction_energy (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hdisj : MaskDisjoint (outputZeroMask r b) out)
    (hweight : maskSize a + (if b then 1 else 0) = 3) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      contraction (graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
        (fun i => leg (o i) false) y) b ^ 2) ≤ ByteLineBounds.a3 := by
  simp_rw [plane_contraction_of_weight inverse out hout e a r b hdisj hweight]
  exact actual_shortened_plane_energy_bound inverse out hout e _ o

section Vanishing
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Four graph zeros leave only the zero word, killed by any zero column. -/
theorem shortened_response_high_zeros (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) (hsize : 4 ≤ maskSize r + maskSize z)
    (marked : Fin 3 → GraphPosition) (T : Fin 3 → V → V → ℝ)
    (hzero : ∀ y, T 0 y 0 = 0) (y : Fin 3 → V) :
    shortenedResponse L r z marked T y = 0 := by
  unfold shortenedResponse
  apply Finset.sum_eq_zero
  intro x _
  have hx := mds_graph_zero_high L hL r z hsize x.val x.property
  have hcoord : markedGraph L r z marked x 0 = 0 := by
    unfold markedGraph
    rw [hx]
    cases marked 0 <;> simp [graphCoordinate]
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
  rw [hcoord, hzero]

theorem low_weight_contraction_zero (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hweight : maskSize a + (if b then 1 else 0) ≤ 1)
    (marked : Fin 3 → GraphPosition) (T : Fin 3 → V → V → ℝ)
    (hzero : ∀ y, T 0 y 0 = 0) (y : Fin 3 → V) :
    contraction (graphResponse L a r marked T y) b = 0 := by
  rw [graphResponse_contraction hV,
    shortened_response_high_zeros L hL _ _
      (by have hc := constraint_balance a r b; omega) marked T hzero, zero_div]

end Vanishing

/-- Both actual ordinary and input-Fourier residual legs kill the zero column. -/
theorem leg_zero_column (o : Orientation) (s : Bool) (y : Byte) : leg o s y 0 = 0 := by
  cases s
  · exact ByteGramDiagonal.residual_zero_column (channel_resources o) y
  · change (∑ x : Byte, residual o y x * byteFourierMatrix x 0) = 0
    simp only [byteFourierMatrix, mul_zero, byteCharacter_zero, mul_one_div]
    rw [← Finset.sum_div]
    change (∑ x : Byte, residualMatrix (channel o) 0 y x) / 16 = 0
    rw [ByteGramDiagonal.residual_row_sum (channel_resources o), zero_div]

theorem actual_low_weight_contraction_zero (inverse : Bool)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hweight : maskSize a + (if b then 1 else 0) ≤ 1)
    (marked : Fin 3 → GraphPosition) (o : Fin 3 → Orientation)
    (s : Fin 3 → Bool) (y : Fin 3 → Byte) :
    contraction (graphResponse (byteDiffusionHom inverse) a r marked
      (fun i => leg (o i) (s i)) y) b = 0 :=
  low_weight_contraction_zero (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) a r b hweight marked
    (fun i => leg (o i) (s i)) (fun y => leg_zero_column (o 0) (s 0) y) y

end AESConcrete.ActivityPlaneContraction
