/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ProjectedReturn

/-!
# Literal domains after the outside projections

Each middle frame branch has its own actual left and right constraint domain.
The input remains the full signed joint coefficient of its outside projection.
No normalization, independence, or operator estimate is introduced.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace AES8.ProjectedGraph
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection
open AES8.ProjectedReturn
open AES8.PhysicalZeroPattern (channelTail frameReturnKernel fourReturnKernel)
open AES8.PhysicalMiddleKernel (channelFrameAtom)
open AES8.WordActivityFrame (wordFrame xi)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

def frameCondition (s : Bool) (u : AES.Word) : Prop := s = true ∨ u = 0
instance (s : Bool) (u : AES.Word) : Decidable (frameCondition s u) := by
  unfold frameCondition
  infer_instance

def frameScalar (s : Bool) : ℝ := if s then xi AES.Word else 1

theorem wordFrame_condition (s : Bool) (u : AES.Word) :
    wordFrame 0 s u = if frameCondition s u then frameScalar s else 0 := by
  cases s <;> by_cases hu : u = 0 <;>
    simp [wordFrame, frameCondition, frameScalar, identityKernel, hu]

theorem channelFrameAtom_factor (c : Fin 4) (s t : Bool) (v w : WordState) :
    channelFrameAtom wordSuperboxKernel 0 c s t v w =
      wordFrame 0 s (v c) * channelTail wordSuperboxKernel 0 c v w *
        wordFrame 0 t (w c) := by
  fin_cases c <;>
    simp [channelFrameAtom, channelTail, coordinateKernel,
      PhysicalMiddleKernel.framePair, Fin.prod_univ_four] <;> ring

def LeftConstraint (r c : Fin 4) (s : Bool) (v : WordState) : Prop :=
  wordMixAddEquiv v r = 0 ∧ frameCondition s (v c)
def RightConstraint (c z : Fin 4) (t : Bool) (x : WordState) : Prop :=
  x z = 0 ∧ frameCondition t (wordMixAddEquiv x c)
instance (r c : Fin 4) (s : Bool) (v : WordState) : Decidable (LeftConstraint r c s v) := by
  unfold LeftConstraint
  infer_instance
instance (c z : Fin 4) (t : Bool) (x : WordState) : Decidable (RightConstraint c z t x) := by
  unfold RightConstraint
  infer_instance

abbrev LeftDomain (r c : Fin 4) (s : Bool) := {v : WordState // LeftConstraint r c s v}
abbrev RightDomain (c z : Fin 4) (t : Bool) := {x : WordState // RightConstraint c z t x}

def inputCoefficient (z : Fin 4) (f : WordState → ℝ) (x : WordState) : ℝ :=
  markedResidual (outsideMask z) (extractZero z f) (fun i => x i.val)

theorem Q_apply (z : Fin 4) (f : WordState → ℝ) (x : WordState) :
    Q z f x = if x z = 0 then inputCoefficient z f x else 0 := by
  rw [Q_eq_embed_residual_extract, embedZero_apply]
  rfl

private theorem frame_integrand (r c z : Fin 4) (s t : Bool)
    (f : WordState → ℝ) (y v x : WordState) :
    projectedChannel wordSuperboxKernel r y (wordMixAddEquiv v) *
      (channelFrameAtom wordSuperboxKernel 0 c s t v (wordMixAddEquiv x) * Q z f x) =
      if y r = 0 then
        (if LeftConstraint r c s v then (1 : ℝ) else 0) *
        ((if RightConstraint c z t x then (1 : ℝ) else 0) *
          (frameScalar s * frameScalar t *
            channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v) *
            channelTail wordSuperboxKernel 0 c v (wordMixAddEquiv x) *
            inputCoefficient z f x)) else 0 := by
  rw [projectedChannel_entry, channelFrameAtom_factor, Q_apply]
  simp only [wordFrame_condition, LeftConstraint, RightConstraint]
  split_ifs <;> simp_all <;> ring

/-- Exact actual domains for all four frame branches, with the shared input. -/
theorem projected_frame_action (r c z : Fin 4) (s t : Bool) (f : WordState → ℝ)
    (y : WordState) :
    Q r (action (frameReturnKernel c s t) (Q z f)) y =
      if y r = 0 then frameScalar s * frameScalar t *
        ∑ v : LeftDomain r c s,
          channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v.val) *
            ∑ x : RightDomain c z t,
              channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) *
                inputCoefficient z f x.val
      else 0 := by
  rw [projected_frame_integral]
  simp only [Finset.mul_sum]
  simp_rw [frame_integrand]
  by_cases hy : y r = 0
  · simp only [hy, if_true]
    simp_rw [← Finset.mul_sum]
    rw [indicator_weight_subtype]
    simp_rw [indicator_weight_subtype]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp [hy]


abbrev LeftHyperplane (r : Fin 4) := {v : WordState // wordMixAddEquiv v r = 0}
abbrev RightHyperplane (z : Fin 4) := {x : WordState // x z = 0}

private theorem four_integrand (r z : Fin 4) (f : WordState → ℝ)
    (y v x : WordState) :
    projectedChannel wordSuperboxKernel r y (wordMixAddEquiv v) *
      (AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x) * Q z f x) =
      if y r = 0 then
        (if wordMixAddEquiv v r = 0 then (1 : ℝ) else 0) *
        ((if x z = 0 then (1 : ℝ) else 0) *
          (channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v) *
            AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x) *
            inputCoefficient z f x)) else 0 := by
  rw [projectedChannel_entry, Q_apply]
  split_ifs <;> simp_all <;> ring

/-- Four middle residuals retain their two distinct three-dimensional domains. -/
theorem projected_four_action (r z : Fin 4) (f : WordState → ℝ) (y : WordState) :
    Q r (action fourReturnKernel (Q z f)) y =
      if y r = 0 then
        ∑ v : LeftHyperplane r,
          channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v.val) *
            ∑ x : RightHyperplane z,
              AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) *
                inputCoefficient z f x.val
      else 0 := by
  rw [projected_four_integral]
  simp only [Finset.mul_sum]
  simp_rw [four_integrand]
  by_cases hy : y r = 0
  · simp only [hy, if_true]
    simp_rw [← Finset.mul_sum]
    rw [indicator_weight_subtype]
    simp_rw [indicator_weight_subtype]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp [hy]

end AES8.ProjectedGraph
