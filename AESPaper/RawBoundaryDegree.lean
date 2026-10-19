import AESPaper.RawBoundaryKernel
import AESPaper.WordDegreeResidual

/-!
# Position aggregation for the actual raw boundary
-/

set_option autoImplicit false
set_option maxRecDepth 1000
set_option maxHeartbeats 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryDegree
open AESMixing AESConcrete
open AESPaper.ProfileSpace
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordDegreeResidual (output_marked_card input_marked_card)

/-- Keep K and T as opaque local parameters throughout the aggregation and
norm transport. This avoids kernel reduction of the concrete AES boundary
while checking the complete proof; hT is only an exact action interface. -/
theorem generic_degree_norm
    (K : AES.WordState → AES.WordState → ℝ)
    (T : ProfileSpace.State → ProfileSpace.State)
    (hT : ∀ (g : ProfileSpace.State) (x : AES.WordState),
      T g x = action K (fun y => g y) x)
    (i j : Fin 5) (c : ℝ) (hc : 0 ≤ c)
    (hblocks : ∀ (a b : Fin 4 → Bool), residualDegree a = i.val →
      residualDegree b = j.val →
      EnergyBound (kernelCompose (productProjection (0 : AES.Word) a)
        (kernelCompose K (productProjection (0 : AES.Word) b))) c)
    (f : ProfileSpace.State) :
    ‖component i (T (component j f))‖ ≤
      (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c) *
        ‖component j f‖ := by
  have h := PositionAggregation.degree_norm (0 : AES.Word) word_card_gt_one
    K i j c hc hblocks (fun x => f x)
  have hin : (fun x => component j f x) =
      degreeComponent (0 : AES.Word) j (fun x => f x) :=
    funext (fun x => component_apply j f x)
  have hs : (fun x => T (component j f) x) =
      action K (degreeComponent (0 : AES.Word) j (fun x => f x)) :=
    (funext (fun x => hT (component j f) x)).trans (congrArg (action K) hin)
  have hout : (fun x => component i (T (component j f)) x) =
      degreeComponent (0 : AES.Word) i
        (action K (degreeComponent (0 : AES.Word) j (fun x => f x))) :=
    (funext (fun x => component_apply i (T (component j f)) x)).trans
      (congrArg (degreeComponent (0 : AES.Word) i) hs)
  -- Scalar transport does not rewrite inside a state-valued function.
  have hoNorm : l2 (degreeComponent (0 : AES.Word) i
      (action K (degreeComponent (0 : AES.Word) j (fun x => f x)))) =
      ‖component i (T (component j f))‖ :=
    (congrArg (fun g : AES.WordState → ℝ => l2 g) hout.symm).trans
      (l2_eq_norm (component i (T (component j f))))
  have hiNorm : l2 (degreeComponent (0 : AES.Word) j (fun x => f x)) = ‖component j f‖ :=
    (congrArg (fun g : AES.WordState → ℝ => l2 g) hin.symm).trans
      (l2_eq_norm (component j f))
  calc
    _ = l2 (degreeComponent (0 : AES.Word) i
        (action K (degreeComponent (0 : AES.Word) j (fun x => f x)))) := hoNorm.symm
    _ ≤ _ := h
    _ = _ := congrArg (fun z : ℝ =>
      (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c) * z) hiNorm

/-- The position aggregation applies to the actual raw boundary operator.
There is no centering, positivity, or product-input hypothesis. -/
theorem boundary_degree_norm (i j : Fin 5) (c : ℝ) (hc : 0 ≤ c)
    (hblocks : ∀ (a b : Fin 4 → Bool), residualDegree a = i.val →
      residualDegree b = j.val → EnergyBound (RawBoundaryKernel.markedKernel a b) c)
    (f : ProfileSpace.State) :
    ‖component i (BoundaryContraction.boundaryLayer (component j f))‖ ≤
      (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c) *
        ‖component j f‖ := by
  apply generic_degree_norm RawBoundaryKernel.rawKernel BoundaryContraction.boundaryLayer
    RawBoundaryKernel.boundaryLayer_eq_action i j c hc ?_ f
  -- Unfold only the position-block wrapper, keeping rawKernel opaque.
  simpa only [RawBoundaryKernel.markedKernel] using hblocks

/-- Connect a physical fixed-position estimate and an independently proved
scalar rounding inequality to the actual degree block. -/
theorem boundary_of_rounding (i j : Fin 5) (raw cap : ℝ) (hr : 0 ≤ raw)
    (hcap : ResidualRounding.coefficient i.val j.val raw ≤ cap)
    (hblocks : ∀ m : GraphPosition → Bool,
      Fintype.card (OutputMarked m) = i.val →
      Fintype.card (InputMarked m) = j.val →
      EnergyBound (RawBoundaryKernel.markedKernel
        (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
        ((WordActivityFrame.conditioningFactor (4-i.val) *
          WordActivityFrame.conditioningFactor (4-j.val)) * raw))
    (f : ProfileSpace.State) :
    ‖component i (BoundaryContraction.boundaryLayer (component j f))‖ ≤
      cap * ‖component j f‖ := by
  have hc := mul_nonneg
    (mul_nonneg (WordActivityFrame.conditioningFactor_nonneg (4-i.val))
      (WordActivityFrame.conditioningFactor_nonneg (4-j.val))) hr
  have h := boundary_degree_norm i j _ hc (by
    intro a b ha hb
    exact hblocks (Sum.elim a b)
      ((output_marked_card a b).trans ha) ((input_marked_card a b).trans hb)) f
  exact h.trans (mul_le_mul_of_nonneg_right hcap (norm_nonneg _))

-- Concrete Fin values must be simplified before matching the natural frame dimensions.
end AESPaper.RawBoundaryDegree
