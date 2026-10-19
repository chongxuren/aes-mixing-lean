import AESPaper.PositionAggregation
import AESPaper.ResidualRounding

/-!
# Actual degree-to-degree residual sandwich bounds
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordDegreeResidual
open AESMixing AESConcrete
open AESPaper.ProfileSpace
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)

/-- Actual physical output count for a pair of residual masks. -/
theorem output_marked_card (a b : Fin 4 → Bool) :
    Fintype.card (OutputMarked (Sum.elim a b)) = residualDegree a := by
  classical
  simp [OutputMarked, residualDegree, Fintype.card_subtype]

/-- Actual physical input count for a pair of residual masks. -/
theorem input_marked_card (a b : Fin 4 → Bool) :
    Fintype.card (InputMarked (Sum.elim a b)) = residualDegree b := by
  classical
  simp [InputMarked, residualDegree, Fintype.card_subtype]

/-- The position aggregation applies to the actual Hilbert-space sandwich.
There is no centering, positivity, or product-input hypothesis. -/
theorem sandwich_degree_norm (i j : Fin 5) (c : ℝ) (hc : 0 ≤ c)
    (hblocks : ∀ (a b : Fin 4 → Bool), residualDegree a = i.val →
      residualDegree b = j.val → EnergyBound (WordGraphKernel.markedKernel a b) c)
    (f : ProfileSpace.State) :
    ‖component i (BoundaryContraction.sandwich (component j f))‖ ≤
      (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c) *
        ‖component j f‖ := by
  have hb : ∀ (a b : Fin 4 → Bool), residualDegree a = i.val →
      residualDegree b = j.val →
      EnergyBound (kernelCompose (productProjection (0 : AES.Word) a)
        (kernelCompose WordGraphKernel.sandwichKernel
          (productProjection (0 : AES.Word) b))) c := hblocks
  have h := PositionAggregation.degree_norm (0 : AES.Word) word_card_gt_one
    WordGraphKernel.sandwichKernel i j c hc hb (fun x => f x)
  have hin : (fun x => component j f x) =
      degreeComponent (0 : AES.Word) j (fun x => f x) :=
    funext (fun x => component_apply j f x)
  have hs : (fun x => BoundaryContraction.sandwich (component j f) x) =
      action WordGraphKernel.sandwichKernel
        (degreeComponent (0 : AES.Word) j (fun x => f x)) :=
    (funext (fun x => WordGraphKernel.sandwich_eq_action (component j f) x)).trans
      (congrArg (action WordGraphKernel.sandwichKernel) hin)
  have hout : (fun x => component i (BoundaryContraction.sandwich (component j f)) x) =
      degreeComponent (0 : AES.Word) i
        (action WordGraphKernel.sandwichKernel
          (degreeComponent (0 : AES.Word) j (fun x => f x))) :=
    (funext (fun x => component_apply i (BoundaryContraction.sandwich (component j f)) x)).trans
      (congrArg (degreeComponent (0 : AES.Word) i) hs)
  rw [← hout, ← hin, l2_eq_norm, l2_eq_norm] at h
  exact h

/-- Connect a physical fixed-position estimate and an independently proved
scalar rounding inequality to the actual degree block. -/
theorem sandwich_of_rounding (i j : Fin 5) (raw cap : ℝ) (hr : 0 ≤ raw)
    (hcap : ResidualRounding.coefficient i.val j.val raw ≤ cap)
    (hblocks : ∀ m : GraphPosition → Bool,
      Fintype.card (OutputMarked m) = i.val →
      Fintype.card (InputMarked m) = j.val →
      EnergyBound (WordGraphKernel.markedKernel
        (fun k => m (Sum.inl k)) (fun k => m (Sum.inr k)))
        ((WordActivityFrame.conditioningFactor (4-i.val) *
          WordActivityFrame.conditioningFactor (4-j.val)) * raw))
    (f : ProfileSpace.State) :
    ‖component i (BoundaryContraction.sandwich (component j f))‖ ≤
      cap * ‖component j f‖ := by
  have hc := mul_nonneg
    (mul_nonneg (WordActivityFrame.conditioningFactor_nonneg (4-i.val))
      (WordActivityFrame.conditioningFactor_nonneg (4-j.val))) hr
  have h := sandwich_degree_norm i j _ hc (by
    intro a b ha hb
    exact hblocks (Sum.elim a b)
      ((output_marked_card a b).trans ha) ((input_marked_card a b).trans hb)) f
  exact h.trans (mul_le_mul_of_nonneg_right hcap (norm_nonneg _))

-- Concrete Fin values must be simplified before matching the natural frame dimensions.
/-- Printed S11 cap for the actual degree-1 output and degree-1 input. -/
theorem sandwich_S11 (f : ProfileSpace.State) :
    ‖component 1 (BoundaryContraction.sandwich (component 1 f))‖ ≤
      (Assembly.S 0 0 / Assembly.q ^ 2) * ‖component 1 f‖ := by
  apply sandwich_of_rounding 1 1 ResidualRounding.raw11 _
    ResidualRounding.raw11_nonnegative ResidualRounding.round11 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw11] using WordResidualOneOne.markedKernel_bound m hO hI

/-- Printed S12 cap for the actual degree-1 output and degree-2 input. -/
theorem sandwich_S12 (f : ProfileSpace.State) :
    ‖component 1 (BoundaryContraction.sandwich (component 2 f))‖ ≤
      (Assembly.S 0 1 / Assembly.q ^ 2) * ‖component 2 f‖ := by
  apply sandwich_of_rounding 1 2 ResidualRounding.raw12 _
    ResidualRounding.raw12_nonnegative ResidualRounding.round12 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw12] using WordResidualOneTwo.markedKernel_bound m hO hI

/-- Printed S13 cap for the actual degree-1 output and degree-3 input. -/
theorem sandwich_S13 (f : ProfileSpace.State) :
    ‖component 1 (BoundaryContraction.sandwich (component 3 f))‖ ≤
      (Assembly.S 0 2 / Assembly.q ^ 2) * ‖component 3 f‖ := by
  apply sandwich_of_rounding 1 3 ResidualRounding.raw13 _
    ResidualRounding.raw13_nonnegative ResidualRounding.round13 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw13] using WordResidualFour.markedKernel_bound13 m hO hI

/-- Printed S22 cap for the actual degree-2 output and degree-2 input. -/
theorem sandwich_S22 (f : ProfileSpace.State) :
    ‖component 2 (BoundaryContraction.sandwich (component 2 f))‖ ≤
      (Assembly.S 1 1 / Assembly.q ^ 2) * ‖component 2 f‖ := by
  apply sandwich_of_rounding 2 2 ResidualRounding.raw22 _
    ResidualRounding.raw22_nonnegative ResidualRounding.round22 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw22] using WordResidualFour.markedKernel_bound22 m hO hI

/-- Printed S14 cap for the actual degree-1 output and degree-4 input. -/
theorem sandwich_S14 (f : ProfileSpace.State) :
    ‖component 1 (BoundaryContraction.sandwich (component 4 f))‖ ≤
      (Assembly.S 0 3 / Assembly.q ^ 2) * ‖component 4 f‖ := by
  apply sandwich_of_rounding 1 4 ResidualRounding.raw14 _
    ResidualRounding.raw14_nonnegative ResidualRounding.round14 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw14] using WordResidualFiveSix.markedKernel_one_four_bound m hO hI

/-- Printed S23 cap for the actual degree-2 output and degree-3 input. -/
theorem sandwich_S23 (f : ProfileSpace.State) :
    ‖component 2 (BoundaryContraction.sandwich (component 3 f))‖ ≤
      (Assembly.S 1 2 / Assembly.q ^ 2) * ‖component 3 f‖ := by
  apply sandwich_of_rounding 2 3 ResidualRounding.raw23 _
    ResidualRounding.raw23_nonnegative ResidualRounding.round23 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw23] using WordResidualFiveSix.markedKernel_two_three_bound m hO hI

/-- Printed S24 cap for the actual degree-2 output and degree-4 input. -/
theorem sandwich_S24 (f : ProfileSpace.State) :
    ‖component 2 (BoundaryContraction.sandwich (component 4 f))‖ ≤
      (Assembly.S 1 3 / Assembly.q ^ 2) * ‖component 4 f‖ := by
  apply sandwich_of_rounding 2 4 ResidualRounding.raw24 _
    ResidualRounding.raw24_nonnegative ResidualRounding.round24 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw24] using WordResidualFiveSix.markedKernel_two_four_bound m hO hI

/-- Printed S33 cap for the actual degree-3 output and degree-3 input. -/
theorem sandwich_S33 (f : ProfileSpace.State) :
    ‖component 3 (BoundaryContraction.sandwich (component 3 f))‖ ≤
      (Assembly.S 2 2 / Assembly.q ^ 2) * ‖component 3 f‖ := by
  apply sandwich_of_rounding 3 3 ResidualRounding.raw33 _
    ResidualRounding.raw33_nonnegative ResidualRounding.round33 ?_ f
  intro m hO hI
  simpa [ResidualRounding.raw33] using WordResidualFiveSix.markedKernel_three_three_bound m hO hI

end AESPaper.WordDegreeResidual
