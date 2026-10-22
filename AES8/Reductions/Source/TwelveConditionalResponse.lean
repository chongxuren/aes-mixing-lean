/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ConditionalSourceResponse
import AESConcrete.RefinedChannelCommutation

/-!
# Exact three-residual, constant-nonzero response for actual component twelve

Positive residual degree removes the stationary reference first. Four actual
support labels have inactive mask zero and exactly one unmarked coordinate.
Pointed projection replaces their three marked channels by residuals and
their remaining channel by constantMatrix0. Initial-source conditioning keeps
one original common source in all factors, including the constant factor.
Only the original source product law is factored.  Constructive work only.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwelveConditionalResponse
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)
open AESPaper.StartingWord (wordLaw sourceInput)
open AESPaper.GroupedLaw (groupedLaw error)
open AES8.SupportProfile (component Label raw)
open AES8.ConditionalSourceResponse

def residualMask : Fin 4 → Fin 16 := ![14, 13, 11, 7]
def patternLabel (j : Fin 4) : Label := (residualMask j, 0)

theorem residualMask_bit : ∀ j i : Fin 4,
    maskBit (residualMask j) i = decide (i ≠ j) := by decide

private theorem emptyMask_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide

def SelectedLabel (p : Label) : Prop := maskSize p.1 = 3 ∧ 4 - maskSize p.2 = 4

instance (p : Label) : Decidable (SelectedLabel p) := by
  unfold SelectedLabel
  infer_instance

theorem patternLabel_selected : ∀ j : Fin 4, SelectedLabel (patternLabel j) := by decide

def patternLabelEquiv : Fin 4 ≃ {p : Label // SelectedLabel p} :=
  Equiv.ofBijective (fun j => ⟨patternLabel j, patternLabel_selected j⟩) (by decide)

/-- Exact four-pattern decomposition, valid for arbitrary signed joint f. -/
theorem component_twelve_eq_sum_raw (f : WordState → ℝ) :
    component f (12 : Fin 14) = fun y => ∑ j : Fin 4, raw (patternLabel j) f y := by
  funext y
  rw [SupportProfile.component_eq_support_residual]
  change (∑ p : Label, if SelectedLabel p then raw p f y else 0) = _
  have hs : (∑ p : {p : Label // SelectedLabel p}, raw p.val f y) =
      ∑ p : Label, if SelectedLabel p then raw p f y else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs]
  exact (patternLabelEquiv.sum_comp (fun p => raw p.val f y)).symm

def patternChannel (j i : Fin 4) : AES.Word → AES.Word → ℝ :=
  if i = j then constantMatrix 0 else residualMatrix AES.wordSuperboxKernel 0

/-- Tensor projection changes factors in place and preserves the full source. -/
theorem support_project_tensorResponse {X : Type*} [Fintype X]
    (marked inactive : Fin 4 → Bool) (T : Fin 4 → AES.Word → AES.Word → ℝ)
    (coords : X → WordState) (mu : X → ℝ) :
    action (supportProduct (0 : AES.Word) marked inactive) (tensorResponse T coords mu) =
      tensorResponse (fun i => kernelCompose (supportPiece 0 (marked i) (inactive i)) (T i))
        coords mu := by
  have hc (y : WordState) (x : X) :
      kernelCompose (supportProduct (0 : AES.Word) marked inactive) (tensorColumn T coords) y x =
        tensorColumn
          (fun i => kernelCompose (supportPiece 0 (marked i) (inactive i)) (T i)) coords y x := by
    unfold kernelCompose supportProduct tensorColumn
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => supportPiece 0 (marked i) (inactive i) (y i) v *
      T i v (coords x i))).symm
  change action (supportProduct (0 : AES.Word) marked inactive) (action (tensorColumn T coords) mu) = _
  rw [← kernelCompose_action]
  funext y
  simp only [action, hc, tensorResponse]

theorem pointed_pattern_left (j i : Fin 4) :
    kernelCompose
      (supportPiece (0 : AES.Word) (maskBit (residualMask j) i) (maskBit (0 : Fin 16) i))
      AES.wordSuperboxKernel = patternChannel j i := by
  by_cases hi : i = j
  · subst i
    simpa [residualMask_bit, emptyMask_bit, supportPiece, patternChannel] using
      (RefinedChannelCommutation.pointed_constant_left AES.word_superbox_pointed)
  · simpa [residualMask_bit, emptyMask_bit, hi, supportPiece, patternChannel, degreePiece] using
      (AESPaper.OneSourceProjection.pointed_degree_left
        AES.wordSuperboxKernel 0 AES.word_superbox_pointed true)

theorem raw_pattern_law_eq_response (j : Fin 4) (b : AES.State) :
    raw (patternLabel j) (groupedLaw 1 b) =
      tensorResponse (patternChannel j)
        (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) (initialProduct b) := by
  change action (supportProduct (0 : AES.Word) (maskBit (residualMask j))
    (maskBit (0 : Fin 16))) (groupedLaw 1 b) = _
  rw [groupedLaw_one_eq_tensorResponse, support_project_tensorResponse]
  simp only [pointed_pattern_left]

def conditionalTensorResponse (T : Fin 4 → AES.Word → AES.Word → ℝ)
    (b : AES.State) (k : Fin 4) (w : OtherAssignments k) : WordState → ℝ :=
  tensorResponse T (fun x : AES.Word => fun i => affineEquiv k w i x) (wordLaw (sourceInput b k))

/-- Exact conditioning for arbitrary factors, not only four residual factors. -/
theorem tensorResponse_eq_probability_mixture
    (T : Fin 4 → AES.Word → AES.Word → ℝ) (b : AES.State) (k : Fin 4) :
    tensorResponse T (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) (initialProduct b) =
      fun y => ∑ w : OtherAssignments k, conditionWeight b k w * conditionalTensorResponse T b k w y := by
  funext y
  let F : WordState → ℝ := fun v =>
    tensorColumn T (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) y v * initialProduct b v
  calc
    _ = ∑ v : WordState, F v := rfl
    _ = ∑ p : AES.Word × OtherAssignments k, F (joinSource k p.1 p.2) :=
      ((sourceSplit k).symm.sum_comp F).symm
    _ = ∑ w : OtherAssignments k, ∑ x : AES.Word, F (joinSource k x w) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      unfold conditionalTensorResponse tensorResponse
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hc :
          tensorColumn T (fun v : WordState => AESPaper.GroupedRecurrence.boundary v) y
            (joinSource k x w) =
          tensorColumn T (fun x : AES.Word => fun i => affineEquiv k w i x) y x := by
        unfold tensorColumn
        apply Finset.prod_congr rfl
        intro i _
        change T i (y i) (AESPaper.GroupedRecurrence.boundary (joinSource k x w) i) =
          T i (y i) (affineEquiv k w i x)
        rw [boundary_joinSource, affineEquiv_apply]
      change tensorColumn T (fun v : WordState => AESPaper.GroupedRecurrence.boundary v) y
          (joinSource k x w) * initialProduct b (joinSource k x w) = _
      rw [hc, initialProduct_joinSource]
      ring

def conditionalPattern (b : AES.State) (k : Fin 4) (w : OtherAssignments k)
    (j : Fin 4) : WordState → ℝ := conditionalTensorResponse (patternChannel j) b k w

/-- The stationary reference is removed at positive degree before replacing
the actual channels. The literal constant channel retains both nonzero tests. -/
theorem actual_component_twelve_eq_probability_mixture (b : AES.State) (k : Fin 4) :
    component (error 1 b) (12 : Fin 14) =
      fun y => ∑ w : OtherAssignments k, conditionWeight b k w *
        ∑ j : Fin 4, conditionalPattern b k w j y := by
  have href : component (error 1 b) (12 : Fin 14) = component (groupedLaw 1 b) (12 : Fin 14) := by
    change component (groupedLaw 1 b - uniformExcept (0 : WordState)) (12 : Fin 14) = _
    rw [OneSourceSupport.component_sub,
      OneSourceSupport.uniform_component_eq_zero (12 : Fin 14) (by decide), sub_zero]
  rw [href, component_twelve_eq_sum_raw]
  funext y
  have hpattern (j : Fin 4) : raw (patternLabel j) (groupedLaw 1 b) y =
      ∑ w : OtherAssignments k, conditionWeight b k w * conditionalPattern b k w j y := by
    exact congrFun ((raw_pattern_law_eq_response j b).trans
      (tensorResponse_eq_probability_mixture (patternChannel j) b k)) y
  simp_rw [hpattern]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end AES8.TwelveConditionalResponse
