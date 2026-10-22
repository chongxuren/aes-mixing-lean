/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.OneSourceSupport
import AES8.Model.LegacyProjection
import AESConcrete.FourResidualStep
import AESPaper.OneSourceProjection
import AESPaper.ManySourceLaw

/-!
# Condition actual first-layer sources before their common boundary response

Component thirteen of the actual grouped error at index one equals the full
four-residual response of the actual initial product law, with the physical
forward boundary retained inside its coordinates. Splitting that initial source
vector into one chosen word and the other three gives an exact probability
mixture of signed common-source residual responses. Each conditional response
uses one original x in all four affine boundary-coordinate permutations.

Only the fixed-input initial word laws are factored. Independence of the four
later boundary observations is neither assumed nor asserted. The exact mixture
identity holds for every chosen k; its nonzero-source interface is packaged
separately for applying existing pointwise resources elsewhere. No numerical
cap, paired-fiber geometry, activity-projection estimate or AES endpoint is
proved or assumed here. Generic weighted-square and energy helpers are included.

Constructive work only; no attacks, local execution, active-source edits,
manuscript edits or predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ConditionalSourceResponse
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)
open AESPaper.StartingWord (wordLaw sourceInput)
open AESPaper.BoundarySourceCoordinates (outputEquiv)
open AESPaper.GroupedLaw (groupedLaw error)
open AES8.SupportProfile (component)

section ForwardLaw

/-- Generic exact change from inverse law weights to forward source labels. -/
theorem action_relabel_eq_forward {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (L : Equiv.Perm X) (f : X → ℝ) :
    action K (lawRelabel L f) = fun y => ∑ x, K y (L x) * f x := by
  funext y
  have h := Equiv.sum_comp L (fun x => K y x * f (L.symm x))
  simpa only [action, lawRelabel, L.symm_apply_apply] using h.symm

def initialProduct (b : AES.State) (x : WordState) : ℝ :=
  ∏ i : Fin 4, wordLaw (sourceInput b i) (x i)

/-- Actual index-one law with its complete original source vector retained. -/
theorem groupedLaw_one_eq_tensorResponse (b : AES.State) :
    groupedLaw 1 b =
      tensorResponse (fun _ : Fin 4 => AES.wordSuperboxKernel)
        (fun x : WordState => AESPaper.GroupedRecurrence.boundary x)
        (initialProduct b) := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, AESPaper.GroupedRecurrence.groupedLaw_succ]
  change action AES.parallelSuperboxKernel
    (lawRelabel AESPaper.GroupedRecurrence.boundary.toEquiv (groupedLaw 0 b)) = _
  rw [action_relabel_eq_forward]
  funext y
  simp only [tensorResponse, tensorColumn, AES.parallelSuperboxKernel,
    coordinateKernel, AESPaper.StartingWord.grouped_initial_product, initialProduct]
  rfl

def fullResidualResponse (b : AES.State) : WordState → ℝ :=
  tensorResponse (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) (initialProduct b)

/-- Positive residual degree removes the actual stationary reference first.
No one-source hypothesis is used in this full-vector response identity. -/
theorem actual_component_thirteen_eq_fullResponse (b : AES.State) :
    component (error 1 b) (13 : Fin 14) = fullResidualResponse b := by
  have href : component (error 1 b) (13 : Fin 14) =
      component (groupedLaw 1 b) (13 : Fin 14) := by
    change component (groupedLaw 1 b - uniformExcept (0 : WordState)) (13 : Fin 14) = _
    rw [OneSourceSupport.component_sub,
      OneSourceSupport.uniform_component_eq_zero (13 : Fin 14) (by decide), sub_zero]
  rw [href, LegacyProjection.component_eq_refinedKernel_action]
  change action (RefinedWordProjection.refinedKernel (0 : AES.Word) 4 4)
    (groupedLaw 1 b) = _
  rw [FourResidualStep.refined_four_full, FourResidualStep.degree_four_tensor]
  change action (productProjection (0 : AES.Word) (fun _ : Fin 4 => true))
    (groupedLaw 1 b) = _
  rw [groupedLaw_one_eq_tensorResponse, AESPaper.OneSourceProjection.project_tensorResponse]
  simp only [AESPaper.OneSourceProjection.pointed_degree_left AES.wordSuperboxKernel 0
    AES.word_superbox_pointed, if_true, fullResidualResponse]

end ForwardLaw

section SourceSplit

abbrev OtherCoordinates (k : Fin 4) := {i : Fin 4 // i ≠ k}
abbrev OtherAssignments (k : Fin 4) := OtherCoordinates k → AES.Word

/-- Exactly three other words; the selected coordinate is represented only by x. -/
def joinSource (k : Fin 4) (x : AES.Word) (w : OtherAssignments k) : WordState :=
  fun i => if hi : i = k then x else w ⟨i, hi⟩

@[simp] theorem joinSource_same (k : Fin 4) (x : AES.Word) (w : OtherAssignments k) :
    joinSource k x w k = x := by simp [joinSource]

@[simp] theorem joinSource_other (k : Fin 4) (x : AES.Word) (w : OtherAssignments k)
    (i : OtherCoordinates k) : joinSource k x w i.val = w i := by
  simp [joinSource, i.property]

def sourceSplit (k : Fin 4) : WordState ≃ AES.Word × OtherAssignments k where
  toFun v := (v k, fun i => v i.val)
  invFun p := joinSource k p.1 p.2
  left_inv v := by
    funext i
    by_cases hi : i = k
    · subst i
      simp [joinSource]
    · simp [joinSource, hi]
  right_inv p := by
    rcases p with ⟨x, w⟩
    apply Prod.ext
    · exact joinSource_same k x w
    · funext i
      exact joinSource_other k x w i

def conditionWeight (b : AES.State) (k : Fin 4) (w : OtherAssignments k) : ℝ :=
  ∏ j : OtherCoordinates k, wordLaw (sourceInput b j.val) (w j)

theorem conditionWeight_nonnegative (b : AES.State) (k : Fin 4)
    (w : OtherAssignments k) : 0 ≤ conditionWeight b k w :=
  Finset.prod_nonneg (fun j _ => AESPaper.StartingWord.wordLaw_nonnegative _ _)

theorem conditionWeight_total (b : AES.State) (k : Fin 4) :
    (∑ w : OtherAssignments k, conditionWeight b k w) = 1 := by
  unfold conditionWeight
  calc
    _ = ∏ j : OtherCoordinates k, ∑ x : AES.Word, wordLaw (sourceInput b j.val) x :=
      (Fintype.prod_sum (fun (j : OtherCoordinates k) (x : AES.Word) =>
        wordLaw (sourceInput b j.val) x)).symm
    _ = 1 := by simp only [AESPaper.StartingWord.wordLaw_total, Finset.prod_const_one]

theorem initialProduct_joinSource (b : AES.State) (k : Fin 4)
    (x : AES.Word) (w : OtherAssignments k) :
    initialProduct b (joinSource k x w) =
      wordLaw (sourceInput b k) x * conditionWeight b k w := by
  unfold initialProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  simp only [joinSource_same, joinSource_other, conditionWeight]

def translation (k : Fin 4) (w : OtherAssignments k) (i : Fin 4) : AES.Word :=
  ∑ j : OtherCoordinates k, outputEquiv j.val i (w j)

/-- Forward physical boundary labels, with all other sources held jointly fixed. -/
theorem boundary_joinSource (k : Fin 4) (x : AES.Word) (w : OtherAssignments k)
    (i : Fin 4) :
    AESPaper.GroupedRecurrence.boundary (joinSource k x w) i =
      outputEquiv k i x + translation k w i := by
  rw [AESPaper.ManySourceLaw.boundary_sum, Fintype.sum_eq_add_sum_subtype_ne _ k]
  simp only [joinSource_same, joinSource_other, translation]

def affineEquiv (k : Fin 4) (w : OtherAssignments k) (i : Fin 4) :
    Equiv.Perm AES.Word :=
  (outputEquiv k i).trans (Equiv.addRight (translation k w i))

@[simp] theorem affineEquiv_apply (k : Fin 4) (w : OtherAssignments k)
    (i : Fin 4) (x : AES.Word) :
    affineEquiv k w i x = outputEquiv k i x + translation k w i := rfl

/-- All four affine labels use the same original chosen source x. -/
def conditionalResponse (b : AES.State) (k : Fin 4) (w : OtherAssignments k) :
    WordState → ℝ :=
  tensorResponse (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun x : AES.Word => fun i => affineEquiv k w i x) (wordLaw (sourceInput b k))

theorem fullResponse_eq_probability_mixture (b : AES.State) (k : Fin 4) :
    fullResidualResponse b =
      fun y => ∑ w : OtherAssignments k, conditionWeight b k w * conditionalResponse b k w y := by
  funext y
  let F : WordState → ℝ := fun v =>
    tensorColumn (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
      (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) y v * initialProduct b v
  calc
    _ = ∑ v : WordState, F v := rfl
    _ = ∑ p : AES.Word × OtherAssignments k, F (joinSource k p.1 p.2) :=
      ((sourceSplit k).symm.sum_comp F).symm
    _ = ∑ w : OtherAssignments k, ∑ x : AES.Word, F (joinSource k x w) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      unfold conditionalResponse tensorResponse
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hc :
          tensorColumn (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
            (fun v : WordState => AESPaper.GroupedRecurrence.boundary v) y (joinSource k x w) =
          tensorColumn (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
            (fun x : AES.Word => fun i => affineEquiv k w i x) y x := by
        unfold tensorColumn
        apply Finset.prod_congr rfl
        intro i _
        change residualMatrix AES.wordSuperboxKernel 0 (y i)
            (AESPaper.GroupedRecurrence.boundary (joinSource k x w) i) =
          residualMatrix AES.wordSuperboxKernel 0 (y i) (affineEquiv k w i x)
        rw [boundary_joinSource, affineEquiv_apply]
      change tensorColumn (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
        (fun v : WordState => AESPaper.GroupedRecurrence.boundary v) y (joinSource k x w) *
          initialProduct b (joinSource k x w) = _
      rw [hc, initialProduct_joinSource]
      ring

/-- Actual centered component, exact for every k before choosing a nonzero word. -/
theorem actual_component_thirteen_eq_probability_mixture (b : AES.State) (k : Fin 4) :
    component (error 1 b) (13 : Fin 14) =
      fun y => ∑ w : OtherAssignments k, conditionWeight b k w * conditionalResponse b k w y := by
  rw [actual_component_thirteen_eq_fullResponse, fullResponse_eq_probability_mixture b k]

/-- Explicit interface for a chosen nonzero original source word. The source
condition is retained for subsequent resource specialization, not used to split
or normalize the other sources. -/
theorem chosen_source_probability_mixture (b : AES.State) (k : Fin 4)
    (hk : sourceInput b k ≠ 0) :
    sourceInput b k ≠ 0 ∧
      (∀ w : OtherAssignments k, 0 ≤ conditionWeight b k w) ∧
      (∑ w : OtherAssignments k, conditionWeight b k w) = 1 ∧
      component (error 1 b) (13 : Fin 14) =
        fun y => ∑ w : OtherAssignments k, conditionWeight b k w * conditionalResponse b k w y :=
  ⟨hk, conditionWeight_nonnegative b k, conditionWeight_total b k,
    actual_component_thirteen_eq_probability_mixture b k⟩

theorem exists_nonzero_source_probability_mixture (b : AES.State) (hb : b ≠ 0) :
    ∃ k : Fin 4, sourceInput b k ≠ 0 ∧
      (∀ w : OtherAssignments k, 0 ≤ conditionWeight b k w) ∧
      (∑ w : OtherAssignments k, conditionWeight b k w) = 1 ∧
      component (error 1 b) (13 : Fin 14) =
        fun y => ∑ w : OtherAssignments k, conditionWeight b k w * conditionalResponse b k w y := by
  have hex : ∃ k : Fin 4, sourceInput b k ≠ 0 := by
    by_contra h
    push Not at h
    exact AESPaper.UniversalInitialization.sourceInput_ne_zero b hb (funext h)
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, chosen_source_probability_mixture b k hk⟩

end SourceSplit

section WeightedEnergy
variable {W Y : Type*} [Fintype W] [Fintype Y]

/-- Jensen for a finite probability mixture, proved by nonnegative variance.
The values f may have either sign. -/
theorem weighted_square_le (eta f : W → ℝ)
    (heta : ∀ w, 0 ≤ eta w) (htotal : (∑ w, eta w) = 1) :
    (∑ w, eta w * f w) ^ 2 ≤ ∑ w, eta w * f w ^ 2 := by
  let m : ℝ := ∑ w, eta w * f w
  have hnonneg : 0 ≤ ∑ w, eta w * (f w - m) ^ 2 :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (heta w) (sq_nonneg _))
  have hpoint (w : W) : eta w * (f w - m) ^ 2 =
      eta w * f w ^ 2 - (2 * m) * (eta w * f w) + m ^ 2 * eta w := by ring
  have heq : (∑ w, eta w * (f w - m) ^ 2) =
      (∑ w, eta w * f w ^ 2) - (2 * m) * (∑ w, eta w * f w) +
        m ^ 2 * (∑ w, eta w) := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
  rw [htotal] at heq
  have hm : (∑ w, eta w * f w) = m := rfl
  rw [hm] at heq
  change m ^ 2 ≤ ∑ w, eta w * f w ^ 2
  nlinarith [heq]

theorem weighted_energy_le (eta : W → ℝ) (F : W → Y → ℝ)
    (heta : ∀ w, 0 ≤ eta w) (htotal : (∑ w, eta w) = 1) :
    (∑ y, (∑ w, eta w * F w y) ^ 2) ≤ ∑ w, eta w * ∑ y, F w y ^ 2 := by
  calc
    _ ≤ ∑ y, ∑ w, eta w * F w y ^ 2 :=
      Finset.sum_le_sum (fun y _ => weighted_square_le eta (fun w => F w y) heta htotal)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

theorem weighted_energy_le_uniform (eta : W → ℝ) (F : W → Y → ℝ)
    (heta : ∀ w, 0 ≤ eta w) (htotal : (∑ w, eta w) = 1)
    (B : ℝ) (henergy : ∀ w, (∑ y, F w y ^ 2) ≤ B) :
    (∑ y, (∑ w, eta w * F w y) ^ 2) ≤ B := by
  calc
    _ ≤ ∑ w, eta w * ∑ y, F w y ^ 2 := weighted_energy_le eta F heta htotal
    _ ≤ ∑ w, eta w * B :=
      Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (henergy w) (heta w))
    _ = B := by rw [← Finset.sum_mul, htotal, _root_.one_mul]

end WeightedEnergy
end AES8.ConditionalSourceResponse
