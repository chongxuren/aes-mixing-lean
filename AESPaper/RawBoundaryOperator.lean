import AESPaper.RawBoundaryKernel
import AESPaper.RawBoundaryIncidence
import AESPaper.WordActivityCounts
import AESPaper.WordMarkedUniform
import AESMixing.ResidualCoordinates

/-!
# Projected incidence bounds for the actual raw boundary contractions

The exact shortened response is the actual incidence matrix with both
all-residual coordinate projectors and one word-frame divisor. Input
residuals retain their literal transpose. The incidence Schur bound and
both projection contractions hold on every signed joint input, including
empty marked input or output coordinate types. Exact endpoint cancellation
uses a witness in the total marked type, not a marked-input assumption.
The natural powers retain their literal truncation. Numerical C/t caps,
activity-frame assembly and position aggregation remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryOperator
open AESMixing AESConcrete
open AESPaper.GroupedRecurrence
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros
  rawResponse sourceCoordinates)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordMarkedMoment (Source)
open AESPaper.RawBoundaryIncidence (q zeroCount)
open AESPaper.RawBoundaryKernel (rawMarkedLeg contractedResponse)
open AESPaper.RectangularFourier (rectAction EnergyBound)
-- Match the standard decidable instances in RawBoundaryKernel and ProfileSpace.

section GenericIncidence
variable {C O I : Type*} [Fintype C] [Fintype O] [Fintype I]
  [DecidableEq O] [DecidableEq I]

/-- Bilinear incidence transport keeps the same source point on both legs. -/
theorem incidence_sandwich_entry (o : C → O) (i : C → I)
    (QO : O → O → ℝ) (QI : I → I → ℝ) (y : O) (x : I) :
    kernelCompose QO (kernelCompose (incidenceMultiplicity o i) QI) y x =
      ∑ c : C, QO y (o c) * QI (i c) x :=
  incidenceMultiplicity_bilinear o i (fun w => QI w x) (fun v => QO y v)

end GenericIncidence

/-- All physical marked output coordinates carry their residual projector. -/
def outputProjection (m : GraphPosition → Bool) :
    (OutputMarked m → AES.Word) → (OutputMarked m → AES.Word) → ℝ :=
  productProjection (0 : AES.Word) (fun _ => true)

/-- The matrix acts on the physical marked input tuple, without relabeling. -/
def inputProjection (m : GraphPosition → Bool) :
    (InputMarked m → AES.Word) → (InputMarked m → AES.Word) → ℝ :=
  productProjection (0 : AES.Word) (fun _ => true)

def projectedIncidence (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (OutputMarked m → AES.Word) → (InputMarked m → AES.Word) → ℝ :=
  kernelCompose (outputProjection m)
    (kernelCompose (RawBoundaryIncidence.incidenceKernel m s) (inputProjection m))

/-- The input factor is QI(source,input), exactly the physical transpose. -/
theorem rawMarkedLeg_product (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : Source m s) (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word) :
    (∏ p : Marked m, rawMarkedLeg m p (WordMarkedSplit.join m y x p)
      (sourceCoordinates boundary.toAddMonoidHom m s c p)) =
      outputProjection m y (RawBoundaryIncidence.outputSource m s c) *
        inputProjection m (RawBoundaryIncidence.inputSource m s c) x := by
  rw [WordMarkedSplit.prod_positions]
  simp only [RawBoundaryKernel.rawMarkedLeg_output, RawBoundaryKernel.rawMarkedLeg_input,
    WordMarkedSplit.join_output, WordMarkedSplit.join_input]
  rfl

/-- Exact projected incidence, before the single activity-frame divisor. -/
theorem rawResponse_eq_projectedIncidence (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word) :
    rawResponse boundary.toAddMonoidHom m s (rawMarkedLeg m) (WordMarkedSplit.join m y x) =
      projectedIncidence m s y x := by
  unfold rawResponse projectedIncidence RawBoundaryIncidence.incidenceKernel
  rw [incidence_sandwich_entry]
  apply Finset.sum_congr rfl
  intro c _
  exact rawMarkedLeg_product m s c y x

/-- The raw physical contraction has exactly one divisor, with the two
coordinate projections explicit on their actual physical sides. -/
theorem reshape_contracted_eq (m : GraphPosition → Bool) (s : Activity m → Bool) :
    WordOperatorDuality.reshape m (contractedResponse m s) =
      fun y x => projectedIncidence m s y x / (65536 : ℝ) ^ uniformCount s := by
  funext y x
  change contractedResponse m s (WordMarkedSplit.join m y x) = _
  rw [RawBoundaryKernel.contractedResponse_shortened, rawResponse_eq_projectedIncidence]

/-- Product of actual output and input MDS fiber caps. -/
def fiberProduct (m : GraphPosition → Bool) (s : Activity m → Bool) : ℝ :=
  q ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))) *
    q ^ (4 - (zeroCount m s + Fintype.card (InputMarked m)))

theorem fiberProduct_nonnegative (m : GraphPosition → Bool) (s : Activity m → Bool) :
    0 ≤ fiberProduct m s := by
  exact mul_nonneg (pow_nonneg RawBoundaryIncidence.q_positive.le _)
    (pow_nonneg RawBoundaryIncidence.q_positive.le _)

/-- The scalar is unscaled: no extra q^2 factor or divisor occurs. -/
def coefficient (m : GraphPosition → Bool) (s : Activity m → Bool) : ℝ :=
  Real.sqrt (fiberProduct m s) / (65536 : ℝ) ^ uniformCount s

theorem coefficient_nonnegative (m : GraphPosition → Bool) (s : Activity m → Bool) :
    0 ≤ coefficient m s :=
  div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by norm_num) _)

theorem coefficient_sq (m : GraphPosition → Bool) (s : Activity m → Bool) :
    coefficient m s ^ 2 = fiberProduct m s / q ^ uniformCount s := by
  have hd : ((65536 : ℝ) ^ uniformCount s) ^ 2 = q ^ uniformCount s := by
    rw [← pow_mul, Nat.mul_comm (uniformCount s) 2, pow_mul]
    norm_num [q]
  rw [coefficient, div_pow, Real.sq_sqrt (fiberProduct_nonnegative m s), hd]

/-- Output projection contraction, actual incidence Schur, and input
projection contraction, in their execution order on an arbitrary input. -/
theorem projectedIncidence_energy (m : GraphPosition → Bool) (s : Activity m → Bool)
    (f : (InputMarked m → AES.Word) → ℝ) :
    (∑ y : OutputMarked m → AES.Word, action (projectedIncidence m s) f y ^ 2) ≤
      fiberProduct m s * ∑ x : InputMarked m → AES.Word, f x ^ 2 := by
  simp only [projectedIncidence, kernelCompose_action]
  calc
    _ ≤ ∑ y : OutputMarked m → AES.Word,
        action (RawBoundaryIncidence.incidenceKernel m s)
          (action (inputProjection m) f) y ^ 2 :=
      productProjection_energy_le (0 : AES.Word) ProfileSpace.word_card_gt_one (fun _ => true) _
    _ ≤ fiberProduct m s * ∑ x : InputMarked m → AES.Word,
        action (inputProjection m) f x ^ 2 :=
      RawBoundaryIncidence.incidence_energy m s (action (inputProjection m) f)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (productProjection_energy_le (0 : AES.Word) ProfileSpace.word_card_gt_one (fun _ => true) f)
      (fiberProduct_nonnegative m s)

theorem projectedIncidence_energyBound (m : GraphPosition → Bool) (s : Activity m → Bool) :
    EnergyBound (projectedIncidence m s) (Real.sqrt (fiberProduct m s)) := by
  intro f
  rw [Real.sq_sqrt (fiberProduct_nonnegative m s)]
  exact projectedIncidence_energy m s f

/-- The generic counting bound applies even if one marked side is empty. -/
theorem contracted_operator_bound (m : GraphPosition → Bool) (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s)) (coefficient m s) := by
  have h := RectangularBounds.energyBound_scale (1 / (65536 : ℝ) ^ uniformCount s)
    (projectedIncidence m s) (Real.sqrt (fiberProduct m s))
    (projectedIncidence_energyBound m s)
  have hc : (1 / (65536 : ℝ) ^ uniformCount s) * Real.sqrt (fiberProduct m s) =
      coefficient m s := by
    unfold coefficient
    ring
  rw [hc] at h
  rw [reshape_contracted_eq]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

/-- Explicit formula for the unscaled coefficient with literal natural powers. -/
theorem contracted_operator_bound_explicit (m : GraphPosition → Bool)
    (s : Activity m → Bool) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (Real.sqrt
        (q ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))) *
          q ^ (4 - (zeroCount m s + Fintype.card (InputMarked m)))) /
        (65536 : ℝ) ^ uniformCount s) :=
  contracted_operator_bound m s

theorem residual_symmetric (y x : AES.Word) :
    residualProjection (0 : AES.Word) y x = residualProjection (0 : AES.Word) x y :=
  degreePiece_symmetric (0 : AES.Word) true y x

theorem residual_zero_column (y : AES.Word) : residualProjection (0 : AES.Word) y 0 = 0 :=
  (residual_symmetric y 0).trans (residualProjection_zero_row (0 : AES.Word) y)

/-- Ordinary residual column sums are also used for the transposed input leg. -/
theorem residual_column_sum (y : AES.Word) :
    (∑ v : AES.Word, residualProjection (0 : AES.Word) v y) = 0 := by
  simpa only [degreePiece, if_true] using
    degreePiece_column_sum (0 : AES.Word) ProfileSpace.word_card_gt_one true y

theorem residual_row_sum (y : AES.Word) :
    (∑ v : AES.Word, residualProjection (0 : AES.Word) y v) = 0 := by
  calc
    _ = ∑ v : AES.Word, residualProjection (0 : AES.Word) v y :=
      Finset.sum_congr rfl (fun v _ => residual_symmetric y v)
    _ = 0 := residual_column_sum y

theorem rawMarkedLeg_zero_column (m : GraphPosition → Bool) (p : Marked m) (y : AES.Word) :
    rawMarkedLeg m p y 0 = 0 := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i => exact residual_zero_column y
  | inr i => exact residualProjection_zero_row (0 : AES.Word) y

/-- Source-index row sums cover output and literal transposed input legs. -/
theorem rawMarkedLeg_row_sum (m : GraphPosition → Bool) (p : Marked m) (y : AES.Word) :
    (∑ v : AES.Word, rawMarkedLeg m p y v) = 0 := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i => exact residual_row_sum y
  | inr i => exact residual_column_sum y

/-- Use the alphabet-generic raw vanishing theorem and the word divisor;
the byte contraction wrapper is not used. -/
theorem contractedResponse_zero_of_high_zeros (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true) (hz : 4 ≤ zeroCount m s)
    (y : Marked m → AES.Word) : contractedResponse m s y = 0 := by
  have hr := MarkedBlockVanishing.rawResponse_zero_of_high_zeros
    boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS m s hm hz
    (rawMarkedLeg m) (rawMarkedLeg_zero_column m) y
  rw [RawBoundaryKernel.contractedResponse_shortened, hr, zero_div]

/-- Any marked output OR input witness cancels the full marked image. -/
theorem contractedResponse_zero_of_uniform_image (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hlow : zeroCount m s + Fintype.card (Marked m) ≤ 4)
    (y : Marked m → AES.Word) : contractedResponse m s y = 0 := by
  obtain ⟨p,hp⟩ := hm
  rw [RawBoundaryKernel.contractedResponse_shortened,
    WordMarkedUniform.rawResponse_zero_of_uniform_image m s hlow (rawMarkedLeg m)
      (⟨p,hp⟩ : Marked m) (rawMarkedLeg_row_sum m ⟨p,hp⟩) y, zero_div]

/-- Exact nonsurviving cancellation requires only a nonempty total marking. -/
theorem contractedResponse_zero_outside_surviving (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < WordMarkedEnergy.dimension m s ∧
      WordMarkedEnergy.dimension m s < Fintype.card (Marked m)))
    (y : Marked m → AES.Word) : contractedResponse m s y = 0 := by
  by_cases hz : 4 ≤ zeroCount m s
  · exact contractedResponse_zero_of_high_zeros m s hm hz y
  · apply contractedResponse_zero_of_uniform_image m s hm _ y
    change ¬ (0 < 4 - zeroCount m s ∧
      4 - zeroCount m s < Fintype.card (Marked m)) at hout
    omega

theorem reshape_zero_outside_surviving (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < WordMarkedEnergy.dimension m s ∧
      WordMarkedEnergy.dimension m s < Fintype.card (Marked m))) :
    WordOperatorDuality.reshape m (contractedResponse m s) = fun _ _ => 0 := by
  funext y x
  exact contractedResponse_zero_outside_surviving m s hm hout (WordMarkedSplit.join m y x)

theorem contracted_operator_zero (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < WordMarkedEnergy.dimension m s ∧
      WordMarkedEnergy.dimension m s < Fintype.card (Marked m))) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s)) 0 := by
  rw [reshape_zero_outside_surviving m s hm hout]
  intro f
  simp [rectAction]

def piecewiseCoefficient (m : GraphPosition → Bool) (s : Activity m → Bool) : ℝ :=
  if 0 < WordMarkedEnergy.dimension m s ∧
    WordMarkedEnergy.dimension m s < Fintype.card (Marked m) then coefficient m s else 0

theorem piecewiseCoefficient_nonnegative (m : GraphPosition → Bool)
    (s : Activity m → Bool) : 0 ≤ piecewiseCoefficient m s := by
  unfold piecewiseCoefficient
  split_ifs
  · exact coefficient_nonnegative m s
  · exact le_rfl

/-- Complete per-choice raw estimate, with exact zero endpoint branches. -/
theorem contracted_operator_piecewise (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true) :
    EnergyBound (WordOperatorDuality.reshape m (contractedResponse m s))
      (piecewiseCoefficient m s) := by
  unfold piecewiseCoefficient
  split_ifs with hs
  · exact contracted_operator_bound m s
  · exact contracted_operator_zero m s hm hs

end AESPaper.RawBoundaryOperator
