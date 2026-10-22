/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighTwelve
import AESConcrete.RefinedChannelCommutation
import AESPaper.OneSourceProjection

/-!
# A literal support-event bridge for first-high output eleven

This reduction retains the actual one-source law, positive-degree reference
removal, inverse boundary transport, exact target support and centered step.
The output-three-support damping is charged to the energy on the literal
three-active-word event after diffusion, rather than to the complete source
component thirteen. That event energy is exactly a constrained common-source
Gram quadratic, with both original source weights retained.

The event Gram estimate is NOT proved here. The last theorem isolates the
explicit sufficient estimate q^5 * eventQuadratic <= 1/62500. Everything
before that scalar assembly has no missing quantitative premise. In
particular, this file does not assert a new unconditional first-high cell,
the complete PhysicalCaps field or the concrete AES theorem.

Constructive proof work only; no attacks, local Lean/scientific execution,
manuscript edits or predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.FirstHighSupportEvent
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.RefinedWordProjection
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_right)
open AES8.LegacyProjection
open AES8.SupportProfile (component profile activeCount supportSize residualDegree)
open AES8.TransferAssembly (centeredStep)
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)

section SupportRestriction

/-- Literal selection of the input support event, before residual projection. -/
def restrictSupport (n : ℕ) (f : WordState → ℝ) (x : WordState) : ℝ :=
  if activeCount x = n then f x else 0

/-- Recover the kernel's row support from the already proved action support.
The point input is used only symbolically; no AES state enumeration occurs. -/
theorem projectionKernel_row_zero (c : Fin 14) (x y : WordState)
    (hx : activeCount x ≠ supportSize c) : projectionKernel c x y = 0 := by
  have h := SupportProfile.component_supported
    (fun t : WordState => if t = y then (1 : ℝ) else 0) c x hx
  rw [component_eq_projectionKernel_action] at h
  simpa only [action, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using h

/-- Symmetry makes the same exact support restriction valid on input. -/
theorem projectionKernel_column_zero (c : Fin 14) (x y : WordState)
    (hy : activeCount y ≠ supportSize c) : projectionKernel c x y = 0 := by
  change refinedKernel (0 : AES.Word) (residualIndex c) (activeIndex c) x y = 0
  rw [refinedKernel_symmetric]
  exact projectionKernel_row_zero c y x hy

/-- A refined projection reads only its matching literal input support event. -/
theorem component_restrictSupport (f : WordState → ℝ) (c : Fin 14) :
    component f c = component (restrictSupport (supportSize c) f) c := by
  simp_rw [component_eq_projectionKernel_action]
  funext y
  unfold action
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : activeCount x = supportSize c
  · simp only [restrictSupport, hx, if_true]
  · rw [projectionKernel_column_zero c y x hx]
    simp only [zero_mul]

/-- The matching literal event energy controls a refined projected input. -/
theorem component_energy_le_restriction (f : WordState → ℝ) (c : Fin 14) :
    (∑ x, component f c x ^ 2) ≤
      ∑ x, restrictSupport (supportSize c) f x ^ 2 := by
  rw [component_restrictSupport f c, component_eq_refinedKernel_action]
  exact FourResidualStep.refined_energy_le (0 : AES.Word)
    SupportProfile.word_card_gt_one (residualIndex c) (activeIndex c)
    (restrictSupport (supportSize c) f)

end SupportRestriction

section ActualBoundary

/-- Forward physical transport of a joint density uses the inverse boundary. -/
def boundaryInput (f : WordState → ℝ) (x : WordState) : ℝ :=
  f (WordCrossZero.wordMixAddEquiv.symm x)

/-- Literal energy on the selected support event after the physical diffusion. -/
def boundaryEventEnergy (n : ℕ) (f : WordState → ℝ) : ℝ :=
  ∑ x, if activeCount (WordCrossZero.wordMixAddEquiv x) = n then f x ^ 2 else 0

theorem restriction_energy_eq_boundaryEvent (n : ℕ) (f : WordState → ℝ) :
    (∑ x, restrictSupport n (boundaryInput f) x ^ 2) = boundaryEventEnergy n f := by
  calc
    _ = ∑ x, if activeCount x = n then
        f (WordCrossZero.wordMixAddEquiv.symm x) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : activeCount x = n <;>
        simp only [restrictSupport, boundaryInput, hx, if_true, if_false,
          zero_pow (by decide : 2 ≠ 0)]
    _ = boundaryEventEnergy n f := by
      let e := WordCrossZero.wordMixAddEquiv.toEquiv
      change (∑ x, if activeCount x = n then f (e.symm x) ^ 2 else 0) =
        ∑ x, if activeCount (e x) = n then f x ^ 2 else 0
      rw [← e.sum_comp (fun x => if activeCount x = n then f (e.symm x) ^ 2 else 0)]
      simp only [e.symm_apply_apply]


-- Positive output degree removes the reference before support reasoning.
-- This is the same short cancellation as ActivityMinor's public theorem,
-- reproduced here to avoid importing its larger selected-channel closure.
private theorem refined_globalUniform_zero {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (d a : Fin 5) (hd : d ≠ 0) :
    kernelCompose (refinedKernel z d a) (DegreeCentering.globalUniformKernel z) = 0 := by
  calc
    _ = kernelCompose (kernelCompose (refinedKernel z d a) (degreeKernel z d))
        (DegreeCentering.globalUniformKernel z) := by
      rw [refinedKernel_compose_degreeKernel z hn d a]
    _ = kernelCompose (refinedKernel z d a)
        (kernelCompose (degreeKernel z d) (DegreeCentering.globalUniformKernel z)) :=
      (compose_assoc _ _ _).symm
    _ = 0 := by
      rw [DegreeCentering.degreeKernel_compose_globalUniformKernel z hn d hd]
      funext y x
      simp only [kernelCompose, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Exact centered-step identity with the target refinement placed before the
parallel channel. Both the target support and inverse diffusion are retained. -/
theorem centered_component_eq_channel (f : WordState → ℝ) (c : Fin 14)
    (hc : residualIndex c ≠ 0) :
    component (centeredStep f) c =
      action AES.parallelSuperboxKernel (component (boundaryInput f) c) := by
  rw [component_eq_refinedKernel_action]
  change action (refinedKernel (0 : AES.Word) (residualIndex c) (activeIndex c))
      (action (WordStepZeros.wordStepKernel - DegreeCentering.globalUniformKernel 0) f) = _
  rw [← kernelCompose_action, compose_sub_right,
    refined_globalUniform_zero (0 : AES.Word) SupportProfile.word_card_gt_one
      (residualIndex c) (activeIndex c) hc,
    sub_zero, kernelCompose_action, WordStepZeros.wordStepKernel_action]
  change action (refinedKernel (0 : AES.Word) (residualIndex c) (activeIndex c))
      (action (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel))
        (boundaryInput f)) = _
  rw [← kernelCompose_action,
    RefinedChannelCommutation.refined_channel_commutes AES.wordSuperboxKernel
      (0 : AES.Word) AES.word_superbox_pointed (residualIndex c) (activeIndex c),
    kernelCompose_action]
  rw [← component_eq_refinedKernel_action (boundaryInput f) c]
  rfl

/-- Genuine support-sensitive damping: the right side is the actual input's
energy on one literal event, rather than its complete component energy. -/
theorem centered_component_energy_le_event (f : WordState → ℝ) (c : Fin 14)
    (hc : residualIndex c ≠ 0) :
    (∑ y, component (centeredStep f) c y ^ 2) ≤
      (SharpWordNorm.rho ^ residualDegree c) ^ 2 * boundaryEventEnergy (supportSize c) f := by
  rw [centered_component_eq_channel f c hc]
  have hdamp :
      (∑ y, action AES.parallelSuperboxKernel (component (boundaryInput f) c) y ^ 2) ≤
      (SharpWordNorm.rho ^ residualDegree c) ^ 2 *
        ∑ x, component (boundaryInput f) c x ^ 2 := by
    simp_rw [component_eq_refinedKernel_action]
    simpa only [residualIndex_val, AES.parallelSuperboxKernel] using
      (RefinedChannelCommutation.refined_damped_energy AES.wordSuperboxKernel
        (0 : AES.Word) SupportProfile.word_card_gt_one AES.word_superbox_pointed
        SharpWordNorm.rho SharpDegreeStep.word_superbox_residual_energy
        (residualIndex c) (activeIndex c) (boundaryInput f))
  exact hdamp.trans (by
    rw [← restriction_energy_eq_boundaryEvent]
    exact mul_le_mul_of_nonneg_left
      (component_energy_le_restriction (boundaryInput f) c) (sq_nonneg _))

/-- Counting-length version of the same support-sensitive energy bound. -/
theorem centered_component_profile_le_event (f : WordState → ℝ) (c : Fin 14)
    (hc : residualIndex c ≠ 0) :
    profile (centeredStep f) c ≤ SharpWordNorm.rho ^ residualDegree c *
      l2 (restrictSupport (supportSize c) (boundaryInput f)) := by
  have he := centered_component_energy_le_event f c hc
  rw [← restriction_energy_eq_boundaryEvent] at he
  exact l2_le_of_energy _ _ (SharpWordNorm.rho ^ residualDegree c)
    (pow_nonneg (by norm_num [SharpWordNorm.rho]) _) he

end ActualBoundary

section ExactCommonSource

variable {Y X : Type*} [Fintype Y] [Fintype X]

/-- Restrict an arbitrary signed response without splitting its common source.
The event may couple every output coordinate. -/
theorem event_response_energy (A : Y → X → ℝ) (mu : X → ℝ)
    (event : Y → Prop) [DecidablePred event] :
    (∑ y, if event y then (∑ x, A y x * mu x) ^ 2 else 0) =
      ∑ x, ∑ z, mu x * mu z *
        ∑ y, if event y then A y x * A y z else 0 := by
  have hgram (x z : X) :
      gram (fun y x => if event y then A y x else 0) x z =
        ∑ y, if event y then A y x * A y z else 0 := by
    unfold gram
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : event y <;> simp only [hy, if_true, if_false, zero_mul]
  calc
    _ = ∑ y, (∑ x, (if event y then A y x else 0) * mu x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y <;>
        simp only [hy, if_true, if_false, zero_mul, Finset.sum_const_zero,
          zero_pow (by decide : 2 ≠ 0)]
    _ = ∑ x, ∑ z, mu x * mu z *
        gram (fun y x => if event y then A y x else 0) x z :=
      gram_quadratic _ mu
    _ = _ := by simp only [hgram]

end ExactCommonSource

section ActualOneSource

/-- The all-residual response column, with the real boundary source coordinates. -/
def oneSourceResidualColumn (k : Fin 4) (y : WordState) (x : AES.Word) : ℝ :=
  ∏ i : Fin 4, residualMatrix AES.wordSuperboxKernel 0 (y i)
    (AESPaper.BoundarySourceCoordinates.outputEquiv k i x)

/-- Literal constrained Gram: the support event remains inside the output sum. -/
def oneSourceEventGram (n : ℕ) (k : Fin 4) (x z : AES.Word) : ℝ :=
  ∑ y : WordState, if activeCount (WordCrossZero.wordMixAddEquiv y) = n then
    oneSourceResidualColumn k y x * oneSourceResidualColumn k y z else 0

/-- Exact two-source quadratic, not a product of independent source laws. -/
def oneSourceEventQuadratic (n : ℕ) (k : Fin 4) (a : AES.Word) : ℝ :=
  ∑ x, ∑ z, AESPaper.StartingWord.wordLaw a x * AESPaper.StartingWord.wordLaw a z *
    oneSourceEventGram n k x z

theorem law_component_thirteen_eq_response (k : Fin 4) (a : AES.Word) :
    component (AESPaper.OneSourceLaw.law k a) (13 : Fin 14) =
      fun y => ∑ x, oneSourceResidualColumn k y x * AESPaper.StartingWord.wordLaw a x := by
  rw [component_eq_refinedKernel_action]
  change action (refinedKernel (0 : AES.Word) 4 4) (AESPaper.OneSourceLaw.law k a) = _
  rw [FourResidualStep.refined_four_full, FourResidualStep.degree_four_tensor]
  change action (productProjection (0 : AES.Word) (fun _ : Fin 4 => true))
      (AESPaper.OneSourceLaw.law k a) = _
  rw [AESPaper.OneSourceProjection.projected_law]
  rfl


/-- Reference removal is exact at positive degree; no all-active-error claim. -/
theorem actual_component_thirteen_eq_response (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a) :
    component (error 1 b) (13 : Fin 14) =
      fun y => ∑ x, oneSourceResidualColumn k y x * AESPaper.StartingWord.wordLaw a x := by
  rw [OneSourceSupport.actual_component_eq_law b k a hsource (13 : Fin 14) (by decide)]
  exact law_component_thirteen_eq_response k a

/-- The actual event energy equals a literal constrained common-source Gram.
The physical diffusion remains in the event, not in a substituted surrogate. -/
theorem actual_thirteen_event_energy_eq (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a) (n : ℕ) :
    boundaryEventEnergy n (component (error 1 b) (13 : Fin 14)) =
      oneSourceEventQuadratic n k a := by
  rw [actual_component_thirteen_eq_response b k a hsource]
  exact event_response_energy (oneSourceResidualColumn k) (AESPaper.StartingWord.wordLaw a)
    (fun y => activeCount (WordCrossZero.wordMixAddEquiv y) = n)

/-- A concrete new source-sensitive estimate with no unproved quantitative
premise. Its RHS is an exact source moment, whose smallness is a separate task. -/
theorem actual_thirteen_to_eleven_energy (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a) :
    (∑ y, component (centeredStep (component (error 1 b) (13 : Fin 14)))
        (11 : Fin 14) y ^ 2) ≤
      (SharpWordNorm.rho ^ (3 : ℕ)) ^ 2 * oneSourceEventQuadratic 3 k a := by
  have he := centered_component_energy_le_event
    (component (error 1 b) (13 : Fin 14)) (11 : Fin 14) (by decide)
  change (∑ y, component (centeredStep (component (error 1 b) (13 : Fin 14)))
      (11 : Fin 14) y ^ 2) ≤
    (SharpWordNorm.rho ^ (3 : ℕ)) ^ 2 *
      boundaryEventEnergy 3 (component (error 1 b) (13 : Fin 14)) at he
  rw [actual_thirteen_event_energy_eq b k a hsource 3] at he
  exact he

end ActualOneSource

section SufficientMoment

def alphaEleven : ℝ := AESRound.Terminal.lambda * AESRound.Certificate.L 11 12

/-- The exact retained moment would suffice at this explicit scaled budget.
This lemma does not discharge its moment hypothesis. -/
theorem event_length_le_of_moment (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a)
    (hmoment : AESPaper.StartingWord.q ^ 5 * oneSourceEventQuadratic 3 k a ≤
      (1 : ℝ) / 62500) :
    (2 : ℝ) ^ 80 *
      l2 (restrictSupport 3 (boundaryInput (component (error 1 b) (13 : Fin 14)))) ≤
      (1 : ℝ) / 250 := by
  have hs : ((2 : ℝ) ^ 80 *
      l2 (restrictSupport 3 (boundaryInput (component (error 1 b) (13 : Fin 14))))) ^ 2 =
      AESPaper.StartingWord.q ^ 5 * oneSourceEventQuadratic 3 k a := by
    rw [mul_pow, l2_sq, restriction_energy_eq_boundaryEvent,
      actual_thirteen_event_energy_eq b k a hsource 3]
    norm_num [AESPaper.StartingWord.q]
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  calc
    _ = AESPaper.StartingWord.q ^ 5 * oneSourceEventQuadratic 3 k a := hs
    _ ≤ (1 : ℝ) / 62500 := hmoment
    _ = ((1 : ℝ) / 250) ^ 2 := by norm_num

/-- Source twelve keeps its already admitted small cross-support cap; only
source thirteen uses the new literal event length. -/
theorem one_source_eleven_le_event (b : AES.State) (hb : activeSourceCount b = 1) :
    profile (centeredStep (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      alphaEleven * profile (error 1 b) (12 : Fin 14) +
        SharpWordNorm.rho ^ (3 : ℕ) *
          l2 (restrictSupport 3 (boundaryInput (component (error 1 b) (13 : Fin 14)))) := by
  rw [OneSourceSupport.actual_highPart_eq_two b hb, TransferAssembly.centeredStep_add]
  apply (TransferAssembly.profile_add_le _ _ (11 : Fin 14)).trans
  apply add_le_add
  · exact LegacyTransfer.profile_le_of_operator_cap (error 1 b) 11 12
      (FirstHighSeveralSource.old_operator_cap 11 12)
  · exact centered_component_profile_le_event
      (component (error 1 b) (13 : Fin 14)) (11 : Fin 14) (by decide)

/-- Exact scalar sufficiency, independent of the still-open moment estimate. -/
theorem scalar_eleven_le :
    (2 : ℝ) ^ 41 *
      (alphaEleven * FirstHighTwelve.b3 + SharpWordNorm.rho ^ (3 : ℕ) * ((1 : ℝ) / 250)) ≤
      (1000 * g (11 : Fin 14)) * d (11 : Fin 14) := by
  norm_num [alphaEleven, FirstHighTwelve.b3, SharpWordNorm.rho, AESRound.Terminal.lambda,
    AESRound.Certificate.L, g, d, vec14_apply, Fin.ext_iff]

/-- Precisely isolated remaining sufficient moment obligation for output11.
This is conditional on a literal source Gram estimate, never on the desired
first-high bound, and is not an unconditional cell-closure claim. -/
theorem firstHigh_eleven_of_event_moment (b : AES.State) (hb : activeSourceCount b = 1)
    (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a)
    (hmoment : AESPaper.StartingWord.q ^ 5 * oneSourceEventQuadratic 3 k a ≤
      (1 : ℝ) / 62500) :
    profile (centeredStep (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      (d (11 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (11 : Fin 14)) := by
  have hscaled : (2 : ℝ) ^ 80 *
      profile (centeredStep (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      alphaEleven * FirstHighTwelve.b3 + SharpWordNorm.rho ^ (3 : ℕ) * ((1 : ℝ) / 250) := by
    calc
      _ ≤ (2 : ℝ) ^ 80 *
          (alphaEleven * profile (error 1 b) (12 : Fin 14) +
            SharpWordNorm.rho ^ (3 : ℕ) *
              l2 (restrictSupport 3 (boundaryInput (component (error 1 b) (13 : Fin 14))))) :=
        mul_le_mul_of_nonneg_left (one_source_eleven_le_event b hb) (by positivity)
      _ = alphaEleven * ((2 : ℝ) ^ 80 * profile (error 1 b) (12 : Fin 14)) +
          SharpWordNorm.rho ^ (3 : ℕ) * ((2 : ℝ) ^ 80 *
            l2 (restrictSupport 3 (boundaryInput (component (error 1 b) (13 : Fin 14))))) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (FirstHighTwelve.component_twelve_scaled_le b hb)
          (FirstHighSeveralSource.old_coefficient_nonneg 11 12))
        (mul_le_mul_of_nonneg_left (event_length_le_of_moment b k a hsource hmoment)
          (pow_nonneg (by norm_num [SharpWordNorm.rho]) 3))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ) ^ 41 * (2 : ℝ) ^ 80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have htotal : NormalizedProfile.factor 1 *
      profile (centeredStep (SupportEvolution.highPart (error 1 b))) (11 : Fin 14) ≤
      (1000 * g (11 : Fin 14)) * d (11 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_eleven_le
  calc
    _ ≤ ((1000 * g (11 : Fin 14)) * d (11 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using htotal
    _ = _ := by ring

end SufficientMoment
end AES8.FirstHighSupportEvent
