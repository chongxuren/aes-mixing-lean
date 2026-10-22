import AESConcrete.ReturnMiddleEnergy
import AESConcrete.Return13_12Scalar
import AESConcrete.RefinedChannelCommutation
import AESConcrete.FirstHighReturn
import AESConcrete.MDSGraphFirstCap
import AESConcrete.DirectIncidenceStepCaps

/-!
# Direct physical two-step bridge for return (13,12)

All identities below use the existing physical blocks and the actual
wordMixAddEquiv, in their original order. The three nonzero-uniform factors
are expanded separately: source insertion, intermediate extraction,
intermediate output insertion. Signed joint three-coordinate inputs are
retained throughout. Input Pythagoras and two finite Cauchy--Schwarz estimates
supply factor 8; no output orthogonality is asserted. The exact scalar
certificate is a separate imported component.

Fixed independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference and AES10/14/16.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.Return13_12Composition
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.NonzeroUniformGraphCap
open AESConcrete.ReturnMiddleGeometry (leg extractLeg sum_insert)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.CenteredWordStepZeros (compose_assoc centeredWordStepKernel)
open AESConcrete.PhysicalProjectionSystem (system step_eq_physical)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)

abbrev Word := AES.Word
abbrev Three := Fin 3 → Word

def sourceProjection : AES.WordState → AES.WordState → ℝ :=
  refinedKernel (0 : Word) 3 4

def threeResidual : Three → Three → ℝ :=
  coordinateKernel (fun _ : Fin 3 => residualMatrix AES.wordSuperboxKernel 0)

/-- Three different rank-one factors, with both physical diffusions retained. -/
def response (r s : Fin 4) (source extract output : Word → ℝ)
    (h : Three → ℝ) : AES.WordState → ℝ :=
  action residualStepKernel (rankOneLeg r output
    (action threeResidual (extractLeg extract r
      (fun z => rankOneLeg s source h (wordMixAddEquiv.symm z)))))

def normalizationSquare : ℝ := 65537 ^ 2 / (4294967296 - 1)
def branchSquare : ℝ := (rho ^ 5 * kappa) ^ 2
def branchCap : ℝ := rho ^ 5 * kappa * Return13_12Scalar.normalizationCube

section FiniteLinearAlgebra

theorem action_sub_div {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (a d : ℝ) (f g : X → ℝ) :
    action K (fun x => (a * f x - g x) / d) =
      fun y => (a * action K f y - action K g y) / d := by
  funext y
  unfold action
  calc
    _ = ∑ x, (a * (K y x * f x) - K y x * g x) / d := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem action_selected_sum {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (f : SupportIndex 3 → X → ℝ) :
    action K (fun x => ∑ p ∈ selectedSupport3, f p x) =
      fun y => ∑ p ∈ selectedSupport3, action K (f p) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

theorem rankOneLeg_sub_div_joint (r : Fin 4) (v : Word → ℝ)
    (a d : ℝ) (f g : Three → ℝ) :
    rankOneLeg r v (fun x => (a * f x - g x) / d) =
      fun x => (a * rankOneLeg r v f x - rankOneLeg r v g x) / d := by
  funext x
  simp only [rankOneLeg]
  ring

theorem rankOneLeg_sub_div_vector (r : Fin 4) (a d : ℝ)
    (u v : Word → ℝ) (h : Three → ℝ) :
    rankOneLeg r (fun x => (a * u x - v x) / d) h =
      fun x => (a * rankOneLeg r u h x - rankOneLeg r v h x) / d := by
  funext x
  simp only [rankOneLeg]
  ring

theorem extractLeg_sub_div_input (v : Word → ℝ) (r : Fin 4) (a d : ℝ)
    (f g : AES.WordState → ℝ) :
    extractLeg v r (fun x => (a * f x - g x) / d) =
      fun w => (a * extractLeg v r f w - extractLeg v r g w) / d := by
  funext w
  unfold extractLeg
  calc
    _ = ∑ t, (a * (v t * f (Fin.insertNth r t w)) -
        v t * g (Fin.insertNth r t w)) / d := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem extractLeg_sub_div_vector (r : Fin 4) (a d : ℝ)
    (u v : Word → ℝ) (f : AES.WordState → ℝ) :
    extractLeg (fun x => (a * u x - v x) / d) r f =
      fun w => (a * extractLeg u r f w - extractLeg v r f w) / d := by
  funext w
  unfold extractLeg
  calc
    _ = ∑ t, (a * (u t * f (Fin.insertNth r t w)) -
        v t * f (Fin.insertNth r t w)) / d := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem extractLeg_rankOneLeg (r : Fin 4) (u : Word → ℝ)
    (hu : (∑ t, u t ^ 2) = 1) (h : Three → ℝ) :
    extractLeg u r (rankOneLeg r u h) = h := by
  funext w
  simp only [extractLeg, rankOneLeg, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  simp_rw [← mul_assoc, ← pow_two]
  rw [← Finset.sum_mul, hu, one_mul]

/-- Exact kernel splitting, including the genuine adjoint, for arbitrary
joint input. The three-coordinate tensor keeps r.succAbove labels. -/
theorem coordinateKernel_rank_leg_action
    (T : Fin 4 → Word → Word → ℝ) (r : Fin 4) (u : Word → ℝ)
    (hr : ∀ y x, T r y x = u y * u x) (f : AES.WordState → ℝ) :
    action (coordinateKernel T) f =
      rankOneLeg r u (action (coordinateKernel (fun i : Fin 3 => T (r.succAbove i)))
        (extractLeg u r f)) := by
  funext y
  have hp (t : Word) (w : Three) :
      coordinateKernel T y (Fin.insertNth r t w) =
        (u (y r) * u t) *
          ∏ i : Fin 3, T (r.succAbove i) (y (r.succAbove i)) (w i) := by
    rw [coordinateKernel, Fin.prod_univ_succAbove
      (fun i : Fin 4 => T i (y i) ((Fin.insertNth r t w : Fin 4 → Word) i)) r]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hr]
  change (∑ x, coordinateKernel T y x * f x) = _
  rw [sum_insert r (fun x => coordinateKernel T y x * f x)]
  simp_rw [hp]
  rw [Finset.sum_comm]
  change (∑ w : Three, ∑ t : Word,
    ((u (y r) * u t) *
      ∏ i : Fin 3, T (r.succAbove i) (y (r.succAbove i)) (w i)) *
        f (Fin.insertNth r t w)) =
    u (y r) * (∑ w : Three,
      (∏ i : Fin 3, T (r.succAbove i) (y (r.succAbove i)) (w i)) *
        ∑ t : Word, u t * f (Fin.insertNth r t w))
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro t _
  ring

end FiniteLinearAlgebra

section ThreeNormalizations

theorem word_nonzero_decomposition :
    (nonzeroUniform : Word → ℝ) = fun x =>
      (65536 * fullUniform x - zeroUnit x) / Real.sqrt (4294967296 - 1) := by
  have hn : 1 < Fintype.card Word := by rw [AES.word_card]; norm_num
  have hs : Real.sqrt (Fintype.card Word : ℝ) = 65536 := by
    rw [AES.word_card]
    norm_num only [Nat.cast_ofNat]
    rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hc : (Fintype.card Word : ℝ) = 4294967296 := by
    rw [AES.word_card]
    norm_num
  funext x
  have he := nonzeroUniform_decomposition hn x
  rw [hs, hc] at he
  exact he

theorem response_source_sub_div (r s : Fin 4) (a d : ℝ)
    (u v extract output : Word → ℝ) (h : Three → ℝ) :
    response r s (fun x => (a * u x - v x) / d) extract output h =
      fun y => (a * response r s u extract output h y -
        response r s v extract output h y) / d := by
  unfold response
  rw [rankOneLeg_sub_div_vector, extractLeg_sub_div_input, action_sub_div,
    rankOneLeg_sub_div_joint, action_sub_div]

theorem response_extract_sub_div (r s : Fin 4) (a d : ℝ)
    (source u v output : Word → ℝ) (h : Three → ℝ) :
    response r s source (fun x => (a * u x - v x) / d) output h =
      fun y => (a * response r s source u output h y -
        response r s source v output h y) / d := by
  unfold response
  rw [extractLeg_sub_div_vector, action_sub_div,
    rankOneLeg_sub_div_joint, action_sub_div]

theorem response_output_sub_div (r s : Fin 4) (a d : ℝ)
    (source extract u v : Word → ℝ) (h : Three → ℝ) :
    response r s source extract (fun x => (a * u x - v x) / d) h =
      fun y => (a * response r s source extract u h y -
        response r s source extract v h y) / d := by
  unfold response
  rw [rankOneLeg_sub_div_vector, action_sub_div]

theorem response_source_nonzero (r s : Fin 4) (extract output : Word → ℝ)
    (h : Three → ℝ) :
    response r s nonzeroUniform extract output h = fun y =>
      (65536 * response r s fullUniform extract output h y -
        response r s zeroUnit extract output h y) / Real.sqrt (4294967296 - 1) := by
  rw [word_nonzero_decomposition, response_source_sub_div]

theorem response_extract_nonzero (r s : Fin 4) (source output : Word → ℝ)
    (h : Three → ℝ) :
    response r s source nonzeroUniform output h = fun y =>
      (65536 * response r s source fullUniform output h y -
        response r s source zeroUnit output h y) / Real.sqrt (4294967296 - 1) := by
  rw [word_nonzero_decomposition, response_extract_sub_div]

theorem response_output_nonzero (r s : Fin 4) (source extract : Word → ℝ)
    (h : Three → ℝ) :
    response r s source extract nonzeroUniform h = fun y =>
      (65536 * response r s source extract fullUniform h y -
        response r s source extract zeroUnit h y) / Real.sqrt (4294967296 - 1) := by
  rw [word_nonzero_decomposition, response_output_sub_div]

/-- The outer estimate uses either the actual ordinary zero-slab or actual
Fourier uniform-coordinate resource; it has no analytic hypothesis. -/
theorem outer_normalized_energy (r : Fin 4) (b : Bool) (h : Three → ℝ) :
    (∑ y, action residualStepKernel (rankOneLeg r (leg b) h) y ^ 2) ≤
      rho ^ 6 * kappa * ∑ x, h x ^ 2 := by
  have hn : 1 < Fintype.card Word := by rw [AES.word_card]; norm_num
  cases b
  · have he := MDSGraphEnergy.word_residual_zero_slab_energy r 0
      (rankOneLeg r zeroUnit h) (zeroUnit_leg_zero_slab r h)
    change (∑ y, action residualTensor
      (fun z => rankOneLeg r zeroUnit h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at he
    rw [← residualStep_action, rankOneLeg_energy r zeroUnit zeroUnit_energy h] at he
    exact he
  · have he := FourierGraphEnergy.word_residual_uniform_coordinate_energy r 0
      (rankOneLeg r fullUniform h) (fullUniform_leg_invariant r h)
    change (∑ y, action residualTensor
      (fun z => rankOneLeg r fullUniform h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at he
    rw [← residualStep_action,
      rankOneLeg_energy r fullUniform (fullUniform_energy hn) h] at he
    exact he

/-- All eight normalized choices share one bound on the same signed h. -/
theorem normalized_response_energy (r s : Fin 4) (a b c : Bool) (h : Three → ℝ) :
    (∑ y, response r s (leg a) (leg b) (leg c) h y ^ 2) ≤
      branchSquare * ∑ x, h x ^ 2 := by
  have hout := outer_normalized_energy r c
    (ReturnMiddleEnergy.middleResponse r s a b h)
  have hmid : (∑ x, ReturnMiddleEnergy.middleResponse r s a b h x ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := ReturnMiddleEnergy.middle_energy r s a b h
  change (∑ y, response r s (leg a) (leg b) (leg c) h y ^ 2) ≤
    rho ^ 6 * kappa * ∑ x, ReturnMiddleEnergy.middleResponse r s a b h x ^ 2 at hout
  have he := hout.trans (mul_le_mul_of_nonneg_left hmid
    (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg))
  calc
    _ ≤ rho ^ 6 * kappa * (rho ^ 4 * kappa * ∑ x, h x ^ 2) := he
    _ = branchSquare * ∑ x, h x ^ 2 := by
      unfold branchSquare
      ring

theorem normalization_sqrt_sq :
    (Real.sqrt (4294967296 - 1 : ℝ)) ^ 2 = 4294967296 - 1 :=
  Real.sq_sqrt (by norm_num)

/-- First expansion: source insertion. -/
theorem source_nonzero_response_energy (r s : Fin 4) (b c : Bool) (h : Three → ℝ) :
    (∑ y, response r s nonzeroUniform (leg b) (leg c) h y ^ 2) ≤
      (normalizationSquare * branchSquare) * ∑ x, h x ^ 2 := by
  rw [response_source_nonzero]
  have he := weighted_sub_energy
    (response r s fullUniform (leg b) (leg c) h)
    (response r s zeroUnit (leg b) (leg c) h)
    65536 (Real.sqrt (4294967296 - 1)) branchSquare (∑ x, h x ^ 2)
    (by norm_num) (normalized_response_energy r s true b c h)
    (normalized_response_energy r s false b c h)
  rw [normalization_sqrt_sq] at he
  convert he using 1 <;> dsimp [normalizationSquare] <;> ring

/-- Second expansion: intermediate extraction, rather than a new input. -/
theorem extract_nonzero_response_energy (r s : Fin 4) (c : Bool) (h : Three → ℝ) :
    (∑ y, response r s nonzeroUniform nonzeroUniform (leg c) h y ^ 2) ≤
      (normalizationSquare ^ 2 * branchSquare) * ∑ x, h x ^ 2 := by
  rw [response_extract_nonzero]
  have he := weighted_sub_energy
    (response r s nonzeroUniform fullUniform (leg c) h)
    (response r s nonzeroUniform zeroUnit (leg c) h)
    65536 (Real.sqrt (4294967296 - 1)) (normalizationSquare * branchSquare)
    (∑ x, h x ^ 2) (by norm_num)
    (source_nonzero_response_energy r s true c h)
    (source_nonzero_response_energy r s false c h)
  rw [normalization_sqrt_sq] at he
  convert he using 1 <;> dsimp [normalizationSquare] <;> ring

theorem branchCap_nonneg : 0 ≤ branchCap :=
  mul_nonneg (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg)
    Return13_12Scalar.normalizationCube_nonneg

theorem branchCap_sq : branchCap ^ 2 = normalizationSquare ^ 3 * branchSquare := by
  have hn : normalizationSquare = (65537 : ℝ) / 65535 := by
    norm_num [normalizationSquare]
  rw [branchCap, mul_pow, Return13_12Scalar.normalizationCube_sq, hn]
  dsimp [branchSquare]
  ring

/-- Third expansion: output insertion. All three original u factors remain
visible in the left side; there is no desired-energy premise. -/
theorem nonzero_response_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ y, response r s nonzeroUniform nonzeroUniform nonzeroUniform h y ^ 2) ≤
      branchCap ^ 2 * ∑ x, h x ^ 2 := by
  rw [response_output_nonzero, branchCap_sq]
  have he := weighted_sub_energy
    (response r s nonzeroUniform nonzeroUniform fullUniform h)
    (response r s nonzeroUniform nonzeroUniform zeroUnit h)
    65536 (Real.sqrt (4294967296 - 1)) (normalizationSquare ^ 2 * branchSquare)
    (∑ x, h x ^ 2) (by norm_num)
    (extract_nonzero_response_energy r s true h)
    (extract_nonzero_response_energy r s false h)
  rw [normalization_sqrt_sq] at he
  convert he using 1 <;> dsimp [normalizationSquare] <;> ring

end ThreeNormalizations

section PhysicalSupportInterface

-- This finite shape identifies the physical absent-residual coordinate;
-- unlike a fresh projection model it is a property of selectedSupport3.
set_option maxRecDepth 100000 in
theorem selected_support_shape : ∀ p : SupportIndex 3, p ∈ selectedSupport3 →
    ∃ r : Fin 4,
      (∀ i, AES.maskBit p.val.1 i = decide (i ≠ r)) ∧
      (∀ i, AES.maskBit p.val.2 i = false) := by decide

def uniformCoordinate (p : SupportIndex 3) : Fin 4 :=
  if hp : p ∈ selectedSupport3 then Classical.choose (selected_support_shape p hp) else 0

theorem uniformCoordinate_shape (p : SupportIndex 3) (hp : p ∈ selectedSupport3) :
    (∀ i, AES.maskBit p.val.1 i = decide (i ≠ uniformCoordinate p)) ∧
    (∀ i, AES.maskBit p.val.2 i = false) := by
  simpa only [uniformCoordinate, dif_pos hp] using
    (Classical.choose_spec (selected_support_shape p hp))

/-- Canonical joint input. Only its distinguished leg is factored. -/
def sourceJoint (p : SupportIndex 3) (f : AES.WordState → ℝ) : Three → ℝ :=
  extractLeg nonzeroUniform (uniformCoordinate p)
    (supportIndexComponent (0 : Word) p f)

theorem source_piece_rank (p : SupportIndex 3) (hp : p ∈ selectedSupport3)
    (f : AES.WordState → ℝ) :
    supportIndexComponent (0 : Word) p f =
      rankOneLeg (uniformCoordinate p) nonzeroUniform (sourceJoint p f) := by
  have hs := uniformCoordinate_shape p hp
  have hm : AES.maskBit p.val.1 (uniformCoordinate p) = false := by
    simpa only [ne_eq, not_true_eq_false, decide_false] using hs.1 (uniformCoordinate p)
  have hn : 1 < Fintype.card Word := by rw [AES.word_card]; norm_num
  obtain ⟨h, hh, _⟩ := supportIndexComponent_nonzero_uniform p (uniformCoordinate p)
    hm (hs.2 _) hn f
  have hj : sourceJoint p f = h := by
    rw [sourceJoint, hh, extractLeg_rankOneLeg _ _ (nonzeroUniform_energy hn)]
  rw [hj]
  exact hh

theorem source_joint_energy (p : SupportIndex 3) (hp : p ∈ selectedSupport3)
    (f : AES.WordState → ℝ) :
    (∑ x, sourceJoint p f x ^ 2) =
      ∑ x, supportIndexComponent (0 : Word) p f x ^ 2 := by
  rw [source_piece_rank p hp]
  exact (rankOneLeg_energy _ _
    (nonzeroUniform_energy (by rw [AES.word_card]; norm_num)) _).symm

theorem source_joint_energy_sum (f : AES.WordState → ℝ) :
    (∑ p ∈ selectedSupport3, ∑ x, sourceJoint p f x ^ 2) ≤ ∑ x, f x ^ 2 := by
  calc
    _ = ∑ p ∈ selectedSupport3,
        ∑ x, supportIndexComponent (0 : Word) p f x ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact source_joint_energy p hp f
    _ ≤ _ := selected_input_energy_le 0 (by rw [AES.word_card]; norm_num) f

theorem source_projection_rank_sum (f : AES.WordState → ℝ) :
    action sourceProjection f = fun x => ∑ p ∈ selectedSupport3,
      rankOneLeg (uniformCoordinate p) nonzeroUniform (sourceJoint p f) x := by
  rw [sourceProjection, refined_three_four_action_sum]
  funext x
  apply Finset.sum_congr rfl
  intro p hp
  exact congrFun (source_piece_rank p hp f) x

/-- Actual selected output piece after the actual parallel superboxes. The
three remaining channels are residual channels, not residual projections. -/
theorem selected_channel_piece (p : SupportIndex 3) (hp : p ∈ selectedSupport3)
    (f : AES.WordState → ℝ) :
    supportIndexComponent (0 : Word) p (action AES.parallelSuperboxKernel f) =
      rankOneLeg (uniformCoordinate p) nonzeroUniform
        (action threeResidual (extractLeg nonzeroUniform (uniformCoordinate p) f)) := by
  let r := uniformCoordinate p
  have hs := uniformCoordinate_shape p hp
  have hker : kernelCompose (supportIndexKernel (0 : Word) p) AES.parallelSuperboxKernel =
      coordinateKernel (fun i : Fin 4 => if i = r then constantMatrix (0 : Word)
        else residualMatrix AES.wordSuperboxKernel 0) := by
    change kernelCompose (coordinateKernel (fun i =>
      supportPiece (0 : Word) (AES.maskBit p.val.1 i) (AES.maskBit p.val.2 i)))
        (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel)) = _
    rw [coordinateKernel_compose]
    congr 1
    funext i
    rw [hs.1 i, hs.2 i]
    by_cases hi : i = r
    · have hm : decide (i ≠ uniformCoordinate p) = false := by
        have he : i = uniformCoordinate p := hi
        simp [he]
      rw [hm, if_pos hi]
      change kernelCompose (constantMatrix (0 : Word)) AES.wordSuperboxKernel =
        constantMatrix (0 : Word)
      exact RefinedChannelCommutation.pointed_constant_left AES.word_superbox_pointed
    · have hn : i ≠ uniformCoordinate p := hi
      have hm : decide (i ≠ uniformCoordinate p) = true := by simp [hn]
      rw [hm, if_neg hi]
      change kernelCompose (residualProjection (0 : Word)) AES.wordSuperboxKernel =
        residualMatrix AES.wordSuperboxKernel 0
      exact FourResidualStep.pointed_residual_left _ _ AES.word_superbox_pointed
  rw [← supportIndexKernel_action, ← kernelCompose_action, hker]
  have he := coordinateKernel_rank_leg_action
    (fun i : Fin 4 => if i = r then constantMatrix (0 : Word)
      else residualMatrix AES.wordSuperboxKernel 0) r nonzeroUniform
    (by
      intro y x
      simp only [if_pos rfl]
      exact nonzeroConstantMatrix_rank_one (by rw [AES.word_card]; norm_num) y x) f
  simpa [threeResidual, r, Fin.succAbove_ne] using he

theorem projected_channel_action (f : AES.WordState → ℝ) :
    action sourceProjection (action AES.parallelSuperboxKernel f) = fun x =>
      ∑ p ∈ selectedSupport3, rankOneLeg (uniformCoordinate p) nonzeroUniform
        (action threeResidual (extractLeg nonzeroUniform (uniformCoordinate p) f)) x := by
  rw [sourceProjection, refined_three_four_action_sum]
  funext x
  apply Finset.sum_congr rfl
  intro p hp
  exact congrFun (selected_channel_piece p hp f) x

theorem source_projection_idempotent (f : AES.WordState → ℝ) :
    action sourceProjection (action sourceProjection f) = action sourceProjection f := by
  rw [← kernelCompose_action]
  change action (kernelCompose (refinedKernel (0 : Word) 3 4)
    (refinedKernel (0 : Word) 3 4)) f = _
  rw [RefinedProjectionCompleteness.refined_compose 0
    (by rw [AES.word_card]; norm_num)]
  rfl

theorem source_projection_centering_zero :
    kernelCompose sourceProjection (DegreeCentering.globalUniformKernel (0 : Word)) = 0 := by
  have hn : 1 < Fintype.card Word := by rw [AES.word_card]; norm_num
  calc
    _ = kernelCompose (kernelCompose sourceProjection (degreeKernel (0 : Word) 3))
        (DegreeCentering.globalUniformKernel (0 : Word)) := by
      rw [sourceProjection, refinedKernel_compose_degreeKernel 0 hn]
    _ = kernelCompose sourceProjection (kernelCompose (degreeKernel (0 : Word) 3)
        (DegreeCentering.globalUniformKernel (0 : Word))) := (compose_assoc _ _ _).symm
    _ = 0 := by
      rw [DegreeCentering.degreeKernel_compose_globalUniformKernel 0 hn 3 (by decide)]
      funext y x
      simp [kernelCompose]

theorem projected_centering_removed (f : AES.WordState → ℝ) :
    action sourceProjection (action centeredWordStepKernel f) =
      action sourceProjection (action WordStepZeros.wordStepKernel f) := by
  rw [← kernelCompose_action, ← kernelCompose_action, centeredWordStepKernel,
    CenteredWordStepZeros.compose_sub_right, source_projection_centering_zero, sub_zero]

/-- Exact physical composition before the two support sums. The inner M is
the pullback below; the outer M remains inside residualStepKernel. -/
theorem physical_composition_action (f : AES.WordState → ℝ) :
    action (kernelCompose (physicalBlock 13 12) (physicalBlock 12 12)) f =
      action residualStepKernel (action sourceProjection
        (action AES.parallelSuperboxKernel
          (fun z => action sourceProjection f (wordMixAddEquiv.symm z)))) := by
  have hmid : physicalBlock 12 12 = kernelCompose sourceProjection
      (kernelCompose centeredWordStepKernel sourceProjection) := rfl
  rw [kernelCompose_action, FourResidualStep.physical_thirteen_kernel, hmid]
  change action (kernelCompose residualStepKernel sourceProjection)
    (action (kernelCompose sourceProjection (kernelCompose centeredWordStepKernel
      sourceProjection)) f) = _
  simp only [kernelCompose_action]
  rw [source_projection_idempotent, projected_centering_removed,
    WordStepZeros.wordStepKernel_action]

end PhysicalSupportInterface

section PhysicalAggregation

theorem rankOneLeg_selected_sum (r : Fin 4) (u : Word → ℝ)
    (h : SupportIndex 3 → Three → ℝ) :
    rankOneLeg r u (fun w => ∑ p ∈ selectedSupport3, h p w) =
      fun x => ∑ p ∈ selectedSupport3, rankOneLeg r u (h p) x := by
  funext x
  simp only [rankOneLeg, Finset.mul_sum]

theorem extractLeg_selected_sum (u : Word → ℝ) (r : Fin 4)
    (f : SupportIndex 3 → AES.WordState → ℝ) :
    extractLeg u r (fun x => ∑ p ∈ selectedSupport3, f p x) =
      fun w => ∑ p ∈ selectedSupport3, extractLeg u r (f p) w := by
  funext w
  simp only [extractLeg, Finset.mul_sum]
  exact Finset.sum_comm

/-- Both support labels belong to the actual four-element selected family.
The same sourceJoint s f is used for every middle label p and all branches. -/
theorem physical_composition_response_sum (f : AES.WordState → ℝ) :
    action (kernelCompose (physicalBlock 13 12) (physicalBlock 12 12)) f =
      fun y => ∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3,
        response (uniformCoordinate p) (uniformCoordinate s)
          nonzeroUniform nonzeroUniform nonzeroUniform (sourceJoint s f) y := by
  rw [physical_composition_action, projected_channel_action, action_selected_sum]
  have he (p : SupportIndex 3) :
      action residualStepKernel (rankOneLeg (uniformCoordinate p) nonzeroUniform
        (action threeResidual (extractLeg nonzeroUniform (uniformCoordinate p)
          (fun z => action sourceProjection f (wordMixAddEquiv.symm z))))) =
        fun y => ∑ s ∈ selectedSupport3,
          response (uniformCoordinate p) (uniformCoordinate s)
            nonzeroUniform nonzeroUniform nonzeroUniform (sourceJoint s f) y := by
    rw [source_projection_rank_sum, extractLeg_selected_sum, action_selected_sum,
      rankOneLeg_selected_sum, action_selected_sum]
    rfl
  funext y
  apply Finset.sum_congr rfl
  intro p _
  exact congrFun (he p) y

/-- Two finite Cauchy--Schwarz bounds are used only for output sums. -/
theorem selected_double_sum_sq_le (a : SupportIndex 3 → SupportIndex 3 → ℝ) :
    (∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3, a p s) ^ 2 ≤
      16 * ∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3, a p s ^ 2 := by
  calc
    _ ≤ 4 * ∑ p ∈ selectedSupport3,
        (∑ s ∈ selectedSupport3, a p s) ^ 2 :=
      selected_sum_sq_le (fun p => ∑ s ∈ selectedSupport3, a p s)
    _ ≤ 4 * ∑ p ∈ selectedSupport3,
        4 * ∑ s ∈ selectedSupport3, a p s ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro p _
      exact selected_sum_sq_le (a p)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Four intermediate labels times the source square-root count of four
give norm factor 8. Output orthogonality is unnecessary. -/
theorem selected_response_energy (h : SupportIndex 3 → Three → ℝ) :
    (∑ y, (∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3,
      response (uniformCoordinate p) (uniformCoordinate s)
        nonzeroUniform nonzeroUniform nonzeroUniform (h s) y) ^ 2) ≤
      (8 * branchCap) ^ 2 * ∑ s ∈ selectedSupport3, ∑ x, h s x ^ 2 := by
  let F := fun p s y => response (uniformCoordinate p) (uniformCoordinate s)
    nonzeroUniform nonzeroUniform nonzeroUniform (h s) y
  change (∑ y, (∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3, F p s y) ^ 2) ≤ _
  calc
    _ ≤ ∑ y, 16 * ∑ p ∈ selectedSupport3,
        ∑ s ∈ selectedSupport3, F p s y ^ 2 :=
      Finset.sum_le_sum (fun y _ => selected_double_sum_sq_le (fun p s => F p s y))
    _ = 16 * ∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3,
        ∑ y, F p s y ^ 2 := by
      rw [← Finset.mul_sum]
      apply congrArg (fun z : ℝ => 16 * z)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ ≤ 16 * ∑ p ∈ selectedSupport3, ∑ s ∈ selectedSupport3,
        branchCap ^ 2 * ∑ x, h s x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro s _
      exact nonzero_response_energy _ _ _
    _ = _ := by
      rw [Finset.sum_const, selectedSupport3_card]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      rw [← Finset.mul_sum]
      ring

theorem physical_composition_energy (f : AES.WordState → ℝ) :
    (∑ y, action (kernelCompose (physicalBlock 13 12) (physicalBlock 12 12)) f y ^ 2) ≤
      Return13_12Scalar.B ^ 2 * ∑ x, f x ^ 2 := by
  rw [physical_composition_response_sum]
  have he := (selected_response_energy (fun s => sourceJoint s f)).trans
    (mul_le_mul_of_nonneg_left (source_joint_energy_sum f) (sq_nonneg (8 * branchCap)))
  calc
    _ ≤ (8 * branchCap) ^ 2 * ∑ x, f x ^ 2 := he
    _ = Return13_12Scalar.B ^ 2 * ∑ x, f x ^ 2 := by
      unfold Return13_12Scalar.B branchCap
      ring

/--
Requested actual system bound, obtained without a composition-energy or
desired-identity hypothesis.
-/
theorem system_composition_norm :
    ‖(system.step 13 12).comp (system.step 12 12)‖ ≤ Return13_12Scalar.B := by
  rw [step_eq_physical, step_eq_physical, ← PhysicalProjectionSystem.operator_compose]
  exact kernelOperator_norm_le _ Return13_12Scalar.B_nonneg physical_composition_energy

end PhysicalAggregation

section ReturnCertificate

theorem side_eleven_norm :
    ‖(system.step 13 11).comp (system.step 11 12)‖ ≤
      Return13_12Scalar.a * Return13_12Scalar.c := by
  have hA := MDSGraphFirstCap.system_thirteen_eleven_step_cap
  have hB := DirectIncidenceStepCaps.system_step_cap 11 12 (by decide)
  exact ((system.step 13 11).opNorm_comp_le (system.step 11 12)).trans
    (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

theorem side_thirteen_norm :
    ‖(system.step 13 13).comp (system.step 13 12)‖ ≤
      rho ^ 4 * Return13_12Scalar.b := by
  have hA := FirstHighReturn.system_step_thirteen_thirteen_norm
  have hB := NonzeroUniformGraphCap.system_thirteen_twelve_step_cap
  exact ((system.step 13 13).opNorm_comp_le (system.step 13 12)).trans
    (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

theorem system_return_bound :
    ‖system.ret 13 12‖ ≤ Return13_12Scalar.B +
      Return13_12Scalar.a * Return13_12Scalar.c + rho ^ 4 * Return13_12Scalar.b := by
  rw [FirstHighReturn.system_ret_eq_three_steps]
  calc
    _ ≤ (‖(system.step 13 11).comp (system.step 11 12)‖ +
        ‖(system.step 13 12).comp (system.step 12 12)‖) +
        ‖(system.step 13 13).comp (system.step 13 12)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Return13_12Scalar.a * Return13_12Scalar.c + Return13_12Scalar.B) +
        rho ^ 4 * Return13_12Scalar.b :=
      add_le_add (add_le_add side_eleven_norm system_composition_norm) side_thirteen_norm
    _ = _ := by ring

theorem system_return_strict :
    ‖system.ret 13 12‖ < AESRound.Terminal.lambda ^ 2 * AESRound.Certificate.J 13 12 :=
  system_return_bound.trans_lt Return13_12Scalar.return_scalar_lt

theorem system_return_cap :
    ‖system.ret 13 12‖ ≤ AESRound.Terminal.lambda ^ 2 * AESRound.Certificate.J 13 12 :=
  le_of_lt system_return_strict

end ReturnCertificate

end AESConcrete.Return13_12Composition
