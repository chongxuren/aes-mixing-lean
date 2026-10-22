import AESConcrete.FourResidualStep
import AESConcrete.WordChannelCommutation

/-!
# Whole-word degree damping for the actual physical step

Candidate extension of the accepted four-residual bound. A pointed channel
with residual energy coefficient ν contracts each whole-coordinate degree d
by ν^d. The proof tensors individual activity/residual pieces on arbitrary
joint inputs, then uses the orthogonality of the input and output patterns.
There is no product-law premise or square-root-of-pattern-count loss.

Positive degree on either the output or input side annihilates global
nonzero-state centering. The actual word permutation and both refined
projections then preserve the energy bound. At ν=21/131072 this meets the
frozen step certificate exactly in column 13 among the positive-degree rows.
Positive input degree also gives bound one for degree-zero output, closing
rows 0, 1, and 2 of that column. Thus thirteen of its fourteen cells follow;
row 3 remains open. No return or experiment bound is supplied.

The independent retained keys, whitening, omitted final MixColumns, ordered
distinct-pair law, and active 10/14/16 objective are unchanged. The separate
10/12/14 objective is untouched. Constructive mathematics only: no attacks,
manuscript edits, historical source edits, or local application workloads.
Compilation, source/object acceptance, and independent review remain separate.
-/

-- Local build-resource overlay: the finite cap classifier exceeded 1200000
-- heartbeats. Mathematical declarations are unchanged; wall timeout is retained.
set_option maxHeartbeats 0

noncomputable section
open scoped BigOperators

namespace AESConcrete.DegreeResidualStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordChannelCommutation
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_right compose_sub_left)
open AESConcrete.DegreeCentering (globalUniformKernel degreeKernel_compose_globalUniformKernel
  globalUniformKernel_compose_degreeKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The alphabet is generic: its concrete specialization below is a word. -/
def channelPiece (D : V → V → ℝ) (z : V) (b : Bool) : V → V → ℝ :=
  if b then residualMatrix D z else activityMatrix z

def pieceBound (ν : ℝ) (b : Bool) : ℝ := if b then ν else 1

theorem pointed_piece_right (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (b : Bool) :
    kernelCompose D (degreePiece z b) = channelPiece D z b := by
  cases b
  · exact pointed_activity_right hD
  · change kernelCompose D (degreePiece z true) = residualMatrix D z
    rw [pointed_degreePiece_commutes hD true]
    exact FourResidualStep.pointed_residual_left D z hD

theorem channelPiece_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (b : Bool) (f : V → ℝ) :
    (∑ y, action (channelPiece D z b) f y ^ 2) ≤
      pieceBound ν b ^ 2 * ∑ x, f x ^ 2 := by
  cases b
  · exact activityMatrix_energy z hn f
  · exact hν f

theorem pieceBound_product (ν : ℝ) (a : Fin 4 → Bool) :
    (∏ i, pieceBound ν (a i)) = ν ^ residualDegree a := by
  simp [pieceBound, residualDegree, Finset.prod_ite]

theorem pattern_right (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (a : Fin 4 → Bool) :
    kernelCompose (coordinateKernel (fun _ : Fin 4 => D)) (productProjection z a) =
      coordinateKernel (fun i => channelPiece D z (a i)) := by
  change kernelCompose (coordinateKernel (fun _ : Fin 4 => D))
    (coordinateKernel (fun i => degreePiece z (a i))) = _
  rw [coordinateKernel_compose]
  simp_rw [pointed_piece_right D z hD]

theorem pattern_commutes (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (a : Fin 4 → Bool)
    (f : (Fin 4 → V) → ℝ) :
    action (coordinateKernel (fun _ : Fin 4 => D))
        (action (productProjection z a) f) =
      action (productProjection z a)
        (action (coordinateKernel (fun _ : Fin 4 => D)) f) := by
  rw [← kernelCompose_action, ← kernelCompose_action,
    coordinate_pattern_commutes (fun _ : Fin 4 => hD)]

/-- A pattern is charged against its own projected input energy. -/
theorem pattern_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (a : Fin 4 → Bool)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => D))
      (action (productProjection z a) f) y ^ 2) ≤
      (ν ^ residualDegree a) ^ 2 * ∑ x, action (productProjection z a) f x ^ 2 := by
  let g := action (productProjection z a) f
  have hproj : action (productProjection z a) g = g := by
    change action (productProjection z a) (action (productProjection z a) f) = _
    rw [← kernelCompose_action, productProjection_compose z hn]
    simp only [if_true]
    rfl
  have he := four_coordinate_energy
    (fun i => channelPiece D z (a i)) (fun i => pieceBound ν (a i))
    (fun i => channelPiece_energy D z hn ν hν (a i)) g
  rw [pieceBound_product, ← pattern_right D z hD a,
    kernelCompose_action, hproj] at he
  exact he

/-- Generic lifting of the inherited byte-degree proof to an arbitrary
alphabet and an explicitly supplied residual coefficient. -/
theorem degree_input_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => D))
      (degreeComponent z d f) y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, degreeComponent z d f x ^ 2 := by
  rw [coordinate_degree_commutes (fun _ : Fin 4 => hD),
    degreeComponent_energy z hn, degreeComponent_energy z hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : degreeIndex a = d
  · simp only [ha, if_true]
    have hd : residualDegree a = d.val := congrArg Fin.val ha
    simpa only [← pattern_commutes D z hD a f, hd] using
      pattern_energy D z hn hD ν hν a f
  · simp [ha]

theorem degree_parallel_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (degreeKernel z d)
      (coordinateKernel (fun _ : Fin 4 => D))) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  rw [kernelCompose_action, degreeKernel_action,
    ← coordinate_degree_commutes (fun _ : Fin 4 => hD)]
  exact (degree_input_energy D z hn hD ν hν d f).trans
    (mul_le_mul_of_nonneg_left (degreeComponent_energy_le z hn d f) (sq_nonneg _))

def centeredPermutedKernel (D : V → V → ℝ) (z : V)
    (e : Equiv.Perm (Fin 4 → V)) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x)) - globalUniformKernel z

private theorem compose_input_relabel {W : Type*} [Fintype W]
    (P K : W → W → ℝ) (e : W → W) :
    kernelCompose P (fun y x => K y (e x)) =
      fun y x => kernelCompose P K y (e x) := rfl

theorem degree_centered_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d : Fin 5) (hd : d ≠ 0)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (degreeKernel z d)
      (centeredPermutedKernel D z e)) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  unfold centeredPermutedKernel
  rw [compose_sub_right, degreeKernel_compose_globalUniformKernel z hn d hd,
    sub_zero, compose_input_relabel, FourResidualStep.input_permutation_action]
  have he := degree_parallel_energy D z hn hD ν hν d (fun x => f (e.symm x))
  rw [Equiv.sum_comp e.symm (fun x => f x ^ 2)] at he
  exact he

/-- Both refinements are the existing exact-support projections. -/
theorem refined_centered_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d a j b : Fin 5) (hd : d ≠ 0)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel z d a)
      (kernelCompose (centeredPermutedKernel D z e) (refinedKernel z j b))) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  let g := action (refinedKernel z j b) f
  let t := action (centeredPermutedKernel D z e) g
  have hinsert : action (refinedKernel z d a) t =
      action (refinedKernel z d a) (action (degreeKernel z d) t) := by
    exact (congrArg (fun K => action K t)
      (refinedKernel_compose_degreeKernel z hn d a)).symm.trans
      (kernelCompose_action (refinedKernel z d a) (degreeKernel z d) t)
  have hcore := degree_centered_energy D z hn hD ν hν d hd e g
  rw [kernelCompose_action] at hcore
  rw [kernelCompose_action, kernelCompose_action]
  change (∑ y, action (refinedKernel z d a) t y ^ 2) ≤ _
  rw [hinsert]
  exact (FourResidualStep.refined_energy_le z hn d a (action (degreeKernel z d) t)).trans
    (hcore.trans (mul_le_mul_of_nonneg_left
      (FourResidualStep.refined_energy_le z hn j b f) (sq_nonneg _)))

/-- The raw permuted channel needs no positive-degree condition. -/
theorem degree_permuted_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (degreeKernel z d)
      (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x))) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  rw [compose_input_relabel, FourResidualStep.input_permutation_action]
  have he := degree_parallel_energy D z hn hD ν hν d (fun x => f (e.symm x))
  rw [Equiv.sum_comp e.symm (fun x => f x ^ 2)] at he
  exact he

theorem refined_permuted_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d a j b : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel z d a)
      (kernelCompose (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x))
        (refinedKernel z j b))) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  let g := action (refinedKernel z j b) f
  let t := action (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x)) g
  have hinsert : action (refinedKernel z d a) t =
      action (refinedKernel z d a) (action (degreeKernel z d) t) := by
    exact (congrArg (fun K => action K t)
      (refinedKernel_compose_degreeKernel z hn d a)).symm.trans
      (kernelCompose_action (refinedKernel z d a) (degreeKernel z d) t)
  have hcore := degree_permuted_energy D z hn hD ν hν d e g
  rw [kernelCompose_action] at hcore
  rw [kernelCompose_action, kernelCompose_action]
  change (∑ y, action (refinedKernel z d a) t y ^ 2) ≤ _
  rw [hinsert]
  exact (FourResidualStep.refined_energy_le z hn d a (action (degreeKernel z d) t)).trans
    (hcore.trans (mul_le_mul_of_nonneg_left
      (FourResidualStep.refined_energy_le z hn j b f) (sq_nonneg _)))

/-- Positive input degree cancels the global uniform term before the raw
permuted-channel estimate, including when the output degree is zero. -/
theorem globalUniformKernel_compose_refined_positive (z : V)
    (hn : 1 < Fintype.card V) (j b : Fin 5) (hj : j ≠ 0) :
    kernelCompose (globalUniformKernel z) (refinedKernel z j b) = 0 := by
  calc
    _ = kernelCompose (globalUniformKernel z)
        (kernelCompose (degreeKernel z j) (refinedKernel z j b)) := by
      rw [degreeKernel_compose_refinedKernel z hn j b]
    _ = kernelCompose (kernelCompose (globalUniformKernel z) (degreeKernel z j))
        (refinedKernel z j b) := compose_assoc _ _ _
    _ = 0 := by
      rw [globalUniformKernel_compose_degreeKernel z hn j hj]
      funext y x
      simp [kernelCompose]

theorem refined_centered_energy_of_input_positive (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d a j b : Fin 5) (hj : j ≠ 0)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel z d a)
      (kernelCompose (centeredPermutedKernel D z e) (refinedKernel z j b))) f y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, f x ^ 2 := by
  unfold centeredPermutedKernel
  rw [compose_sub_left, globalUniformKernel_compose_refined_positive z hn j b hj, sub_zero]
  exact refined_permuted_energy D z hn hD ν hν d a j b e f

-- Specialize by exact terms. Keeping all algebra above generic avoids the
-- expensive concrete-state reduction observed in the four-residual build.
theorem physical_degree_energy (i j : Fin 14) (hi : (blockType i).1 ≠ 0)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      ((21/131072 : ℝ) ^ (blockType i).1.val) ^ 2 * ∑ x, f x ^ 2 := by
  exact refined_centered_energy AES.wordSuperboxKernel (0 : AES.Word)
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed (21/131072 : ℝ)
    SharpDampedWordNorm.word_superbox_residual_energy
    (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2 hi
    wordMixAddEquiv.toEquiv f

theorem physical_degree_norm (i j : Fin 14) (hi : (blockType i).1 ≠ 0) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ (21/131072 : ℝ) ^ (blockType i).1.val :=
  kernelOperator_norm_le _ (by positivity) (physical_degree_energy i j hi)

theorem physical_input_positive_degree_energy (i j : Fin 14)
    (hj : (blockType j).1 ≠ 0) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      ((21/131072 : ℝ) ^ (blockType i).1.val) ^ 2 * ∑ x, f x ^ 2 := by
  exact refined_centered_energy_of_input_positive AES.wordSuperboxKernel (0 : AES.Word)
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed (21/131072 : ℝ)
    SharpDampedWordNorm.word_superbox_residual_energy
    (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2 hj
    wordMixAddEquiv.toEquiv f

theorem physical_input_positive_degree_norm (i j : Fin 14)
    (hj : (blockType j).1 ≠ 0) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ (21/131072 : ℝ) ^ (blockType i).1.val :=
  kernelOperator_norm_le _ (by positivity) (physical_input_positive_degree_energy i j hj)

/-- This iff characterizes sufficiency of this uniform estimate, not the
unknown sharper norm of a block whose certificate cap is smaller. -/
theorem positive_uniform_cap_iff (i j : Fin 14) (hi : (blockType i).1 ≠ 0) :
    (21/131072 : ℝ) ^ (blockType i).1.val ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j ↔ j = 13 := by
  fin_cases i <;> norm_num [blockType] at hi
  all_goals
    fin_cases j <;>
      norm_num [blockType, AESRound.Terminal.lambda, AESRound.Certificate.L] <;> decide

/-- Ten positive-degree column-13 cells, including the already accepted
(13,13) cell. The nine additional cells have output indices 4 through 12. -/
theorem positive_column_thirteen_step_cap (i : Fin 14) (hi : (blockType i).1 ≠ 0) :
    ‖kernelOperator (physicalBlock i 13)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i 13 := by
  exact (physical_degree_norm i 13 hi).trans ((positive_uniform_cap_iff i 13 hi).mpr rfl)

theorem column_thirteen_uniform_cap_iff (i : Fin 14) :
    (21/131072 : ℝ) ^ (blockType i).1.val ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i 13 ↔ i ≠ 3 := by
  fin_cases i <;>
    norm_num [blockType, AESRound.Terminal.lambda, AESRound.Certificate.L] <;> decide

/-- Thirteen cells of the actual source-13 step column. Excluding row 3
records insufficiency of this bound, not failure of the actual certificate. -/
theorem column_thirteen_step_cap (i : Fin 14) (hi : i ≠ 3) :
    ‖kernelOperator (physicalBlock i 13)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i 13 := by
  exact (physical_input_positive_degree_norm i 13 (by decide)).trans
    ((column_thirteen_uniform_cap_iff i).mpr hi)

end AESConcrete.DegreeResidualStep
