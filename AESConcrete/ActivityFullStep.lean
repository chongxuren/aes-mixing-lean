import AESConcrete.ActivityRankOneStep
import AESConcrete.ActivityMDSCounts

/-!
# All activity-only centered step caps

This separate extension derives the raw activity kernel from the actual
degree-zero exact-support projections and the MDS graph counts. The pointed
parallel word channel is removed by its proved projection identity. Global
nonzero centering then leaves one signed rank-one kernel. Only after that
identity is established are the sixteen frozen scalar entries checked.

Constructive mathematics only; no attacks, manuscript or historical edits,
goals, schedules, or local application workloads. Independent uniform retained
keys, whitening, omitted final MixColumns, ordered distinct pairs and the
10/14/16 target are fixed. Return caps, initialization, experiment linkage and
the full target remain open; the separate 10/12/14 target is unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityFullStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.ActivityRankOneStep (activityIndicator activityMass supportIndicator)
open AESConcrete.ActivityMDSCounts (supportCount)
open AESConcrete.DegreeCentering (globalUniformKernel)
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_left compose_sub_right)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

private theorem zero_degree_mask : ∀ p : SupportIndex 0,
    AES.maskBit p.val.1 = (fun _ : Fin 4 => false) := by decide

private theorem inactive_complement_count : ∀ r : Fin 16,
    (Finset.univ.filter (fun i : Fin 4 => ¬ AES.maskBit r i = true)).card =
      4-AES.maskSize r := by decide

/-- Each unmarked exact-support projection averages on its actual support. -/
theorem supportIndex_zero_rank_one (p : SupportIndex 0) (y x : Fin 4 → V) :
    supportIndexKernel (0 : V) p y x =
      supportIndicator p.val.2 y * supportIndicator p.val.2 x /
        ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2) := by
  have hden : (∏ i : Fin 4, if AES.maskBit p.val.2 i then (1 : ℝ)
      else (Fintype.card V : ℝ)-1) =
      ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    rw [inactive_complement_count]
  unfold supportIndexKernel supportProduct
  rw [zero_degree_mask]
  simp_rw [supportPiece_unmarked, supportDualConstant]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, hden]
  change supportIndicator p.val.2 y *
      (supportIndicator p.val.2 x / ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2)) = _
  ring

/-- All selected masks have the same exact support averaging denominator. -/
theorem refined_activity_kernel (a : Fin 5) (y x : Fin 4 → V) :
    refinedKernel (0 : V) 0 a y x =
      ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y * supportIndicator p.val.2 x /
          ((Fintype.card V : ℝ)-1)^a.val else 0 := by
  unfold refinedKernel
  change (∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
      supportIndexKernel (0 : V) p y x else 0) =
    ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
      supportIndicator p.val.2 y * supportIndicator p.val.2 x /
        ((Fintype.card V : ℝ)-1)^a.val else 0
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    have hexp : 4-AES.maskSize p.val.2 = a.val := by omega
    simpa only [hexp] using (supportIndex_zero_rank_one (V := V) p y x)
  · simp only [hp, if_false]

private theorem support_graph_sum (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 16) (a b : Fin 5)
    (ha : AES.maskSize r + a.val = 4) (hb : AES.maskSize s + b.val = 4) :
    (∑ z, supportIndicator r (L z) * supportIndicator s z) =
      supportCount (Fintype.card V) (a.val+b.val) := by
  simpa only [supportIndicator, ActivityMDSCounts.supportWeight] using
    ActivityMDSCounts.supportWeight_graph_sum_of_active_sizes L hL r s a b ha hb

/-- The diffusion sandwich is computed from exact graph-support counts. -/
theorem diffusion_activity_rank_one (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a b : Fin 5) :
    kernelCompose (fun y z => refinedKernel (0 : V) 0 a y (L z))
      (refinedKernel (0 : V) 0 b) =
      fun y x => supportCount (Fintype.card V) (a.val+b.val) /
        ((Fintype.card V : ℝ)-1)^(a.val+b.val) *
          activityIndicator a y * activityIndicator b x := by
  funext y x
  let c : ℝ := supportCount (Fintype.card V) (a.val+b.val) /
    ((Fintype.card V : ℝ)-1)^(a.val+b.val)
  have hpair (p q : SupportIndex 0) :
      (∑ z : Fin 4 → V,
        (if AES.maskSize p.val.2 + a.val = 4 then
          supportIndicator p.val.2 y * supportIndicator p.val.2 (L z) /
            ((Fintype.card V : ℝ)-1)^a.val else 0) *
        (if AES.maskSize q.val.2 + b.val = 4 then
          supportIndicator q.val.2 z * supportIndicator q.val.2 x /
            ((Fintype.card V : ℝ)-1)^b.val else 0)) =
        c * (if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
          (if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · by_cases hq : AES.maskSize q.val.2 + b.val = 4
      · simp only [hp, hq, if_true]
        calc
          _ = (supportIndicator p.val.2 y * supportIndicator q.val.2 x /
              ((Fintype.card V : ℝ)-1)^(a.val+b.val)) *
              ∑ z, supportIndicator p.val.2 (L z) * supportIndicator q.val.2 z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            rw [pow_add]
            ring
          _ = _ := by
            rw [support_graph_sum L hL p.val.2 q.val.2 a b hp hq]
            dsimp [c]
            ring
      · simp [hp, hq]
    · simp [hp]
  change (∑ z, refinedKernel (0 : V) 0 a y (L z) *
    refinedKernel (0 : V) 0 b z x) = _
  simp_rw [refined_activity_kernel, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : SupportIndex 0, ∑ q : SupportIndex 0,
        c * (if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
          (if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact hpair p q
    _ = c * (∑ p : SupportIndex 0,
        if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
        (∑ q : SupportIndex 0,
        if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      rw [← ActivityRankOneStep.activityIndicator_formula hn a,
        ← ActivityRankOneStep.activityIndicator_formula hn b]

/-- The pointed local channel fixes the actual activity output projection. -/
theorem raw_activity_rank_one (D : V → V → ℝ) (hn : 1 < Fintype.card V)
    (hD : PointedBistochastic D 0) (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a b : Fin 5) :
    kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x))
        (refinedKernel (0 : V) 0 b)) =
      fun y x => supportCount (Fintype.card V) (a.val+b.val) /
        ((Fintype.card V : ℝ)-1)^(a.val+b.val) *
          activityIndicator a y * activityIndicator b x := by
  rw [compose_assoc]
  have hleft : kernelCompose (refinedKernel (0 : V) 0 a)
      (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) =
      fun y x => refinedKernel (0 : V) 0 a y (L x) := by
    funext y x
    exact congrFun (congrFun (AllActiveStep.refined_zero_parallel_fixed D hn hD a) y) (L x)
  rw [hleft]
  exact diffusion_activity_rank_one hn L hL a b

def activityCoefficient (q : ℝ) (a b : Fin 5) : ℝ :=
  supportCount q (a.val+b.val) / (q-1)^(a.val+b.val) - 1/(q^4-1)

def activitySquaredBound (q : ℝ) (a b : Fin 5) : ℝ :=
  activityCoefficient q a b ^ 2 * activityMass q a * activityMass q b

/-- Exact centered coefficient, with both finite-field denominators retained. -/
theorem centered_activity_rank_one (D : V → V → ℝ) (hn : 1 < Fintype.card V)
    (hD : PointedBistochastic D 0) (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0) :
    kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (refinedKernel (0 : V) 0 b)) =
      fun y x => activityCoefficient (Fintype.card V) a b *
        activityIndicator a y * activityIndicator b x := by
  rw [compose_sub_left, compose_sub_right, raw_activity_rank_one D hn hD L hL a b]
  funext y x
  change (supportCount (Fintype.card V) (a.val+b.val) /
    ((Fintype.card V : ℝ)-1)^(a.val+b.val) *
      activityIndicator a y * activityIndicator b x : ℝ) - _ = _
  rw [ActivityRankOneStep.uniform_sandwich a b ha hb]
  unfold activityCoefficient
  ring

/-- Counting-measure Cauchy--Schwarz for an arbitrary signed rank-one kernel. -/
theorem rank_one_scalar_energy_le {W : Type*} [Fintype W]
    (u v : W → ℝ) (c : ℝ) (f : W → ℝ) :
    (∑ y, action (fun y x => c*u y*v x) f y ^ 2) ≤
      (c^2 * (∑ y, u y^2) * (∑ x, v x^2)) * ∑ x, f x^2 := by
  have hact (y : W) : action (fun y x => c*u y*v x) f y =
      (c*u y) * ∑ x, v x*f x := by
    unfold action
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have he : (∑ y, action (fun y x => c*u y*v x) f y ^ 2) =
      (c^2 * ∑ y, u y^2) * (∑ x, v x*f x)^2 := by
    simp_rw [hact, mul_pow]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hc : 0 ≤ c^2 * ∑ y, u y^2 :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [he]
  calc
    _ ≤ (c^2 * ∑ y, u y^2) * ((∑ x, v x^2) * ∑ x, f x^2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v f) hc
    _ = _ := by ring

theorem activity_step_energy (D : V → V → ℝ) (hn : 1 < Fintype.card V)
    (hD : PointedBistochastic D 0) (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (refinedKernel (0 : V) 0 b))) f y ^ 2) ≤
      activitySquaredBound (Fintype.card V) a b * ∑ x, f x^2 := by
  rw [centered_activity_rank_one D hn hD L hL a b ha hb]
  simpa only [ActivityRankOneStep.activityIndicator_energy hn, activitySquaredBound] using
    rank_one_scalar_energy_le (activityIndicator (V := V) a) (activityIndicator b)
      (activityCoefficient (Fintype.card V) a b) f

def activityPair (i j : Fin 14) : Prop :=
  (blockType i).1 = 0 ∧ (blockType j).1 = 0

instance (i j : Fin 14) : Decidable (activityPair i j) := by
  unfold activityPair
  infer_instance

private theorem blockType_active : ∀ i : Fin 14, (blockType i).2 ≠ 0 := by decide

theorem activityPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => activityPair ij.1 ij.2)).card = 16 := by decide

/-- Scalar certificate checks occur only after deriving the actual kernel. -/
theorem certificate_activity_bounds (i j : Fin 14) (h : activityPair i j) :
    0 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L i j ∧
      activitySquaredBound (Fintype.card AES.Word) (blockType i).2 (blockType j).2 ≤
        (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 := by
  simp only [AES.word_card]
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | norm_num [activitySquaredBound, activityCoefficient, supportCount, activityMass,
        blockType, Nat.choose, Finset.sum_range_succ, AESRound.Terminal.lambda,
        AESRound.Certificate.L]

theorem physical_activity_rank_one (i j : Fin 14) (h : activityPair i j) :
    physicalBlock i j = fun y x =>
      activityCoefficient (Fintype.card AES.Word) (blockType i).2 (blockType j).2 *
        activityIndicator (blockType i).2 y * activityIndicator (blockType j).2 x := by
  unfold physicalBlock RefinedStepZeros.refinedCenteredBlock
  rw [h.1, h.2]
  exact centered_activity_rank_one AES.wordSuperboxKernel
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    (blockType i).2 (blockType j).2 (blockType_active i) (blockType_active j)

theorem physical_activity_energy (i j : Fin 14) (h : activityPair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 * ∑ x, f x^2 := by
  rw [physical_activity_rank_one i j h]
  have he := rank_one_scalar_energy_le (activityIndicator (V := AES.Word) (blockType i).2)
    (activityIndicator (blockType j).2)
    (activityCoefficient (Fintype.card AES.Word) (blockType i).2 (blockType j).2) f
  rw [ActivityRankOneStep.activityIndicator_energy (by rw [AES.word_card]; norm_num),
    ActivityRankOneStep.activityIndicator_energy (by rw [AES.word_card]; norm_num)] at he
  exact he.trans (mul_le_mul_of_nonneg_right (certificate_activity_bounds i j h).2
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem physical_activity_step_cap (i j : Fin 14) (h : activityPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j :=
  kernelOperator_norm_le _ (certificate_activity_bounds i j h).1 (physical_activity_energy i j h)

end AESConcrete.ActivityFullStep
