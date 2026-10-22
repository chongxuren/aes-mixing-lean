import AESConcrete.BranchStepCaps
import AESMixing.SupportRepresentation

/-!
# Rank-one activity steps in the raw branch-zero region

An activity indicator is defined by applying the actual degree-zero exact-
support projection to the constant-one function. Its counting-measure energy
is exactly choose(4,a)*(q-1)^a. In the region a+b≤4 the established raw
branch-zero theorem leaves the negative global uniform sandwich, with kernel
-I_a(y)*I_b(x)/(q^4-1). Cauchy--Schwarz gives its exact squared coefficient;
the six frozen scalar comparisons retain q-1 and q^4-1 without rounding either
denominator.

Independent retained keys, whitening, omitted final MixColumns, ordered
distinct pairs and the 10/14/16 target are fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityRankOneStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.DegreeCentering (globalUniformKernel distinguishedState)
open AESConcrete.CenteredWordStepZeros (compose_sub_left compose_sub_right)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The exact active-count indicator, obtained from the existing projection. -/
def activityIndicator (a : Fin 5) : (Fin 4 → V) → ℝ :=
  action (refinedKernel (0 : V) 0 a) (fun _ => 1)

def activityMass (q : ℝ) (a : Fin 5) : ℝ :=
  (Nat.choose 4 a.val : ℝ) * (q-1)^a.val

private theorem supportConstant_sq (b : Bool) (x : V) :
    supportConstant b x ^ 2 = supportConstant b x := by
  cases b <;> by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

private theorem supportConstant_sum (b : Bool) :
    (∑ x : V, supportConstant b x) =
      if b then 1 else (Fintype.card V : ℝ)-1 := by
  simpa only [supportConstant_sq] using (supportConstant_energy (V := V) b)

private theorem supportDualConstant_sum (hn : 1 < Fintype.card V) (b : Bool) :
    (∑ x : V, supportDualConstant b x) = 1 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold supportDualConstant
  rw [← Finset.sum_div, supportConstant_sum]
  cases b <;> simp [ne_of_gt (show 0 < (Fintype.card V : ℝ)-1 by linarith)]

private theorem unmarked_row_sum (hn : 1 < Fintype.card V) (b : Bool) (y : V) :
    (∑ x : V, supportPiece (0 : V) false b y x) = supportConstant b y := by
  simp_rw [supportPiece_unmarked]
  rw [← Finset.mul_sum, supportDualConstant_sum hn, mul_one]

private theorem zero_degree_mask : ∀ p : SupportIndex 0,
    AES.maskBit p.val.1 = (fun _ : Fin 4 => false) := by decide

private theorem inactive_complement_count : ∀ r : Fin 16,
    (Finset.univ.filter (fun i : Fin 4 => ¬ AES.maskBit r i = true)).card =
      4-AES.maskSize r := by decide

def supportIndicator (r : Fin 16) (y : Fin 4 → V) : ℝ :=
  ∏ i, supportConstant (AES.maskBit r i) (y i)

private theorem supportIndicator_sum (r : Fin 16) :
    (∑ y : Fin 4 → V, supportIndicator r y) =
      ((Fintype.card V : ℝ)-1)^(4-AES.maskSize r) := by
  unfold supportIndicator
  rw [← Fintype.prod_sum (fun i x => supportConstant (AES.maskBit r i) x)]
  simp_rw [supportConstant_sum]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [inactive_complement_count]

private theorem supportIndex_row_sum (hn : 1 < Fintype.card V)
    (p : SupportIndex 0) (y : Fin 4 → V) :
    (∑ x, supportIndexKernel (0 : V) p y x) = supportIndicator p.val.2 y := by
  unfold supportIndexKernel supportProduct
  rw [zero_degree_mask]
  rw [← Fintype.prod_sum (fun i x => supportPiece (0 : V) false (AES.maskBit p.val.2 i) (y i) x)]
  simp_rw [unmarked_row_sum hn]
  rfl

theorem activityIndicator_formula (hn : 1 < Fintype.card V) (a : Fin 5)
    (y : Fin 4 → V) :
    activityIndicator a y =
      ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y else 0 := by
  unfold activityIndicator action refinedKernel
  simp only [mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact supportIndex_row_sum hn p y
  · simp only [hp, if_false, Finset.sum_const_zero]

/-- Exact counting factor, with no enumeration of alphabet states. -/
theorem activityIndicator_sum (hn : 1 < Fintype.card V) (a : Fin 5) :
    (∑ y : Fin 4 → V, activityIndicator a y) = activityMass (Fintype.card V) a := by
  simp_rw [activityIndicator_formula hn]
  rw [Finset.sum_comm]
  have hselect (p : SupportIndex 0) :
      AES.maskSize p.val.2 + a.val = 4 ↔ supportIndexSize p = a := by
    have hs := supportIndexSize_eq p
    have hb := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
    have hz := p.property.2
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      rw [h] at hs
      omega
  have hterm (p : SupportIndex 0) :
      (∑ y : Fin 4 → V, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y else 0) =
      if supportIndexSize p = a then ((Fintype.card V : ℝ)-1)^a.val else 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · rw [if_pos ((hselect p).mp hp)]
      simp only [hp, if_true]
      rw [supportIndicator_sum]
      congr 1
      omega
    · simp only [hp, if_false, Finset.sum_const_zero,
        if_neg (fun h => hp ((hselect p).mpr h))]
  simp_rw [hterm]
  calc
    _ = ∑ u : Fin 5, (Nat.choose 4 0 * Nat.choose 4 u.val : ℕ) *
        (if u = a then ((Fintype.card V : ℝ)-1)^a.val else 0) :=
      supportIndex_sum_by_size (0 : Fin 5)
        (fun u => if u = a then ((Fintype.card V : ℝ)-1)^a.val else 0)
    _ = _ := by simp [activityMass, mul_ite]

/-- Symmetric idempotence converts the projected-one mass to its energy. -/
theorem activityIndicator_energy (hn : 1 < Fintype.card V) (a : Fin 5) :
    (∑ y : Fin 4 → V, activityIndicator a y ^ 2) =
      activityMass (Fintype.card V) a := by
  have hfix : action (refinedKernel (0 : V) 0 a) (activityIndicator a) =
      activityIndicator a := by
    unfold activityIndicator
    rw [← kernelCompose_action, RefinedProjectionCompleteness.refined_compose (0 : V) hn]
  calc
    _ = ∑ y : Fin 4 → V,
        (∑ x, refinedKernel (0 : V) 0 a y x) * activityIndicator a y := by
      apply Finset.sum_congr rfl
      intro y _
      simp [activityIndicator, action, pow_two]
    _ = ∑ y : Fin 4 → V, ∑ x,
        refinedKernel (0 : V) 0 a y x * activityIndicator a y := by
      simp_rw [Finset.sum_mul]
    _ = ∑ x : Fin 4 → V, action (refinedKernel (0 : V) 0 a) (activityIndicator a) x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      unfold action
      apply Finset.sum_congr rfl
      intro y _
      rw [refinedKernel_symmetric (0 : V) 0 a y x]
    _ = ∑ x : Fin 4 → V, activityIndicator a x := by rw [hfix]
    _ = _ := activityIndicator_sum hn a

private theorem uniform_refined_right (a : Fin 5) (ha : a ≠ 0)
    (y x : Fin 4 → V) :
    kernelCompose (globalUniformKernel (0 : V)) (refinedKernel 0 0 a) y x =
      if y = distinguishedState (0 : V) then 0 else
        activityIndicator a x / ((Fintype.card V : ℝ)^4-1) := by
  by_cases hy : y = distinguishedState (0 : V)
  · simp [kernelCompose, globalUniformKernel, hy]
  · rw [if_neg hy]
    have hterm (w : Fin 4 → V) :
        globalUniformKernel (0 : V) y w * refinedKernel 0 0 a w x =
          refinedKernel 0 0 a w x / ((Fintype.card V : ℝ)^4-1) := by
      by_cases hw : w = distinguishedState (0 : V)
      · subst w
        simp only [RefinedProjectionCompleteness.refined_at_zero (0 : V) 0 a ha x,
          mul_zero, zero_div]
      · simp [globalUniformKernel, hy, hw, Fintype.card_fun, Fintype.card_fin,
          Nat.cast_pow, div_eq_mul_inv, mul_comm]
    unfold kernelCompose
    simp_rw [hterm]
    rw [← Finset.sum_div]
    congr 1
    simp only [activityIndicator, action, mul_one]
    apply Finset.sum_congr rfl
    intro w _
    exact refinedKernel_symmetric (0 : V) 0 a w x

theorem uniform_sandwich (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0)
    (y x : Fin 4 → V) :
    kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose (globalUniformKernel 0) (refinedKernel 0 0 b)) y x =
      activityIndicator a y * activityIndicator b x / ((Fintype.card V : ℝ)^4-1) := by
  have hpzero : refinedKernel (0 : V) 0 a y (distinguishedState 0) = 0 := by
    rw [refinedKernel_symmetric]
    exact RefinedProjectionCompleteness.refined_at_zero (0 : V) 0 a ha y
  change (∑ v, refinedKernel (0 : V) 0 a y v *
    kernelCompose (globalUniformKernel 0) (refinedKernel 0 0 b) v x) = _
  simp_rw [uniform_refined_right b hb]
  have hterm (v : Fin 4 → V) :
      refinedKernel (0 : V) 0 a y v *
        (if v = distinguishedState 0 then 0 else
          activityIndicator b x / ((Fintype.card V : ℝ)^4-1)) =
      (refinedKernel (0 : V) 0 a y v * activityIndicator b x) /
        ((Fintype.card V : ℝ)^4-1) := by
    by_cases hv : v = distinguishedState (0 : V)
    · subst v
      simp [hpzero]
    · simp only [hv, if_false]
      ring
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  simp [activityIndicator, action]

/-- The branch-zero region leaves exactly one negative rank-one kernel. -/
theorem centered_activity_rank_one (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.val+b.val ≤ 4) :
    kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (refinedKernel (0 : V) 0 b)) =
      fun y x => -(activityIndicator a y * activityIndicator b x /
        ((Fintype.card V : ℝ)^4-1)) := by
  rw [compose_sub_left, compose_sub_right,
    ActivityBranchZeros.raw_refined_branch_zero D hD L hL 0 a 0 b hab hb]
  funext y x
  change (0 : ℝ) - _ = _
  rw [uniform_sandwich a b ha hb]
  ring

/-- Counting-measure energy of an arbitrary negative rank-one kernel. -/
theorem rank_one_energy_le {W : Type*} [Fintype W]
    (u v : W → ℝ) (m : ℝ) (f : W → ℝ) :
    (∑ y, action (fun y x => -(u y*v x/m)) f y ^ 2) ≤
      ((∑ y, u y^2) * (∑ x, v x^2) / m^2) * ∑ x, f x^2 := by
  have hact (y : W) : action (fun y x => -(u y*v x/m)) f y =
      -(u y/m) * ∑ x, v x*f x := by
    unfold action
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have he : (∑ y, action (fun y x => -(u y*v x/m)) f y ^ 2) =
      ((∑ y, u y^2) / m^2) * (∑ x, v x*f x)^2 := by
    simp_rw [hact, mul_pow, neg_sq, div_pow]
    rw [← Finset.sum_mul, ← Finset.sum_div]
  have hc : 0 ≤ (∑ y, u y^2) / m^2 :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg m)
  rw [he]
  calc
    _ ≤ ((∑ y, u y^2) / m^2) * ((∑ x, v x^2) * ∑ x, f x^2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v f) hc
    _ = _ := by ring

theorem activity_step_energy (D : V → V → ℝ) (hn : 1 < Fintype.card V)
    (hD : PointedBistochastic D 0) (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.val+b.val ≤ 4)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel (0 : V) 0 a)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (refinedKernel (0 : V) 0 b))) f y ^ 2) ≤
      (activityMass (Fintype.card V) a * activityMass (Fintype.card V) b /
        ((Fintype.card V : ℝ)^4-1)^2) * ∑ x, f x^2 := by
  rw [centered_activity_rank_one D hD L hL a b ha hb hab]
  simpa only [activityIndicator_energy hn] using
    rank_one_energy_le (activityIndicator (V := V) a) (activityIndicator b)
      ((Fintype.card V : ℝ)^4-1) f

def rankPair (i j : Fin 14) : Prop :=
  (blockType i).1 = 0 ∧ (blockType j).1 = 0 ∧
    (blockType i).2.val + (blockType j).2.val ≤ 4

instance (i j : Fin 14) : Decidable (rankPair i j) := by
  unfold rankPair
  infer_instance

private theorem blockType_active : ∀ i : Fin 14, (blockType i).2 ≠ 0 := by decide

theorem rankPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => rankPair ij.1 ij.2)).card = 6 := by decide

/-- Exact scalar comparison only, after the operator coefficient is derived. -/
theorem certificate_rankone_bounds (i j : Fin 14) (h : rankPair i j) :
    0 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L i j ∧
      activityMass (Fintype.card AES.Word) (blockType i).2 *
        activityMass (Fintype.card AES.Word) (blockType j).2 /
          ((Fintype.card AES.Word : ℝ)^4-1)^2 ≤
        (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 := by
  simp only [AES.word_card]
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | norm_num [activityMass, blockType, Nat.choose, AESRound.Terminal.lambda,
        AESRound.Certificate.L]

theorem physical_rank_one (i j : Fin 14) (h : rankPair i j) :
    physicalBlock i j = fun y x =>
      -(activityIndicator (blockType i).2 y * activityIndicator (blockType j).2 x /
        ((Fintype.card AES.Word : ℝ)^4-1)) := by
  unfold physicalBlock RefinedStepZeros.refinedCenteredBlock
  rw [h.1, h.2.1]
  exact centered_activity_rank_one AES.wordSuperboxKernel AES.word_superbox_pointed
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    (blockType i).2 (blockType j).2 (blockType_active i) (blockType_active j) h.2.2

theorem physical_rank_energy (i j : Fin 14) (h : rankPair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 * ∑ x, f x^2 := by
  rw [physical_rank_one i j h]
  have he := rank_one_energy_le (activityIndicator (V := AES.Word) (blockType i).2)
    (activityIndicator (blockType j).2) ((Fintype.card AES.Word : ℝ)^4-1) f
  rw [activityIndicator_energy (by rw [AES.word_card]; norm_num),
    activityIndicator_energy (by rw [AES.word_card]; norm_num)] at he
  exact he.trans (mul_le_mul_of_nonneg_right (certificate_rankone_bounds i j h).2
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem physical_rank_step_cap (i j : Fin 14) (h : rankPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j :=
  kernelOperator_norm_le _ (certificate_rankone_bounds i j h).1 (physical_rank_energy i j h)

end AESConcrete.ActivityRankOneStep
