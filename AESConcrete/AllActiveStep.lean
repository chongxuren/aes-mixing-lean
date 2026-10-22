import AESConcrete.DegreeResidualStep

/-!
# The all-active activity output against a positive-degree input

The (0,4) refined projection is rank one on the indicator of four nonzero
words. On mean-zero inputs its averaging functional equals minus the sum
over the complementary event. Cauchy--Schwarz therefore bounds its squared
norm by (q^4-(q-1)^4)/(q-1)^4. At q=2^32 this is below 9/q, giving 3/65536.
The actual pointed word channel fixes the activity output, and positive
input degree kills global centering. No MDS or byte estimate is required.

This separate candidate targets only the remaining (3,13) step cell. The
independent retained keys, whitening, omitted final MixColumns, ordered
distinct pairs, and 10/14/16 objective are fixed. The separate 10/12/14
objective is unchanged. Constructive mathematics only; no attacks,
manuscript/historical edits, or local application workloads. Compilation
and independent review remain obligations outside source authoring.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.AllActiveStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordChannelCommutation
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_left)
open AESConcrete.DegreeCentering (degreeComponent_sum_zero)
open AESConcrete.DegreeResidualStep
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def activeIndicator (x : Fin 4 → V) : ℝ :=
  ∏ i, supportConstant false (x i)

private theorem supportConstant_sq (x : V) :
    supportConstant false x ^ 2 = supportConstant false x := by
  by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

theorem activeIndicator_sq (x : Fin 4 → V) :
    activeIndicator x ^ 2 = activeIndicator x := by
  simp only [activeIndicator, ← Finset.prod_pow, supportConstant_sq]

theorem activeIndicator_energy :
    (∑ x : Fin 4 → V, activeIndicator x ^ 2) = ((Fintype.card V : ℝ)-1)^4 := by
  simp only [activeIndicator, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin 4) (x : V) => supportConstant false x ^ 2)]
  simp only [supportConstant_energy, Bool.false_eq_true, if_false,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem activeIndicator_sum :
    (∑ x : Fin 4 → V, activeIndicator x) = ((Fintype.card V : ℝ)-1)^4 := by
  simpa only [activeIndicator_sq] using (activeIndicator_energy (V := V))

theorem inactiveIndicator_energy :
    (∑ x : Fin 4 → V, (1-activeIndicator x)^2) =
      (Fintype.card V : ℝ)^4 - ((Fintype.card V : ℝ)-1)^4 := by
  have hpoint (x : Fin 4 → V) : (1-activeIndicator x)^2 = 1-activeIndicator x := by
    nlinarith [activeIndicator_sq x]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, activeIndicator_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

private def emptySupport : SupportIndex 0 := ⟨(0,0), by decide⟩

private theorem all_active_selection : ∀ p : SupportIndex 0,
    AES.maskSize p.val.2 + (4 : Fin 5).val = 4 ↔ p = emptySupport := by decide

private theorem zero_mask : AES.maskBit (0 : Fin 16) = (fun _ : Fin 4 => false) := by decide

theorem refined_all_active_tensor :
    refinedKernel (0 : V) 0 4 = coordinateKernel (fun _ : Fin 4 => constantMatrix (0 : V)) := by
  funext y x
  unfold refinedKernel
  change (∑ p : SupportIndex 0,
    if AES.maskSize p.val.2 + 4 = 4 then supportIndexKernel (0 : V) p y x else 0) = _
  calc
    _ = if AES.maskSize emptySupport.val.2 + 4 = 4 then
        supportIndexKernel (0 : V) emptySupport y x else 0 := by
      apply Finset.sum_eq_single emptySupport
      · intro p _ hp
        have hnot : ¬ AES.maskSize p.val.2 + 4 = 4 :=
          fun h => hp ((all_active_selection p).mp h)
        rw [if_neg hnot]
      · simp
    _ = _ := by
      have hzero : AES.maskSize emptySupport.val.2 + 4 = 4 := by decide
      rw [if_pos hzero]
      simp only [supportIndexKernel, emptySupport, supportProduct, zero_mask,
        supportPiece, Bool.false_eq_true, if_false, coordinateKernel]

theorem refined_all_active_rank_one (y x : Fin 4 → V) :
    refinedKernel (0 : V) 0 4 y x =
      activeIndicator y * activeIndicator x / ((Fintype.card V : ℝ)-1)^4 := by
  rw [refined_all_active_tensor]
  have hlocal (u v : V) : constantMatrix (0 : V) u v =
      supportConstant false u * (supportConstant false v / ((Fintype.card V : ℝ)-1)) := by
    simpa only [supportPiece, Bool.false_eq_true, if_false, supportDualConstant] using
      (supportPiece_unmarked (V := V) false u v)
  simp only [coordinateKernel]
  simp_rw [hlocal]
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, activeIndicator] <;> ring

private theorem rank_one_complement_energy {W : Type*} [Fintype W]
    (a : W → ℝ) (m c : ℝ) (hm : 0 < m)
    (hasq : ∑ x, a x ^ 2 = m)
    (hcomp : (∑ x, (1-a x)^2) ≤ c^2*m)
    (f : W → ℝ) (hf : (∑ x, f x) = 0) :
    (∑ y, action (fun y x => a y * a x / m) f y ^ 2) ≤ c^2 * ∑ x, f x ^ 2 := by
  have hact (y : W) : action (fun y x => a y * a x / m) f y =
      (a y / m) * ∑ x, a x * f x := by
    unfold action
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have he : (∑ y, action (fun y x => a y * a x / m) f y ^ 2) =
      (∑ x, a x * f x)^2 / m := by
    simp_rw [hact, mul_pow, div_pow]
    rw [← Finset.sum_mul, ← Finset.sum_div, hasq]
    field_simp [ne_of_gt hm]
    <;> ring
  have hsum : (∑ x, (1-a x)*f x) = -(∑ x, a x*f x) := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, hf]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => 1-a x) f
  rw [hsum, neg_sq] at hcs
  rw [he]
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ (∑ x, (1-a x)^2) * ∑ x, f x^2 := hcs
    _ ≤ (c^2*m) * ∑ x, f x^2 :=
      mul_le_mul_of_nonneg_right hcomp (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by ring

/-- The only numerical premise is the displayed finite cardinal inequality. -/
theorem all_active_energy_of_sum_zero (hn : 1 < Fintype.card V) (c : ℝ)
    (hcard : (Fintype.card V : ℝ)^4 - ((Fintype.card V : ℝ)-1)^4 ≤
      c^2 * ((Fintype.card V : ℝ)-1)^4)
    (f : (Fin 4 → V) → ℝ) (hf : (∑ x, f x) = 0) :
    (∑ y, action (refinedKernel (0 : V) 0 4) f y ^ 2) ≤ c^2 * ∑ x, f x ^ 2 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hm : 0 < ((Fintype.card V : ℝ)-1)^4 := pow_pos (by linarith) _
  have hk : refinedKernel (0 : V) 0 4 = fun y x =>
      activeIndicator y * activeIndicator x / ((Fintype.card V : ℝ)-1)^4 := by
    funext y x
    exact refined_all_active_rank_one y x
  rw [hk]
  exact rank_one_complement_energy activeIndicator _ c hm activeIndicator_energy
    (by rw [inactiveIndicator_energy]; exact hcard) f hf

theorem refined_zero_parallel_fixed (D : V → V → ℝ)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D 0) (a : Fin 5) :
    kernelCompose (refinedKernel (0 : V) 0 a)
      (coordinateKernel (fun _ : Fin 4 => D)) = refinedKernel (0 : V) 0 a := by
  have hp := refinedKernel_compose_degreeKernel (0 : V) hn 0 a
  calc
    _ = kernelCompose (kernelCompose (refinedKernel (0 : V) 0 a) (degreeKernel 0 0))
        (coordinateKernel (fun _ : Fin 4 => D)) := by rw [hp]
    _ = kernelCompose (refinedKernel (0 : V) 0 a)
        (kernelCompose (degreeKernel 0 0) (coordinateKernel (fun _ : Fin 4 => D))) :=
      (compose_assoc _ _ _).symm
    _ = _ := by rw [coordinate_degree_zero_left (fun _ : Fin 4 => hD), hp]

private theorem compose_input_relabel {W : Type*} [Fintype W]
    (P K : W → W → ℝ) (e : W → W) :
    kernelCompose P (fun y x => K y (e x)) =
      fun y x => kernelCompose P K y (e x) := rfl

theorem all_active_centered_step_energy (D : V → V → ℝ)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D 0) (c : ℝ)
    (hcard : (Fintype.card V : ℝ)^4 - ((Fintype.card V : ℝ)-1)^4 ≤
      c^2 * ((Fintype.card V : ℝ)-1)^4)
    (j b : Fin 5) (hj : j ≠ 0) (e : Equiv.Perm (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (refinedKernel (0 : V) 0 4)
      (kernelCompose (centeredPermutedKernel D 0 e) (refinedKernel (0 : V) j b))) f y ^ 2) ≤
      c^2 * ∑ x, f x ^ 2 := by
  have hleft : kernelCompose (refinedKernel (0 : V) 0 4)
      (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x)) =
      fun y x => refinedKernel (0 : V) 0 4 y (e x) :=
    (compose_input_relabel (refinedKernel (0 : V) 0 4)
      (coordinateKernel (fun _ : Fin 4 => D)) (fun x => e x)).trans
      (congrArg (fun K => fun y x => K y (e x)) (refined_zero_parallel_fixed D hn hD 4))
  unfold centeredPermutedKernel
  rw [compose_sub_left, globalUniformKernel_compose_refined_positive (0 : V) hn j b hj,
    sub_zero, compose_assoc, hleft, kernelCompose_action,
    FourResidualStep.input_permutation_action]
  have hfix : action (degreeKernel (0 : V) j) (action (refinedKernel (0 : V) j b) f) =
      action (refinedKernel (0 : V) j b) f :=
    (kernelCompose_action _ _ f).symm.trans
      (congrArg (fun K => action K f) (degreeKernel_compose_refinedKernel (0 : V) hn j b))
  have hs := degreeComponent_sum_zero (0 : V) hn j hj (action (refinedKernel (0 : V) j b) f)
  rw [← degreeKernel_action, hfix] at hs
  have hp : (∑ x, action (refinedKernel (0 : V) j b) f (e.symm x)) = 0 := by
    rw [Equiv.sum_comp e.symm (fun x => action (refinedKernel (0 : V) j b) f x)]
    exact hs
  have he := all_active_energy_of_sum_zero hn c hcard
    (fun x => action (refinedKernel (0 : V) j b) f (e.symm x)) hp
  rw [Equiv.sum_comp e.symm (fun x => action (refinedKernel (0 : V) j b) f x ^ 2)] at he
  exact he.trans (mul_le_mul_of_nonneg_left (FourResidualStep.refined_energy_le 0 hn j b f)
    (sq_nonneg c))

theorem source_thirteen_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 3 13) f y ^ 2) ≤
      (3/65536 : ℝ)^2 * ∑ x, f x ^ 2 := by
  exact all_active_centered_step_energy AES.wordSuperboxKernel
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed (3/65536 : ℝ)
    (by rw [AES.word_card]; norm_num) 4 4 (by decide) wordMixAddEquiv.toEquiv f

theorem source_thirteen_norm :
    ‖kernelOperator (physicalBlock 3 13)‖ ≤ (3/65536 : ℝ) :=
  kernelOperator_norm_le _ (by norm_num) source_thirteen_energy

theorem source_thirteen_step_cap :
    ‖kernelOperator (physicalBlock 3 13)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L 3 13 := by
  apply source_thirteen_norm.trans
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L]

end AESConcrete.AllActiveStep
