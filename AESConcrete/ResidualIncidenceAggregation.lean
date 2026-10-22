import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.FourResidualStep
import AESConcrete.RefinedProjectionCompleteness
import AESMixing.OrthogonalComparison

/-!
# Selected-support incidence for arbitrary joint inputs

The actual exact-support projection is assembled with its exact orthogonal
multiplicities. Counting measure and support-embedding normalization are
retained throughout.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ResidualIncidenceAggregation
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient

set_option maxRecDepth 100000

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem selected_kernel_sum (z : V) (d a : Fin 5) :
    (fun y x => ∑ p : SelectedSupport d a, supportIndexKernel z p.val y x) =
      refinedKernel z d a := by
  funext y x
  unfold refinedKernel
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem selected_action_sum (z : V) (d a : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (fun y => ∑ p : SelectedSupport d a, supportIndexComponent z p.val f y) =
      action (refinedKernel z d a) f := by
  rw [← selected_kernel_sum z d a]
  funext y
  change (∑ p : SelectedSupport d a, ∑ x, supportIndexKernel z p.val y x * f x) =
    ∑ x, (∑ p : SelectedSupport d a, supportIndexKernel z p.val y x) * f x
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem selected_orthogonal (z : V) (hn : 1 < Fintype.card V) (d a : Fin 5)
    (p r : SelectedSupport d a) (hpr : p ≠ r) (f g : (Fin 4 → V) → ℝ) :
    (∑ x, supportIndexComponent z p.val f x * supportIndexComponent z r.val g x) = 0 := by
  apply supportIndex_orthogonal z hn p.val r.val _ f g
  intro h
  exact hpr (Subtype.ext h)

theorem constant_comparison_energy {A B : Type*} [Fintype A] [Fintype B]
    (c : ℝ) (f : B → ℝ) :
    (∑ a : A, action (fun _ : A => fun _ : B => c) f a ^ 2) ≤
      ((Fintype.card A : ℝ) * (Fintype.card B : ℝ) * c^2) * ∑ b, f b^2 := by
  have hs : (∑ b, f b)^2 ≤ (Fintype.card B : ℝ) * ∑ b, f b^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : B => (1 : ℝ)) f
  have hact (a : A) : action (fun _ : A => fun _ : B => c) f a = c * ∑ b, f b := by
    simp only [action, Finset.mul_sum]
  simp_rw [hact, mul_pow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ ≤ (Fintype.card A : ℝ) * (c^2 * ((Fintype.card B : ℝ) * ∑ b, f b^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sq_nonneg c))
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem selected_comparison_energy (m : ℝ) (hm : 1 ≤ m)
    (d a e b : Fin 5) (hda : d ≤ a) (heb : e ≤ b)
    (f : SelectedSupport e b → ℝ) :
    (∑ p : SelectedSupport d a,
      action (fun _ : SelectedSupport d a => fun _ : SelectedSupport e b =>
        coefficient m d a e b) f p ^ 2) ≤
      comparisonCap m d a e b ^ 2 * ∑ r, f r^2 := by
  have h := constant_comparison_energy (A := SelectedSupport d a)
    (B := SelectedSupport e b) (coefficient m d a e b) f
  rw [selectedSupport_card d a hda, selectedSupport_card e b heb,
    multiplicity_coefficient_sq m hm, ← comparisonCap_sq m hm] at h
  exact h

variable [AddCommGroup V]

theorem selected_support_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5) (he : 0 < e.val)
    (p : SelectedSupport d a) (r : SelectedSupport e b)
    (f g : (Fin 4 → V) → ℝ) :
    |∑ x, supportIndexComponent 0 p.val g (L x) * supportIndexComponent 0 r.val f x| ≤
      coefficient (Fintype.card V) d a e b *
        l2 (supportIndexComponent 0 r.val f) * l2 (supportIndexComponent 0 p.val g) := by
  have hcard : 0 < Fintype.card (MaskCoordinates r.val.val.1) := by
    rw [maskCoordinates_card, r.val.property.2]
    exact he
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hcard
  have h := supportProduct_diffusion_bilinear L hL hn p.val.val.2 r.val.val.2
    p.val.val.1 r.val.val.1 p.val.property.1 r.val.property.1 k f g
  rw [selected_coefficient d a e b p r] at h
  exact h

theorem refined_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (he : 0 < e.val)
    (f g : (Fin 4 → V) → ℝ) :
    |∑ x, action (refinedKernel 0 d a) g (L x) * action (refinedKernel 0 e b) f x| ≤
      comparisonCap (Fintype.card V) d a e b *
        l2 (action (refinedKernel 0 e b) f) * l2 (action (refinedKernel 0 d a) g) := by
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  have h := orthogonal_bilinear_comparison
    (fun r : SelectedSupport e b => supportIndexComponent 0 r.val f)
    (fun p : SelectedSupport d a => supportIndexComponent 0 p.val g) L
    (fun p r hpr => selected_orthogonal 0 hn e b p r hpr f f)
    (fun p r hpr => selected_orthogonal 0 hn d a p r hpr g g)
    (fun _ : SelectedSupport d a => fun _ : SelectedSupport e b =>
      coefficient (Fintype.card V) d a e b)
    (comparisonCap (Fintype.card V) d a e b) (comparisonCap_nonneg _ _ _ _ _)
    (selected_comparison_energy _ hm d a e b hda heb)
    (fun p r => selected_support_bilinear L hL hn d a e b he p r f g)
  have hout (x : Fin 4 → V) :
      (∑ p : SelectedSupport d a, supportIndexComponent 0 p.val g x) =
        action (refinedKernel 0 d a) g x :=
    congrFun (selected_action_sum 0 d a g) x
  have hin (x : Fin 4 → V) :
      (∑ r : SelectedSupport e b, supportIndexComponent 0 r.val f x) =
        action (refinedKernel 0 e b) f x :=
    congrFun (selected_action_sum 0 e b f) x
  simpa only [hout, hin, selected_action_sum] using h

theorem refined_inner (z : V) (d a : Fin 5) (f g : (Fin 4 → V) → ℝ) :
    (∑ x, action (refinedKernel z d a) f x * g x) =
      ∑ x, f x * action (refinedKernel z d a) g x := by
  simp only [action, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [refinedKernel_symmetric z d a y x]
  ring

def diffusionTransfer (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (d a e b : Fin 5)
    (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (refinedKernel 0 d a) (fun y => action (refinedKernel 0 e b) f (L.symm y))

/-- The projected input energy is retained before the optional contraction. -/
theorem refined_diffusion_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (he : 0 < e.val) (f : (Fin 4 → V) → ℝ) :
    (∑ x, diffusionTransfer L d a e b f x^2) ≤
      squaredBound (Fintype.card V) d a e b * ∑ x, action (refinedKernel 0 e b) f x^2 := by
  let g := diffusionTransfer L d a e b f
  let c := comparisonCap (Fintype.card V) d a e b
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  have heq : (∑ x, action (refinedKernel 0 d a) g (L x) *
      action (refinedKernel 0 e b) f x) = ∑ y, g y^2 := by
    calc
      _ = ∑ y, action (refinedKernel 0 d a) g y *
          action (refinedKernel 0 e b) f (L.symm y) := by
        have hs := Equiv.sum_comp L.toEquiv
          (fun y => action (refinedKernel 0 d a) g y *
            action (refinedKernel 0 e b) f (L.symm y))
        change (∑ x, action (refinedKernel 0 d a) g (L x) *
          action (refinedKernel 0 e b) f (L.symm (L x))) =
            ∑ y, action (refinedKernel 0 d a) g y *
              action (refinedKernel 0 e b) f (L.symm y) at hs
        simpa only [L.symm_apply_apply] using hs
      _ = ∑ y, g y * action (refinedKernel 0 d a)
          (fun x => action (refinedKernel 0 e b) f (L.symm x)) y :=
        refined_inner 0 d a g _
      _ = _ := by simp only [g, diffusionTransfer, pow_two]
  have hp : l2 (action (refinedKernel 0 d a) g) ≤ l2 g := by
    simpa only [one_mul] using l2_le_of_energy (action (refinedKernel 0 d a) g) g 1
      (by norm_num) (by simpa only [one_pow, one_mul] using
        FourResidualStep.refined_energy_le 0 hn d a g)
  have hb := refined_diffusion_bilinear L.toAddMonoidHom hL hn d a e b hda heb he f g
  change |∑ x, action (refinedKernel 0 d a) g (L x) *
      action (refinedKernel 0 e b) f x| ≤
    comparisonCap (Fintype.card V) d a e b *
      l2 (action (refinedKernel 0 e b) f) * l2 (action (refinedKernel 0 d a) g) at hb
  rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), ← l2_sq g] at hb
  have hg := l2_nonneg g
  have hfg := l2_nonneg (action (refinedKernel 0 e b) f)
  have hc : 0 ≤ c := comparisonCap_nonneg _ _ _ _ _
  have ht := hb.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hc hfg))
  have hnorm : l2 g ≤ c * l2 (action (refinedKernel 0 e b) f) := by
    by_cases hz : l2 g = 0
    · rw [hz]
      exact mul_nonneg hc hfg
    · have hg' : 0 < l2 g := lt_of_le_of_ne hg (Ne.symm hz)
      exact le_of_mul_le_mul_right (by simpa only [pow_two] using ht) hg'
  have hsq := (sq_le_sq₀ hg (mul_nonneg hc hfg)).mpr hnorm
  simpa only [mul_pow, l2_sq, g, c, comparisonCap_sq _ hm] using hsq

theorem refined_diffusion_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (he : 0 < e.val) (f : (Fin 4 → V) → ℝ) :
    (∑ x, diffusionTransfer L d a e b f x^2) ≤
      squaredBound (Fintype.card V) d a e b * ∑ x, f x^2 := by
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  exact (refined_diffusion_energy L hL hn d a e b hda heb he f).trans
    (mul_le_mul_of_nonneg_left (FourResidualStep.refined_energy_le 0 hn e b f)
      (squaredBound_nonneg _ hm d a e b))

end AESConcrete.ResidualIncidenceAggregation
