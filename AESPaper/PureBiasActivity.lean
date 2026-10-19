import AESPaper.PureBiasStartup
import AESPaper.ActivityReferenceCorrection
import AESPaper.OneSourceLaw

/-!
# The full-uniform activity component is the nonempty pure J/Z sum

Residual degree zero contains exactly the literal patterns having J or Z in
each word coordinate. For a unit-mass vector, its all-J projection is full
uniform. Removing that reference therefore leaves precisely the fifteen
nonempty pure J/Z terms. Their orthogonality gives an exact energy identity,
without any independence assumption on the output law.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.PureBiasActivity
open AESMixing AESConcrete
open AESPaper.PureBiasStartup (purePattern)
open AESPaper.StartingWord (q)
open AESPaper.ManySourceBounds (activeSourceCount)

/-- The subset records Z labels only; R labels are excluded by the hypothesis
of `purePattern_of_residualIndex_zero`. -/
def biasPositions (a : Fin 4 → Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => a i = 1)

theorem label_of_not_two : ∀ s : Fin 3, s ≠ 2 → (if s = 1 then 1 else 0) = s := by
  decide

theorem purePattern_of_residualIndex_zero (a : Fin 4 → Fin 3)
    (ha : TernaryDegree.residualIndex a = 0) :
    purePattern (biasPositions a) = a := by
  have hm : TernaryDegree.residualMask a = fun _ => false :=
    (degreeIndex_zero_iff (TernaryDegree.residualMask a)).mp ha
  have hn (i : Fin 4) : a i ≠ 2 := by
    intro hi
    have h := congrFun hm i
    simp only [TernaryDegree.residualMask, hi, decide_true] at h
    contradiction
  funext i
  simp only [purePattern, biasPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact label_of_not_two (a i) (hn i)

/-- Reindexing, with no analytic or probabilistic premise. -/
theorem sum_pure_patterns (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ a : Fin 4 → Fin 3, if TernaryDegree.residualIndex a = 0 then F a else 0) =
      ∑ S : Finset (Fin 4), F (purePattern S) := by
  have h := OneSourceLaw.sum_supported_embedding purePattern
    PureBiasStartup.purePattern_injective
    (fun a => if TernaryDegree.residualIndex a = 0 then F a else 0) (by
      intro a ha
      by_cases hzero : TernaryDegree.residualIndex a = 0
      · exfalso
        exact ha (Finset.mem_image.mpr
          ⟨biasPositions a, Finset.mem_univ _, purePattern_of_residualIndex_zero a hzero⟩)
      · exact if_neg hzero)
  simpa only [PureBiasStartup.purePattern_residualIndex, if_true] using h

/-- Removing the empty subset term from a finite sum. -/
theorem sum_without_empty (F : Finset (Fin 4) → ℝ) :
    (∑ S : Finset (Fin 4), F S) - F ∅ =
      ∑ S : Finset (Fin 4), if S = ∅ then 0 else F S := by
  have hp (S : Finset (Fin 4)) :
      (if S = ∅ then 0 else F S) = F S - (if S = ∅ then F ∅ else 0) := by
    by_cases hS : S = ∅ <;> simp [hS]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The nonempty subsets split into singleton and at-least-two subsets. -/
theorem nonempty_sum_split (F : Finset (Fin 4) → ℝ) :
    (∑ S : Finset (Fin 4), if S = ∅ then 0 else F S) =
      (∑ c : Fin 4, F {c}) +
      ∑ S : Finset (Fin 4), if 2 ≤ S.card then F S else 0 := by
  have hi : Function.Injective (fun c : Fin 4 => ({c} : Finset (Fin 4))) := by
    intro c d h
    change ({c} : Finset (Fin 4)) = {d} at h
    have hc : c ∈ ({d} : Finset (Fin 4)) := by
      rw [← h]
      exact Finset.mem_singleton_self c
    exact Finset.mem_singleton.mp hc
  have hsingle :
      (∑ S : Finset (Fin 4), if S.card = 1 then F S else 0) = ∑ c : Fin 4, F {c} := by
    have h := OneSourceLaw.sum_supported_embedding
      (fun c : Fin 4 => ({c} : Finset (Fin 4))) hi
      (fun S => if S.card = 1 then F S else 0) (by
        intro S hS
        by_cases hcard : S.card = 1
        · exfalso
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
          exact hS (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc.symm⟩)
        · exact if_neg hcard)
    simpa only [Finset.card_singleton, if_true] using h
  have hp (S : Finset (Fin 4)) :
      (if S = ∅ then 0 else F S) =
        (if S.card = 1 then F S else 0) + (if 2 ≤ S.card then F S else 0) := by
    by_cases hS : S = ∅
    · subst S
      simp
    · have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      by_cases hcard : S.card = 1
      · have hnot : ¬ 2 ≤ S.card := by omega
        simp only [if_neg hS, if_pos hcard, if_neg hnot, add_zero]
      · have htwo : 2 ≤ S.card := by omega
        simp only [if_neg hS, if_neg hcard, if_pos htwo, zero_add]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, hsingle]

section Generic
variable {V : Type*} [Fintype V] [AddCommGroup V] [DecidableEq V]

/-- Literal pure ternary output projections equal the J/Z subset kernels. -/
theorem pure_projection (z : V) (S : Finset (Fin 4)) :
    TernaryTensor.tensorProjection z (purePattern S) = BiasTensorEnergy.kernel z S := by
  funext y x
  change (∏ i, UniformBias.piece z (purePattern S i) (y i) (x i)) =
    ∏ i, if i ∈ S then UniformBias.biasKernel z (y i) (x i)
      else UniformBias.uniformKernel (y i) (x i)
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [purePattern, hi, UniformBias.piece]

/-- Degree zero contains all sixteen pure J/Z patterns. -/
theorem degree_zero_expansion (z : V) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z 0 f =
      fun y => ∑ S : Finset (Fin 4), action (BiasTensorEnergy.kernel z S) f y := by
  rw [TernaryDegree.degreeComponent_eq_grouped]
  funext y
  change (∑ a : Fin 4 → Fin 3, if TernaryDegree.residualIndex a = 0 then
    action (TernaryTensor.tensorProjection z a) f y else 0) = _
  rw [sum_pure_patterns]
  simp only [pure_projection]

/-- Unit mass fixes the all-J term, even for signed correlated vectors. -/
theorem empty_projection (z : V) (f : (Fin 4 → V) → ℝ) (hm : (∑ x, f x) = 1) :
    action (BiasTensorEnergy.kernel z ∅) f =
      (CenteredConvolution.uniform : (Fin 4 → V) → ℝ) := by
  funext y
  have hk (x : Fin 4 → V) : BiasTensorEnergy.kernel z ∅ y x =
      1 / (Fintype.card (Fin 4 → V) : ℝ) := by
    simp [BiasTensorEnergy.kernel, UniformBias.uniformKernel,
      Fintype.card_fun, one_div_pow]
  change (∑ x, BiasTensorEnergy.kernel z ∅ y x * f x) =
    1 / (Fintype.card (Fin 4 → V) : ℝ)
  simp only [hk]
  rw [← Finset.mul_sum, hm, mul_one]

/-- Exact vector identity after removing full uniform. -/
theorem degree_zero_centered (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (hm : (∑ x, f x) = 1) :
    degreeComponent z 0 (f - (CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) =
      fun y => ∑ S : Finset (Fin 4),
        if S = ∅ then 0 else action (BiasTensorEnergy.kernel z S) f y := by
  have he : degreeComponent z 0 (f - (CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) =
      degreeComponent z 0 f - CenteredConvolution.uniform := by
    rw [← degreeKernel_action, action_sub, degreeKernel_action, degreeKernel_action,
      ActivityReferenceCorrection.degree_zero_full_uniform z hn]
  rw [he, degree_zero_expansion]
  funext y
  change (∑ S : Finset (Fin 4), action (BiasTensorEnergy.kernel z S) f y) -
    CenteredConvolution.uniform y = _
  rw [← congrFun (empty_projection z f hm) y]
  exact sum_without_empty (fun S => action (BiasTensorEnergy.kernel z S) f y)

theorem pure_orthogonal (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (S T : Finset (Fin 4)) (hST : S ≠ T) :
    (∑ y, action (BiasTensorEnergy.kernel z S) f y *
      action (BiasTensorEnergy.kernel z T) f y) = 0 := by
  rw [← pure_projection z S, ← pure_projection z T]
  exact TernaryTensor.tensorProjection_orthogonal z hn _ _
    (fun h => hST (PureBiasStartup.purePattern_injective h)) f f

/-- The centered activity energy is exactly the nonempty pure-pattern sum. -/
theorem degree_zero_centered_energy (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) (hm : (∑ x, f x) = 1) :
    (∑ y, degreeComponent z 0
      (f - (CenteredConvolution.uniform : (Fin 4 → V) → ℝ)) y ^ 2) =
      ∑ S : Finset (Fin 4), if S = ∅ then 0 else
        (∑ y, action (BiasTensorEnergy.kernel z S) f y ^ 2) := by
  have ho (S T : Finset (Fin 4)) (hST : S ≠ T) :
      (∑ y, (if S = ∅ then 0 else action (BiasTensorEnergy.kernel z S) f y) *
        (if T = ∅ then 0 else action (BiasTensorEnergy.kernel z T) f y)) = 0 := by
    by_cases hS : S = ∅ <;> by_cases hT : T = ∅ <;>
      simp only [hS, hT, if_true, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
    exact pure_orthogonal z hn f S T hST
  have he := orthogonal_family_energy
    (fun (S : Finset (Fin 4)) y =>
      if S = ∅ then 0 else action (BiasTensorEnergy.kernel z S) f y) ho
  rw [degree_zero_centered z hn f hm, he]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S = ∅ <;> simp [hS]

end Generic

/-- Output projection and actual startup channel term are the same vector. -/
theorem actual_projection (b : AES.State) (S : Finset (Fin 4)) :
    action (BiasTensorEnergy.kernel (0 : AES.Word) S) (GroupedLaw.groupedLaw 1 b) =
      BiasStartup.term b (purePattern S) := by
  rw [← pure_projection, BiasStartup.term_projection]

theorem actual_full_uniform_component (b : AES.State) :
    degreeComponent (0 : AES.Word) 0
      (GroupedLaw.groupedLaw 1 b - (CenteredConvolution.uniform : AES.WordState → ℝ)) =
      fun y => ∑ S : Finset (Fin 4),
        if S = ∅ then 0 else BiasStartup.term b (purePattern S) y := by
  rw [degree_zero_centered (0 : AES.Word) AES.word_card_gt_one
    (GroupedLaw.groupedLaw 1 b) (GroupedLaw.grouped_total 1 b)]
  simp only [actual_projection]

theorem actual_full_uniform_energy (b : AES.State) :
    (∑ y, degreeComponent (0 : AES.Word) 0
      (GroupedLaw.groupedLaw 1 b - (CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2) =
      ∑ S : Finset (Fin 4), if S = ∅ then 0 else
        (∑ y, BiasStartup.term b (purePattern S) y ^ 2) := by
  rw [degree_zero_centered_energy (0 : AES.Word) AES.word_card_gt_one
    (GroupedLaw.groupedLaw 1 b) (GroupedLaw.grouped_total 1 b)]
  simp only [actual_projection]

/-- Exact split precedes and is independent of the numerical estimates. -/
theorem actual_full_uniform_energy_split (b : AES.State) :
    (∑ y, degreeComponent (0 : AES.Word) 0
      (GroupedLaw.groupedLaw 1 b - (CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2) =
      (∑ c : Fin 4, ∑ y, BiasStartup.term b (purePattern {c}) y ^ 2) +
      ∑ S : Finset (Fin 4), if 2 ≤ S.card then
        (∑ y, BiasStartup.term b (purePattern S) y ^ 2) else 0 := by
  rw [actual_full_uniform_energy]
  exact nonempty_sum_split (fun S => ∑ y, BiasStartup.term b (purePattern S) y ^ 2)

/-- Several-source full-uniform degree-zero budget, before reference correction. -/
theorem full_uniform_activity_scaled_energy_lt (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, degreeComponent (0 : AES.Word) 0
      (GroupedLaw.groupedLaw 1 b - (CenteredConvolution.uniform : AES.WordState → ℝ)) y ^ 2) <
      4001/1000 := by
  have hs : q^5 * (∑ c : Fin 4, ∑ y, BiasStartup.term b (purePattern {c}) y ^ 2) <
      1000001/250000 := by
    simpa only [PureBiasStartup.purePattern_singleton] using
      BiasStartup.singleZ_total_scaled_energy_lt b hb
  have hm := PureBiasStartup.multiple_total_scaled_energy_lt b (by omega : 0 < activeSourceCount b)
  rw [actual_full_uniform_energy_split, mul_add]
  linarith

/-- Actual reference is uniform on nonzero states; its exact correction is
supplied by `ActivityReferenceCorrection`, not absorbed into the term estimates. -/
theorem actual_activity_scaled_energy_lt (b : AES.State) (hb0 : b ≠ 0)
    (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) <
      4001/1000 := by
  exact ActivityReferenceCorrection.actual_scaled_energy_lt_of_full_uniform b hb0 _
    (full_uniform_activity_scaled_energy_lt b hb).le

/-- This proves only the several-source activity entry of the target profile. -/
theorem actual_activity_envelope (b : AES.State) (hb0 : b ≠ 0)
    (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, degreeComponent (0 : AES.Word) 0 (GroupedLaw.error 1 b) y ^ 2) <
      (21/10 : ℝ)^2 :=
  lt_trans (actual_activity_scaled_energy_lt b hb0 hb) (by norm_num)

end AESPaper.PureBiasActivity
