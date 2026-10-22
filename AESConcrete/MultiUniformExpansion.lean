import AESConcrete.NonzeroUniformGraphCap
import AESConcrete.GeneralMDSGraphSupport
import AESMixing.SupportNorm
import AESMixing.L2Sums

/-!
# Normalized joint support components and their uniform-subset expansion

A Boolean selection on the
unmarked-active positions is exactly a subset of those positions. The same
arbitrary signed joint residual function occurs in every expansion term.
Normalization, exact expansion, geometric premises and heterogeneous norm
aggregation are separate interfaces. No independence of input coordinates
or orthogonality of outputs is assumed.

Constructive bounds only; no attacks, workloads, manuscript or historical
edits, goals or schedules. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and 10/14/16 stay fixed.
This module by itself asserts no new physical cap or accepted result.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MultiUniformExpansion
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.NonzeroUniformGraphCap
  (nonzeroUniform fullUniform zeroUnit nonzeroUniform_energy
    fullUniform_energy zeroUnit_energy nonzeroUniform_decomposition)

/-- The inactive positions outside the residual mask. -/
abbrev InactivePositions (r E : Fin 16) :=
  {i : OtherCoordinates E // maskBit r i.val = true}

/-- The unmarked-active positions; their values carry unit nonzero uniforms. -/
abbrev UniformPositions (r E : Fin 16) :=
  {i : OtherCoordinates E // maskBit r i.val ≠ true}

/-- One Boolean choice for each unmarked-active position, hence one subset. -/
abbrev Selection (r E : Fin 16) := UniformPositions r E → Bool

set_option maxRecDepth 100000 in
theorem uniformPositions_card : ∀ r E : Fin 16, MaskDisjoint r E →
    Fintype.card (UniformPositions r E) = 4 - (maskSize r + maskSize E) := by decide

theorem selection_card (r E : Fin 16) :
    Fintype.card (Selection r E) = 2 ^ Fintype.card (UniformPositions r E) := by simp

/-- The selected subset, in the physical four-coordinate mask API. -/
def selectionMask (r E : Fin 16) (σ : Selection r E) : Fin 16 :=
  maskBitsEquiv.symm (fun i =>
    if hE : maskBit E i = true then false
    else if hr : maskBit r i = true then false else σ ⟨⟨i, hE⟩, hr⟩)

theorem selectionMask_bit (r E : Fin 16) (σ : Selection r E) (i : Fin 4) :
    maskBit (selectionMask r E σ) i =
      if hE : maskBit E i = true then false
      else if hr : maskBit r i = true then false else σ ⟨⟨i, hE⟩, hr⟩ := by
  exact congrFun (maskBitsEquiv.apply_symm_apply _) i

theorem selectionMask_disjoint (r E : Fin 16) (σ : Selection r E) :
    MaskDisjoint (selectionMask r E σ) E := by
  intro i hi hE
  rw [selectionMask_bit, dif_pos hE] at hi
  exact Bool.false_ne_true hi

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The unit vector appropriate to one nonresidual position. -/
def normalizedLeg (b : Bool) (x : V) : ℝ :=
  if b then zeroUnit x else nonzeroUniform x

theorem normalizedLeg_energy (hn : 1 < Fintype.card V) (b : Bool) :
    (∑ x : V, normalizedLeg b x ^ 2) = 1 := by
  cases b
  · exact nonzeroUniform_energy hn
  · exact zeroUnit_energy

/-- An isometric embedding; only the coordinates in `E` remain joint. -/
def multiUniform (r E : Fin 16) (h : (MaskCoordinates E → V) → ℝ) :
    (Fin 4 → V) → ℝ :=
  coordinateEmbedding (fun i => maskBit E i = true)
    (fun i => normalizedLeg (maskBit r i.val)) h

theorem multiUniform_energy (hn : 1 < Fintype.card V) (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) :
    (∑ x, multiUniform r E h x ^ 2) = ∑ w, h w ^ 2 := by
  exact coordinateEmbedding_isometry _ _
    (fun i => normalizedLeg_energy hn (maskBit r i.val)) h

/-- The positive scalar absorbed into the joint residual on normalization. -/
def normalization (r E : Fin 16) : ℝ :=
  ∏ i : OtherCoordinates E,
    if maskBit r i.val then 1 else Real.sqrt ((Fintype.card V : ℝ) - 1)

omit [AddCommGroup V] [DecidableEq V] in
theorem normalization_pos (hn : 1 < Fintype.card V) (r E : Fin 16) :
    0 < normalization (V := V) r E := by
  have hq : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply Finset.prod_pos
  intro i _
  split_ifs
  · norm_num
  · exact Real.sqrt_pos.2 (by linarith)

omit [AddCommGroup V] [DecidableEq V] in
/-- The per-leg normalization agrees with the existing support norm factor. -/
theorem normalization_eq_supportNormFactor (hn : 1 < Fintype.card V)
    (r E : Fin 16) (hr : MaskDisjoint r E) :
    normalization (V := V) r E = supportNormFactor V r E := by
  have hq : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hq' : 0 ≤ (Fintype.card V : ℝ) - 1 := by linarith
  have he : normalization (V := V) r E ^ 2 =
      ((Fintype.card V : ℝ) - 1) ^ (4 - (maskSize r + maskSize E)) := by
    unfold normalization
    rw [← Finset.prod_pow]
    have hc (i : OtherCoordinates E) :
        (if maskBit r i.val then (1 : ℝ) else Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 2 =
          if maskBit r i.val then 1 else (Fintype.card V : ℝ) - 1 := by
      split_ifs
      · norm_num
      · exact Real.sq_sqrt hq'
    simp_rw [hc]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
    rw [unmarked_coordinate_count r E hr]
  have hs : supportNormFactor V r E ^ 2 =
      ((Fintype.card V : ℝ) - 1) ^ (4 - (maskSize r + maskSize E)) := by
    exact Real.sq_sqrt (pow_nonneg hq' _)
  apply (sq_eq_sq₀ (le_of_lt (normalization_pos hn r E))
    (le_of_lt (supportNormFactor_pos hn r E))).mp
  exact he.trans hs.symm

private theorem supportConstant_normalized (hn : 1 < Fintype.card V)
    (b : Bool) (x : V) :
    supportConstant b x =
      (if b then 1 else Real.sqrt ((Fintype.card V : ℝ) - 1)) * normalizedLeg b x := by
  have hq : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hs : Real.sqrt ((Fintype.card V : ℝ) - 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  cases b
  · simp only [Bool.false_eq_true, if_false, normalizedLeg, nonzeroUniform]
    field_simp [hs]
  · simp only [if_true, normalizedLeg, zeroUnit, one_mul]

theorem supportEmbedding_normalized (hn : 1 < Fintype.card V) (r E : Fin 16)
    (g : (MaskCoordinates E → V) → ℝ) :
    supportEmbedding r E g =
      multiUniform r E (fun w => normalization (V := V) r E * g w) := by
  funext x
  simp only [supportEmbedding, multiUniform, coordinateEmbedding]
  simp_rw [supportConstant_normalized hn]
  rw [Finset.prod_mul_distrib]
  change g _ * (normalization (V := V) r E * _) =
    (normalization (V := V) r E * g _) * _
  ring

private theorem action_scale {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (c : ℝ) (f : X → ℝ) :
    action K (fun x => c * f x) = fun y => c * action K f y := by
  funext y
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every genuine support component has one normalized, arbitrary signed
joint residual, with exactly the component's counting energy. -/
theorem supportIndexComponent_multi_uniform {d : ℕ} (p : SupportIndex d)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (MaskCoordinates p.val.1 → V) → ℝ,
      markedResidual p.val.1 h = h ∧
      supportIndexComponent (0 : V) p f = multiUniform p.val.2 p.val.1 h ∧
      (∑ x, supportIndexComponent (0 : V) p f x ^ 2) = ∑ w, h w ^ 2 := by
  obtain ⟨g, hg, he⟩ := supportProduct_residual_representation hn
    p.val.2 p.val.1 p.property.1 f
  let h := fun w => normalization (V := V) p.val.2 p.val.1 * g w
  have hh : markedResidual p.val.1 h = h := by
    unfold h markedResidual
    rw [action_scale]
    exact congrArg (fun g => fun w => normalization (V := V) p.val.2 p.val.1 * g w) hg
  have hp : supportIndexComponent (0 : V) p f = multiUniform p.val.2 p.val.1 h := by
    change action (supportProduct 0 (maskBit p.val.1) (maskBit p.val.2)) f = _
    rw [he, supportEmbedding_normalized hn]
  exact ⟨h, hh, hp, by rw [hp]; exact multiUniform_energy hn _ _ h⟩

/-- Full uniforms on the selected subset, zero units at every other
nonresidual position, and the same joint `h` on the residual mask. -/
def expansionLeg (r E : Fin 16) (σ : Selection r E)
    (i : OtherCoordinates E) (x : V) : ℝ :=
  if hr : maskBit r i.val = true then zeroUnit x
  else if σ ⟨i, hr⟩ then fullUniform x else zeroUnit x

def expansionTerm (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → V) → ℝ) : (Fin 4 → V) → ℝ :=
  coordinateEmbedding (fun i => maskBit E i = true) (expansionLeg r E σ) h

theorem expansionTerm_energy (hn : 1 < Fintype.card V) (r E : Fin 16)
    (σ : Selection r E) (h : (MaskCoordinates E → V) → ℝ) :
    (∑ x, expansionTerm r E σ h x ^ 2) = ∑ w, h w ^ 2 := by
  apply coordinateEmbedding_isometry
  intro i
  unfold expansionLeg
  split_ifs
  · exact zeroUnit_energy
  · exact fullUniform_energy hn
  · exact zeroUnit_energy

/-- The exact coefficient of this subset, including every unit normalization. -/
def expansionCoefficient (r E : Fin 16) (σ : Selection r E) : ℝ :=
  ∏ i : UniformPositions r E,
    (if σ i then Real.sqrt (Fintype.card V : ℝ) else -1) /
      Real.sqrt ((Fintype.card V : ℝ) - 1)

private theorem nonzeroUniform_choice_sum (hn : 1 < Fintype.card V) (x : V) :
    nonzeroUniform x = ∑ b : Bool,
      ((if b then Real.sqrt (Fintype.card V : ℝ) else -1) /
        Real.sqrt ((Fintype.card V : ℝ) - 1)) *
      (if b then fullUniform x else zeroUnit x) := by
  rw [nonzeroUniform_decomposition hn]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  ring

private theorem multiUniform_split (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) (x : Fin 4 → V) :
    multiUniform r E h x = h (fun i => x i.val) *
      (∏ i : InactivePositions r E, zeroUnit (x i.val.val)) *
      ∏ i : UniformPositions r E, nonzeroUniform (x i.val.val) := by
  unfold multiUniform coordinateEmbedding
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : OtherCoordinates E => maskBit r i.val = true)]
  have hI (i : InactivePositions r E) :
      normalizedLeg (maskBit r i.val.val) (x i.val.val) = zeroUnit (x i.val.val) := by
    simp [normalizedLeg, i.property]
  have hA (i : UniformPositions r E) :
      normalizedLeg (maskBit r i.val.val) (x i.val.val) = nonzeroUniform (x i.val.val) := by
    simp [normalizedLeg, i.property]
  simp_rw [hI, hA]
  ring

private theorem expansionTerm_split (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → V) → ℝ) (x : Fin 4 → V) :
    expansionTerm r E σ h x = h (fun i => x i.val) *
      (∏ i : InactivePositions r E, zeroUnit (x i.val.val)) *
      ∏ i : UniformPositions r E,
        if σ i then fullUniform (x i.val.val) else zeroUnit (x i.val.val) := by
  unfold expansionTerm coordinateEmbedding
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : OtherCoordinates E => maskBit r i.val = true)]
  have hI (i : InactivePositions r E) :
      expansionLeg r E σ i.val (x i.val.val) = zeroUnit (x i.val.val) := by
    simp [expansionLeg, i.property]
  have hA (i : UniformPositions r E) :
      expansionLeg r E σ i.val (x i.val.val) =
        if σ i then fullUniform (x i.val.val) else zeroUnit (x i.val.val) := by
    simp [expansionLeg, i.property]
  simp_rw [hI, hA]
  ring

/-- Exact finite subset expansion. No norm estimate or triangle loss occurs
in this algebraic identity. The joint residual is shared by all terms. -/
theorem multiUniform_subset_expansion (hn : 1 < Fintype.card V) (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) :
    multiUniform r E h = fun x => ∑ σ : Selection r E,
      expansionCoefficient (V := V) r E σ * expansionTerm r E σ h x := by
  funext x
  rw [multiUniform_split]
  simp_rw [nonzeroUniform_choice_sum hn]
  rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, expansionTerm_split]
  unfold expansionCoefficient
  ring

/-- Every selected term is invariant under the entire selected translation
subspace, including simultaneous changes in several coordinates. -/
theorem expansionTerm_invariant (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → V) → ℝ) :
    ∀ (x : Fin 4 → V) (t : MaskCoordinates (selectionMask r E σ) → V),
      expansionTerm r E σ h (x + extendCoordinates (selectionMask r E σ) t) =
        expansionTerm r E σ h x := by
  intro x t
  have hmarked : (fun i : MaskCoordinates E =>
      (x + extendCoordinates (selectionMask r E σ) t) i.val) = fun i => x i.val := by
    funext i
    have hi : maskBit (selectionMask r E σ) i.val ≠ true := by
      rw [selectionMask_bit, dif_pos i.property]
      exact Bool.false_ne_true
    simp [extendCoordinates, hi]
  unfold expansionTerm coordinateEmbedding
  rw [hmarked]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  unfold expansionLeg
  by_cases hr : maskBit r i.val = true
  · have hi : maskBit (selectionMask r E σ) i.val ≠ true := by
      rw [selectionMask_bit, dif_neg i.property, dif_pos hr]
      exact Bool.false_ne_true
    simp [hr, extendCoordinates, hi]
  · by_cases hs : σ ⟨i, hr⟩ = true
    · simp [hr, hs, fullUniform]
    · have hi : maskBit (selectionMask r E σ) i.val ≠ true := by
        simpa only [selectionMask_bit, dif_neg i.property, dif_neg hr] using hs
      simp [hr, hs, extendCoordinates, hi]

/-- The same term is supported on the residual mask union the selected
uniform mask; nonselected positions outside the residual are fixed at zero. -/
theorem expansionTerm_supported (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → V) → ℝ) :
    ∀ x, expansionTerm r E σ h x ≠ 0 →
      maskProjection (maskUnion E (selectionMask r E σ)) x = x := by
  intro x hx
  funext i
  by_cases hU : maskBit (maskUnion E (selectionMask r E σ)) i = true
  · simp [maskProjection, hU]
  · have hE : maskBit E i ≠ true := by
      intro hi
      apply hU
      rw [maskUnion_bit, hi]
      rfl
    have hS : maskBit (selectionMask r E σ) i ≠ true := by
      intro hi
      apply hU
      rw [maskUnion_bit, hi]
      simp
    have hz : x i = 0 := by
      by_contra hxi
      apply hx
      have hleg : expansionLeg r E σ (⟨i, hE⟩ : OtherCoordinates E) (x i) = 0 := by
        unfold expansionLeg
        by_cases hr : maskBit r i = true
        · simp [hr, zeroUnit, supportConstant, identityKernel, hxi]
        · have hs : σ ⟨⟨i, hE⟩, hr⟩ ≠ true := by
            simpa only [selectionMask_bit, dif_neg hE, dif_neg hr] using hS
          simp [hr, hs, zeroUnit, supportConstant, identityKernel, hxi]
      unfold expansionTerm coordinateEmbedding
      rw [show (∏ j : OtherCoordinates E, expansionLeg r E σ j (x j.val)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ (⟨i, hE⟩ : OtherCoordinates E)) hleg]
      exact mul_zero _
    simp [maskProjection, hU, hz]

section HeterogeneousAggregation

/-- Triangle aggregation retains each coefficient and each term's own norm
cap. In particular it does not replace heterogeneous caps by their maximum. -/
theorem heterogeneous_l2_sum {I X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq I] (s : Finset I) (K : Y → X → ℝ)
    (c a : I → ℝ) (f : I → X → ℝ) (g : Z → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (he : ∀ i ∈ s, (∑ y, action K (f i) y ^ 2) ≤ a i ^ 2 * ∑ x, g x ^ 2) :
    l2 (fun y => ∑ i ∈ s, c i * action K (f i) y) ≤
      (∑ i ∈ s, |c i| * a i) * l2 g := by
  calc
    _ ≤ ∑ i ∈ s, l2 (fun y => c i * action K (f i) y) :=
      l2_finset_sum_le s _
    _ = ∑ i ∈ s, |c i| * l2 (action K (f i)) := by simp_rw [l2_scale]
    _ ≤ ∑ i ∈ s, |c i| * (a i * l2 g) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (l2_le_of_energy _ g (a i) (ha i hi) (he i hi)) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

private theorem action_fintype_weighted_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (c : I → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, c i * f i x) =
      fun y => ∑ i, c i * action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact operator action on the subset expansion. -/
theorem multiUniform_action_expansion {Y : Type*} (K : Y → (Fin 4 → V) → ℝ)
    (hn : 1 < Fintype.card V) (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) :
    action K (multiUniform r E h) = fun y => ∑ σ : Selection r E,
      expansionCoefficient (V := V) r E σ * action K (expansionTerm r E σ h) y := by
  rw [multiUniform_subset_expansion hn]
  exact action_fintype_weighted_sum K _ _

/-- Heterogeneous per-subset energy estimates give the exact weighted sum
of norm caps. The common input norm is the joint residual's norm. -/
theorem multiUniform_action_l2 {Y : Type*} [Fintype Y]
    (K : Y → (Fin 4 → V) → ℝ) (hn : 1 < Fintype.card V) (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) (a : Selection r E → ℝ)
    (ha : ∀ σ, 0 ≤ a σ)
    (he : ∀ σ, (∑ y, action K (expansionTerm r E σ h) y ^ 2) ≤
      a σ ^ 2 * ∑ w, h w ^ 2) :
    l2 (action K (multiUniform r E h)) ≤
      (∑ σ : Selection r E, |expansionCoefficient (V := V) r E σ| * a σ) * l2 h := by
  rw [multiUniform_action_expansion K hn]
  exact heterogeneous_l2_sum Finset.univ K
    (expansionCoefficient (V := V) r E) a (fun σ => expansionTerm r E σ h) h
    (fun σ _ => ha σ) (fun σ _ => he σ)

/-- The same heterogeneous estimate in counting-energy form, ready for
selected-support multiplicity and input-energy aggregation. -/
theorem multiUniform_action_energy {Y : Type*} [Fintype Y]
    (K : Y → (Fin 4 → V) → ℝ) (hn : 1 < Fintype.card V) (r E : Fin 16)
    (h : (MaskCoordinates E → V) → ℝ) (a : Selection r E → ℝ)
    (ha : ∀ σ, 0 ≤ a σ)
    (he : ∀ σ, (∑ y, action K (expansionTerm r E σ h) y ^ 2) ≤
      a σ ^ 2 * ∑ w, h w ^ 2) :
    (∑ y, action K (multiUniform r E h) y ^ 2) ≤
      (∑ σ : Selection r E, |expansionCoefficient (V := V) r E σ| * a σ) ^ 2 *
        ∑ w, h w ^ 2 := by
  have hb : 0 ≤ ∑ σ : Selection r E, |expansionCoefficient (V := V) r E σ| * a σ :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg (abs_nonneg _) (ha σ))
  have hs := (sq_le_sq₀ (l2_nonneg (action K (multiUniform r E h)))
    (mul_nonneg hb (l2_nonneg h))).mpr (multiUniform_action_l2 K hn r E h a ha he)
  simpa only [mul_pow, l2_sq] using hs

end HeterogeneousAggregation
end AESConcrete.MultiUniformExpansion
