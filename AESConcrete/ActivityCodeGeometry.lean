import AESConcrete.MultiUniformExpansion
import AESConcrete.MixedCodeMoment
import AESMixing.DualInformation
import AESMixing.ActivityColumns

/-!
# Actual diffusion images of activity-only uniform subsets

The code is the additive image of a coordinate-supported input subgroup.
Its parameter bijection proves its cardinality; actual equal-size MDS
restrictions prove its information sets. The normalized expansion identity
is separate from these geometric statements and from the later moment bound.

Constructive mathematics only; no attacks. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct pairs and 10/14/16 stay
fixed. No manuscript, historical source, other objective, goal or schedule
is changed. This module alone adds no physical cap or full-round theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityCodeGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
open AESConcrete.NonzeroUniformGraphCap (fullUniform zeroUnit residualStep_action)
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

attribute [local instance] Classical.propDecidable

section Geometry
variable {V : Type*} [AddCommGroup V]

/-- The actual input subspace, with all coordinates outside `U` fixed at zero. -/
def supportedSubgroup (U : Fin 16) : AddSubgroup (Fin 4 → V) where
  carrier := {x | maskProjection U x = x}
  zero_mem' := by
    funext i
    simp [maskProjection]
  add_mem' := by
    intro x y hx hy
    funext i
    have hxi := congrFun hx i
    have hyi := congrFun hy i
    by_cases hi : maskBit U i = true <;> simp_all [maskProjection]
  neg_mem' := by
    intro x hx
    funext i
    have hxi := congrFun hx i
    by_cases hi : maskBit U i = true
    · simp [maskProjection, hi]
    · have hz : x i = 0 := by
        simpa [maskProjection, hi] using hxi.symm
      simp [maskProjection, hi, hz]

/-- The subgroup is transported by the actual additive diffusion. -/
def imageCode (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (U : Fin 16) :
    AddSubgroup (Fin 4 → V) :=
  (supportedSubgroup U).map L.toAddMonoidHom

theorem mem_imageCode_iff (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (U : Fin 16) (z : Fin 4 → V) :
    z ∈ imageCode L U ↔ maskProjection U (L.symm z) = L.symm z := by
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := AddSubgroup.mem_map.mp hz
    change maskProjection U x = x at hx
    have he : L.symm z = x := by rw [← hxz]; exact L.symm_apply_apply x
    simpa only [he] using hx
  · intro hz
    apply AddSubgroup.mem_map.mpr
    exact ⟨L.symm z, hz, L.apply_symm_apply z⟩

/-- Coordinates in `U` parameterize the code once, without multiplicity. -/
def codeEquiv (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (U : Fin 16) :
    imageCode L U ≃ (MaskCoordinates U → V) where
  toFun c := restrictCoordinates U (L.symm c.val)
  invFun w := ⟨L (extendCoordinates U w),
    (mem_imageCode_iff L U _).mpr (by
      rw [L.symm_apply_apply]
      exact extend_supported U w)⟩
  left_inv c := by
    apply Subtype.ext
    change L (extendCoordinates U (restrictCoordinates U (L.symm c.val))) = c.val
    rw [extend_restrict, (mem_imageCode_iff L U c.val).mp c.property,
      L.apply_symm_apply]
  right_inv w := by
    change restrictCoordinates U (L.symm (L (extendCoordinates U w))) = w
    rw [L.symm_apply_apply, restrict_extend]

variable [Fintype V]

instance imageCodeFintype (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (U : Fin 16) :
    Fintype (imageCode L U) := Fintype.ofFinite _

theorem imageCode_card (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (U : Fin 16) :
    Fintype.card (imageCode L U) = Fintype.card V ^ maskSize U := by
  rw [Fintype.card_congr (codeEquiv L U), Fintype.card_fun, maskCoordinates_card]

/-- The restrictions are of the actual physical output coordinates. -/
theorem imageCode_restriction_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (U out : Fin 16) (hsize : maskSize out = maskSize U) :
    Function.Bijective
      (subgroupRestriction (imageCode L U) (fun i => maskBit out i = true)) := by
  have he : (fun c : imageCode L U =>
      restrictedMap L.toAddMonoidHom out U (codeEquiv L U c)) =
      subgroupRestriction (imageCode L U) (fun i => maskBit out i = true) := by
    funext c i
    change L (extendCoordinates U (restrictCoordinates U (L.symm c.val))) i.val =
      c.val i.val
    rw [extend_restrict, (mem_imageCode_iff L U c.val).mp c.property,
      L.apply_symm_apply]
  rw [← he]
  exact (mds_restricted_bijective L.toAddMonoidHom hL out U hsize).comp
    (codeEquiv L U).bijective

end Geometry

/-- The actual whole-word code used by the activity-only expansion. -/
abbrev wordCode (U : Fin 16) : AddSubgroup AES.WordState :=
  imageCode wordMixAddEquiv U

theorem wordCode_card (U : Fin 16) :
    Fintype.card (wordCode U) = 4294967296 ^ maskSize U := by
  rw [imageCode_card, AES.word_card]
  norm_num

theorem wordCode_restriction_bijective (U out : Fin 16)
    (hsize : maskSize out = maskSize U) :
    Function.Bijective
      (subgroupRestriction (wordCode U) (fun i => maskBit out i = true)) :=
  imageCode_restriction_bijective wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS U out hsize

section Normalization
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The unique residual tuple when the residual mask is empty. -/
def emptyTuple : MaskCoordinates 0 → V := fun i => (empty_mask_coordinate i).elim

omit [AddCommGroup V] [Fintype V] [DecidableEq V] in
theorem emptyTuple_unique [AddCommGroup V] [Fintype V] [DecidableEq V]
    (w : MaskCoordinates 0 → V) : w = emptyTuple := by
  funext i
  exact (empty_mask_coordinate i).elim

theorem emptyTuple_energy (h : (MaskCoordinates 0 → V) → ℝ) :
    (∑ w, h w ^ 2) = h emptyTuple ^ 2 := by
  letI : Unique (MaskCoordinates 0 → V) :=
    ⟨⟨emptyTuple⟩, emptyTuple_unique⟩
  exact Fintype.sum_unique _

private theorem empty_mask_bit (i : Fin 4) : maskBit 0 i ≠ true :=
  fun hi => empty_mask_coordinate ⟨i, hi⟩

private def emptyOtherEquiv : OtherCoordinates 0 ≃ Fin 4 where
  toFun i := i.val
  invFun i := ⟨i, empty_mask_bit i⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := rfl

private theorem expansionLeg_empty (r : Fin 16) (σ : Selection r 0)
    (i : OtherCoordinates 0) (x : V) :
    expansionLeg r 0 σ i x =
      if maskBit (selectionMask r 0 σ) i.val then fullUniform x else zeroUnit x := by
  rw [selectionMask_bit, dif_neg i.property]
  by_cases hr : maskBit r i.val = true
  · simp [expansionLeg, hr]
  · simp only [expansionLeg, dif_neg hr]

private theorem expansionTerm_empty_product (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → V) → ℝ) (x : Fin 4 → V) :
    expansionTerm r 0 σ h x = h emptyTuple *
      ∏ i : Fin 4, if maskBit (selectionMask r 0 σ) i then
        fullUniform (x i) else zeroUnit (x i) := by
  unfold expansionTerm coordinateEmbedding
  rw [emptyTuple_unique (fun i : MaskCoordinates 0 => x i.val)]
  congr 1
  simp_rw [expansionLeg_empty]
  exact Equiv.prod_comp emptyOtherEquiv
    (fun i => if maskBit (selectionMask r 0 σ) i then
      fullUniform (x i) else zeroUnit (x i))

private theorem uniform_zero_product (U : Fin 16) (x : Fin 4 → V) :
    (∏ i : Fin 4, if maskBit U i then fullUniform (x i) else zeroUnit (x i)) =
      if maskProjection U x = x then
        (1 / Real.sqrt (Fintype.card V : ℝ)) ^ maskSize U else 0 := by
  by_cases hs : maskProjection U x = x
  · rw [if_pos hs]
    have hf (i : Fin 4) :
        (if maskBit U i then fullUniform (x i) else zeroUnit (x i)) =
          if maskBit U i then 1 / Real.sqrt (Fintype.card V : ℝ) else 1 := by
      by_cases hi : maskBit U i = true
      · simp [hi, fullUniform]
      · have hz : x i = 0 := by
          have hh := congrFun hs i
          simpa [maskProjection, hi] using hh.symm
        simp [hi, hz, zeroUnit, supportConstant, identityKernel]
    simp_rw [hf]
    rw [Finset.prod_ite]
    simp [AES.maskSize]
  · rw [if_neg hs]
    by_contra hp
    apply hs
    funext i
    by_cases hi : maskBit U i = true
    · simp [maskProjection, hi]
    · have hfactor := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hz : x i = 0 := by
        by_contra hxi
        exact hfactor (by simp [hi, zeroUnit, supportConstant, identityKernel, hxi])
      simp [maskProjection, hi, hz]

omit [AddCommGroup V] [Fintype V] [DecidableEq V] in
private theorem sqrt_card_pow [AddCommGroup V] [Fintype V] [DecidableEq V] (n : ℕ) :
    Real.sqrt ((Fintype.card V : ℝ) ^ n) =
      Real.sqrt (Fintype.card V : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg _) n), ih, pow_succ]

/-- Unit-indicator normalization is exactly the product of full-uniform legs.
There is no additional code-size or probability-normalization factor. -/
theorem expansionTerm_pullback_eq_generic
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → V) → ℝ) :
    (fun z => expansionTerm r 0 σ h (L.symm z)) = fun z =>
      h emptyTuple * unitSubgroupIndicator (imageCode L (selectionMask r 0 σ)) z := by
  funext z
  rw [expansionTerm_empty_product, uniform_zero_product]
  unfold unitSubgroupIndicator
  rw [imageCode_card, Nat.cast_pow, sqrt_card_pow]
  simp only [div_pow, one_pow]
  rw [mem_imageCode_iff]
  by_cases hs : maskProjection (selectionMask r 0 σ) (L.symm z) = L.symm z <;>
    simp [hs]

theorem expansionTerm_pullback_eq (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (fun z => expansionTerm r 0 σ h (wordMixAddEquiv.symm z)) = fun z =>
      h emptyTuple * unitSubgroupIndicator (wordCode (selectionMask r 0 σ)) z :=
  expansionTerm_pullback_eq_generic wordMixAddEquiv r σ h

private theorem action_scale {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (c : ℝ) (f : X → ℝ) :
    action K (fun x => c * f x) = fun y => c * action K f y := by
  funext y
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact physical-input normalization, with the scalar residual's full
counting energy retained for the subsequent heterogeneous aggregation. -/
theorem word_expansionTerm_energy_eq (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r 0 σ h) y ^ 2) =
      (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
        residualMatrix AES.wordSuperboxKernel 0))
        (unitSubgroupIndicator (wordCode (selectionMask r 0 σ))) y ^ 2) *
          ∑ w, h w ^ 2 := by
  rw [residualStep_action, expansionTerm_pullback_eq, action_scale]
  simp_rw [residualTensor, mul_pow]
  rw [← Finset.mul_sum, emptyTuple_energy]
  ring

end Normalization

section Endpoints

private theorem size_zero_mask : ∀ U : Fin 16, maskSize U = 0 → U = 0 := by decide

private theorem size_four_bit : ∀ U : Fin 16, maskSize U = 4 →
    ∀ i : Fin 4, maskBit U i = true := by decide

private theorem maskProjection_empty (x : AES.WordState) : maskProjection 0 x = 0 := by
  funext i
  simp [maskProjection, empty_mask_bit]

theorem wordCode_zero_mem (U : Fin 16) (hU : maskSize U = 0) (z : AES.WordState) :
    z ∈ wordCode U ↔ z = 0 := by
  rw [mem_imageCode_iff, size_zero_mask U hU, maskProjection_empty]
  constructor
  · intro hz
    apply wordMixAddEquiv.symm.injective
    simpa only [map_zero] using hz.symm
  · rintro rfl
    simp only [map_zero]

theorem wordCode_full_mem (U : Fin 16) (hU : maskSize U = 4) (z : AES.WordState) :
    z ∈ wordCode U := by
  apply (mem_imageCode_iff wordMixAddEquiv U z).mpr
  funext i
  simp [maskProjection, size_four_bit U hU i]

/-- A zero-dimensional code is the zero point, killed by an actual zero
column of the residual tensor. -/
theorem wordCode_zero_action (U : Fin 16) (hU : maskSize U = 0) :
    action (coordinateKernel (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0))
      (unitSubgroupIndicator (wordCode U)) = 0 := by
  funext y
  have hu : unitSubgroupIndicator (wordCode U) =
      fun z : AES.WordState => if z = 0 then 1 else 0 := by
    funext z
    simp [unitSubgroupIndicator, wordCode_zero_mem U hU]
  rw [hu]
  simp [action, coordinateKernel, AES.word_residual_zero_column]

private theorem word_residual_row_sum (y : AES.Word) :
    (∑ x, residualMatrix AES.wordSuperboxKernel 0 y x) = 0 := by
  unfold residualMatrix
  rw [Finset.sum_sub_distrib, AES.word_superbox_pointed.row_sum,
    (activityMatrix_pointed (0 : AES.Word) AES.word_card_gt_one).row_sum]
  norm_num

/-- A full-dimensional code is constant on the whole state space; each
actual residual word channel kills that constant leg. -/
theorem wordCode_full_action (U : Fin 16) (hU : maskSize U = 4) :
    action (coordinateKernel (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0))
      (unitSubgroupIndicator (wordCode U)) = 0 := by
  funext y
  unfold action
  simp only [unitSubgroupIndicator, wordCode_full_mem U hU, if_true, mul_one_div]
  rw [← Finset.sum_div]
  change (∑ x : Fin 4 → AES.Word,
    ∏ i : Fin 4, residualMatrix AES.wordSuperboxKernel 0 (y i) (x i)) / _ = 0
  rw [← Fintype.prod_sum (fun i x => residualMatrix AES.wordSuperboxKernel 0 (y i) x)]
  simp only [word_residual_row_sum, Fin.prod_univ_four, zero_mul, zero_div]

end Endpoints
end AESConcrete.ActivityCodeGeometry
