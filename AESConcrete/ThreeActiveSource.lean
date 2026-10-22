import AESConcrete.MultiUniformExpansion
import AESConcrete.ResidualIncidenceCoefficient

/-!
# Actual three-active source with a joint residual pair

The two residual inputs keep their physical labels; they are not ordered and
their amplitude is not factored. The remaining active input is a singleton
nonzero-uniform leg, and the one inactive input is zero. The source includes
all zero values and is three-dimensional over the word alphabet.

Candidate source interfaces only. Constructive mathematics only; no attacks.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the fixed 10/14/16 target stay unchanged. Accepted
sources, tooling, historical records and manuscripts remain frozen.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)

set_option maxRecDepth 100000

/-- Both original residual labels, without choosing an order. -/
abbrev ResidualPositions (p : SelectedSupport 2 3) := MaskCoordinates p.val.val.1

/-- The original active nonresidual labels. -/
abbrev SourceUniformPositions (p : SelectedSupport 2 3) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem residualPositions_card (p : SelectedSupport 2 3) :
    Fintype.card (ResidualPositions p) = 2 := by
  have hd := p.val.property.2
  norm_num at hd
  simpa only [← Nat.card_eq_fintype_card, ResidualPositions] using
    (maskCoordinates_card p.val.val.1).trans hd

theorem sourceUniformPositions_card (p : SelectedSupport 2 3) :
    Fintype.card (SourceUniformPositions p) = 1 := by
  have hc := MultiUniformExpansion.uniformPositions_card
    p.val.val.2 p.val.val.1 p.val.property.1
  have hs : 4 - (maskSize p.val.val.2 + maskSize p.val.val.1) = 1 := by
    have hp := p.property
    have hd := p.val.property.2
    omega
  simpa only [← Nat.card_eq_fintype_card, SourceUniformPositions] using hc.trans hs

theorem inactivePositions_card (p : SelectedSupport 2 3) :
    Fintype.card (MaskCoordinates p.val.val.2) = 1 := by
  have hz : maskSize p.val.val.2 = 1 := by
    have hp := p.property
    omega
  simpa only [← Nat.card_eq_fintype_card] using
    (maskCoordinates_card p.val.val.2).trans hz

def uniformIndexEquiv (p : SelectedSupport 2 3) : SourceUniformPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformPosition (p : SelectedSupport 2 3) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 0

theorem uniformPosition_unique (p : SelectedSupport 2 3)
    (i : SourceUniformPositions p) : i = uniformPosition p := by
  apply (uniformIndexEquiv p).injective
  exact Subsingleton.elim _ _

def uniformLabel (p : SelectedSupport 2 3) : Fin 4 := (uniformPosition p).val.val

theorem uniformLabel_not_residual (p : SelectedSupport 2 3) :
    maskBit p.val.val.1 (uniformLabel p) ≠ true := (uniformPosition p).val.property

theorem uniformLabel_not_inactive (p : SelectedSupport 2 3) :
    maskBit p.val.val.2 (uniformLabel p) ≠ true := (uniformPosition p).property

theorem residual_not_inactive (p : SelectedSupport 2 3) (i : ResidualPositions p) :
    maskBit p.val.val.2 i.val ≠ true := by
  intro hi
  exact p.val.property.1 i.val hi i.property

theorem uniformLabel_eq_of_unmarked (p : SelectedSupport 2 3) (i : Fin 4)
    (hE : maskBit p.val.val.1 i ≠ true) (hz : maskBit p.val.val.2 i ≠ true) :
    i = uniformLabel p :=
  congrArg (fun j : SourceUniformPositions p => j.val.val)
    (uniformPosition_unique p ⟨⟨i, hE⟩, hz⟩)

theorem other_nonuniform_inactive (p : SelectedSupport 2 3)
    (i : OtherCoordinates p.val.val.1) (hi : i ≠ (uniformPosition p).val) :
    maskBit p.val.val.2 i.val = true := by
  by_contra hz
  apply hi
  exact congrArg (fun j : SourceUniformPositions p => j.val)
    (uniformPosition_unique p ⟨i, hz⟩)

section Source
variable {V : Type*} [Zero V]

/-- The three-input source: the joint residual tuple and one uniform value. -/
def source (p : SelectedSupport 2 3) (u : ResidualPositions p → V) (v : V) : Fin 4 → V :=
  fun i => if hE : maskBit p.val.val.1 i = true then u ⟨i, hE⟩
    else if i = uniformLabel p then v else 0

@[simp]
theorem source_residual (p : SelectedSupport 2 3) (u : ResidualPositions p → V)
    (v : V) (i : ResidualPositions p) : source p u v i.val = u i := by
  simp only [source, dif_pos i.property]

@[simp]
theorem source_uniform (p : SelectedSupport 2 3) (u : ResidualPositions p → V) (v : V) :
    source p u v (uniformLabel p) = v := by
  simp [source, uniformLabel_not_residual p]

theorem source_inactive (p : SelectedSupport 2 3) (u : ResidualPositions p → V)
    (v : V) (i : Fin 4) (hi : maskBit p.val.val.2 i = true) : source p u v i = 0 := by
  have hE : maskBit p.val.val.1 i ≠ true := p.val.property.1 i hi
  have hu : i ≠ uniformLabel p := by
    intro he
    subst i
    exact uniformLabel_not_inactive p hi
  simp only [source, dif_neg hE, if_neg hu]

/-- Zero only on the original inactive input; this is a three-dimensional source. -/
def OnSource (p : SelectedSupport 2 3) (x : Fin 4 → V) : Prop :=
  ∀ i : Fin 4, maskBit p.val.val.2 i = true → x i = 0

theorem source_onSource (p : SelectedSupport 2 3) (u : ResidualPositions p → V) (v : V) :
    OnSource p (source p u v) := fun i hi => source_inactive p u v i hi

theorem source_reconstruct (p : SelectedSupport 2 3) (x : Fin 4 → V)
    (hx : OnSource p x) :
    source p (fun i => x i.val) (x (uniformLabel p)) = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · exact source_residual p _ _ ⟨i, hE⟩
  · by_cases hz : maskBit p.val.val.2 i = true
    · exact (source_inactive p _ _ i hz).trans (hx i hz).symm
    · have hi := uniformLabel_eq_of_unmarked p i hE hz
      subst i
      exact source_uniform p _ _

theorem source_injective (p : SelectedSupport 2 3) :
    Function.Injective (fun uv : (ResidualPositions p → V) × V => source p uv.1 uv.2) := by
  intro uv uv' he
  apply Prod.ext
  · funext i
    have hr := congrFun he i.val
    simpa only [source_residual] using hr
  · have hu := congrFun he (uniformLabel p)
    simpa only [source_uniform] using hu

/-- Exact physical source equivalence, including every zero value. -/
def sourceEquiv (p : SelectedSupport 2 3) :
    ((ResidualPositions p → V) × V) ≃ {x : Fin 4 → V // OnSource p x} where
  toFun uv := ⟨source p uv.1 uv.2, source_onSource p uv.1 uv.2⟩
  invFun x := (fun i => x.val i.val, x.val (uniformLabel p))
  left_inv uv := by
    apply Prod.ext
    · funext i
      exact source_residual p uv.1 uv.2 i
    · exact source_uniform p uv.1 uv.2
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property

end Source

section NormalizedRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exactly one normalized uniform leg and the same joint signed amplitude. -/
theorem multiUniform_source (p : SelectedSupport 2 3)
    (h : (ResidualPositions p → V) → ℝ) (u : ResidualPositions p → V) (v : V) :
    multiUniform p.val.val.2 p.val.val.1 h (source p u v) = h u * nonzeroUniform v := by
  have hcoords : (fun i : ResidualPositions p => source p u v i.val) = u := by
    funext i
    exact source_residual p u v i
  have hprod : (∏ i : OtherCoordinates p.val.val.1,
      normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) =
      nonzeroUniform v := by
    rw [Finset.prod_eq_single (uniformPosition p).val]
    · change normalizedLeg (maskBit p.val.val.2 (uniformLabel p))
        (source p u v (uniformLabel p)) = nonzeroUniform v
      rw [source_uniform]
      simp only [normalizedLeg, if_neg (uniformLabel_not_inactive p)]
    · intro i _ hi
      have hz := other_nonuniform_inactive p i hi
      rw [source_inactive p u v i.val hz]
      simp [normalizedLeg, hz, zeroUnit, supportConstant, identityKernel]
    · simp
  unfold multiUniform coordinateEmbedding
  change h (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

theorem component_off_source (p : SelectedSupport 2 3) (f : (Fin 4 → V) → ℝ)
    (x : Fin 4 → V) (hx : ¬ OnSource p x) :
    supportIndexComponent (0 : V) p.val f x = 0 := by
  by_contra hnonzero
  apply hx
  intro i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero p.val i hi f x hnonzero

/-- Exact original energy of an arbitrary signed joint residual tuple.
No independence, positivity, or vanishing-at-zero premise is added. -/
theorem normalized_source_representation (p : SelectedSupport 2 3)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (ResidualPositions p → V) → ℝ,
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnSource p x → supportIndexComponent (0 : V) p.val f x = 0) := by
  obtain ⟨h, _, hG, henergy⟩ := supportIndexComponent_multi_uniform p.val hn f
  refine ⟨h, ?_, henergy, ?_⟩
  · intro u v
    rw [hG]
    exact multiUniform_source p h u v
  · intro x hx
    exact component_off_source p f x hx

end NormalizedRepresentation

theorem word_source_representation (p : SelectedSupport 2 3) (f : AES.WordState → ℝ) :
    ∃ h : (ResidualPositions p → AES.Word) → ℝ,
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnSource p x → supportIndexComponent (0 : AES.Word) p.val f x = 0) :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.ThreeActiveSource
