import AESConcrete.MultiUniformExpansion
import AESConcrete.ResidualIncidenceCoefficient

/-!
# Actual three-active source with one residual and two uniform labels

The residual mask is a physical singleton, evaluated as one word. The two
original uniform labels remain a labelled tuple; neither their values nor the
signed residual amplitude are factored or replaced. The fourth, inactive input
is zero, and all zero values of the three active inputs remain present.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference pairs and the fixed 10/14/16 target remain
unchanged. No inventory is extended.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)

set_option maxRecDepth 100000

abbrev ResidualPositions (p : SelectedSupport 1 3) := MaskCoordinates p.val.val.1

/-- Both original active nonresidual labels; no ordering is chosen. -/
abbrev SourceUniformPositions (p : SelectedSupport 1 3) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem residualPositions_card (p : SelectedSupport 1 3) :
    Fintype.card (ResidualPositions p) = 1 := by
  have hd := p.val.property.2
  norm_num at hd
  simpa only [← Nat.card_eq_fintype_card, ResidualPositions] using
    (maskCoordinates_card p.val.val.1).trans hd

theorem sourceUniformPositions_card (p : SelectedSupport 1 3) :
    Fintype.card (SourceUniformPositions p) = 2 := by
  have hc := MultiUniformExpansion.uniformPositions_card
    p.val.val.2 p.val.val.1 p.val.property.1
  have hs : 4 - (maskSize p.val.val.2 + maskSize p.val.val.1) = 2 := by
    have hp := p.property
    have hd := p.val.property.2
    omega
  simpa only [← Nat.card_eq_fintype_card, SourceUniformPositions] using hc.trans hs

theorem uniformTuple_card {V : Type*} [Fintype V] (p : SelectedSupport 1 3) :
    Fintype.card (SourceUniformPositions p → V) = Fintype.card V ^ 2 := by
  rw [Fintype.card_fun, sourceUniformPositions_card]

theorem inactivePositions_card (p : SelectedSupport 1 3) :
    Fintype.card (MaskCoordinates p.val.val.2) = 1 := by
  have hz : maskSize p.val.val.2 = 1 := by
    have hp := p.property
    omega
  simpa only [← Nat.card_eq_fintype_card] using
    (maskCoordinates_card p.val.val.2).trans hz

def residualIndexEquiv (p : SelectedSupport 1 3) : ResidualPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [residualPositions_card]; simp)

def residualPosition (p : SelectedSupport 1 3) : ResidualPositions p :=
  (residualIndexEquiv p).symm 0

theorem residualPosition_unique (p : SelectedSupport 1 3) (i : ResidualPositions p) :
    i = residualPosition p := by
  apply (residualIndexEquiv p).injective
  exact Subsingleton.elim _ _

def residualLabel (p : SelectedSupport 1 3) : Fin 4 := (residualPosition p).val

theorem residualLabel_mem (p : SelectedSupport 1 3) :
    maskBit p.val.val.1 (residualLabel p) = true := (residualPosition p).property

theorem residualLabel_not_inactive (p : SelectedSupport 1 3) :
    maskBit p.val.val.2 (residualLabel p) ≠ true := by
  intro hz
  exact p.val.property.1 _ hz (residualLabel_mem p)

theorem residualLabel_eq_of_mem (p : SelectedSupport 1 3) (i : Fin 4)
    (hi : maskBit p.val.val.1 i = true) : i = residualLabel p :=
  congrArg Subtype.val (residualPosition_unique p ⟨i, hi⟩)

def residualTupleEquiv {V : Type*} (p : SelectedSupport 1 3) :
    (ResidualPositions p → V) ≃ V where
  toFun x := x (residualPosition p)
  invFun u := fun _ => u
  left_inv x := by
    funext i
    exact congrArg x (residualPosition_unique p i).symm
  right_inv _ := rfl

section Source
variable {V : Type*} [Zero V]

/-- One residual value, both physical uniform values and one inactive zero. -/
def source (p : SelectedSupport 1 3) (u : V) (v : SourceUniformPositions p → V) :
    Fin 4 → V :=
  fun i => if hE : maskBit p.val.val.1 i = true then u
    else if hz : maskBit p.val.val.2 i = true then 0 else v ⟨⟨i, hE⟩, hz⟩

@[simp]
theorem source_residual (p : SelectedSupport 1 3) (u : V)
    (v : SourceUniformPositions p → V) : source p u v (residualLabel p) = u := by
  simp only [source, dif_pos (residualLabel_mem p)]

@[simp]
theorem source_uniform (p : SelectedSupport 1 3) (u : V)
    (v : SourceUniformPositions p → V) (i : SourceUniformPositions p) :
    source p u v i.val.val = v i := by
  simp only [source, dif_neg i.val.property, dif_neg i.property]

theorem source_inactive (p : SelectedSupport 1 3) (u : V)
    (v : SourceUniformPositions p → V) (i : Fin 4)
    (hi : maskBit p.val.val.2 i = true) : source p u v i = 0 := by
  have hE : maskBit p.val.val.1 i ≠ true := p.val.property.1 i hi
  simp only [source, dif_neg hE, dif_pos hi]

/-- Exactly the original inactive input is fixed, including every active zero. -/
def OnSource (p : SelectedSupport 1 3) (x : Fin 4 → V) : Prop :=
  ∀ i : Fin 4, maskBit p.val.val.2 i = true → x i = 0

theorem source_onSource (p : SelectedSupport 1 3) (u : V)
    (v : SourceUniformPositions p → V) : OnSource p (source p u v) :=
  fun i hi => source_inactive p u v i hi

theorem source_reconstruct (p : SelectedSupport 1 3) (x : Fin 4 → V)
    (hx : OnSource p x) :
    source p (x (residualLabel p)) (fun i => x i.val.val) = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · have hi := residualLabel_eq_of_mem p i hE
    subst i
    exact source_residual p _ _
  · by_cases hz : maskBit p.val.val.2 i = true
    · exact (source_inactive p _ _ i hz).trans (hx i hz).symm
    · exact source_uniform p _ _ ⟨⟨i, hE⟩, hz⟩

theorem source_injective (p : SelectedSupport 1 3) :
    Function.Injective
      (fun uv : V × (SourceUniformPositions p → V) => source p uv.1 uv.2) := by
  intro uv uv' he
  apply Prod.ext
  · have hr := congrFun he (residualLabel p)
    simpa only [source_residual] using hr
  · funext i
    have hu := congrFun he i.val.val
    simpa only [source_uniform] using hu

/-- Three-dimensional physical source, with all original input labels. -/
def sourceEquiv (p : SelectedSupport 1 3) :
    (V × (SourceUniformPositions p → V)) ≃ {x : Fin 4 → V // OnSource p x} where
  toFun uv := ⟨source p uv.1 uv.2, source_onSource p uv.1 uv.2⟩
  invFun x := (x.val (residualLabel p), fun i => x.val i.val.val)
  left_inv uv := by
    apply Prod.ext
    · exact source_residual p uv.1 uv.2
    · funext i
      exact source_uniform p uv.1 uv.2 i
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property

end Source

section NormalizedRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Both unit-energy uniform factors remain, at their original labels. -/
theorem multiUniform_source (p : SelectedSupport 1 3)
    (g : (ResidualPositions p → V) → ℝ) (u : V)
    (v : SourceUniformPositions p → V) :
    multiUniform p.val.val.2 p.val.val.1 g (source p u v) =
      g (fun _ => u) * ∏ i : SourceUniformPositions p, nonzeroUniform (v i) := by
  have hcoords : (fun i : ResidualPositions p => source p u v i.val) = fun _ => u := by
    funext i
    rw [residualPosition_unique p i]
    exact source_residual p u v
  have hprod : (∏ i : OtherCoordinates p.val.val.1,
      normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) =
      ∏ i : SourceUniformPositions p, nonzeroUniform (v i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun i : OtherCoordinates p.val.val.1 => maskBit p.val.val.2 i.val = true)]
    have hI (i : MultiUniformExpansion.InactivePositions p.val.val.2 p.val.val.1) :
        normalizedLeg (maskBit p.val.val.2 i.val.val) (source p u v i.val.val) = 1 := by
      rw [source_inactive p u v i.val.val i.property]
      simp [normalizedLeg, i.property, zeroUnit, supportConstant, identityKernel]
    have hU (i : SourceUniformPositions p) :
        normalizedLeg (maskBit p.val.val.2 i.val.val) (source p u v i.val.val) =
          nonzeroUniform (v i) := by
      rw [source_uniform]
      simp only [normalizedLeg, if_neg i.property]
    simp_rw [hI, hU]
    simp only [Finset.prod_const_one, one_mul]
  unfold multiUniform coordinateEmbedding
  change g (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

theorem component_off_source (p : SelectedSupport 1 3) (f : (Fin 4 → V) → ℝ)
    (x : Fin 4 → V) (hx : ¬ OnSource p x) :
    supportIndexComponent (0 : V) p.val f x = 0 := by
  by_contra hnonzero
  apply hx
  intro i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero p.val i hi f x hnonzero

/-- The same arbitrary signed one-word amplitude has exactly the original
source energy. Positivity, independence and `h 0 = 0` are not premises. -/
theorem normalized_source_representation (p : SelectedSupport 1 3)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : V → ℝ,
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnSource p x → supportIndexComponent (0 : V) p.val f x = 0) := by
  obtain ⟨g, _, hG, henergy⟩ := supportIndexComponent_multi_uniform p.val hn f
  refine ⟨fun u => g (fun _ => u), ?_, ?_, ?_⟩
  · intro u v
    rw [hG]
    exact multiUniform_source p g u v
  · rw [henergy]
    change (∑ w : ResidualPositions p → V, g w ^ 2) =
      ∑ u : V, g ((residualTupleEquiv (V := V) p).symm u) ^ 2
    exact ((residualTupleEquiv (V := V) p).symm.sum_comp (fun w => g w ^ 2)).symm
  · intro x hx
    exact component_off_source p f x hx

end NormalizedRepresentation

theorem word_source_representation (p : SelectedSupport 1 3)
    (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnSource p x → supportIndexComponent (0 : AES.Word) p.val f x = 0) :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.DoubleUniformSource
