import AESConcrete.MultiUniformExpansion
import AESConcrete.ResidualIncidenceCoefficient

/-!
# Actual two-active source with one residual and one uniform coordinate

The selected source has its original physical labels. Singleton index and
tuple equivalences identify the one residual coordinate and one nonzero-uniform
coordinate; the other two coordinates are exactly zero. The public normalized
support representation supplies the same arbitrary signed residual amplitude
and its exact counting energy. No private splitting theorem is imported.

Future source bridge only: no operator bound, Fourier geometry, physical cap,
inventory increment, compilation or acceptance is asserted. Constructive
mathematics only; no attacks. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and fixed 10/14/16 remain
unchanged. Frozen candidate/accepted sources, tooling, manuscripts, objectives,
memory and schedules are not modified by this separate module.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoActiveSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)

set_option maxRecDepth 100000

/-- The actual residual input labels of the selected `(1,2)` support. -/
abbrev ResidualPositions (p : SelectedSupport 1 2) :=
  MaskCoordinates p.val.val.1

/-- The actual active, nonresidual input labels. -/
abbrev SourceUniformPositions (p : SelectedSupport 1 2) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem residualPositions_card (p : SelectedSupport 1 2) :
    Fintype.card (ResidualPositions p) = 1 := by
  have hd := p.val.property.2
  norm_num at hd
  simpa only [← Nat.card_eq_fintype_card, ResidualPositions] using
    (maskCoordinates_card p.val.val.1).trans hd

theorem sourceUniformPositions_card (p : SelectedSupport 1 2) :
    Fintype.card (SourceUniformPositions p) = 1 := by
  have hc := MultiUniformExpansion.uniformPositions_card
    p.val.val.2 p.val.val.1 p.val.property.1
  have hs : 4 - (maskSize p.val.val.2 + maskSize p.val.val.1) = 1 := by
    have hp := p.property
    have hd := p.val.property.2
    omega
  simpa only [← Nat.card_eq_fintype_card, SourceUniformPositions] using hc.trans hs

/-- The remaining two physical labels are the original inactive inputs. -/
theorem inactivePositions_card (p : SelectedSupport 1 2) :
    Fintype.card (MaskCoordinates p.val.val.2) = 2 := by
  have hz : maskSize p.val.val.2 = 2 := by
    have hp := p.property
    omega
  simpa only [← Nat.card_eq_fintype_card] using
    (maskCoordinates_card p.val.val.2).trans hz

/-- Singleton equivalences choose labels without changing physical masks. -/
def residualIndexEquiv (p : SelectedSupport 1 2) : ResidualPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [residualPositions_card]; simp)

def uniformIndexEquiv (p : SelectedSupport 1 2) : SourceUniformPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def residualPosition (p : SelectedSupport 1 2) : ResidualPositions p :=
  (residualIndexEquiv p).symm 0

def uniformPosition (p : SelectedSupport 1 2) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 0

theorem residualPosition_unique (p : SelectedSupport 1 2) (i : ResidualPositions p) :
    i = residualPosition p := by
  apply (residualIndexEquiv p).injective
  exact Subsingleton.elim _ _

theorem uniformPosition_unique (p : SelectedSupport 1 2)
    (i : SourceUniformPositions p) : i = uniformPosition p := by
  apply (uniformIndexEquiv p).injective
  exact Subsingleton.elim _ _

def residualLabel (p : SelectedSupport 1 2) : Fin 4 := (residualPosition p).val

def uniformLabel (p : SelectedSupport 1 2) : Fin 4 := (uniformPosition p).val.val

theorem residualLabel_mem (p : SelectedSupport 1 2) :
    maskBit p.val.val.1 (residualLabel p) = true := (residualPosition p).property

theorem uniformLabel_not_residual (p : SelectedSupport 1 2) :
    maskBit p.val.val.1 (uniformLabel p) ≠ true := (uniformPosition p).val.property

theorem uniformLabel_not_inactive (p : SelectedSupport 1 2) :
    maskBit p.val.val.2 (uniformLabel p) ≠ true := (uniformPosition p).property

theorem residualLabel_not_inactive (p : SelectedSupport 1 2) :
    maskBit p.val.val.2 (residualLabel p) ≠ true := by
  intro hz
  exact p.val.property.1 _ hz (residualLabel_mem p)

theorem labels_ne (p : SelectedSupport 1 2) : residualLabel p ≠ uniformLabel p := by
  intro he
  apply uniformLabel_not_residual p
  rw [← he]
  exact residualLabel_mem p

theorem residualLabel_eq_of_mem (p : SelectedSupport 1 2) (i : Fin 4)
    (hi : maskBit p.val.val.1 i = true) : i = residualLabel p :=
  congrArg Subtype.val (residualPosition_unique p ⟨i, hi⟩)

theorem uniformLabel_eq_of_unmarked (p : SelectedSupport 1 2) (i : Fin 4)
    (hE : maskBit p.val.val.1 i ≠ true) (hz : maskBit p.val.val.2 i ≠ true) :
    i = uniformLabel p :=
  congrArg (fun j : SourceUniformPositions p => j.val.val)
    (uniformPosition_unique p ⟨⟨i, hE⟩, hz⟩)

/-- All other nonresidual labels are genuinely inactive. -/
theorem other_nonuniform_inactive (p : SelectedSupport 1 2)
    (i : OtherCoordinates p.val.val.1) (hi : i ≠ (uniformPosition p).val) :
    maskBit p.val.val.2 i.val = true := by
  by_contra hz
  apply hi
  exact congrArg (fun j : SourceUniformPositions p => j.val)
    (uniformPosition_unique p ⟨i, hz⟩)

section TupleEquivalences
variable {V : Type*}

/-- Evaluation of the actual singleton residual tuple as one alphabet value. -/
def residualTupleEquiv (p : SelectedSupport 1 2) : (ResidualPositions p → V) ≃ V where
  toFun x := x (residualPosition p)
  invFun u := fun _ => u
  left_inv x := by
    funext i
    exact congrArg x (residualPosition_unique p i).symm
  right_inv _ := rfl

/-- Evaluation of the actual singleton uniform tuple as one alphabet value. -/
def uniformTupleEquiv (p : SelectedSupport 1 2) :
    (SourceUniformPositions p → V) ≃ V where
  toFun x := x (uniformPosition p)
  invFun v := fun _ => v
  left_inv x := by
    funext i
    exact congrArg x (uniformPosition_unique p i).symm
  right_inv _ := rfl

end TupleEquivalences

section SourcePlane
variable {V : Type*} [Zero V]

/-- Original physical source: residual `u`, uniform `v`, two inactive zeros. -/
def source (p : SelectedSupport 1 2) (u v : V) : Fin 4 → V :=
  fun i => if i = residualLabel p then u else if i = uniformLabel p then v else 0

@[simp]
theorem source_residual (p : SelectedSupport 1 2) (u v : V) :
    source p u v (residualLabel p) = u := by simp [source]

@[simp]
theorem source_uniform (p : SelectedSupport 1 2) (u v : V) :
    source p u v (uniformLabel p) = v := by
  simp [source, Ne.symm (labels_ne p)]

theorem source_inactive (p : SelectedSupport 1 2) (u v : V) (i : Fin 4)
    (hi : maskBit p.val.val.2 i = true) : source p u v i = 0 := by
  have hr : i ≠ residualLabel p := by
    intro he
    subst i
    exact residualLabel_not_inactive p hi
  have hu : i ≠ uniformLabel p := by
    intro he
    subst i
    exact uniformLabel_not_inactive p hi
  simp only [source, if_neg hr, if_neg hu]

/-- This plane includes zero values of both active coordinates. -/
def OnPlane (p : SelectedSupport 1 2) (x : Fin 4 → V) : Prop :=
  ∀ i : Fin 4, maskBit p.val.val.2 i = true → x i = 0

theorem source_onPlane (p : SelectedSupport 1 2) (u v : V) : OnPlane p (source p u v) :=
  fun i hi => source_inactive p u v i hi

/-- The original residual and uniform coordinates recover every plane point. -/
theorem source_reconstruct (p : SelectedSupport 1 2) (x : Fin 4 → V) (hx : OnPlane p x) :
    source p (x (residualLabel p)) (x (uniformLabel p)) = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · have hi := residualLabel_eq_of_mem p i hE
    subst i
    exact source_residual p _ _
  · by_cases hz : maskBit p.val.val.2 i = true
    · exact (source_inactive p _ _ i hz).trans (hx i hz).symm
    · have hi := uniformLabel_eq_of_unmarked p i hE hz
      subst i
      exact source_uniform p _ _

theorem source_injective (p : SelectedSupport 1 2) :
    Function.Injective (fun uv : V × V => source p uv.1 uv.2) := by
  intro uv uv' he
  apply Prod.ext
  · have hr := congrFun he (residualLabel p)
    simpa only [source_residual] using hr
  · have hu := congrFun he (uniformLabel p)
    simpa only [source_uniform] using hu

/-- Exact two-coordinate parameterization with the original inactive mask. -/
def sourcePlaneEquiv (p : SelectedSupport 1 2) :
    (V × V) ≃ {x : Fin 4 → V // OnPlane p x} where
  toFun uv := ⟨source p uv.1 uv.2, source_onPlane p uv.1 uv.2⟩
  invFun x := (x.val (residualLabel p), x.val (uniformLabel p))
  left_inv uv := Prod.ext (source_residual p uv.1 uv.2) (source_uniform p uv.1 uv.2)
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property

end SourcePlane

section NormalizedRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Evaluate only public normalized-embedding definitions on the actual plane.
The unique uniform leg survives; both inactive zero-unit legs equal one. -/
theorem multiUniform_source (p : SelectedSupport 1 2)
    (g : (ResidualPositions p → V) → ℝ) (u v : V) :
    multiUniform p.val.val.2 p.val.val.1 g (source p u v) =
      g (fun _ => u) * nonzeroUniform v := by
  have hcoords : (fun i : ResidualPositions p => source p u v i.val) = fun _ => u := by
    funext i
    rw [residualPosition_unique p i]
    exact source_residual p u v
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
  change g (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

/-- The actual support component vanishes off its physical two-input plane. -/
theorem component_off_plane (p : SelectedSupport 1 2) (f : (Fin 4 → V) → ℝ)
    (x : Fin 4 → V) (hx : ¬ OnPlane p x) :
    supportIndexComponent (0 : V) p.val f x = 0 := by
  by_contra hnonzero
  apply hx
  intro i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero p.val i hi f x hnonzero

/-- One arbitrary signed `h`, the exact original source energy, and exact
off-plane support. No residual-at-zero or independence premise is introduced. -/
theorem normalized_source_representation (p : SelectedSupport 1 2)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : V → ℝ,
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnPlane p x → supportIndexComponent (0 : V) p.val f x = 0) := by
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
    exact component_off_plane p f x hx

end NormalizedRepresentation

/-- Actual AES-word specialization for the `(10,5)` source obligation. -/
theorem word_source_representation (p : SelectedSupport 1 2)
    (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∀ x, ¬ OnPlane p x → supportIndexComponent (0 : AES.Word) p.val f x = 0) :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.TwoActiveSource
