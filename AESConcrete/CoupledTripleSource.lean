import AESConcrete.CoupledTripleFiber
import AESConcrete.MultiUniformExpansion

/-!
# Physical source with a joint residual triple and one original uniform label

`(12,12)` source representation.

The full four-word input is a joint residual triple plus its sole ORIGINAL
uniform complement, including every zero value. Its one unit nonzero-uniform
factor occurs exactly once. Arbitrary signed joint amplitudes need no marked
fixed point; only extraction from an actual support component supplies one. No
factorization, centering or endpoint-cancellation premise is introduced.

Geometry and source normalization are the only roles here. Constructive fixed
independent-uniform-retained-key AES10/14/16, whitening, omitted final
MixColumns and ordered-distinct reference law remain fixed.

The selected minor, four analytic response energies, scalar aggregation,
physical factor16 and certificate/operator conversion remain separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleSource
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber (ResidualPositions originalUniformLabel)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform nonzeroUniform_energy)

set_option maxRecDepth 100000

/-- The actual multi-uniform input labels, with their physical indices. -/
abbrev SourceUniformPositions (p : SelectedSupport 3 4) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem sourceUniformPositions_card (p : SelectedSupport 3 4) :
    Fintype.card (SourceUniformPositions p) = 1 :=
  CoupledTripleFiber.multiUniformPositions_card p

/-- The sole uniform position is the original complement of the residual mask. -/
def uniformPosition (p : SelectedSupport 3 4) : SourceUniformPositions p :=
  ⟨⟨originalUniformLabel p, CoupledTripleFiber.originalUniform_not_residual p⟩,
    CoupledTripleFiber.originalUniform_not_inactive p⟩

theorem uniformPosition_label (p : SelectedSupport 3 4) :
    (uniformPosition p).val.val = originalUniformLabel p := rfl

theorem uniformPosition_unique (p : SelectedSupport 3 4)
    (i : SourceUniformPositions p) : i = uniformPosition p := by
  apply Subtype.ext
  apply Subtype.ext
  exact CoupledTripleFiber.multiUniformLabel_eq p i

theorem otherPosition_unique (p : SelectedSupport 3 4)
    (i : OtherCoordinates p.val.val.1) : i = (uniformPosition p).val := by
  apply Subtype.ext
  exact CoupledTripleFiber.nonretained_eq_omitted p i.val i.property

/-- Evaluating at the physical uniform label identifies its singleton tuple. -/
def uniformTupleEquiv {V : Type*} (p : SelectedSupport 3 4) :
    (SourceUniformPositions p → V) ≃ V where
  toFun v := v (uniformPosition p)
  invFun v := fun _ => v
  left_inv v := by
    funext i
    exact congrArg v (uniformPosition_unique p i).symm
  right_inv _ := rfl

theorem uniformTuple_card {V : Type*} [Fintype V] (p : SelectedSupport 3 4) :
    Fintype.card (SourceUniformPositions p → V) = Fintype.card V := by
  rw [Fintype.card_fun, sourceUniformPositions_card, pow_one]

section Source
variable {V : Type*} [AddCommGroup V]

/-- Full four-coordinate completion at the original input support. -/
def source (p : SelectedSupport 3 4) (u : ResidualPositions p → V) (v : V) :
    Fin 4 → V := CoupledTripleFiber.complete p u v

@[simp]
theorem source_residual (p : SelectedSupport 3 4) (u : ResidualPositions p → V)
    (v : V) (i : ResidualPositions p) : source p u v i.val = u i :=
  CoupledTripleFiber.complete_retained p u v i

@[simp]
theorem source_uniform (p : SelectedSupport 3 4) (u : ResidualPositions p → V)
    (v : V) : source p u v (originalUniformLabel p) = v :=
  CoupledTripleFiber.complete_omitted p u v

theorem source_uniform_position (p : SelectedSupport 3 4)
    (u : ResidualPositions p → V) (v : V) (i : SourceUniformPositions p) :
    source p u v i.val.val = v := by
  rw [CoupledTripleFiber.multiUniformLabel_eq p i]
  exact source_uniform p u v

theorem source_reconstruct (p : SelectedSupport 3 4) (x : Fin 4 → V) :
    source p (restrictCoordinates p.val.val.1 x) (x (originalUniformLabel p)) = x :=
  CoupledTripleFiber.complete_reconstruct p x

/-- This is a full-source equivalence, not an equivalence of a retained image. -/
def sourceEquiv (p : SelectedSupport 3 4) :
    ((ResidualPositions p → V) × V) ≃ (Fin 4 → V) :=
  CoupledTripleFiber.sourceEquiv p

@[simp]
theorem sourceEquiv_apply (p : SelectedSupport 3 4)
    (uv : (ResidualPositions p → V) × V) :
    sourceEquiv p uv = source p uv.1 uv.2 := rfl

theorem source_injective (p : SelectedSupport 3 4) :
    Function.Injective (fun uv : (ResidualPositions p → V) × V =>
      source p uv.1 uv.2) :=
  (sourceEquiv p).injective

theorem source_zero (p : SelectedSupport 3 4) :
    source p (0 : ResidualPositions p → V) 0 = 0 :=
  CoupledTripleFiber.complete_zero p

theorem source_pair_add (p : SelectedSupport 3 4)
    (uv uv' : (ResidualPositions p → V) × V) :
    source p (uv + uv').1 (uv + uv').2 =
      source p uv.1 uv.2 + source p uv'.1 uv'.2 :=
  CoupledTripleFiber.complete_add p uv.1 uv'.1 uv.2 uv'.2

def sourceAddEquiv (p : SelectedSupport 3 4) :
    ((ResidualPositions p → V) × V) ≃+ (Fin 4 → V) :=
  { sourceEquiv p with map_add' := source_pair_add p }

theorem residualHom_source (p : SelectedSupport 3 4) (u : ResidualPositions p → V)
    (v : V) : CoupledTripleFiber.residualHom p (source p u v) = u := by
  funext i
  exact source_residual p u v i

theorem source_uniform_axis (p : SelectedSupport 3 4) (v : V) :
    source p (0 : ResidualPositions p → V) v = Pi.single (originalUniformLabel p) v :=
  CoupledTripleFiber.complete_zero_left p v

end Source

section NormalizedRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- A joint amplitude on the original residual triple, with one unit leg. -/
def normalizedAmplitude (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → V) → ℝ) : ((ResidualPositions p → V) × V) → ℝ :=
  fun uv => h uv.1 * nonzeroUniform uv.2

/-- The corresponding function on every physical four-coordinate input. -/
def physicalAmplitude (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → V) → ℝ) (x : Fin 4 → V) : ℝ :=
  h (CoupledTripleFiber.residualHom p x) * nonzeroUniform (x (originalUniformLabel p))

theorem physicalAmplitude_source (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → V) → ℝ) (u : ResidualPositions p → V) (v : V) :
    physicalAmplitude p h (source p u v) = h u * nonzeroUniform v := by
  simp only [physicalAmplitude, residualHom_source, source_uniform]

/-- Exact energy for every signed joint h; no marked fixed point is assumed. -/
theorem normalizedAmplitude_energy (p : SelectedSupport 3 4)
    (hn : 1 < Fintype.card V) (h : (ResidualPositions p → V) → ℝ) :
    (∑ uv, normalizedAmplitude p h uv ^ 2) = ∑ u, h u ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [normalizedAmplitude, mul_pow]
  rw [← Finset.mul_sum, nonzeroUniform_energy hn, mul_one]

theorem physicalAmplitude_energy (p : SelectedSupport 3 4)
    (hn : 1 < Fintype.card V) (h : (ResidualPositions p → V) → ℝ) :
    (∑ x, physicalAmplitude p h x ^ 2) = ∑ u, h u ^ 2 := by
  calc
    _ = ∑ uv : (ResidualPositions p → V) × V,
        physicalAmplitude p h (source p uv.1 uv.2) ^ 2 :=
      (Equiv.sum_comp (sourceEquiv p) (fun x => physicalAmplitude p h x ^ 2)).symm
    _ = ∑ uv, normalizedAmplitude p h uv ^ 2 := by
      apply Finset.sum_congr rfl
      intro uv _
      rw [physicalAmplitude_source]
      rfl
    _ = ∑ u, h u ^ 2 := normalizedAmplitude_energy p hn h

theorem multiUniform_source (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → V) → ℝ) (u : ResidualPositions p → V) (v : V) :
    multiUniform p.val.val.2 p.val.val.1 h (source p u v) = h u * nonzeroUniform v := by
  have hcoords : (fun i : ResidualPositions p => source p u v i.val) = u := by
    funext i
    exact source_residual p u v i
  have hprod : (∏ i : OtherCoordinates p.val.val.1,
      normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) =
      nonzeroUniform v := by
    rw [Finset.prod_eq_single (uniformPosition p).val]
    · change normalizedLeg (maskBit p.val.val.2 (originalUniformLabel p))
        (source p u v (originalUniformLabel p)) = nonzeroUniform v
      rw [source_uniform]
      simp only [normalizedLeg, if_neg (CoupledTripleFiber.originalUniform_not_inactive p)]
    · intro i _ hi
      exact (hi (otherPosition_unique p i)).elim
    · simp
  unfold multiUniform coordinateEmbedding
  change h (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

theorem multiUniform_eq_physicalAmplitude (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → V) → ℝ) :
    multiUniform p.val.val.2 p.val.val.1 h = physicalAmplitude p h := by
  funext x
  obtain ⟨uv, huv⟩ := (sourceEquiv p).surjective x
  have hs : source p uv.1 uv.2 = x := huv
  rw [← hs, multiUniform_source, physicalAmplitude_source]

/-- Only this genuine support-component extraction supplies the fixed point. -/
theorem supportIndexComponent_representation (p : SelectedSupport 3 4)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (ResidualPositions p → V) → ℝ,
      markedResidual p.val.val.1 h = h ∧
      supportIndexComponent (0 : V) p.val f = physicalAmplitude p h ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 := by
  obtain ⟨h, hh, hG, henergy⟩ := supportIndexComponent_multi_uniform p.val hn f
  exact ⟨h, hh, hG.trans (multiUniform_eq_physicalAmplitude p h), henergy⟩

theorem normalized_source_representation (p : SelectedSupport 3 4)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (ResidualPositions p → V) → ℝ,
      markedResidual p.val.val.1 h = h ∧
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 := by
  obtain ⟨h, hh, hG, henergy⟩ := supportIndexComponent_representation p hn f
  refine ⟨h, hh, ?_, henergy⟩
  intro u v
  rw [hG]
  exact physicalAmplitude_source p h u v

end NormalizedRepresentation

abbrev SourceWord (p : SelectedSupport 3 4) := (ResidualPositions p → AES.Word) × AES.Word

def sourceWordEquiv (p : SelectedSupport 3 4) : SourceWord p ≃ AES.WordState :=
  sourceEquiv p

def sourceWordAddEquiv (p : SelectedSupport 3 4) : SourceWord p ≃+ AES.WordState :=
  sourceAddEquiv p

theorem word_normalizedAmplitude_energy (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → AES.Word) → ℝ) :
    (∑ uv, normalizedAmplitude p h uv ^ 2) = ∑ u, h u ^ 2 :=
  normalizedAmplitude_energy p AES.word_card_gt_one h

theorem word_physicalAmplitude_energy (p : SelectedSupport 3 4)
    (h : (ResidualPositions p → AES.Word) → ℝ) :
    (∑ x, physicalAmplitude p h x ^ 2) = ∑ u, h u ^ 2 :=
  physicalAmplitude_energy p AES.word_card_gt_one h

theorem word_source_representation (p : SelectedSupport 3 4) (f : AES.WordState → ℝ) :
    ∃ h : (ResidualPositions p → AES.Word) → ℝ,
      markedResidual p.val.val.1 h = h ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * nonzeroUniform v) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.CoupledTripleSource
