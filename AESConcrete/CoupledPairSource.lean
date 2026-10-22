import AESConcrete.CoupledPairFiber

/-!
# Physical source with two residual and two original uniform labels

The residual amplitude is an arbitrary signed joint function on its two
physical labels. The source equivalence enumerates all four physical input
words, including zeros. It does not parameterize the retained triple. The two
unit nonzero-uniform input factors occur once each.

The actual support-component representation supplies a marked-residual fixed
point and exact counting energy. Analytic responses may use arbitrary joint
amplitudes without importing that fixed-point property as an implicit premise.
No Fourier estimate, physical cap or inventory change is asserted.
Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairSource
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairFiber (ResidualPositions inactiveLabel_not)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)

set_option maxRecDepth 100000

/-- Both original active nonresidual labels retain their physical indices. -/
abbrev SourceUniformPositions (p : SelectedSupport 2 4) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem sourceUniformPositions_card (p : SelectedSupport 2 4) :
    Fintype.card (SourceUniformPositions p) = 2 := by
  rw [Fintype.card_congr (CoupledPairFiber.originalUniformPositionEquiv p)]
  exact CoupledPairFiber.originalUniformPositions_card p

theorem uniformTuple_card {V : Type*} [Fintype V] (p : SelectedSupport 2 4) :
    Fintype.card (SourceUniformPositions p → V) = Fintype.card V ^ 2 := by
  rw [Fintype.card_fun, sourceUniformPositions_card]

section Source
variable {V : Type*} [Zero V]

def source (p : SelectedSupport 2 4) (u : ResidualPositions p → V)
    (v : SourceUniformPositions p → V) : Fin 4 → V :=
  fun i => if hE : maskBit p.val.val.1 i = true then u ⟨i, hE⟩
    else if hz : maskBit p.val.val.2 i = true then 0 else v ⟨⟨i, hE⟩, hz⟩

@[simp]
theorem source_residual (p : SelectedSupport 2 4) (u : ResidualPositions p → V)
    (v : SourceUniformPositions p → V) (i : ResidualPositions p) :
    source p u v i.val = u i := by
  simp only [source, dif_pos i.property]

@[simp]
theorem source_uniform (p : SelectedSupport 2 4) (u : ResidualPositions p → V)
    (v : SourceUniformPositions p → V) (i : SourceUniformPositions p) :
    source p u v i.val.val = v i := by
  simp only [source, dif_neg i.val.property, dif_neg i.property]

theorem source_reconstruct (p : SelectedSupport 2 4) (x : Fin 4 → V) :
    source p (fun i => x i.val) (fun i => x i.val.val) = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · exact source_residual p _ _ ⟨i, hE⟩
  · exact source_uniform p _ _ ⟨⟨i, hE⟩, inactiveLabel_not p i⟩

theorem source_injective (p : SelectedSupport 2 4) :
    Function.Injective (fun uv : (ResidualPositions p → V) ×
      (SourceUniformPositions p → V) => source p uv.1 uv.2) := by
  intro uv uv' he
  apply Prod.ext
  · funext i
    have hr := congrFun he i.val
    simpa only [source_residual] using hr
  · funext i
    have hu := congrFun he i.val.val
    simpa only [source_uniform] using hu

/-- Full four-word source equivalence, independent of any output projection. -/
def sourceEquiv (p : SelectedSupport 2 4) :
    ((ResidualPositions p → V) × (SourceUniformPositions p → V)) ≃ (Fin 4 → V) where
  toFun uv := source p uv.1 uv.2
  invFun x := (fun i => x i.val, fun i => x i.val.val)
  left_inv uv := by
    apply Prod.ext
    · funext i
      exact source_residual p uv.1 uv.2 i
    · funext i
      exact source_uniform p uv.1 uv.2 i
  right_inv x := source_reconstruct p x

theorem source_zero (p : SelectedSupport 2 4) : source p (0 : ResidualPositions p → V) 0 = 0 := by
  funext i
  simp [source]

end Source

section AdditiveSource
variable {V : Type*} [AddCommGroup V]

theorem source_pair_add (p : SelectedSupport 2 4)
    (uv uv' : (ResidualPositions p → V) × (SourceUniformPositions p → V)) :
    source p (uv + uv').1 (uv + uv').2 = source p uv.1 uv.2 + source p uv'.1 uv'.2 := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · simp [source, hE]
  · simp [source, hE, inactiveLabel_not p i]

def sourceAddEquiv (p : SelectedSupport 2 4) :
    ((ResidualPositions p → V) × (SourceUniformPositions p → V)) ≃+ (Fin 4 → V) :=
  { sourceEquiv p with map_add' := source_pair_add p }

theorem residualHom_source (p : SelectedSupport 2 4) (u : ResidualPositions p → V)
    (v : SourceUniformPositions p → V) :
    CoupledPairFiber.residualHom p (source p u v) = u := by
  funext i
  exact source_residual p u v i

end AdditiveSource

section ActualRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exact joint amplitude times the two original unit nonzero-uniform factors. -/
theorem multiUniform_source (p : SelectedSupport 2 4)
    (h : (ResidualPositions p → V) → ℝ) (u : ResidualPositions p → V)
    (v : SourceUniformPositions p → V) :
    multiUniform p.val.val.2 p.val.val.1 h (source p u v) =
      h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i) := by
  have hcoords : (fun i : ResidualPositions p => source p u v i.val) = u := by
    funext i
    exact source_residual p u v i
  have hprod : (∏ i : OtherCoordinates p.val.val.1,
      normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) =
      ∏ i : SourceUniformPositions p, nonzeroUniform (v i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun i : OtherCoordinates p.val.val.1 => maskBit p.val.val.2 i.val = true)]
    have hI (i : MultiUniformExpansion.InactivePositions p.val.val.2 p.val.val.1) :
        normalizedLeg (maskBit p.val.val.2 i.val.val) (source p u v i.val.val) = 1 :=
      (inactiveLabel_not p i.val.val i.property).elim
    have hU (i : SourceUniformPositions p) :
        normalizedLeg (maskBit p.val.val.2 i.val.val) (source p u v i.val.val) =
          nonzeroUniform (v i) := by
      rw [source_uniform]
      simp only [normalizedLeg, if_neg i.property]
    simp_rw [hI, hU]
    simp only [Finset.prod_const_one, one_mul]
  unfold multiUniform coordinateEmbedding
  change h (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

/-- The extracted amplitude is joint and has exactly the component's energy. -/
theorem normalized_source_representation (p : SelectedSupport 2 4)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (ResidualPositions p → V) → ℝ,
      markedResidual p.val.val.1 h = h ∧
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 := by
  obtain ⟨h, hh, hG, henergy⟩ := supportIndexComponent_multi_uniform p.val hn f
  refine ⟨h, hh, ?_, henergy⟩
  intro u v
  rw [hG]
  exact multiUniform_source p h u v

end ActualRepresentation

abbrev SourceWord (p : SelectedSupport 2 4) :=
  (ResidualPositions p → AES.Word) × (SourceUniformPositions p → AES.Word)

def sourceWordEquiv (p : SelectedSupport 2 4) : SourceWord p ≃ AES.WordState :=
  sourceEquiv p

theorem word_source_representation (p : SelectedSupport 2 4) (f : AES.WordState → ℝ) :
    ∃ h : (ResidualPositions p → AES.Word) → ℝ,
      markedResidual p.val.val.1 h = h ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.CoupledPairSource
