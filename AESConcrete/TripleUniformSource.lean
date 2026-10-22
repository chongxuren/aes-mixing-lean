import AESConcrete.MultiUniformExpansion
import AESConcrete.ResidualIncidenceCoefficient

/-!
# Future source interface: one residual and three original uniform inputs

SelectedSupport 1 4 has no inactive input. Its physical residual label is a
singleton, while all three other original labels remain a labelled tuple.
The extracted actual amplitude retains the marked-residual fixed-point
consequences h(0)=0 and sum h=0. Arbitrary signed response amplitudes are a
separate interface and are not silently given these properties.

Future candidate only, outside the current double-uniform source inventory.
No compilation, MDS geometry, physical cap or inventory admission is asserted.
Constructive mathematics only; no attacks. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct reference pairs and the
fixed AES 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion
  (multiUniform normalizedLeg supportIndexComponent_multi_uniform)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)

set_option maxRecDepth 100000

abbrev ResidualPositions (p : SelectedSupport 1 4) := MaskCoordinates p.val.val.1

/-- The original three nonresidual active labels, without choosing an order. -/
abbrev SourceUniformPositions (p : SelectedSupport 1 4) :=
  MultiUniformExpansion.UniformPositions p.val.val.2 p.val.val.1

theorem inactiveMask_size (p : SelectedSupport 1 4) : maskSize p.val.val.2 = 0 := by
  have hp := p.property
  omega

theorem inactiveLabel_not (p : SelectedSupport 1 4) (i : Fin 4) :
    maskBit p.val.val.2 i ≠ true := by
  intro hi
  have hpos : 0 < Fintype.card (MaskCoordinates p.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, inactiveMask_size] at hpos
  omega

theorem residualPositions_card (p : SelectedSupport 1 4) :
    Fintype.card (ResidualPositions p) = 1 := by
  have hd := p.val.property.2
  norm_num at hd
  simpa only [← Nat.card_eq_fintype_card, ResidualPositions] using
    (maskCoordinates_card p.val.val.1).trans hd

theorem sourceUniformPositions_card (p : SelectedSupport 1 4) :
    Fintype.card (SourceUniformPositions p) = 3 := by
  have hc := MultiUniformExpansion.uniformPositions_card
    p.val.val.2 p.val.val.1 p.val.property.1
  have hs : 4 - (maskSize p.val.val.2 + maskSize p.val.val.1) = 3 := by
    have hp := p.property
    have hd := p.val.property.2
    omega
  simpa only [← Nat.card_eq_fintype_card, SourceUniformPositions] using hc.trans hs

theorem uniformTuple_card {V : Type*} [Fintype V] (p : SelectedSupport 1 4) :
    Fintype.card (SourceUniformPositions p → V) = Fintype.card V ^ 3 := by
  rw [Fintype.card_fun, sourceUniformPositions_card]

def residualIndexEquiv (p : SelectedSupport 1 4) : ResidualPositions p ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [residualPositions_card]; simp)

def residualPosition (p : SelectedSupport 1 4) : ResidualPositions p :=
  (residualIndexEquiv p).symm 0

theorem residualPosition_unique (p : SelectedSupport 1 4) (i : ResidualPositions p) :
    i = residualPosition p := by
  apply (residualIndexEquiv p).injective
  exact Subsingleton.elim _ _

def residualLabel (p : SelectedSupport 1 4) : Fin 4 := (residualPosition p).val

theorem residualLabel_mem (p : SelectedSupport 1 4) :
    maskBit p.val.val.1 (residualLabel p) = true := (residualPosition p).property

theorem residualLabel_eq_of_mem (p : SelectedSupport 1 4) (i : Fin 4)
    (hi : maskBit p.val.val.1 i = true) : i = residualLabel p :=
  congrArg Subtype.val (residualPosition_unique p ⟨i, hi⟩)

def residualTupleEquiv {V : Type*} (p : SelectedSupport 1 4) :
    (ResidualPositions p → V) ≃ V where
  toFun x := x (residualPosition p)
  invFun u := fun _ => u
  left_inv x := by
    funext i
    exact congrArg x (residualPosition_unique p i).symm
  right_inv _ := rfl

section Source
variable {V : Type*} [Zero V]

/-- Four original input values; the inactive branch is impossible for this type. -/
def source (p : SelectedSupport 1 4) (u : V) (v : SourceUniformPositions p → V) :
    Fin 4 → V :=
  fun i => if hE : maskBit p.val.val.1 i = true then u
    else if hz : maskBit p.val.val.2 i = true then 0 else v ⟨⟨i, hE⟩, hz⟩

@[simp]
theorem source_residual (p : SelectedSupport 1 4) (u : V)
    (v : SourceUniformPositions p → V) : source p u v (residualLabel p) = u := by
  simp only [source, dif_pos (residualLabel_mem p)]

@[simp]
theorem source_uniform (p : SelectedSupport 1 4) (u : V)
    (v : SourceUniformPositions p → V) (i : SourceUniformPositions p) :
    source p u v i.val.val = v i := by
  simp only [source, dif_neg i.val.property, dif_neg i.property]

theorem source_inactive (p : SelectedSupport 1 4) (u : V)
    (v : SourceUniformPositions p → V) (i : Fin 4)
    (hi : maskBit p.val.val.2 i = true) : source p u v i = 0 :=
  (inactiveLabel_not p i hi).elim

theorem source_reconstruct (p : SelectedSupport 1 4) (x : Fin 4 → V) :
    source p (x (residualLabel p)) (fun i => x i.val.val) = x := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · have hi := residualLabel_eq_of_mem p i hE
    subst i
    exact source_residual p _ _
  · exact source_uniform p _ _ ⟨⟨i, hE⟩, inactiveLabel_not p i⟩

theorem source_injective (p : SelectedSupport 1 4) :
    Function.Injective
      (fun uv : V × (SourceUniformPositions p → V) => source p uv.1 uv.2) := by
  intro uv uv' he
  apply Prod.ext
  · have hr := congrFun he (residualLabel p)
    simpa only [source_residual] using hr
  · funext i
    have hu := congrFun he i.val.val
    simpa only [source_uniform] using hu

/-- This equivalence is to all four source inputs, not to three retained outputs. -/
def sourceEquiv (p : SelectedSupport 1 4) :
    (V × (SourceUniformPositions p → V)) ≃ (Fin 4 → V) where
  toFun uv := source p uv.1 uv.2
  invFun x := (x (residualLabel p), fun i => x i.val.val)
  left_inv uv := by
    apply Prod.ext
    · exact source_residual p uv.1 uv.2
    · funext i
      exact source_uniform p uv.1 uv.2 i
  right_inv x := source_reconstruct p x

theorem source_zero (p : SelectedSupport 1 4) : source p (0 : V) 0 = 0 := by
  funext i
  simp [source]

theorem source_residual_axis (p : SelectedSupport 1 4) (u : V) :
    source p u 0 = Pi.single (residualLabel p) u := by
  funext i
  by_cases hi : i = residualLabel p
  · subst i
    simp
  · have hE : maskBit p.val.val.1 i ≠ true := by
      intro hE
      exact hi (residualLabel_eq_of_mem p i hE)
    simp [source, hE, hi]

end Source

section AdditiveSource
variable {V : Type*} [AddCommGroup V]

theorem source_pair_add (p : SelectedSupport 1 4)
    (uv uv' : V × (SourceUniformPositions p → V)) :
    source p (uv + uv').1 (uv + uv').2 = source p uv.1 uv.2 + source p uv'.1 uv'.2 := by
  funext i
  by_cases hE : maskBit p.val.val.1 i = true
  · simp [source, hE]
  · simp [source, hE, inactiveLabel_not p i]

def sourceAddEquiv (p : SelectedSupport 1 4) :
    (V × (SourceUniformPositions p → V)) ≃+ (Fin 4 → V) :=
  { sourceEquiv p with map_add' := source_pair_add p }

end AdditiveSource

section ActualRepresentation
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exactly three unit nonzero-uniform factors retain their physical labels. -/
theorem multiUniform_source (p : SelectedSupport 1 4)
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
  change g (fun i : ResidualPositions p => source p u v i.val) *
      (∏ i : OtherCoordinates p.val.val.1,
        normalizedLeg (maskBit p.val.val.2 i.val) (source p u v i.val)) = _
  rw [hcoords, hprod]

/-- The actual amplitude's zero and zero-sum constraints follow from its
marked-residual fixed point, before any diffusion or response estimate. -/
theorem residual_amplitude_constraints (p : SelectedSupport 1 4)
    (hn : 1 < Fintype.card V) (g : (ResidualPositions p → V) → ℝ)
    (hg : markedResidual p.val.val.1 g = g) :
    g (fun _ => 0) = 0 ∧ (∑ u : V, g (fun _ => u)) = 0 := by
  have hgzero : g 0 = 0 := by
    calc
      g 0 = markedResidual p.val.val.1 g 0 := (congrFun hg 0).symm
      _ = 0 := markedResidual_zero p.val.val.1 (residualPosition p) g
  have hgsum : (∑ w, g w) = 0 := by
    have hs := markedResidual_sum hn p.val.val.1 (residualPosition p) g
    rw [hg] at hs
    exact hs
  constructor
  · exact hgzero
  · have hs := (residualTupleEquiv (V := V) p).symm.sum_comp (fun w => g w)
    change (∑ u : V, g (fun _ => u)) = ∑ w, g w at hs
    exact hs.trans hgsum

/-- Actual source representation and exact counting energy, retaining both
residual constraints. The signed h is not assumed positive or factored. -/
theorem normalized_source_representation (p : SelectedSupport 1 4)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : V → ℝ,
      h 0 = 0 ∧ (∑ u, h u) = 0 ∧
      (∀ u v, supportIndexComponent (0 : V) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : V) p.val f x ^ 2) = ∑ u, h u ^ 2 := by
  obtain ⟨g, hg, hG, henergy⟩ := supportIndexComponent_multi_uniform p.val hn f
  obtain ⟨hgzero, hgsum⟩ := residual_amplitude_constraints p hn g hg
  refine ⟨fun u => g (fun _ => u), hgzero, hgsum, ?_, ?_⟩
  · intro u v
    rw [hG]
    exact multiUniform_source p g u v
  · rw [henergy]
    change (∑ w : ResidualPositions p → V, g w ^ 2) =
      ∑ u : V, g ((residualTupleEquiv (V := V) p).symm u) ^ 2
    exact ((residualTupleEquiv (V := V) p).symm.sum_comp (fun w => g w ^ 2)).symm

end ActualRepresentation

theorem word_source_representation (p : SelectedSupport 1 4) (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      h 0 = 0 ∧ (∑ u, h u) = 0 ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) p.val f (source p u v) =
        h u * ∏ i : SourceUniformPositions p, nonzeroUniform (v i)) ∧
      (∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2) = ∑ u, h u ^ 2 :=
  normalized_source_representation p AES.word_card_gt_one f

end AESConcrete.TripleUniformSource
