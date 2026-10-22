import AES8.Math.PaperRestrictedDiffusionMass
import AESConcrete.WordColumnGram
import AESConcrete.WordColumnBounds
import AESMixing.SupportRepresentation

/-!
# Support projection of a pointed tensor channel

Exact physical factorization for an arbitrary finite additive alphabet and
an arbitrary joint source. The extra nonzero indicator retains the actual
source event; every unmarked nonzero position supplies one inverse alphabet
factor in counting-measure energy. No probability or norm cap is assumed.
The source indicator is kept inside the summed source weight, so the same
identity applies to correlated inputs and to additional source restrictions.
Constructive mathematics only; no attacks or manuscript changes.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperPointedSupportResponse
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.WordColumnGram (tensorResponse)
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Left residual projection gives the actual residual channel. -/
theorem residualProjection_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0) :
    kernelCompose (residualProjection 0) S = residualMatrix S 0 := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  change action (residualProjection 0) (action S f) = action (S - activityMatrix 0) f
  rw [residualProjection_action, wordResidual, hS.average_action,
    kernel_action_sub, activityMatrix_action]

/-- The zero part of a pointed channel is unchanged. -/
theorem zeroPart_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0) (f : V → ℝ) :
    zeroPart 0 (action S f) = zeroPart 0 f := by
  funext y
  simp only [zeroPart, hS.action_zero]

theorem zeroMatrix_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0) :
    kernelCompose (zeroMatrix (0 : V)) S = zeroMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, zeroMatrix_action, zeroPart_channel S hS]

theorem constantMatrix_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0) :
    kernelCompose (constantMatrix (0 : V)) S = constantMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, constantMatrix_action,
    hS.average_action, zeroPart_channel S hS]

theorem unmarked_support_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0) (b : Bool) :
    kernelCompose (supportPiece (0 : V) false b) S =
      supportPiece 0 false b := by
  cases b
  · simpa only [supportPiece, Bool.false_eq_true, if_false] using constantMatrix_channel S hS
  · simpa only [supportPiece, Bool.false_eq_true, if_false, if_true] using zeroMatrix_channel S hS

/-- The marked residual column, retaining each physical output position. -/
def markedColumn (S : V → V → ℝ) (out : Fin 16)
    (y : MaskCoordinates out → V) (v : (Fin 4 → V)) : ℝ :=
  ∏ i : MaskCoordinates out, residualMatrix S 0 (y i) (v i.val)

def unmarkedConstant (r out : Fin 16) (y : (Fin 4 → V)) : ℝ :=
  ∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportConstant (maskBit r i.val) (y i.val)

def unmarkedDual (r out : Fin 16) (v : (Fin 4 → V)) : ℝ :=
  ∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportDualConstant (maskBit r i.val) (v i.val)

/-- Exact one-column factorization after the pointed channel. -/
theorem projected_substitution_factor (S : V → V → ℝ) (hS : PointedBistochastic S 0) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y v : (Fin 4 → V)) :
    kernelCompose (supportProduct (0 : V) (maskBit out) (maskBit r))
      (coordinateKernel (fun _ : Fin 4 => S)) y v =
      markedColumn S out (fun i => y i.val) v * unmarkedConstant r out y *
        unmarkedDual r out v := by
  change kernelCompose
    (coordinateKernel (fun i : Fin 4 => supportPiece (0 : V) (maskBit out i) (maskBit r i)))
    (coordinateKernel (fun _ : Fin 4 => S)) y v = _
  rw [coordinateKernel_compose]
  change (∏ i : Fin 4,
    kernelCompose (supportPiece (0 : V) (maskBit out i) (maskBit r i)) S
      (y i) (v i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin 4 => maskBit out i = true)]
  have hm (i : MaskCoordinates out) :
      kernelCompose (supportPiece (0 : V) (maskBit out i.val) (maskBit r i.val))
        S (y i.val) (v i.val) =
        residualMatrix S 0 (y i.val) (v i.val) := by
    have hi : maskBit r i.val = false :=
      Bool.eq_false_iff.mpr (fun h => hr i.val h i.property)
    rw [i.property, hi]
    simpa only [supportPiece, if_true, Bool.false_eq_true, if_false, degreePiece, bytePiece] using
      congrFun (congrFun (residualProjection_channel S hS) (y i.val)) (v i.val)
  have hu (i : {i : Fin 4 // maskBit out i ≠ true}) :
      kernelCompose (supportPiece (0 : V) (maskBit out i.val) (maskBit r i.val))
        S (y i.val) (v i.val) =
        supportConstant (maskBit r i.val) (y i.val) *
          supportDualConstant (maskBit r i.val) (v i.val) := by
    have hi : maskBit out i.val = false := Bool.eq_false_iff.mpr i.property
    rw [hi, unmarked_support_channel S hS]
    exact supportPiece_unmarked (V := V) (maskBit r i.val) (y i.val) (v i.val)
  simp_rw [hm, hu]
  rw [Finset.prod_mul_distrib]
  change _ * (_ * _) = _ * _ * _
  exact (mul_assoc _ _ _).symm

/-- Exactly r is zero, including all unmarked and marked physical positions. -/
def exactZeroPattern (r : Fin 16) (v : (Fin 4 → V)) : Prop :=
  ∀ i : Fin 4, v i = 0 ↔ maskBit r i = true

instance (r : Fin 16) : DecidablePred (exactZeroPattern (V := V) r) := by
  intro v
  unfold exactZeroPattern
  infer_instance

/-- Product of the dual constants on its exact support. -/
theorem unmarkedDual_on_pattern (r out : Fin 16) (hr : MaskDisjoint r out) (v : (Fin 4 → V))
    (hv : exactZeroPattern r v) :
    unmarkedDual r out v = ((1 : ℝ)/((Fintype.card V : ℝ)-1)) ^ (4-(maskSize r+maskSize out)) := by
  unfold unmarkedDual
  calc
    _ = ∏ i : {i : Fin 4 // maskBit out i ≠ true},
        if maskBit r i.val = true then (1 : ℝ) else (1 : ℝ)/((Fintype.card V : ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : maskBit r i.val = true
      · have hzero : v i.val = 0 := (hv i.val).mpr hi
        simp [supportDualConstant, supportConstant, identityKernel, hi, hzero]
      · have hnonzero : v i.val ≠ 0 := fun hzero => hi ((hv i.val).mp hzero)
        simp [supportDualConstant, supportConstant, identityKernel, hi, hnonzero]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
      rw [unmarked_coordinate_count r out hr]

/-- Outside the exact support, a dual or marked residual factor vanishes. -/
theorem markedColumn_mul_dual_zero (S : V → V → ℝ) (hS : PointedBistochastic S 0) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y : MaskCoordinates out → V) (v : (Fin 4 → V))
    (hv : ¬ exactZeroPattern r v) :
    markedColumn S out y v * unmarkedDual r out v = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hv
  by_cases hri : maskBit r i = true
  · have hvi : v i ≠ 0 := by
      intro hzero
      exact hi ⟨fun _ => hri, fun _ => hzero⟩
    have hoi : maskBit out i ≠ true := hr i hri
    have hd : unmarkedDual r out v = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : {j : Fin 4 // maskBit out j ≠ true}))
      simp [supportDualConstant, supportConstant, identityKernel, hri, hvi]
    rw [hd, mul_zero]
  · have hvi : v i = 0 := by
      by_contra hnonzero
      exact hi ⟨fun hzero => (hnonzero hzero).elim, fun hr => (hri hr).elim⟩
    by_cases hoi : maskBit out i = true
    · have hm : markedColumn S out y v = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : MaskCoordinates out))
        change residualMatrix S 0 (y ⟨i,hoi⟩) (v i) = 0
        rw [hvi]
        exact AESConcrete.pointed_residual_zero_column hS _
      rw [hm, zero_mul]
    · have hd : unmarkedDual r out v = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : {j : Fin 4 // maskBit out j ≠ true}))
        simp [supportDualConstant, supportConstant, identityKernel, hri, hvi]
      rw [hd, mul_zero]

theorem markedColumn_mul_dual (S : V → V → ℝ) (hS : PointedBistochastic S 0) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y : MaskCoordinates out → V) (v : (Fin 4 → V)) :
    markedColumn S out y v * unmarkedDual r out v =
      ((1 : ℝ)/((Fintype.card V : ℝ)-1)) ^ (4-(maskSize r+maskSize out)) *
        (if exactZeroPattern r v then markedColumn S out y v else 0) := by
  by_cases hv : exactZeroPattern r v
  · rw [if_pos hv, unmarkedDual_on_pattern r out hr v hv]
    exact mul_comm _ _
  · rw [if_neg hv, mul_zero]
    exact markedColumn_mul_dual_zero S hS r out hr y v hv

theorem projected_substitution_entry (S : V → V → ℝ) (hS : PointedBistochastic S 0) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y v : (Fin 4 → V)) :
    kernelCompose (supportProduct (0 : V) (maskBit out) (maskBit r))
      (coordinateKernel (fun _ : Fin 4 => S)) y v =
      (((1 : ℝ)/((Fintype.card V : ℝ)-1)) ^ (4-(maskSize r+maskSize out)) *
        (if exactZeroPattern r v then markedColumn S out (fun i => y i.val) v else 0)) *
          unmarkedConstant r out y := by
  rw [projected_substitution_factor S hS r out hr]
  calc
    _ = (markedColumn S out (fun i => y i.val) v * unmarkedDual r out v) *
        unmarkedConstant r out y := by ring
    _ = _ := by rw [markedColumn_mul_dual S hS r out hr]

variable {X : Type*} [Fintype X]

/-- A nonnegative original-source weight is bounded by its total mass.
Keep this generic to avoid unfolding concrete finite word alphabets. -/
theorem source_weight_le_mass (mu : X → ℝ) (hmu : ∀ x, 0 ≤ mu x) (x : X) :
    mu x ≤ ∑ y, mu y := by
  classical
  exact Finset.single_le_sum (fun y _ => hmu y) (Finset.mem_univ x)

/-- Keep the exact zero event, including nonzero status at every other
position. This is an indicator on the original source, without conditioning. -/
def exactSource (r : Fin 16) (coord : X → Fin 4 → V) (mu : X → ℝ) (x : X) : ℝ :=
  if exactZeroPattern r (coord x) then mu x else 0

theorem project_tensorResponse (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (S : V → V → ℝ) (coord : X → Fin 4 → V) (mu : X → ℝ) (y : Fin 4 → V) :
    action K (tensorResponse (fun _ : Fin 4 => S) coord mu) y =
      ∑ x : X, kernelCompose K (coordinateKernel (fun _ : Fin 4 => S))
        y (coord x) * mu x := by
  simp only [action, tensorResponse, AESConcrete.WordColumnGram.tensorColumn,
    coordinateKernel, kernelCompose, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Exact support component of an arbitrary source after the pointed
tensor channel. No product-source or source-mass hypothesis is used. -/
theorem support_response (S : V → V → ℝ) (hS : PointedBistochastic S 0)
    (r out : Fin 16) (hr : MaskDisjoint r out)
    (coord : X → Fin 4 → V) (mu : X → ℝ) :
    action (supportProduct (0 : V) (maskBit out) (maskBit r))
      (tensorResponse (fun _ : Fin 4 => S) coord mu) =
      fun y => (1 / ((Fintype.card V : ℝ)-1)) ^ (4-(maskSize r+maskSize out)) *
        supportEmbedding r out
          (tensorResponse (fun _ : MaskCoordinates out => residualMatrix S 0)
            (fun x i => coord x i.val) (exactSource r coord mu)) y := by
  funext y
  rw [project_tensorResponse]
  change (∑ x : X,
    kernelCompose (supportProduct (0 : V) (maskBit out) (maskBit r))
      (coordinateKernel (fun _ : Fin 4 => S)) y (coord x) * mu x) =
    (1 / ((Fintype.card V : ℝ)-1)) ^ (4-(maskSize r+maskSize out)) *
      ((∑ x : X, markedColumn S out (fun i => y i.val) (coord x) *
        exactSource r coord mu x) * unmarkedConstant r out y)
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [projected_substitution_entry S hS r out hr]
  by_cases hp : exactZeroPattern r (coord x)
  · simp only [exactSource, if_pos hp]
    ring
  · simp only [exactSource, if_neg hp]
    ring

/-- One inverse nonzero-alphabet factor per unmarked nonzero output after
taking counting-measure energy. The response keeps the exact source event. -/
theorem support_energy (hq : 1 < Fintype.card V)
    (S : V → V → ℝ) (hS : PointedBistochastic S 0)
    (r out : Fin 16) (hr : MaskDisjoint r out)
    (coord : X → Fin 4 → V) (mu : X → ℝ) :
    (∑ y : Fin 4 → V,
      action (supportProduct (0 : V) (maskBit out) (maskBit r))
        (tensorResponse (fun _ : Fin 4 => S) coord mu) y ^ 2) =
      (∑ u : MaskCoordinates out → V,
        tensorResponse (fun _ : MaskCoordinates out => residualMatrix S 0)
          (fun x i => coord x i.val) (exactSource r coord mu) u ^ 2) /
        ((Fintype.card V : ℝ)-1) ^ (4-(maskSize r+maskSize out)) := by
  simp_rw [congrFun (support_response S hS r out hr coord mu), mul_pow]
  rw [← Finset.mul_sum, supportEmbedding_energy r out hr]
  have hcpos : (1 : ℝ) < Fintype.card V := by exact_mod_cast hq
  have hc : (Fintype.card V : ℝ)-1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcpos)
  have hp : ((Fintype.card V : ℝ)-1) ^ (4-(maskSize r+maskSize out)) ≠ 0 :=
    pow_ne_zero _ hc
  simp only [div_pow, one_pow]
  field_simp [hp] <;> ring

end AES8.PaperPointedSupportResponse
