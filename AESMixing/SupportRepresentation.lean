import AESMixing.SupportProduct
import AESMixing.SupportEmbedding
import AESMixing.ProjectedIncidence

/-! Every orthogonal support piece has the joint residual representation
used in the incidence estimate. This bridges the abstract decomposition
to the concrete support embeddings; no product-input assumption is made. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def supportDualConstant (b : Bool) (x : V) : ℝ :=
  supportConstant b x / (if b then 1 else (Fintype.card V : ℝ)-1)

theorem supportPiece_unmarked (b : Bool) (y x : V) :
    supportPiece 0 false b y x = supportConstant b y * supportDualConstant b x := by
  cases b <;> by_cases hy : y = 0 <;> by_cases hx : x = 0 <;>
    simp [supportPiece,constantMatrix,activityMatrix,zeroMatrix,identityKernel,
      supportConstant,supportDualConstant,hy,hx]

theorem supportProduct_factor (r out : Fin 16) (hr : MaskDisjoint r out)
    (y x : Fin 4 → V) :
    supportProduct 0 (maskBit out) (maskBit r) y x =
      (∏ i : MaskCoordinates out, residualProjection 0 (y i.val) (x i.val)) *
      (∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportConstant (maskBit r i.val) (y i.val)) *
      (∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportDualConstant (maskBit r i.val) (x i.val)) := by
  unfold supportProduct
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => maskBit out i = true)]
  have hm (i : MaskCoordinates out) :
      supportPiece 0 (maskBit out i.val) (maskBit r i.val) (y i.val) (x i.val) =
        residualProjection 0 (y i.val) (x i.val) := by
    have hi : maskBit r i.val ≠ true := fun h => hr i.val h i.property
    simp [supportPiece,i.property,hi]
  have hu (i : {i : Fin 4 // maskBit out i ≠ true}) :
      supportPiece 0 (maskBit out i.val) (maskBit r i.val) (y i.val) (x i.val) =
        supportConstant (maskBit r i.val) (y i.val) *
          supportDualConstant (maskBit r i.val) (x i.val) := by
    have hi : maskBit out i.val = false := Bool.eq_false_iff.mpr i.property
    rw [hi,supportPiece_unmarked]
  simp_rw [hm,hu]
  rw [Finset.prod_mul_distrib,mul_assoc]

def supportCoefficient (r out : Fin 16) (f : (Fin 4 → V) → ℝ)
    (u : MaskCoordinates out → V) : ℝ :=
  ∑ v : {i : Fin 4 // maskBit out i ≠ true} → V,
    (∏ i, supportDualConstant (maskBit r i.val) (v i)) *
      f ((Equiv.piEquivPiSubtypeProd (fun i => maskBit out i = true) (fun _ => V)).symm (u,v))

theorem supportProduct_embedding (r out : Fin 16) (hr : MaskDisjoint r out)
    (f : (Fin 4 → V) → ℝ) :
    action (supportProduct 0 (maskBit out) (maskBit r)) f =
      supportEmbedding r out (markedResidual out (supportCoefficient r out f)) := by
  funext y
  let e := Equiv.piEquivPiSubtypeProd (fun i => maskBit out i = true) (fun _ => V)
  rw [show action (supportProduct 0 (maskBit out) (maskBit r)) f y =
      ∑ uv, supportProduct 0 (maskBit out) (maskBit r) y (e.symm uv) * f (e.symm uv) from
    (e.symm.sum_comp (fun x => supportProduct 0 (maskBit out) (maskBit r) y x * f x)).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [supportProduct_factor r out hr]
  have hm (u : MaskCoordinates out → V)
      (v : {i : Fin 4 // maskBit out i ≠ true} → V) (i : MaskCoordinates out) :
      e.symm (u,v) i.val = u i := by simp [e,Equiv.piEquivPiSubtypeProd,i.property]
  have hu (u : MaskCoordinates out → V)
      (v : {i : Fin 4 // maskBit out i ≠ true} → V)
      (i : {i : Fin 4 // maskBit out i ≠ true}) :
      e.symm (u,v) i.val = v i := by simp [e,Equiv.piEquivPiSubtypeProd,i.property]
  simp_rw [hm,hu]
  simp only [supportEmbedding,coordinateEmbedding,markedResidual,action,
    productProjection,degreePiece,ite_true,supportCoefficient]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem markedResidual_idempotent (hn : 1 < Fintype.card V) (s : Fin 16)
    (f : (MaskCoordinates s → V) → ℝ) :
    markedResidual s (markedResidual s f) = markedResidual s f := by
  unfold markedResidual
  rw [← kernelCompose_action,productProjection_compose 0 hn,if_pos rfl]

theorem supportProduct_residual_representation (hn : 1 < Fintype.card V)
    (r out : Fin 16) (hr : MaskDisjoint r out) (f : (Fin 4 → V) → ℝ) :
    ∃ g : (MaskCoordinates out → V) → ℝ,
      markedResidual out g = g ∧
      action (supportProduct 0 (maskBit out) (maskBit r)) f = supportEmbedding r out g := by
  exact ⟨markedResidual out (supportCoefficient r out f),
    markedResidual_idempotent hn out _,supportProduct_embedding r out hr f⟩

end AESMixing
