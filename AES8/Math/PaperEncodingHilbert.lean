import AES8.Math.PaperEncoding
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Encoding into unequal finite-dimensional real Hilbert spaces

The output is the algebraic dependent tensor product, with its Hilbert norm.
The norm is constructed from a product orthonormal basis, and the product
inner-product identity is proved below. Thus the tensor interpretation and the
isometric padding used by the estimate are conclusions, not correspondence
premises. No encoded norm or energy estimate is assumed.

Frozen manuscript: `paper-merged` f902bb94, `lem:encoding`. This leaf owns only
the finite Hilbert transport; the information-set estimate remains in the
frozen rectangular leaf. Constructive validation only; no attacks.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace AES8.PaperEncodingHilbert

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {H : K → Type*} [∀ k, NormedAddCommGroup (H k)]
  [∀ k, InnerProductSpace ℝ (H k)] [∀ k, FiniteDimensional ℝ (H k)]

/-- Product-basis coordinates on the actual dependent algebraic tensor product. -/
def tensorCoordinates {B : K → Type*} [∀ k, Fintype (B k)]
    (b : ∀ k, OrthonormalBasis (B k) ℝ (H k)) :
    (⨂[ℝ] k, H k) ≃ₗ[ℝ] EuclideanSpace ℝ (∀ k, B k) :=
  (Basis.piTensorProduct (fun k => (b k).toBasis)).equivFun.trans
    (WithLp.linearEquiv 2 ℝ ((∀ k, B k) → ℝ)).symm

omit [DecidableEq K] [∀ k, FiniteDimensional ℝ (H k)] in
@[simp] theorem tensorCoordinates_tprod {B : K → Type*} [∀ k, Fintype (B k)]
    (b : ∀ k, OrthonormalBasis (B k) ℝ (H k)) (v : ∀ k, H k) (y : ∀ k, B k) :
    tensorCoordinates b (PiTensorProduct.tprod ℝ v) y =
      ∏ k, (b k).repr (v k) (y k) := by
  simp [tensorCoordinates, Module.Basis.equivFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply]

omit [∀ k, FiniteDimensional ℝ (H k)] in
/-- The coordinates of pure tensors have exactly the Hilbert product pairing. -/
theorem tensorCoordinates_inner_tprod {B : K → Type*} [∀ k, Fintype (B k)]
    (b : ∀ k, OrthonormalBasis (B k) ℝ (H k)) (v w : ∀ k, H k) :
    inner ℝ (tensorCoordinates b (PiTensorProduct.tprod ℝ v))
      (tensorCoordinates b (PiTensorProduct.tprod ℝ w)) =
        ∏ k, inner ℝ (v k) (w k) := by
  simp only [PiLp.inner_apply, tensorCoordinates_tprod, RCLike.inner_apply,
    conj_trivial, ← Finset.prod_mul_distrib]
  trans ∏ k, ∑ y : B k, (b k).repr (w k) y * (b k).repr (v k) y
  · exact (Fintype.prod_sum (fun k (y : B k) =>
      (b k).repr (w k) y * (b k).repr (v k) y)).symm
  apply Finset.prod_congr rfl
  intro k _
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using
    (b k).repr.inner_map_map (v k) (w k)

/-- Actual dependent algebraic tensor, distinguished from its coordinate model. -/
abbrev HilbertTensor (H : K → Type*) [∀ k, AddCommGroup (H k)]
    [∀ k, Module ℝ (H k)] := ⨂[ℝ] k, H k

/-- The chosen basis is used solely to construct the finite Hilbert structure. -/
def standardTensorCoordinates :
    HilbertTensor H ≃ₗ[ℝ]
      EuclideanSpace ℝ (∀ k, Fin (Module.finrank ℝ (H k))) :=
  tensorCoordinates (fun k => stdOrthonormalBasis ℝ (H k))

instance tensorFiniteDimensional : FiniteDimensional ℝ (HilbertTensor H) :=
  FiniteDimensional.of_injective (standardTensorCoordinates (H := H)).toLinearMap
    (standardTensorCoordinates (H := H)).injective

instance tensorNormedAddCommGroup : NormedAddCommGroup (HilbertTensor H) :=
  NormedAddCommGroup.induced _ _ (standardTensorCoordinates (H := H))
    (standardTensorCoordinates (H := H)).injective

instance tensorInnerProductSpace : InnerProductSpace ℝ (HilbertTensor H) :=
  InnerProductSpace.induced (standardTensorCoordinates (H := H))

/-- The product-basis map is a proved isometry for the constructed Hilbert norm. -/
def tensorRepr : HilbertTensor H ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (∀ k, Fin (Module.finrank ℝ (H k))) where
  toLinearEquiv := standardTensorCoordinates
  norm_map' _ := rfl

/-- This identity characterizes the Hilbert tensor pairing on pure tensors. -/
@[simp] theorem inner_tprod (v w : ∀ k, H k) :
    inner ℝ (PiTensorProduct.tprod ℝ v) (PiTensorProduct.tprod ℝ w) =
      ∏ k, inner ℝ (v k) (w k) :=
  tensorCoordinates_inner_tprod (fun k => stdOrthonormalBasis ℝ (H k)) v w

/-- A linear map preserving the product pairing on pure tensors preserves it
on all tensors. This is algebraic tensor induction, with no norm premise. -/
theorem inner_map_of_tprod {T : Type*} [NormedAddCommGroup T]
    [InnerProductSpace ℝ T] (F : HilbertTensor H →ₗ[ℝ] T)
    (hF : ∀ v w, inner ℝ (F (PiTensorProduct.tprod ℝ v))
      (F (PiTensorProduct.tprod ℝ w)) = ∏ k, inner ℝ (v k) (w k))
    (x y : HilbertTensor H) : inner ℝ (F x) (F y) = inner ℝ x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s w => simp [map_smul, real_inner_smul_left,
        real_inner_smul_right, hF, inner_tprod]
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

/-- Any supplied product orthonormal basis gives the same Hilbert norm.
This proves independence of the basis used to construct the tensor norm. -/
def tensorCoordinatesIsometry {B : K → Type*} [∀ k, Fintype (B k)]
    (b : ∀ k, OrthonormalBasis (B k) ℝ (H k)) :
    HilbertTensor H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (∀ k, B k) :=
  (tensorCoordinates b).isometryOfInner
    (inner_map_of_tprod (tensorCoordinates b).toLinearMap
      (tensorCoordinates_inner_tprod b))

/- The common space is a finite orthogonal direct sum, not a common-dimension
assumption on the original output family. Even zero-dimensional factors work. -/
abbrev CommonIndex := (k : K) × Fin (Module.finrank ℝ (H k))

def includeCoordinate (k : K) : H k →ₗᵢ[ℝ] PiLp 2 H where
  toLinearMap :=
    { toFun := PiLp.single 2 k
      map_add' _ _ := PiLp.single_add 2 k
      map_smul' r v := by
        ext j
        by_cases h : j = k
        · subst j
          simp
        · simp [h] }
  norm_map' v := PiLp.norm_single 2 H k v

/-- Each unequal output has a proved isometric embedding in the common space. -/
def padding (k : K) : H k →ₗᵢ[ℝ] EuclideanSpace ℝ (CommonIndex (H := H)) :=
  (Pi.orthonormalBasis (fun k => stdOrthonormalBasis ℝ (H k))).repr.toLinearIsometry.comp
    (includeCoordinate k)

/-- Product-coordinate map after applying the actual local isometric paddings. -/
def paddedTensorMap : HilbertTensor H →ₗ[ℝ]
    EuclideanSpace ℝ (K → CommonIndex (H := H)) :=
  (tensorCoordinates (fun _ : K =>
    EuclideanSpace.basisFun (CommonIndex (H := H)) ℝ)).toLinearMap.comp
      (PiTensorProduct.map (fun k => (padding k).toLinearMap))

@[simp] theorem paddedTensorMap_tprod (v : ∀ k, H k) (y : K → CommonIndex (H := H)) :
    paddedTensorMap (PiTensorProduct.tprod ℝ v) y = ∏ k, padding k (v k) (y k) := by
  simp [paddedTensorMap, tensorCoordinates_tprod]

/-- Tensoring the unequal local embeddings is isometric, proved from their
product inner products and algebraic tensor induction. -/
def tensorPadding : HilbertTensor H →ₗᵢ[ℝ]
    EuclideanSpace ℝ (K → CommonIndex (H := H)) :=
  (paddedTensorMap (H := H)).isometryOfInner
    (inner_map_of_tprod (H := H) (paddedTensorMap (H := H)) (by
    intro v w
    dsimp only [paddedTensorMap, LinearMap.comp_apply]
    rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    calc
      _ = ∏ k, inner ℝ (padding k (v k)) (padding k (w k)) :=
        tensorCoordinates_inner_tprod
          (fun _ : K => EuclideanSpace.basisFun (CommonIndex (H := H)) ℝ) _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro k _
        exact (padding k).inner_map_map (v k) (w k)))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Literal tensor-column sum over the code, with the unequal Hilbert outputs. -/
def encoderLinear (C : Finset (K → V))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) :
    EuclideanSpace ℝ C →ₗ[ℝ] HilbertTensor H where
  toFun f := ∑ c : C, f c • PiTensorProduct.tprod ℝ
    (fun k => A k (PaperEncoding.basisVector (c.val k)))
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_smul, Finset.smul_sum]

/-- Finite input dimension makes the actual algebraic encoder continuous. -/
def encoder (C : Finset (K → V))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) :
    EuclideanSpace ℝ C →L[ℝ] HilbertTensor H :=
  (encoderLinear C A).toContinuousLinearMap

@[simp] theorem encoder_apply (C : Finset (K → V))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) (f : EuclideanSpace ℝ C) :
    encoder C A f = ∑ c : C, f c • PiTensorProduct.tprod ℝ
      (fun k => A k (PaperEncoding.basisVector (c.val k))) := rfl

/-- The common matrix is derived from the actual operators and basis responses. -/
def paddedMatrix (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k)
    (k : K) (y : CommonIndex (H := H)) (x : V) : ℝ :=
  padding k (A k (PaperEncoding.basisVector x)) y

theorem paddedLocal_eq (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) (k : K) :
    PaperKernelBounds.kernelOperator (paddedMatrix A k) =
      (padding k).toContinuousLinearMap.comp (A k) := by
  ext f y
  have hf : f = ∑ x : V, f x • PaperEncoding.basisVector x := by
    ext z
    simp [PaperEncoding.basisVector]
  rw [hf]
  simp [paddedMatrix, PaperKernelBounds.kernelOperator_apply,
    PaperKernelBounds.kernelAction, PaperEncoding.basisVector, mul_comm]

/-- Exact operator correspondence, derived on all inputs from the literal
tensor sum. No correspondence hypothesis is present. -/
theorem tensorPadding_encoder (C : Finset (K → V))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) :
    (tensorPadding (H := H)).toContinuousLinearMap.comp (encoder C A) =
      PaperEncoding.encoder C (paddedMatrix A) := by
  ext f y
  simp [encoder_apply, tensorPadding, PaperEncoding.encoder_apply,
    paddedTensorMap_tprod, paddedMatrix, PaperEncoding.tensorColumn]

/-- The paper's actual tensor encoder bound for arbitrary unequal finite
real Hilbert output spaces, including zero-dimensional outputs. -/
theorem paper_encoding_norm (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (PaperEncoding.informationProjection C s))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) (ν δ : ℝ)
    (hν : 0 ≤ ν) (hδ : 0 ≤ δ)
    (hA : ∀ k, ‖A k‖ ≤ ν)
    (hcol : ∀ k x, ‖A k (PaperEncoding.basisVector x)‖ ^ 2 ≤ δ) :
    ‖encoder C A‖ ≤ ν ^ s.card *
      δ ^ (((Fintype.card K : ℝ) - (s.card : ℝ)) / 2) := by
  have hm (k : K) : ‖PaperKernelBounds.kernelOperator (paddedMatrix A k)‖ = ‖A k‖ := by
    rw [paddedLocal_eq]
    exact (padding k).norm_toContinuousLinearMap_comp
  have hc (k : K) (x : V) :
      ‖PaperKernelBounds.kernelOperator (paddedMatrix A k)
        (PaperEncoding.basisVector x)‖ ^ 2 ≤ δ := by
    rw [paddedLocal_eq]
    simpa using hcol k x
  have he := PaperEncoding.paper_encoding_norm C s hinfo (paddedMatrix A) ν δ hν hδ
    (fun k => (hm k).trans_le (hA k)) hc
  rw [← tensorPadding_encoder] at he
  simpa only [LinearIsometry.norm_toContinuousLinearMap_comp] using he

/-- In the paper's nonempty coordinate/alphabet setting, the actual local
bounds already imply the signs of both uniform caps. -/
theorem paper_encoding_norm_of_nonempty [Nonempty K] [Nonempty V]
    (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (PaperEncoding.informationProjection C s))
    (A : ∀ k, EuclideanSpace ℝ V →L[ℝ] H k) (ν δ : ℝ)
    (hA : ∀ k, ‖A k‖ ≤ ν)
    (hcol : ∀ k x, ‖A k (PaperEncoding.basisVector x)‖ ^ 2 ≤ δ) :
    ‖encoder C A‖ ≤ ν ^ s.card *
      δ ^ (((Fintype.card K : ℝ) - (s.card : ℝ)) / 2) := by
  let k : K := Classical.arbitrary K
  let x : V := Classical.arbitrary V
  exact paper_encoding_norm C s hinfo A ν δ
    ((norm_nonneg _).trans (hA k)) ((sq_nonneg _).trans (hcol k x)) hA hcol

end AES8.PaperEncodingHilbert
