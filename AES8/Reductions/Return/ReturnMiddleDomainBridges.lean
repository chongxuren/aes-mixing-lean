/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ProjectedGraph
import AES8.Reductions.Return.ReturnFourMiddle

/-!
# Literal projected-domain transports for the 00 and four-middle kernels

The 00 graphs map bijectively onto their attained middle images, never onto
all ambient triples. The existing image overlap bound is transported by those
exact counting bijections. The four-middle hyperplanes are identified with
ReturnFourMiddle's actual graph types by identity on the physical word state.
Every coefficient function may be signed and joint. All residual channels
remain literal; no endpoint, inverse metric or input restriction is absorbed.

This is a middle operator bridge; branch composition and return-cell closure
are separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
noncomputable section
open scoped BigOperators

namespace AES8.ReturnMiddleDomainBridges
open AESMixing AESMixing.AES
open AES8.ProjectedGraph
open AES8.ZeroOutsideProjection (outsideMask OutsideCoordinates outsideMask_bit_iff)
open AES8.MDSFiberCollision AES8.MDSFiberIncidence AES8.MarkedZeroFiber
open AES8.MarkedZeroOverlap (singleMask selectedSplit inputValue outputValue)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

-- Only four position names and four-bit masks are decided here.
private theorem single_size : ∀ r : Fin 4, maskSize (singleMask r) = 1 := by decide
private theorem outside_size : ∀ c : Fin 4, maskSize (outsideMask c) = 3 := by decide
private theorem zero_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem zero_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
private theorem single_outside_disjoint : ∀ c : Fin 4,
    MaskDisjoint (singleMask c) (outsideMask c) := by decide

private theorem disjoint_zero (m : Fin 16) : MaskDisjoint m 0 := by
  intro i _ hi
  rw [zero_bit] at hi
  contradiction

/-- The 00 left domain is its literal two-prescription forward MDS graph. -/
def zeroLeftGraph (r c : Fin 4) :
    LeftDomain r c false ≃ ZeroGraph (singleMask r) (singleMask c) where
  toFun v := ⟨v.val, (PhysicalZeroPattern.singleton_graph_iff r c v.val).mpr
    (by simpa only [LeftConstraint, frameCondition, Bool.false_eq_true, false_or]
      using v.property)⟩
  invFun v := ⟨v.val, by
    simpa only [LeftConstraint, frameCondition, Bool.false_eq_true, false_or]
      using (PhysicalZeroPattern.singleton_graph_iff r c v.val).mp v.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The right prescription retains both the literal input and forward output zero. -/
def zeroRightGraph (c z : Fin 4) :
    RightDomain c z false ≃ ZeroGraph (singleMask c) (singleMask z) where
  toFun x := ⟨x.val, (PhysicalZeroPattern.singleton_graph_iff c z x.val).mpr
    ⟨(by simpa only [frameCondition, Bool.false_eq_true, false_or] using x.property.2),
      x.property.1⟩⟩
  invFun x := ⟨x.val, by
    have hx := (PhysicalZeroPattern.singleton_graph_iff c z x.val).mp x.property
    exact ⟨hx.2, Or.inr hx.1⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Literal left input-middle observation onto its attained three-coordinate image. -/
def zeroLeftImage (r c : Fin 4) :
    LeftDomain r c false ≃ InputImage (singleMask r) (singleMask c) (outsideMask c) :=
  (zeroLeftGraph r c).trans
    (graphImageEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
      (singleMask r) (singleMask c) 0 (outsideMask c) 0 0
      (disjoint_zero (singleMask r)) (single_outside_disjoint c)
      (by rw [single_size, single_size, zero_size, outside_size]; decide))

/-- Literal right output-middle observation onto its attained image. -/
def zeroRightImage (c z : Fin 4) :
    RightDomain c z false ≃ OutputImage (singleMask c) (singleMask z) (outsideMask c) :=
  (zeroRightGraph c z).trans
    (ordinaryOutsideEquiv (singleMask c) (singleMask z) (outsideMask c)
      (single_size c) (single_size z) (outside_size c) (single_outside_disjoint c))

@[simp] theorem zeroLeftImage_value (r c : Fin 4) (v : LeftDomain r c false)
    (i : OutsideCoordinates c) : inputValue (zeroLeftImage r c v) i = v.val i.val := rfl

@[simp] theorem zeroRightImage_value (c z : Fin 4) (x : RightDomain c z false)
    (i : OutsideCoordinates c) :
    outputValue (zeroRightImage c z x) i = wordMixAddEquiv x.val i.val := by
  change boundary x.val i.val = _
  rw [ReturnFourMiddle.boundary_apply_forward]

/-- All three actual middle residual channels, with the omitted c explicit. -/
def zeroKernel (r c z : Fin 4) (v : LeftDomain r c false)
    (x : RightDomain c z false) : ℝ :=
  ∏ i : OutsideCoordinates c,
    residualMatrix wordSuperboxKernel 0 (v.val i.val) (wordMixAddEquiv x.val i.val)

theorem zeroKernel_eq_image (r c z : Fin 4) (v : LeftDomain r c false)
    (x : RightDomain c z false) :
    zeroKernel r c z v x = MarkedZeroOverlap.tensorKernel
      (fun _ : OutsideCoordinates c => residualMatrix wordSuperboxKernel 0)
      (zeroLeftImage r c v) (zeroRightImage c z x) := by
  unfold zeroKernel MarkedZeroOverlap.tensorKernel
  simp only [zeroLeftImage_value, zeroRightImage_value]

theorem zero_action_eq_image (r c z : Fin 4) (f : RightDomain c z false → ℝ)
    (v : LeftDomain r c false) :
    action (zeroKernel r c z) f v =
      action (MarkedZeroOverlap.tensorKernel
        (fun _ : OutsideCoordinates c => residualMatrix wordSuperboxKernel 0))
        (fun x => f ((zeroRightImage c z).symm x)) (zeroLeftImage r c v) := by
  unfold action
  rw [← (zeroRightImage c z).symm.sum_comp (fun x : RightDomain c z false =>
    zeroKernel r c z v x * f x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [zeroKernel_eq_image, Equiv.apply_symm_apply]

/-- The actual image overlap estimate, transported without a normalization factor. -/
theorem actual_zero_energy (r c z : Fin 4) (f : RightDomain c z false → ℝ) :
    (∑ v : LeftDomain r c false, action (zeroKernel r c z) f v ^ 2) ≤
      OneSourceEventMoment.columnCap ^ 2 * SharpWordNorm.rho ^ 2 * ∑ x, f x ^ 2 := by
  simp_rw [zero_action_eq_image r c z f]
  rw [(zeroLeftImage r c).sum_comp (fun y =>
    action (MarkedZeroOverlap.tensorKernel
      (fun _ : OutsideCoordinates c => residualMatrix wordSuperboxKernel 0))
      (fun x => f ((zeroRightImage c z).symm x)) y ^ 2)]
  have he := MarkedZeroOverlap.tensor_energy
    (singleMask r) (singleMask c) (singleMask c) (singleMask z) (outsideMask c)
    (single_size r) (single_size c) (single_size c) (single_size z)
    (single_outside_disjoint c) (single_outside_disjoint c)
    (selectedSplit (outsideMask c) (outside_size c))
    (fun _ : OutsideCoordinates c => residualMatrix wordSuperboxKernel 0)
    OneSourceEventMoment.columnCap SharpWordNorm.rho
    (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
    OneSourceEventMoment.residual_column_le
    SharpDegreeStep.word_superbox_residual_energy
    OneSourceEventMoment.residual_row_le
    (fun x => f ((zeroRightImage c z).symm x))
  rw [(zeroRightImage c z).symm.sum_comp (fun x => f x ^ 2)] at he
  exact he

/-- No caller-supplied middle estimate, sign, independence or constancy premise. -/
theorem actual_zero_l2 (r c z : Fin 4) (f : RightDomain c z false → ℝ) :
    l2 (action (zeroKernel r c z) f) ≤
      (OneSourceEventMoment.columnCap * SharpWordNorm.rho) * l2 f := by
  apply l2_le_of_energy _ f (OneSourceEventMoment.columnCap * SharpWordNorm.rho)
    (mul_nonneg (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
      (by norm_num [SharpWordNorm.rho]))
  rw [mul_pow]
  exact actual_zero_energy r c z f

/-- The product kernel is exactly the actual physical three-middle factor. -/
theorem zeroKernel_eq_channelTail (r c z : Fin 4) (v : LeftDomain r c false)
    (x : RightDomain c z false) :
    zeroKernel r c z v x =
      PhysicalZeroPattern.channelTail wordSuperboxKernel 0 c v.val
        (wordMixAddEquiv x.val) := by
  unfold zeroKernel PhysicalZeroPattern.channelTail
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : Fin 4 => maskBit (outsideMask c) i = true)]
  have hm (i : OutsideCoordinates c) :
      (if i.val = c then (1 : ℝ) else residualMatrix wordSuperboxKernel 0
        (v.val i.val) (wordMixAddEquiv x.val i.val)) =
      residualMatrix wordSuperboxKernel 0 (v.val i.val) (wordMixAddEquiv x.val i.val) :=
    if_neg ((outsideMask_bit_iff c i.val).mp i.property)
  have hu (i : {i : Fin 4 // ¬maskBit (outsideMask c) i = true}) :
      (if i.val = c then (1 : ℝ) else residualMatrix wordSuperboxKernel 0
        (v.val i.val) (wordMixAddEquiv x.val i.val)) = 1 := by
    have hi : i.val = c := by
      by_contra hne
      exact i.property ((outsideMask_bit_iff c i.val).mpr hne)
    exact if_pos hi
  simp_rw [hm, hu]
  simp only [Finset.prod_const_one, _root_.mul_one]

def fourLeftGraph (r : Fin 4) : LeftHyperplane r ≃ ReturnFourMiddle.H_L r where
  toFun v := ⟨v.val, (ReturnFourMiddle.left_graph_iff r v.val).mpr v.property⟩
  invFun v := ⟨v.val, (ReturnFourMiddle.left_graph_iff r v.val).mp v.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def fourRightGraph (z : Fin 4) : RightHyperplane z ≃ ReturnFourMiddle.H_R z where
  toFun x := ⟨x.val, (ReturnFourMiddle.right_graph_iff z x.val).mpr x.property⟩
  invFun x := ⟨x.val, (ReturnFourMiddle.right_graph_iff z x.val).mp x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- All four middle residuals on the actual projected hyperplanes. -/
def fourKernel (r z : Fin 4) (v : LeftHyperplane r) (x : RightHyperplane z) : ℝ :=
  AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val)

theorem fourKernel_eq_graph (r z : Fin 4) (v : LeftHyperplane r)
    (x : RightHyperplane z) :
    fourKernel r z v x =
      ReturnFourMiddle.actualKernel (fourLeftGraph r v) (fourRightGraph z x) := rfl

theorem four_action_eq_graph (r z : Fin 4) (f : RightHyperplane z → ℝ)
    (v : LeftHyperplane r) :
    action (fourKernel r z) f v =
      action ReturnFourMiddle.actualKernel (fun x => f ((fourRightGraph z).symm x))
        (fourLeftGraph r v) := by
  unfold action
  rw [← (fourRightGraph z).symm.sum_comp (fun x : RightHyperplane z =>
    fourKernel r z v x * f x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [fourKernel_eq_graph, Equiv.apply_symm_apply]

/-- Transport the existing actual four-middle norm bound along identity graph maps. -/
theorem actual_four_l2 (r z : Fin 4) (f : RightHyperplane z → ℝ) :
    l2 (action (fourKernel r z) f) ≤
      (OneSourceEventMoment.columnCap * SharpWordNorm.rho ^ 2) * l2 f := by
  have he := ReturnFourMiddle.actual_l2 r z (fun x => f ((fourRightGraph z).symm x))
  have hout : l2 (action (fourKernel r z) f) =
      l2 (action (ReturnFourMiddle.actualKernel (r := r) (z := z))
        (fun x => f ((fourRightGraph z).symm x))) := by
    unfold l2
    simp_rw [four_action_eq_graph r z f]
    rw [(fourLeftGraph r).sum_comp (fun v =>
      action (ReturnFourMiddle.actualKernel (r := r) (z := z))
        (fun x => f ((fourRightGraph z).symm x)) v ^ 2)]
  have hin : l2 (fun x => f ((fourRightGraph z).symm x)) = l2 f := by
    unfold l2
    rw [(fourRightGraph z).symm.sum_comp (fun x => f x ^ 2)]
  rw [← hout, hin] at he
  exact he

end AES8.ReturnMiddleDomainBridges
