import AES8.Math.PaperThinPlane
import AES8.Math.PaperThinLinesRaw
import AES8.Math.PaperThinLinesOperator
import AES8.Math.PaperMDSOverlap
import AES8.Math.PaperFiberKernelPower

/-!
# Normalized line--plane overlaps on actual extended affine MDS graphs

The outside labels are restrictions in the extended physical graph. The four
middle coordinates are separate from the outside positions. The literal
kernel uses only those four middle coordinates. The graph dimensions are one
and two; the middle projection is injective by MDS. Normalizers and all raw
partial-sum bounds are derived, rather than supplied as desired caps.

Frozen correspondence: `lem:line-plane`, paper commit
`f902bb94fc826983181b1712d7b57cf9cbe22f4d`. Constructive proof checking only.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperThinPlane

open PaperMDSGram PaperMDSFiber PaperMDSOverlap PaperThinHolder
open PaperThinLines PaperFiberKernel PaperKernelBounds FiberIncidence

attribute [local instance] Classical.propDecidable

variable {K V 𝕜 : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V] [RCLike 𝕜]

/-- The empty prescribed fiber has exactly the points of the affine graph. -/
def affineEmptyEquiv (C : AddSubgroup (K → V)) (offset : K → V) :
    AffineCode C offset ≃ AffineFiber C offset ∅ 0 where
  toFun x := ⟨x.val, ⟨x.property, by simp⟩⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

def graphLineCoordinate (C : AddSubgroup (K → V)) (hk : 1 ≤ Fintype.card K)
    (hC : IsMDS C 1) (offset : K → V) (i : K) : AffineCode C offset ≃ V :=
  (affineEmptyEquiv C offset).trans
    (affineCoordinateEquiv C 1 hk hC offset ∅ 0 (by simp) i (by simp))

def graphPlanePair (D : AddSubgroup (K → V)) (hk : 2 ≤ Fintype.card K)
    (hD : IsMDS D 2) (offset : K → V) (i j : K) (hij : i ≠ j) :
    AffineCode D offset ≃ (V × V) :=
  (affineEmptyEquiv D offset).trans
    (affinePlanePairEquiv D 2 hk hD offset ∅ 0 (by simp) i j
      (by simp) (by simp) hij)

def planeRowCap (a : ℕ) (H T : ℝ) : ℝ := H ^ (2 - a) * T ^ a

def planeColCap (b : ℕ) (H T r s : ℝ) : ℝ :=
  if b = 0 then H * r ^ 2 else if b = 1 then T * s ^ 2 else H * T

theorem plane_caps_nonneg (a b : ℕ) (H S r s : ℝ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) :
    0 ≤ planeRowCap a H S * planeColCap b H S r s := by
  apply mul_nonneg
  · exact mul_nonneg (pow_nonneg hH _) (pow_nonneg hS _)
  · unfold planeColCap
    split_ifs
    · exact mul_nonneg hH (sq_nonneg r)
    · exact mul_nonneg hS (sq_nonneg s)
    · exact mul_nonneg hH hS

/-- The literal displayed square-root quotient equals the power-normalized
coefficient. This identity also covers zero-dimensional fibers. -/
theorem plane_normalization_sqrt_quotient (q a b : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) * Real.sqrt z =
      Real.sqrt (z / (q : ℝ) ^ (a + b)) := by
  rw [← FiberNormalization.div_sqrt_pow_product, Real.sqrt_div hz]
  congr 1
  rw [← Real.sqrt_mul (Nat.cast_nonneg (q ^ a)), ← Nat.cast_mul, ← pow_add,
    Nat.cast_pow]

/-- The raw row `H²` and total `HT` bounds on the literal restricted
complex/real product kernel. Only local second moments are used. -/
theorem graph_plane_raw_bounds
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s) :
    (∀ x : AffineCode C offC,
      (∑ y : AffineCode D offD,
        absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y)
      ≤ H ^ 2) ∧
    ((∑ x : AffineCode C offC, ∑ y : AffineCode D offD,
      absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y)
      ≤ H * S) := by
  let e := fun a => graphLineCoordinate C hk1 hC offC (i a)
  let q := graphPlanePair D hk2 hD offD (j 0) (j 1)
    (j.injective.ne (by decide))
  let d := graphPlanePair D hk2 hD offD (j 2) (j 3)
    (j.injective.ne (by decide))
  constructor
  · intro x
    have hb := plane_row q d (fun a b => ‖T a (x.val (i a)) b‖)
      H h.delta_nonneg (fun a => h.row_second a _)
    simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc, q, d, graphPlanePair,
      affinePlanePairEquiv, affineEmptyEquiv] using hb
  · have hb := line_plane_total e q d (fun a x y => ‖T a x y‖)
      H S h.delta_nonneg h.tau_nonneg (fun a x => h.row_second a x)
      (fun a => h.total_second a)
    simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc, e, q, d, graphLineCoordinate,
      graphPlanePair, affineEmptyEquiv, affinePlanePairEquiv,
      affineCoordinateEquiv] using hb

/-- A generic partial sum for an injective, surjective outside map is
exactly one point. This helper asserts no analytic bound. -/
theorem injective_partial_sum {A O : Type*} [Fintype A] [Fintype O]
    [DecidableEq O] (p : A → O) (hp : Function.Injective p)
    (hs : Function.Surjective p) (F : A → ℝ) (o : O) :
    ∃ x, (∑ a, if p a = o then F a else 0) = F x := by
  obtain ⟨x, hx⟩ := hs o
  refine ⟨x, ?_⟩
  have hiff (a : A) : p a = o ↔ a = x := by
    constructor
    · intro ha
      exact hp (ha.trans hx.symm)
    · intro ha
      exact ha ▸ hx
  simp_rw [hiff]
  simp

/-- The empty outside label is unique, so its raw partial sum is the total. -/
theorem empty_outside_partial_sum (C : AddSubgroup (K → V)) (offset : K → V)
    (F : AffineCode C offset → ℝ) (o : OutsideLabel C offset ∅) :
    (∑ x, if outsideProjection C offset ∅ x = o then F x else 0) = ∑ x, F x := by
  have he (x : AffineCode C offset) : outsideProjection C offset ∅ x = o := by
    apply Subtype.ext
    funext a
    exact False.elim (Finset.notMem_empty a.val a.property)
  simp only [he, if_true]

/-- Exact left partial-sum cap for both outside-fiber dimensions. -/
theorem graph_plane_left_partial
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (outside : Finset K) (o : OutsideLabel C offC outside) :
    (∑ x : AffineCode C offC, if outsideProjection C offC outside x = o then
      ∑ y : AffineCode D offD,
        absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y
      else 0) ≤ planeRowCap (1 - min 1 outside.card) H S := by
  obtain ⟨hrow, htotal⟩ := graph_plane_raw_bounds C D hk1 hk2 hC hD offC offD i j
    T H S r s h
  by_cases ho : outside = ∅
  · subst outside
    rw [empty_outside_partial_sum]
    simpa [planeRowCap] using htotal
  · have hlarge : 1 ≤ outside.card := Finset.one_le_card.mpr
      (Finset.nonempty_iff_ne_empty.mpr ho)
    obtain ⟨x, hx⟩ := injective_partial_sum (outsideProjection C offC outside)
      (outsideProjection_injective_large C 1 hC offC outside hlarge)
      (outsideProjection_surjective C offC outside)
      (fun x => ∑ y : AffineCode D offD,
        absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y) o
    rw [hx]
    simpa [planeRowCap, Nat.min_eq_left hlarge] using hrow x

/-- Exact right partial-sum cap for the full plane, shortened line, and
singleton. The middle coordinates lie outside the prescribed outside set. -/
theorem graph_plane_right_partial
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (outside : Finset K) (hout : ∀ a, j a ∉ outside)
    (o : OutsideLabel D offD outside) :
    (∑ x : AffineCode C offC, ∑ y : AffineCode D offD,
      if outsideProjection D offD outside y = o then
        absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y
      else 0) ≤ planeColCap (2 - min 2 outside.card) H S r s := by
  by_cases hlarge : 2 ≤ outside.card
  · rw [Finset.sum_comm]
    have he : (∑ y : AffineCode D offD, ∑ x : AffineCode C offC,
        if outsideProjection D offD outside y = o then
          absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y
        else 0) =
        ∑ y : AffineCode D offD, if outsideProjection D offD outside y = o then
          ∑ x : AffineCode C offC,
            absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y
          else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : outsideProjection D offD outside y = o <;> simp [hy]
    rw [he]
    obtain ⟨y, hy⟩ := injective_partial_sum (outsideProjection D offD outside)
      (outsideProjection_injective_large D 2 hD offD outside hlarge)
      (outsideProjection_surjective D offD outside)
      (fun y => ∑ x : AffineCode C offC,
        absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y) o
    rw [hy]
    have hb := four_transport (fun a => graphLineCoordinate C hk1 hC offC (i a))
      (fun a b => ‖T a b (y.val (j a))‖) H r h.delta_nonneg
      (fun a => h.col_fourth a _)
    simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc, graphLineCoordinate,
      affineEmptyEquiv, affineCoordinateEquiv, planeColCap, Nat.min_eq_left hlarge]
      using hb
  · by_cases hempty : outside = ∅
    · subst outside
      have he (y : AffineCode D offD) : outsideProjection D offD ∅ y = o := by
        apply Subtype.ext
        funext a
        exact False.elim (Finset.notMem_empty a.val a.property)
      simp only [he, if_true]
      have hb := (graph_plane_raw_bounds C D hk1 hk2 hC hD offC offD i j
        T H S r s h).2
      simpa [planeColCap] using hb
    · have hcard : outside.card = 1 := by
        have hp := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      have he (x : AffineCode C offC) :
          (∑ y : AffineCode D offD, if outsideProjection D offD outside y = o then
            absoluteKernel T (fun x a => x.val (i a)) (fun y a => y.val (j a)) x y
            else 0) =
          ∑ y : AffineFiber D offD outside (outsideTarget outside o.val),
            ∏ a, ‖T a (x.val (i a)) (y.val (j a))‖ := by
        change rawFiberSum (outsideProjection D offD outside)
          (fun y => ∏ a, ‖T a (x.val (i a)) (y.val (j a))‖) o = _
        rw [raw_admissible_sum_eq]
        exact raw_outside_sum D offD outside o.val
          (fun z => ∏ a, ‖T a (x.val (i a)) (z (j a))‖)
      simp_rw [he]
      have hb := four_transport
        (fun a => Equiv.prodCongr (graphLineCoordinate C hk1 hC offC (i a))
          (affineCoordinateEquiv D 2 hk2 hD offD outside
            (outsideTarget outside o.val) (by omega) (j a) (hout a)))
        (fun a z => ‖T a z.1 z.2‖) S s h.tau_nonneg
        (by intro a; simpa only [Fintype.sum_prod_type] using h.total_fourth a)
      simpa [absoluteKernel, Fin.prod_univ_succ, mul_assoc, Fintype.sum_prod_type,
        graphLineCoordinate, affineEmptyEquiv, affineCoordinateEquiv,
        planeColCap, hcard] using hb

/-- All six normalized line--plane cases in one theorem, on literal affine
graph spaces and the actual admissible outside partitions. Local fourth
moments are hypotheses; kernel-sum and fiber-cardinality caps are conclusions. -/
theorem paper_line_plane_norm
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (leftOutside rightOutside : Finset K) (hout : ∀ a, j a ∉ rightOutside) :
    let a := 1 - min 1 leftOutside.card
    let b := 2 - min 2 rightOutside.card
    let p := outsideProjection C offC leftOutside
    let q := outsideProjection D offD rightOutside
    let B := lineKernel T (fun x : AffineCode C offC => fun a => x.val (i a))
      (fun y : AffineCode D offD => fun a => y.val (j a))
    (∀ f : EuclideanSpace 𝕜 (OutsideLabel C offC leftOutside),
      ‖fiberLift p (Fintype.card V ^ a) f‖ = ‖f‖) ∧
    (∀ f : EuclideanSpace 𝕜 (OutsideLabel D offD rightOutside),
      ‖fiberLift q (Fintype.card V ^ b) f‖ = ‖f‖) ∧
    ‖(fiberLift p (Fintype.card V ^ a)).adjoint.comp
      ((kernelOperator B).comp (fiberLift q (Fintype.card V ^ b)))‖ ≤
      (Fintype.card V : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) *
        Real.sqrt (planeRowCap a H S * planeColCap b H S r s) := by
  dsimp only
  apply paper_fiber_kernel_norm_pow
    (M := absoluteKernel T (fun x : AffineCode C offC => fun a => x.val (i a))
      (fun y : AffineCode D offD => fun a => y.val (j a)))
  · exact Fintype.card_pos_iff.mpr ⟨(0 : V)⟩
  · exact outside_fiber_card C 1 hk1 hC offC leftOutside
  · exact outside_fiber_card D 2 hk2 hD offD rightOutside
  · exact absoluteKernel_nonneg T _ _
  · intro x y
    exact (norm_lineKernel T _ _ x y).le
  · exact graph_plane_left_partial C D hk1 hk2 hC hD offC offD i j
      T H S r s h leftOutside
  · exact graph_plane_right_partial C D hk1 hk2 hC hD offC offD i j
      T H S r s h rightOutside hout

/-- MDS makes the four middle-coordinate map an actual inclusion for a line. -/
theorem graph_line_middle_injective (C : AddSubgroup (K → V))
    (hk : 1 ≤ Fintype.card K) (hC : IsMDS C 1) (offset : K → V)
    (i : Fin 4 ↪ K) :
    Function.Injective (fun x : AffineCode C offset => fun a => x.val (i a)) := by
  intro x y hxy
  apply (graphLineCoordinate C hk hC offset (i 0)).injective
  exact congrFun hxy 0

/-- The same actual middle inclusion for the plane is injective because
its first two middle coordinates already form an information pair. -/
theorem graph_plane_middle_injective (D : AddSubgroup (K → V))
    (hk : 2 ≤ Fintype.card K) (hD : IsMDS D 2) (offset : K → V)
    (j : Fin 4 ↪ K) :
    Function.Injective (fun y : AffineCode D offset => fun a => y.val (j a)) := by
  intro x y hxy
  apply (graphPlanePair D hk hD offset (j 0) (j 1)
    (j.injective.ne (by decide))).injective
  exact Prod.ext (congrFun hxy 0) (congrFun hxy 1)

/-- The paper's literal five-factor tensor overlap has the same six-entry
bound. Both middle maps are genuine inclusions by the preceding MDS lemmas. -/
theorem paper_line_plane_tensor_norm
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (leftOutside rightOutside : Finset K) (hout : ∀ a, j a ∉ rightOutside) :
    let a := 1 - min 1 leftOutside.card
    let b := 2 - min 2 rightOutside.card
    let p := outsideProjection C offC leftOutside
    let q := outsideProjection D offD rightOutside
    let left := fun x : AffineCode C offC => fun a => x.val (i a)
    let right := fun y : AffineCode D offD => fun a => y.val (j a)
    ‖(fiberLift p (Fintype.card V ^ a)).adjoint.comp
      (((coordinateInclusion left).adjoint.comp
        ((coordinateTensorOperator T).comp (coordinateInclusion right))).comp
          (fiberLift q (Fintype.card V ^ b)))‖ ≤
      (Fintype.card V : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) *
        Real.sqrt (planeRowCap a H S * planeColCap b H S r s) := by
  dsimp only
  rw [normalized_overlap_correspondence]
  exact (paper_line_plane_norm C D hk1 hk2 hC hD offC offD i j T H S r s h
    leftOutside rightOutside hout).2.2

/-- The five-factor endpoint with exactly the square-root quotient displayed
in frozen `eq:line-plane`, for all six outside-fiber choices. -/
theorem paper_line_plane_tensor_sqrt_norm
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (leftOutside rightOutside : Finset K) (hout : ∀ a, j a ∉ rightOutside) :
    let a := 1 - min 1 leftOutside.card
    let b := 2 - min 2 rightOutside.card
    let p := outsideProjection C offC leftOutside
    let q := outsideProjection D offD rightOutside
    let left := fun x : AffineCode C offC => fun a => x.val (i a)
    let right := fun y : AffineCode D offD => fun a => y.val (j a)
    ‖(fiberLift p (Fintype.card V ^ a)).adjoint.comp
      (((coordinateInclusion left).adjoint.comp
        ((coordinateTensorOperator T).comp (coordinateInclusion right))).comp
          (fiberLift q (Fintype.card V ^ b)))‖ ≤
      Real.sqrt ((planeRowCap a H S * planeColCap b H S r s) /
        (Fintype.card V : ℝ) ^ (a + b)) := by
  have hb := paper_line_plane_tensor_norm C D hk1 hk2 hC hD offC offD i j
    T H S r s h leftOutside rightOutside hout
  dsimp only at hb ⊢
  rw [plane_normalization_sqrt_quotient _ _ _ _
    (plane_caps_nonneg _ _ H S r s h.delta_nonneg h.tau_nonneg)] at hb
  exact hb

/-- Taking the literal Hilbert adjoint exchanges the two code sides and
preserves the norm bound, with no extra moment hypothesis. -/
theorem paper_line_plane_adjoint_norm
    (C D : AddSubgroup (K → V)) (hk1 : 1 ≤ Fintype.card K)
    (hk2 : 2 ≤ Fintype.card K) (hC : IsMDS C 1) (hD : IsMDS D 2)
    (offC offD : K → V) (i j : Fin 4 ↪ K)
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (leftOutside rightOutside : Finset K) (hout : ∀ a, j a ∉ rightOutside) :
    let a := 1 - min 1 leftOutside.card
    let b := 2 - min 2 rightOutside.card
    let p := outsideProjection C offC leftOutside
    let q := outsideProjection D offD rightOutside
    let B := lineKernel T (fun x : AffineCode C offC => fun a => x.val (i a))
      (fun y : AffineCode D offD => fun a => y.val (j a))
    ‖((fiberLift p (Fintype.card V ^ a)).adjoint.comp
      ((kernelOperator B).comp (fiberLift q (Fintype.card V ^ b)))).adjoint‖ ≤
      (Fintype.card V : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) *
        Real.sqrt (planeRowCap a H S * planeColCap b H S r s) := by
  dsimp only
  rw [LinearIsometryEquiv.norm_map]
  exact (paper_line_plane_norm C D hk1 hk2 hC hD offC offD i j T H S r s h
    leftOutside rightOutside hout).2.2

/-- The adjoint really exchanges the two fiber maps and uses the conjugate
transpose of the raw middle kernel. This identity is independent of bounds. -/
theorem fiber_overlap_adjoint {L R X Y : Type*}
    [Fintype L] [Fintype R] [Fintype X] [Fintype Y]
    [DecidableEq L] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
    (p : L → X) (q : R → Y) (m n : ℕ) (B : L → R → 𝕜) :
    ((fiberLift p m).adjoint.comp
      ((kernelOperator B).comp (fiberLift q n))).adjoint =
      (fiberLift q n).adjoint.comp
        ((kernelOperator (Matrix.conjTranspose B)).comp (fiberLift p m)) := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, kernelOperator_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

end AES8.PaperThinPlane
