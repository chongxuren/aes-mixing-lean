import AES8.Math.PaperMDSShortening
import AES8.Math.PaperThinPlaneEndpoint

/-!
# Normalized line--plane overlaps on arbitrary larger affine shortenings

This is the full physical shortening interface of frozen paper `lem:line-plane`,
commit f902bb94fc826983181b1712d7b57cf9cbe22f4d. Left and right graphs may have
different physical coordinate types and arbitrary original dimensions. Fixed
coordinates remain in each literal ambient graph. The admissible outside labels,
their image sizes, fiber sizes, normalized indicators and tensor compression
are constructed; no desired energy, norm, or correspondence is a hypothesis.
Local entry moments and the original additive MDS property remain hypotheses.
Constructive proof checking only; no attacks or numerical AES instantiation.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperThinPlaneShort

open PaperMDSGram PaperMDSFiber PaperThinHolder PaperThinLines PaperThinPlane
open PaperMDSShortening PaperFiberKernel PaperKernelBounds

attribute [local instance] Classical.propDecidable

variable {K J V 𝕜 : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V] [RCLike 𝕜]

abbrev Line := PhysicalShortening K V 1 4
abbrev Plane := PhysicalShortening J V 2 4

def lineCoordinate (L : Line (K := K) (V := V)) (a : Fin 4) : L.Points ≃ V :=
  affineCoordinateEquiv L.code L.dimension L.dimension_le L.mds L.offset L.fixed L.target
    L.remaining (L.middle a) (L.middle_unfixed a)

def planePair (P : Plane (J := J) (V := V)) (a b : Fin 4) (hab : a ≠ b) :
    P.Points ≃ (V × V) :=
  affinePlanePairEquiv P.code P.dimension P.dimension_le P.mds P.offset P.fixed P.target
    P.remaining (P.middle a) (P.middle b) (P.middle_unfixed a) (P.middle_unfixed b)
      (P.middle.injective.ne hab)

def middle {d n : ℕ} (G : PhysicalShortening K V d n) (x : G.Points) : Fin n → V :=
  fun a => x.val (G.middle a)

theorem line_middle_injective (L : Line (K := K) (V := V)) :
    Function.Injective (middle L) := by
  intro x y hxy
  exact (lineCoordinate L 0).injective (congrFun hxy 0)

theorem plane_middle_injective (P : Plane (J := J) (V := V)) :
    Function.Injective (middle P) := by
  intro x y hxy
  exact (planePair P 0 1 (by decide)).injective
    (Prod.ext (congrFun hxy 0) (congrFun hxy 1))

/-- These are equivalences onto the actual four-coordinate middle codes,
so the retained-word indexing introduces no duplicate middle label. -/
def lineMiddleEquiv (L : Line (K := K) (V := V)) : L.Points ≃ Set.range (middle L) :=
  Equiv.ofInjective (middle L) (line_middle_injective L)

def planeMiddleEquiv (P : Plane (J := J) (V := V)) : P.Points ≃ Set.range (middle P) :=
  Equiv.ofInjective (middle P) (plane_middle_injective P)

theorem line_fiber_dimensions (L : Line (K := K) (V := V)) :
    L.fiberDimension = 0 ∨ L.fiberDimension = 1 := by
  unfold PhysicalShortening.fiberDimension PhysicalShortening.outsideRank
  omega

theorem plane_fiber_dimensions (P : Plane (J := J) (V := V)) :
    P.fiberDimension = 0 ∨ P.fiberDimension = 1 ∨ P.fiberDimension = 2 := by
  unfold PhysicalShortening.fiberDimension PhysicalShortening.outsideRank
  omega

/-- Direct physical raw bounds; only local second moments occur. -/
theorem raw_bounds (L : Line (K := K) (V := V)) (P : Plane (J := J) (V := V))
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s) :
    (∀ x : L.Points, (∑ y : P.Points, absoluteKernel T (middle L) (middle P) x y) ≤ H ^ 2) ∧
    (∑ x : L.Points, ∑ y : P.Points, absoluteKernel T (middle L) (middle P) x y) ≤ H * S := by
  constructor
  · intro x
    have hb := plane_row (planePair P 0 1 (by decide)) (planePair P 2 3 (by decide))
      (fun a b => ‖T a (x.val (L.middle a)) b‖) H h.delta_nonneg
      (fun a => h.row_second a _)
    simpa [absoluteKernel, middle, Fin.prod_univ_succ, mul_assoc, planePair,
      affinePlanePairEquiv] using hb
  · have hb := line_plane_total (lineCoordinate L) (planePair P 0 1 (by decide))
      (planePair P 2 3 (by decide)) (fun a x y => ‖T a x y‖) H S
      h.delta_nonneg h.tau_nonneg (fun a x => h.row_second a x)
      (fun a => h.total_second a)
    simpa [absoluteKernel, middle, Fin.prod_univ_succ, mul_assoc, lineCoordinate,
      planePair, affinePlanePairEquiv, affineCoordinateEquiv] using hb

/-- The actual left outside partition yields precisely rho_0 or rho_1. -/
theorem left_partial (L : Line (K := K) (V := V)) (P : Plane (J := J) (V := V))
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (o : L.Labels) :
    (∑ x : L.Points, if L.projection x = o then
      ∑ y : P.Points, absoluteKernel T (middle L) (middle P) x y else 0) ≤
      planeRowCap L.fiberDimension H S := by
  obtain ⟨hrow, htotal⟩ := raw_bounds L P T H S r s h
  by_cases ho : L.observed = ∅
  · simp only [L.projection_empty ho o, if_true]
    simpa [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank, ho,
      planeRowCap] using htotal
  · have hlarge : 1 ≤ L.observed.card :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr ho)
    obtain ⟨x, hx⟩ := injective_partial_sum L.projection
      (L.projection_injective hlarge) L.projection_surjective
      (fun x => ∑ y : P.Points, absoluteKernel T (middle L) (middle P) x y) o
    rw [hx]
    simpa [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
      Nat.min_eq_left hlarge, planeRowCap] using hrow x

/-- All three right outside dimensions use their actual physical fibers.
The middle coordinates remain unfixed after the extra outside prescription. -/
theorem right_partial (L : Line (K := K) (V := V)) (P : Plane (J := J) (V := V))
    (T : Fin 4 → V → V → 𝕜) (H S r s : ℝ) (h : EntryMoments T H S r s)
    (o : P.Labels) :
    (∑ x : L.Points, ∑ y : P.Points, if P.projection y = o then
      absoluteKernel T (middle L) (middle P) x y else 0) ≤
      planeColCap P.fiberDimension H S r s := by
  by_cases hlarge : 2 ≤ P.observed.card
  · rw [Finset.sum_comm]
    have he (y : P.Points) :
        (∑ x : L.Points, if P.projection y = o then
          absoluteKernel T (middle L) (middle P) x y else 0) =
        if P.projection y = o then
          ∑ x : L.Points, absoluteKernel T (middle L) (middle P) x y else 0 := by
      by_cases hy : P.projection y = o <;> simp [hy]
    simp_rw [he]
    obtain ⟨y, hy⟩ := injective_partial_sum P.projection
      (P.projection_injective hlarge) P.projection_surjective
      (fun y => ∑ x : L.Points, absoluteKernel T (middle L) (middle P) x y) o
    rw [hy]
    have hb := four_transport (lineCoordinate L)
      (fun a b => ‖T a b (y.val (P.middle a))‖) H r h.delta_nonneg
      (fun a => h.col_fourth a _)
    simpa [absoluteKernel, middle, Fin.prod_univ_succ, mul_assoc, lineCoordinate,
      affineCoordinateEquiv, PhysicalShortening.fiberDimension,
      PhysicalShortening.outsideRank, Nat.min_eq_left hlarge, planeColCap] using hb
  · by_cases hempty : P.observed = ∅
    · simp only [P.projection_empty hempty o, if_true]
      simpa [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
        hempty, planeColCap] using (raw_bounds L P T H S r s h).2
    · have hcard : P.observed.card = 1 := by
        have := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      have he (x : L.Points) :
          (∑ y : P.Points, if P.projection y = o then
            absoluteKernel T (middle L) (middle P) x y else 0) =
          ∑ y : AffineFiber P.code P.offset (P.fixed ∪ P.observed)
            (mergedTarget P.fixed P.observed P.target o.val),
            ∏ a, ‖T a (x.val (L.middle a)) (y.val (P.middle a))‖ :=
        P.raw_sum o (fun y => ∏ a, ‖T a (x.val (L.middle a)) (y (P.middle a))‖)
      simp_rw [he]
      have hdim : (P.fixed ∪ P.observed).card + 1 = P.dimension := by
        rw [Finset.card_union_of_disjoint P.outside_unfixed, hcard]
        have := P.remaining
        omega
      have hmiddle (a : Fin 4) : P.middle a ∉ P.fixed ∪ P.observed := by
        simp only [Finset.mem_union, not_or]
        exact ⟨P.middle_unfixed a, P.middle_outside a⟩
      have hb := four_transport
        (fun a => Equiv.prodCongr (lineCoordinate L a)
          (affineCoordinateEquiv P.code P.dimension P.dimension_le P.mds P.offset
            (P.fixed ∪ P.observed) (mergedTarget P.fixed P.observed P.target o.val)
            hdim (P.middle a) (hmiddle a)))
        (fun a z => ‖T a z.1 z.2‖) S s h.tau_nonneg
        (by intro a; simpa only [Fintype.sum_prod_type] using h.total_fourth a)
      simpa [absoluteKernel, middle, Fin.prod_univ_succ, mul_assoc, Fintype.sum_prod_type,
        lineCoordinate, affineCoordinateEquiv, PhysicalShortening.fiberDimension,
        PhysicalShortening.outsideRank, hcard, planeColCap] using hb

/-- Normalized actual indicator maps are isometries and their kernel
compression satisfies every one of the paper's six line--plane cases. -/
theorem paper_affine_line_plane (L : Line (K := K) (V := V))
    (P : Plane (J := J) (V := V)) (T : Fin 4 → V → V → 𝕜)
    (H S r s : ℝ) (h : EntryMoments T H S r s) :
    (∀ f : EuclideanSpace 𝕜 L.Labels,
      ‖fiberLift L.projection (Fintype.card V ^ L.fiberDimension) f‖ = ‖f‖) ∧
    (∀ f : EuclideanSpace 𝕜 P.Labels,
      ‖fiberLift P.projection (Fintype.card V ^ P.fiberDimension) f‖ = ‖f‖) ∧
    ‖(fiberLift L.projection (Fintype.card V ^ L.fiberDimension)).adjoint.comp
      ((kernelOperator (lineKernel T (middle L) (middle P))).comp
        (fiberLift P.projection (Fintype.card V ^ P.fiberDimension)))‖ ≤
      (Fintype.card V : ℝ) ^ (-(((L.fiberDimension + P.fiberDimension : ℕ) : ℝ)) / 2) *
        Real.sqrt (planeRowCap L.fiberDimension H S * planeColCap P.fiberDimension H S r s) := by
  apply paper_fiber_kernel_norm_pow
    (M := absoluteKernel T (middle L) (middle P))
  · exact Fintype.card_pos_iff.mpr ⟨(0 : V)⟩
  · exact L.fiber_card
  · exact P.fiber_card
  · exact absoluteKernel_nonneg T _ _
  · intro x y
    exact (norm_lineKernel T _ _ x y).le
  · exact left_partial L P T H S r s h
  · exact right_partial L P T H S r s h

/-- Literal five-factor tensor compression on retained shortened graph
points, with the displayed square-root quotient of `eq:line-plane`. -/
theorem paper_affine_line_plane_tensor (L : Line (K := K) (V := V))
    (P : Plane (J := J) (V := V)) (T : Fin 4 → V → V → 𝕜)
    (H S r s : ℝ) (h : EntryMoments T H S r s) :
    ‖(fiberLift L.projection (Fintype.card V ^ L.fiberDimension)).adjoint.comp
      (((coordinateInclusion (middle L)).adjoint.comp
        ((coordinateTensorOperator T).comp (coordinateInclusion (middle P)))).comp
          (fiberLift P.projection (Fintype.card V ^ P.fiberDimension)))‖ ≤
      Real.sqrt ((planeRowCap L.fiberDimension H S * planeColCap P.fiberDimension H S r s) /
        (Fintype.card V : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  rw [normalized_overlap_correspondence]
  have hb := (paper_affine_line_plane L P T H S r s h).2.2
  rw [plane_normalization_sqrt_quotient _ _ _ _
    (plane_caps_nonneg _ _ H S r s h.delta_nonneg h.tau_nonneg)] at hb
  exact hb

/-- The literal Hilbert adjoint exchanges both code and outside-label
spaces and preserves the same six-case bound. -/
theorem paper_affine_line_plane_adjoint (L : Line (K := K) (V := V))
    (P : Plane (J := J) (V := V)) (T : Fin 4 → V → V → 𝕜)
    (H S r s : ℝ) (h : EntryMoments T H S r s) :
    ‖(fiberLift P.projection (Fintype.card V ^ P.fiberDimension)).adjoint.comp
      ((kernelOperator (Matrix.conjTranspose (lineKernel T (middle L) (middle P)))).comp
        (fiberLift L.projection (Fintype.card V ^ L.fiberDimension)))‖ ≤
      Real.sqrt ((planeRowCap L.fiberDimension H S * planeColCap P.fiberDimension H S r s) /
        (Fintype.card V : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  rw [← fiber_overlap_adjoint, LinearIsometryEquiv.norm_map]
  have hb := (paper_affine_line_plane L P T H S r s h).2.2
  rw [plane_normalization_sqrt_quotient _ _ _ _
    (plane_caps_nonneg _ _ H S r s h.delta_nonneg h.tau_nonneg)] at hb
  exact hb

end AES8.PaperThinPlaneShort
