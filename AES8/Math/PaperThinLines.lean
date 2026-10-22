import AES8.Math.PaperThinLinesFibers
import AES8.Math.PaperThinLinesOperator

/-!
# The normalized two-line bound (`lem:lines`)

The physical endpoint uses arbitrary affine shortenings of larger MDS graphs.
The middle and outside positions are disjoint. MDS derives the middle
parametrizations, outside singleton/whole classification and q^a fiber sizes;
local moments derive the partial sums; literal inclusion identities derive the
operator correspondence. There is no assumed target sum or norm bound.

The generic finite intermediate below states its coordinate-bijection premises
explicitly. The final `paper_affine_two_lines` discharges them from MDS.
No concrete AES resources, attacks, manuscript edits or numerical searches.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperThinLines
open PaperKernelBounds PaperFiberKernel PaperMDSFiber PaperMDSGram PaperThinHolder
attribute [local instance] Classical.propDecidable

variable {𝕜 V K H L R : Type*} [RCLike 𝕜]
  [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype H] [DecidableEq H] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- The power coefficient is exactly the paper's square-root quotient. -/
theorem normalization_sqrt_quotient (q a b : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) * Real.sqrt A =
      Real.sqrt (A / (q : ℝ) ^ (a + b)) := by
  rw [← FiberNormalization.div_sqrt_pow_product]
  apply (sq_eq_sq₀
    (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (Real.sqrt_nonneg _)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hA,
    Real.sq_sqrt (Nat.cast_nonneg (q ^ a)),
    Real.sq_sqrt (Nat.cast_nonneg (q ^ b)),
    Real.sq_sqrt (div_nonneg hA (pow_nonneg (Nat.cast_nonneg q) _))]
  simp only [Nat.cast_pow, ← pow_add]

theorem partialCap_nonneg (s : Finset K) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ partialCap s A B := by
  unfold partialCap
  split_ifs <;> assumption

/-- The full normalized overlap, including the two ambient coordinate
inclusions and the product-coordinate tensor action. -/
def normalizedLineOverlap {n : ℕ} (T : Fin n → V → V → 𝕜)
    (wordL : L → K → V) (wordR : R → H → V)
    (iL : Fin n → K) (iR : Fin n → H) (s : Finset K) (t : Finset H) :
    EuclideanSpace 𝕜 (OutsideLabels wordR t) →L[𝕜]
      EuclideanSpace 𝕜 (OutsideLabels wordL s) :=
  (fiberLift (outside wordL s) (Fintype.card V ^ outsideDimension s)).adjoint.comp
    (((coordinateInclusion (fun x j => wordL x (iL j))).adjoint.comp
      ((coordinateTensorOperator T).comp
        (coordinateInclusion (fun y j => wordR y (iR j))))).comp
          (fiberLift (outside wordR t) (Fintype.card V ^ outsideDimension t)))

/-- Finite-coordinate intermediate. The coordinate assumptions here are
bijectivity/injectivity, not desired moment sums, fiber laws or operator laws.
The physical MDS theorem below proves these assumptions. -/
theorem normalized_line_norm (n : ℕ) (hn : n = 3 ∨ n = 4)
    (T : Fin n → V → V → 𝕜) (wordL : L → K → V) (wordR : R → H → V)
    (iL : Fin n → K) (iR : Fin n → H) (s : Finset K) (t : Finset H)
    (hmidL : ∀ j, Function.Bijective (fun x => wordL x (iL j)))
    (hmidR : ∀ j, Function.Bijective (fun y => wordR y (iR j)))
    (houtL : ∀ i ∈ s, Function.Injective (fun x => wordL x i))
    (houtR : ∀ i ∈ t, Function.Injective (fun y => wordR y i))
    (δ τ r z : ℝ) (hm : EntryMoments T δ τ r z) :
    ‖normalizedLineOverlap T wordL wordR iL iR s t‖ ≤
      (Fintype.card V : ℝ) ^
        (-(((outsideDimension s + outsideDimension t : ℕ) : ℝ)) / 2) *
      Real.sqrt (partialCap s (δ * r ^ (n - 2)) (τ * z ^ (n - 2)) *
        partialCap t (δ * r ^ (n - 2)) (τ * z ^ (n - 2))) := by
  let eL : Fin n → L ≃ V := fun j => Equiv.ofBijective _ (hmidL j)
  let eR : Fin n → R ≃ V := fun j => Equiv.ofBijective _ (hmidR j)
  obtain ⟨hrow, hcol, htotal⟩ := raw_bounds n hn T eL eR δ τ r z hm
  simp only [eL, eR, Equiv.ofBijective_apply] at hrow hcol htotal
  let M := absoluteKernel T (fun x j => wordL x (iL j)) (fun y j => wordR y (iR j))
  have hr : ∀ o, (∑ x, if outside wordL s x = o then ∑ y, M x y else 0) ≤
      partialCap s (δ * r ^ (n - 2)) (τ * z ^ (n - 2)) := by
    intro o
    rcases outside_fiber_classification wordL s houtL o with ⟨hs, hall⟩ | ⟨hs, x, hx⟩
    · simp only [hall, if_true]
      simpa only [partialCap, hs, if_true] using htotal
    · simp_rw [hx]
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, partialCap, hs,
        if_false] using hrow x
  have hc : ∀ o, (∑ x, ∑ y, if outside wordR t y = o then M x y else 0) ≤
      partialCap t (δ * r ^ (n - 2)) (τ * z ^ (n - 2)) := by
    intro o
    rw [Finset.sum_comm]
    have he : (∑ y, ∑ x, if outside wordR t y = o then M x y else 0) =
        ∑ y, if outside wordR t y = o then ∑ x, M x y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : outside wordR t y = o <;> simp [hy]
    rw [he]
    rcases outside_fiber_classification wordR t houtR o with ⟨ht, hall⟩ | ⟨ht, y, hy⟩
    · simp only [hall, if_true]
      rw [Finset.sum_comm]
      simpa only [partialCap, ht, if_true] using htotal
    · simp_rw [hy]
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, partialCap, ht,
        if_false] using hcol y
  unfold normalizedLineOverlap
  rw [coordinateTensor_compression]
  exact fiber_kernel_norm_pow (outside wordL s) (outside wordR t)
    (Fintype.card V) (outsideDimension s) (outsideDimension t)
    (lineKernel T (fun x j => wordL x (iL j)) (fun y j => wordR y (iR j))) M _ _
    (absoluteKernel_nonneg T _ _) (fun x y => le_of_eq (norm_lineKernel T _ _ x y)) hr hc

/-- Literal displayed `sqrt(R_a R_b / q^(a+b))` form of the generic finite
intermediate; all partial sums and classification are still derived. -/
theorem normalized_line_norm_sqrt (n : ℕ) (hn : n = 3 ∨ n = 4)
    (T : Fin n → V → V → 𝕜) (wordL : L → K → V) (wordR : R → H → V)
    (iL : Fin n → K) (iR : Fin n → H) (s : Finset K) (t : Finset H)
    (hmidL : ∀ j, Function.Bijective (fun x => wordL x (iL j)))
    (hmidR : ∀ j, Function.Bijective (fun y => wordR y (iR j)))
    (houtL : ∀ i ∈ s, Function.Injective (fun x => wordL x i))
    (houtR : ∀ i ∈ t, Function.Injective (fun y => wordR y i))
    (δ τ r z : ℝ) (hm : EntryMoments T δ τ r z) :
    ‖normalizedLineOverlap T wordL wordR iL iR s t‖ ≤
      Real.sqrt ((partialCap s (δ * r ^ (n - 2)) (τ * z ^ (n - 2)) *
        partialCap t (δ * r ^ (n - 2)) (τ * z ^ (n - 2))) /
          (Fintype.card V : ℝ) ^ (outsideDimension s + outsideDimension t)) := by
  have hA := mul_nonneg hm.delta_nonneg (pow_nonneg hm.rowScale_nonneg (n - 2))
  have hB := mul_nonneg hm.tau_nonneg (pow_nonneg hm.totalScale_nonneg (n - 2))
  have hb := normalized_line_norm n hn T wordL wordR iL iR s t
    hmidL hmidR houtL houtR δ τ r z hm
  rw [normalization_sqrt_quotient _ _ _ _
    (mul_nonneg (partialCap_nonneg s _ _ hA hB) (partialCap_nonneg t _ _ hA hB))] at hb
  exact hb

section PhysicalAffineGraphs
variable [AddCommGroup V]

/-- Middle-coordinate projection is an actual injection on a shortened line.
The first middle coordinate alone determines the entire graph point. -/
theorem affineShortLine_middle_injective (n : ℕ) (hn : 0 < n)
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hC : IsMDS C k) (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : Fin n → K) (hi : ∀ j, i j ∉ fixed) :
    Function.Injective (fun x : AffineShortLine C offset fixed target =>
      fun j => x.val (i j)) := by
  intro x y hxy
  apply (affineShortLineCoordinate C k hk hC offset fixed target hdim
    (i ⟨0, hn⟩) (hi _)).injective
  exact congrFun hxy ⟨0, hn⟩

/-- Physical affine-graph endpoint for the paper's two-line lemma.

`C,D` may be larger MDS graphs shortened by arbitrary fixed labels. Their
remaining dimension is one. `iL,iR` enumerate the distinct middle positions;
`s,t` are physical outside positions disjoint from both the shortening and
middle positions. The bounds include arbitrary signed/complex inputs, and
the two displayed indicator maps are certified isometries.
-/
theorem paper_affine_two_lines (n : ℕ) (hn : n = 3 ∨ n = 4)
    (C : AddSubgroup (K → V)) (D : AddSubgroup (H → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card H)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC : K → V) (offD : H → V) (fixedC : Finset K) (fixedD : Finset H)
    (targetC : K → V) (targetD : H → V)
    (hdimC : fixedC.card + 1 = k) (hdimD : fixedD.card + 1 = l)
    (iL : Fin n ↪ K) (iR : Fin n ↪ H)
    (hiL : ∀ j, iL j ∉ fixedC) (hiR : ∀ j, iR j ∉ fixedD)
    (s : Finset K) (t : Finset H)
    (hs : Disjoint s fixedC) (ht : Disjoint t fixedD)
    (hsMiddle : ∀ j, iL j ∉ s) (htMiddle : ∀ j, iR j ∉ t)
    (T : Fin n → V → V → 𝕜) (δ τ r z : ℝ) (hm : EntryMoments T δ τ r z) :
    let wordL := fun x : AffineShortLine C offC fixedC targetC => x.val
    let wordR := fun y : AffineShortLine D offD fixedD targetD => y.val
    (∀ f : EuclideanSpace 𝕜 (OutsideLabels wordL s),
      ‖fiberLift (outside wordL s) (Fintype.card V ^ outsideDimension s) f‖ = ‖f‖) ∧
    (∀ f : EuclideanSpace 𝕜 (OutsideLabels wordR t),
      ‖fiberLift (outside wordR t) (Fintype.card V ^ outsideDimension t) f‖ = ‖f‖) ∧
    ‖normalizedLineOverlap T wordL wordR iL iR s t‖ ≤
      Real.sqrt ((partialCap s (δ * r ^ (n - 2)) (τ * z ^ (n - 2)) *
        partialCap t (δ * r ^ (n - 2)) (τ * z ^ (n - 2))) /
          (Fintype.card V : ℝ) ^ (outsideDimension s + outsideDimension t)) := by
  let wordL := fun x : AffineShortLine C offC fixedC targetC => x.val
  let wordR := fun y : AffineShortLine D offD fixedD targetD => y.val
  have houtL : ∀ i ∈ s, Function.Injective (fun x => wordL x i) := by
    intro i hi
    exact (affineShortLineCoordinate C k hk hC offC fixedC targetC hdimC i
      (fun hf => (Finset.disjoint_left.mp hs) hi hf)).injective
  have houtR : ∀ i ∈ t, Function.Injective (fun y => wordR y i) := by
    intro i hi
    exact (affineShortLineCoordinate D l hl hD offD fixedD targetD hdimD i
      (fun hf => (Finset.disjoint_left.mp ht) hi hf)).injective
  have hq : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨(0 : V)⟩
  have hcardL : ∀ o : OutsideLabels wordL s,
      Fintype.card {x : AffineShortLine C offC fixedC targetC // outside wordL s x = o} =
        Fintype.card V ^ outsideDimension s := by
    intro o
    rw [← Nat.card_eq_fintype_card]
    apply outside_fiber_card (K := K) (V := V)
      (L := AffineShortLine C offC fixedC targetC) wordL s houtL
    simpa only [Nat.card_eq_fintype_card] using
      affineShortLine_card C k hk hC offC fixedC targetC hdimC
  have hcardR : ∀ o : OutsideLabels wordR t,
      Fintype.card {y : AffineShortLine D offD fixedD targetD // outside wordR t y = o} =
        Fintype.card V ^ outsideDimension t := by
    intro o
    rw [← Nat.card_eq_fintype_card]
    apply outside_fiber_card (K := H) (V := V)
      (L := AffineShortLine D offD fixedD targetD) wordR t houtR
    simpa only [Nat.card_eq_fintype_card] using
      affineShortLine_card D l hl hD offD fixedD targetD hdimD
  refine ⟨?_, ?_, ?_⟩
  · exact fiberLift_norm (outside wordL s) _ (pow_pos hq _) hcardL
  · exact fiberLift_norm (outside wordR t) _ (pow_pos hq _) hcardR
  · exact normalized_line_norm_sqrt n hn T wordL wordR iL iR s t
      (fun j => (affineShortLineCoordinate C k hk hC offC fixedC targetC hdimC
        (iL j) (hiL j)).bijective)
      (fun j => (affineShortLineCoordinate D l hl hD offD fixedD targetD hdimD
        (iR j) (hiR j)).bijective) houtL houtR δ τ r z hm

end PhysicalAffineGraphs
end AES8.PaperThinLines
