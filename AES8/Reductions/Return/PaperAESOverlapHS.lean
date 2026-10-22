import AES8.Reductions.Return.PaperAESOverlapBound
import AES8.Math.PaperMDSShortening
import AES8.Math.FiniteCoordinatePartition

/-!
# Hilbert--Schmidt overlap on literal affine MDS shortenings

Frozen paper f902bb94, `eq:aesasm-overlap-hs`. Information restrictions and
outside fiber sizes are derived from the original larger MDS graph. The
raw squared Hilbert--Schmidt sum and normalized complex operator bound have
separate proofs. The ordinary AES case discharges its entry cap; the other
equal-bit case retains its explicit local entry premise.
Constructive proof checking only; no attacks, searches or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapHS
open AESMixing AESConcrete PaperMDSGram PaperMDSFiber PaperMDSShortening
open PaperKernelBounds PaperFiberKernel PaperAESOverlapResources

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

section InformationSums
variable {C D M V : Type*} [Fintype C] [Fintype D] [Fintype M]
  [DecidableEq M] [Fintype V] [DecidableEq V]

/-- The scalar interface used by the sum proof. Actual shortening instances
below derive this property from the original additive MDS code. -/
def Information (word : C → M → V) (s : ℕ) : Prop :=
  ∀ J : Finset M, J.card = s →
    Function.Bijective (fun c : C => fun j : J => word c j.val)

def rawKernel (T : M → V → V → ℝ) (L : C → M → V) (R : D → M → V)
    (y : C) (x : D) : ℝ := ∏ i, T i (L y i) (R x i)

/-- The ordered squared Hilbert--Schmidt estimate, before scalar factoring.
Every summation is over the actual graph points. -/
theorem raw_hs_ordered (L : C → M → V) (R : D → M → V)
    (s t : ℕ) (hL : Information L s) (hR : Information R t)
    (hst : s ≤ t) (ht : t ≤ Fintype.card M)
    (T : M → V → V → ℝ) (e δ H : ℝ) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hentry : ∀ i y x, |T i y x| ≤ e)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ δ)
    (htotal : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ H) :
    (∑ y, ∑ x, rawKernel T L R y x ^ 2) ≤
      (e ^ 2) ^ (Fintype.card M - t) * δ ^ (t - s) * H ^ s := by
  obtain ⟨J, _, hJ⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ : Finset M).card by simpa using ht)
  obtain ⟨I, hIJ, hI⟩ := Finset.exists_subset_card_eq (show s ≤ J.card by omega)
  let ER : D ≃ (J → V) := Equiv.ofBijective _ (hR J hJ)
  let EL : C ≃ (I → V) := Equiv.ofBijective _ (hL I hI)
  let row : M → V → ℝ := fun i y => ∑ x, T i y x ^ 2
  have hentrySq (i : M) (y x : V) : T i y x ^ 2 ≤ e ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (hentry i y x)
  have hpoint (y : C) :
      (∑ x, rawKernel T L R y x ^ 2) ≤
        (e ^ 2) ^ (Fintype.card M - t) * ∏ j : J, row j.val (L y j.val) := by
    have hsplit (x : D) : rawKernel T L R y x ^ 2 =
        (∏ j : J, T j.val (L y j.val) (R x j.val) ^ 2) *
          (∏ j : ↥((Finset.univ : Finset M) \ J),
            T j.val (L y j.val) (R x j.val) ^ 2) := by
      simp only [rawKernel, ← Finset.prod_pow]
      exact FiniteCoordinatePartition.prod_split J Finset.univ (Finset.subset_univ _)
        (fun i => T i (L y i) (R x i) ^ 2)
    have hrest (x : D) :
        (∏ j : ↥((Finset.univ : Finset M) \ J),
          T j.val (L y j.val) (R x j.val) ^ 2) ≤
            (e ^ 2) ^ (Fintype.card M - t) := by
      calc
        _ ≤ ∏ _ : ↥((Finset.univ : Finset M) \ J), e ^ 2 :=
          Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ => hentrySq _ _ _)
        _ = _ := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
            Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, hJ]
    have hsum : (∑ x : D, ∏ j : J, T j.val (L y j.val) (R x j.val) ^ 2) =
        ∏ j : J, row j.val (L y j.val) := by
      calc
        _ = ∑ u : J → V, ∏ j : J, T j.val (L y j.val) (u j) ^ 2 :=
          ER.sum_comp (fun u => ∏ j : J, T j.val (L y j.val) (u j) ^ 2)
        _ = _ := by
          change (∑ u : J → V, ∏ j : J, T j.val (L y j.val) (u j) ^ 2) =
            ∏ j : J, ∑ x : V, T j.val (L y j.val) x ^ 2
          exact (Fintype.prod_sum (fun j : J => fun x : V => T j.val (L y j.val) x ^ 2)).symm
    calc
      _ ≤ ∑ x : D, (∏ j : J, T j.val (L y j.val) (R x j.val) ^ 2) *
          (e ^ 2) ^ (Fintype.card M - t) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (hrest x)
          (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, hsum]; ring
  have hleft : (∑ y : C, ∏ j : J, row j.val (L y j.val)) ≤ δ ^ (t - s) * H ^ s := by
    have hb := FiberCollision.information_set_sum_bound EL
      (fun y : C => fun j : ↥(J \ I) => L y j.val)
      (fun i : I => row i.val) (fun j : ↥(J \ I) => row j.val) H δ hδ
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (fun i => htotal i.val) (fun j => hrow j.val)
    have hsplit (y : C) : (∏ j : J, row j.val (L y j.val)) =
        (∏ i : I, row i.val (EL y i)) *
          (∏ j : ↥(J \ I), row j.val (L y j.val)) := by
      change (∏ j : J, row j.val (L y j.val)) =
        (∏ i : I, row i.val (L y i.val)) *
          (∏ j : ↥(J \ I), row j.val (L y j.val))
      rw [Finset.prod_coe_sort J (fun i => row i (L y i))]
      exact FiniteCoordinatePartition.prod_split I J hIJ (fun i => row i (L y i))
    calc
      _ = ∑ y : C, (∏ i : I, row i.val (EL y i)) *
          (∏ j : ↥(J \ I), row j.val (L y j.val)) :=
        Finset.sum_congr rfl (fun y _ => hsplit y)
      _ ≤ H ^ Fintype.card I * δ ^ Fintype.card ↥(J \ I) := hb
      _ = _ := by
        simp only [Fintype.card_coe, Finset.card_sdiff_of_subset hIJ, hI, hJ]
        ring
  calc
    _ ≤ ∑ y : C, (e ^ 2) ^ (Fintype.card M - t) *
        ∏ j : J, row j.val (L y j.val) := Finset.sum_le_sum (fun y _ => hpoint y)
    _ = (e ^ 2) ^ (Fintype.card M - t) *
        ∑ y : C, ∏ j : J, row j.val (L y j.val) := (Finset.mul_sum _ _ _).symm
    _ ≤ (e ^ 2) ^ (Fintype.card M - t) * (δ ^ (t - s) * H ^ s) :=
      mul_le_mul_of_nonneg_left hleft (pow_nonneg (sq_nonneg _) _)
    _ = _ := by ring

def coefficient (m s t : ℕ) (e δ H : ℝ) : ℝ :=
  e ^ (m - max s t) * Real.rpow δ (((max s t - min s t : ℕ) : ℝ) / 2) *
    Real.rpow H (((min s t : ℕ) : ℝ) / 2)

theorem coefficient_nonneg (m s t : ℕ) (e δ H : ℝ)
    (he : 0 ≤ e) (hδ : 0 ≤ δ) (hH : 0 ≤ H) : 0 ≤ coefficient m s t e δ H :=
  mul_nonneg (mul_nonneg (pow_nonneg he _) (Real.rpow_nonneg hδ _))
    (Real.rpow_nonneg hH _)

theorem coefficient_sq (m s t : ℕ) (e δ H : ℝ) (hδ : 0 ≤ δ) (hH : 0 ≤ H) :
    coefficient m s t e δ H ^ 2 =
      (e ^ 2) ^ (m - max s t) * δ ^ (max s t - min s t) * H ^ min s t := by
  have hd : Real.rpow δ (((max s t - min s t : ℕ) : ℝ) / 2) ^ (2 : ℕ) =
      δ ^ (max s t - min s t) := by
    calc
      _ = Real.rpow δ ((max s t - min s t : ℕ) : ℝ) :=
        PaperWholeGraphReturn.rpow_half_square _ _ hδ
      _ = _ := Real.rpow_natCast _ _
  have hh : Real.rpow H (((min s t : ℕ) : ℝ) / 2) ^ (2 : ℕ) = H ^ min s t := by
    calc
      _ = Real.rpow H ((min s t : ℕ) : ℝ) :=
        PaperWholeGraphReturn.rpow_half_square _ _ hH
      _ = _ := Real.rpow_natCast _ _
  unfold coefficient
  rw [mul_pow, mul_pow, hd, hh, ← pow_mul, Nat.mul_comm, pow_mul]

theorem raw_hs (L : C → M → V) (R : D → M → V)
    (s t : ℕ) (hL : Information L s) (hR : Information R t)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (T : M → V → V → ℝ) (e δ H : ℝ) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (hentry : ∀ i y x, |T i y x| ≤ e)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ δ)
    (hcol : ∀ i x, (∑ y, T i y x ^ 2) ≤ δ)
    (htotal : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ H) :
    (∑ y, ∑ x, rawKernel T L R y x ^ 2) ≤ coefficient (Fintype.card M) s t e δ H ^ 2 := by
  rw [coefficient_sq _ _ _ _ _ _ hδ hH]
  by_cases hst : s ≤ t
  · simpa only [max_eq_right hst, min_eq_left hst] using
      raw_hs_ordered L R s t hL hR hst ht T e δ H he hδ hentry hrow htotal
  · have hts : t ≤ s := by omega
    have hb := raw_hs_ordered R L t s hR hL hts hs (fun i x y => T i y x)
      e δ H he hδ (fun i x y => hentry i y x) hcol
      (by intro i; rw [Finset.sum_comm]; exact htotal i)
    rw [Finset.sum_comm]
    simpa only [rawKernel, max_eq_left hts, min_eq_right hts] using hb

end InformationSums

section PhysicalShortenings
variable {KL KR V : Type*} [Fintype KL] [DecidableEq KL]
  [Fintype KR] [DecidableEq KR] [AddCommGroup V] [Fintype V] [DecidableEq V]

def shortMiddle {s n : ℕ} (L : PhysicalShortening KL V s n) (x : L.Points) : Fin n → V :=
  fun i => x.val (L.middle i)

/-- Information coordinates of a shortening are derived from the larger
MDS graph, while its retained words keep all physical fixed coordinates. -/
theorem short_information {s n : ℕ} (L : PhysicalShortening KL V s n) :
    Information (shortMiddle L) s := by
  intro J hJ
  let S := J.map L.middle
  have hd : Disjoint L.fixed S := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hj
    exact L.middle_unfixed j hi
  have hb := PaperThinHolder.affine_projection_bijective L.code L.dimension L.dimension_le L.mds
    L.offset L.fixed S hd (by simpa only [S, Finset.card_map, hJ] using L.remaining) L.target
  let f : J → S := fun j => ⟨L.middle j.val,
    Finset.mem_map.mpr ⟨j.val, j.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (L.middle.injective (congrArg Subtype.val h))
    · intro i
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp i.property
      exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  let E : J ≃ S := Equiv.ofBijective f hf
  constructor
  · intro x y hxy
    apply hb.injective
    funext i
    obtain ⟨j, rfl⟩ := E.surjective i
    exact congrFun hxy j
  · intro u
    obtain ⟨x, hx⟩ := hb.surjective (fun i => u (E.symm i))
    refine ⟨x, ?_⟩
    funext j
    have hj := congrFun hx (E j)
    change x.val (L.middle j.val) = u (E.symm (E j)) at hj
    change x.val (L.middle j.val) = u j
    simpa only [Equiv.symm_apply_apply] using hj

def normalizedOverlap {s t n : ℕ} (L : PhysicalShortening KL V s n)
    (R : PhysicalShortening KR V t n) (T : Fin n → V → V → ℝ) :=
  (fiberLift (𝕜 := ℂ) L.projection (Fintype.card V ^ L.fiberDimension)).adjoint.comp
    ((kernelOperator (fun y x => (rawKernel T (shortMiddle L) (shortMiddle R) y x : ℂ))).comp
      (fiberLift (𝕜 := ℂ) R.projection (Fintype.card V ^ R.fiberDimension)))

theorem fiber_norm_le_one {s n : ℕ} (L : PhysicalShortening KL V s n) :
    ‖fiberLift (𝕜 := ℂ) L.projection (Fintype.card V ^ L.fiberDimension)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [fiberLift_norm _ _ (pow_pos Fintype.card_pos _) L.fiber_card f, one_mul]

/-- Literal normalized complex overlap; no desired norm or fiber identity
is supplied as a premise. This theorem permits every complex input. -/
theorem normalized_overlap_norm {s t n : ℕ}
    (L : PhysicalShortening KL V s n) (R : PhysicalShortening KR V t n)
    (hs : s ≤ n) (ht : t ≤ n) (T : Fin n → V → V → ℝ)
    (e δ H : ℝ) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (hentry : ∀ i y x, |T i y x| ≤ e)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ δ)
    (hcol : ∀ i x, (∑ y, T i y x ^ 2) ≤ δ)
    (htotal : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ H) :
    ‖normalizedOverlap L R T‖ ≤ coefficient n s t e δ H := by
  let B : L.Points → R.Points → ℝ := rawKernel T (shortMiddle L) (shortMiddle R)
  let c := coefficient n s t e δ H
  have hc : 0 ≤ c := coefficient_nonneg _ _ _ _ _ _ he hδ hH
  have hhs : (∑ y, ∑ x, B y x ^ 2) ≤ c ^ 2 := by
    simpa only [Fintype.card_fin] using raw_hs (shortMiddle L) (shortMiddle R) s t
      (short_information L) (short_information R)
      (by simpa only [Fintype.card_fin] using hs)
      (by simpa only [Fintype.card_fin] using ht) T e δ H he hδ hH hentry hrow hcol htotal
  have hreal : ∀ f : R.Points → ℝ, l2 (action B f) ≤ c * l2 f := by
    intro f
    have hb := (PaperGraphResponseMatrix.energy_le_hilbertSchmidt B f).trans
      (mul_le_mul_of_nonneg_right hhs (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (l2_nonneg _) (mul_nonneg hc (l2_nonneg _))).mp
    simpa only [mul_pow, l2_sq] using hb
  have hraw := PaperAESOverlapBound.complex_kernel_norm_of_real_l2 B c hc hreal
  have hleft : ‖(fiberLift (𝕜 := ℂ) L.projection
      (Fintype.card V ^ L.fiberDimension)).adjoint‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact fiber_norm_le_one L
  have hright := fiber_norm_le_one R
  unfold normalizedOverlap
  calc
    _ ≤ ‖(fiberLift (𝕜 := ℂ) L.projection
        (Fintype.card V ^ L.fiberDimension)).adjoint‖ *
        ‖(kernelOperator (fun y x => (B y x : ℂ))).comp
          (fiberLift (𝕜 := ℂ) R.projection (Fintype.card V ^ R.fiberDimension))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (c * 1) := by
      apply mul_le_mul hleft _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hraw hright (norm_nonneg _) hc)
    _ = _ := by ring

end PhysicalShortenings

section AESInstantiation
variable {KL KR : Type*} [Fintype KL] [DecidableEq KL] [Fintype KR] [DecidableEq KR]

/-- Explicit entry-cap interface for either equal Fourier orientation.
The true/true 27/q resource is deliberately not inferred here. -/
theorem equal_bits_norm_of_entry {s t n : ℕ}
    (L : PhysicalShortening KL AES.Word s n) (R : PhysicalShortening KR AES.Word t n)
    (hs : s ≤ n) (ht : t ≤ n) (adjoint bit : Bool)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed adjoint bit bit y x| ≤ entry) :
    ‖normalizedOverlap L R (fun _ => PaperWordMixedGram.mixed adjoint bit bit)‖ ≤
      coefficient n s t entry delta total := by
  exact normalized_overlap_norm L R hs ht _ entry delta total entry_nonneg delta_nonneg
    total_nonneg (fun _ => hentry) (fun _ => mixed_row_energy adjoint bit bit)
    (fun _ => mixed_column_energy adjoint bit bit) (fun _ => mixed_total_energy adjoint bit bit)

/-- Unconditional ordinary residual and adjoint HS menu branch on arbitrary
larger physical affine shortenings, including both actual fiber maps. -/
theorem ordinary_norm {s t n : ℕ}
    (L : PhysicalShortening KL AES.Word s n) (R : PhysicalShortening KR AES.Word t n)
    (hs : s ≤ n) (ht : t ≤ n) (adjoint : Bool) :
    ‖normalizedOverlap L R (fun _ => PaperWordMixedGram.mixed adjoint false false)‖ ≤
      coefficient n s t entry delta total :=
  equal_bits_norm_of_entry L R hs ht adjoint false (ordinary_entry adjoint)

end AESInstantiation
end AES8.PaperAESOverlapHS
