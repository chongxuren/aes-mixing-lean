import AES8.Math.PaperMDSGram
import AES8.Math.PaperKernelBounds
import AES8.Math.PaperMDSFiber
import AESMixing.IncidenceKernel

/-!
# Reduced code matrices and exact unit-code vectorization

This is the raw matrix used by both whole-graph and incidence estimates.
Multiplication on its right becomes a transposed local leg on vectorization.
The alphabet and both coordinate types are arbitrary.  Physical AES graph
identification is deliberately separate from this algebraic interface.
Constructive proofs only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperGraphResponseMatrix
open AESMixing PaperMDSGram

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {I M V : Type*} [Fintype I] [Fintype M] [Fintype V]
  [DecidableEq I] [DecidableEq M] [AddCommGroup V] [DecidableEq V]

/-- Raw graph coefficient, independent of its eventual physical origin. -/
def rawGraphMatrix (C : AddSubgroup ((I ⊕ M) → V)) (c : ℝ)
    (y : I → V) (x : M → V) : ℝ :=
  c * if Sum.elim y x ∈ C then 1 else 0

/-- All middle word maps occur here, once, on the left graph. -/
def leftMatrix (C : AddSubgroup ((I ⊕ M) → V)) (c : ℝ)
    (O W : V → V → ℝ) : (I → V) → (M → V) → ℝ :=
  kernelCompose (kernelCompose (coordinateKernel (fun _ : I => O))
    (rawGraphMatrix C c)) (coordinateKernel (fun _ : M => W))

/-- Right multiplication forces the middle transpose in the vectorized map. -/
def vectorizedLocal (O W : V → V → ℝ) : (I ⊕ M) → V → V → ℝ :=
  Sum.elim (fun _ => O) (fun _ y x => W x y)

theorem vectorizedLocal_apply (O W : V → V → ℝ)
    (y : I → V) (x : M → V) (a : I → V) (b : M → V) :
    coordinateKernel (vectorizedLocal (I := I) (M := M) O W)
        (Sum.elim y x) (Sum.elim a b) =
      coordinateKernel (fun _ : I => O) y a *
        coordinateKernel (fun _ : M => W) b x := by
  simp only [coordinateKernel, vectorizedLocal, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]

theorem leftMatrix_raw_vectorization (C : AddSubgroup ((I ⊕ M) → V))
    (c : ℝ) (O W : V → V → ℝ) (y : I → V) (x : M → V) :
    leftMatrix C c O W y x = c * ∑ z : (I ⊕ M) → V,
      if z ∈ C then
        coordinateKernel (vectorizedLocal (I := I) (M := M) O W) (Sum.elim y x) z
      else 0 := by
  rw [← (Equiv.sumArrowEquivProdArrow I M V).symm.sum_comp
    (fun z : (I ⊕ M) → V => if z ∈ C then
      coordinateKernel (vectorizedLocal (I := I) (M := M) O W) (Sum.elim y x) z else 0),
    Fintype.sum_prod_type]
  change _ = c * ∑ a : I → V, ∑ b : M → V,
    if Sum.elim a b ∈ C then
      coordinateKernel (vectorizedLocal (I := I) (M := M) O W)
        (Sum.elim y x) (Sum.elim a b) else 0
  simp_rw [vectorizedLocal_apply]
  unfold leftMatrix kernelCompose rawGraphMatrix
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hz : Sum.elim a b ∈ C <;> simp [hz] <;> ring

/-- Exact conversion, including the unit-code normalization factor. -/
theorem leftMatrix_unit_vectorization (C : AddSubgroup ((I ⊕ M) → V))
    (c : ℝ) (O W : V → V → ℝ) (y : I → V) (x : M → V) :
    leftMatrix C c O W y x =
      (c * Real.sqrt (Fintype.card C : ℝ)) *
        action (coordinateKernel (vectorizedLocal (I := I) (M := M) O W))
          (unitSubgroupIndicator C) (Sum.elim y x) := by
  have hs : (∑ z : (I ⊕ M) → V, if z ∈ C then
      coordinateKernel (vectorizedLocal (I := I) (M := M) O W) (Sum.elim y x) z
      else 0) = ∑ z : C,
      coordinateKernel (vectorizedLocal (I := I) (M := M) O W) (Sum.elim y x) z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hn : Real.sqrt (Fintype.card C : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  rw [leftMatrix_raw_vectorization, hs, subgroup_action_formula]
  field_simp

/-- The literal squared Hilbert--Schmidt energy of the same raw matrix. -/
theorem leftMatrix_energy_eq (C : AddSubgroup ((I ⊕ M) → V))
    (c : ℝ) (O W : V → V → ℝ) :
    (∑ y : I → V, ∑ x : M → V, leftMatrix C c O W y x ^ 2) =
      (c ^ 2 * (Fintype.card C : ℝ)) *
        ∑ z : (I ⊕ M) → V,
          action (coordinateKernel (vectorizedLocal (I := I) (M := M) O W))
            (unitSubgroupIndicator C) z ^ 2 := by
  rw [← (Equiv.sumArrowEquivProdArrow I M V).symm.sum_comp
    (fun z : (I ⊕ M) → V =>
      action (coordinateKernel (vectorizedLocal (I := I) (M := M) O W))
        (unitSubgroupIndicator C) z ^ 2), Fintype.sum_prod_type]
  change (∑ y : I → V, ∑ x : M → V, leftMatrix C c O W y x ^ 2) =
    (c ^ 2 * (Fintype.card C : ℝ)) * ∑ y : I → V, ∑ x : M → V,
      action (coordinateKernel (vectorizedLocal (I := I) (M := M) O W))
        (unitSubgroupIndicator C) (Sum.elim y x) ^ 2
  simp_rw [leftMatrix_unit_vectorization, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), ← Finset.mul_sum]

/-- Cauchy--Schwarz turns a squared Hilbert--Schmidt cap into an arbitrary
signed-input bound without changing any entry or cancellation. -/
theorem energy_le_hilbertSchmidt {A B : Type*} [Fintype A] [Fintype B]
    (T : A → B → ℝ) (f : B → ℝ) :
    (∑ y, action T f y ^ 2) ≤
      (∑ y, ∑ x, T y x ^ 2) * ∑ x, f x ^ 2 := by
  calc
    _ ≤ ∑ y, (∑ x, T y x ^ 2) * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun y _ =>
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T y) f)
    _ = _ := (Finset.sum_mul _ _ _).symm

def graphCoefficient (i m d : ℕ) : ℝ :=
  Real.rpow (4294967296 : ℝ) (((i : ℝ) + (m : ℝ) - 4 - (d : ℝ)) / 2)

/-- An information set inside a large observed set makes every nonempty
fiber a singleton; the small branch retains its exact MDS count. -/
theorem prescribed_card_le {K : Type*} [Fintype K] [DecidableEq K]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (fixed : Finset K) (target : K → V) :
    Fintype.card (PaperMDSFiber.Fiber C fixed target) ≤
      Fintype.card V ^ (k - min k fixed.card) := by
  by_cases hsmall : fixed.card ≤ k
  · rw [Nat.min_eq_right hsmall,
      PaperMDSFiber.prescribed_card C k hk hMDS fixed hsmall target]
  · obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq (show k ≤ fixed.card by omega)
    have hinj := (hMDS (fun i => i ∈ info) (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard)).injective
    have hsingle : Subsingleton (PaperMDSFiber.Fiber C fixed target) := by
      constructor
      intro c d
      apply Subtype.ext
      apply hinj
      funext i
      exact (c.property i.val (hsub i.property)).trans
        (d.property i.val (hsub i.property)).symm
    letI := hsingle
    have hb := Fintype.card_le_of_injective
      (fun _ : PaperMDSFiber.Fiber C fixed target => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    simpa only [Nat.min_eq_left (show k ≤ fixed.card by omega), Nat.sub_self,
      pow_zero, Fintype.card_unit] using hb

def leftPositions : Finset (I ⊕ M) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem mem_leftPositions_inl (i : I) :
    Sum.inl i ∈ leftPositions (I := I) (M := M) := by simp [leftPositions]

@[simp] theorem not_mem_leftPositions_inr (i : M) :
    Sum.inr i ∉ leftPositions (I := I) (M := M) := by simp [leftPositions]

@[simp] theorem leftPositions_card :
    (leftPositions (I := I) (M := M)).card = Fintype.card I := by simp [leftPositions]

def rowFiberEquiv (C : AddSubgroup ((I ⊕ M) → V)) (y : I → V) :
    {x : M → V // Sum.elim y x ∈ C} ≃
      PaperMDSFiber.Fiber C (leftPositions (I := I) (M := M)) (Sum.elim y 0) where
  toFun x := ⟨⟨Sum.elim y x.val, x.property⟩, by
    intro i hi
    cases i with
    | inl i => rfl
    | inr i => exact False.elim (not_mem_leftPositions_inr i hi)⟩
  invFun c := ⟨fun i => c.val.val (Sum.inr i), by
    have he : Sum.elim y (fun i => c.val.val (Sum.inr i)) = c.val.val := by
      funext i
      cases i with
      | inl i => exact (c.property (Sum.inl i) (mem_leftPositions_inl i)).symm
      | inr i => rfl
    rw [he]
    exact c.val.property⟩
  left_inv x := Subtype.ext rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i with
    | inl i => exact (c.property (Sum.inl i) (mem_leftPositions_inl i)).symm
    | inr i => rfl

theorem raw_indicator_row_sum_le (C : AddSubgroup ((I ⊕ M) → V))
    (k : ℕ) (hk : k ≤ Fintype.card (I ⊕ M)) (hMDS : IsMDS C k) (y : I → V) :
    (∑ x : M → V, if Sum.elim y x ∈ C then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ (k - min k (Fintype.card I)) := by
  rw [real_indicator_sum_card, Fintype.card_congr (rowFiberEquiv C y)]
  have h := prescribed_card_le C k hk hMDS
    (leftPositions (I := I) (M := M)) (Sum.elim y 0)
  rw [leftPositions_card] at h
  exact_mod_cast h

/-- Every attained outside label has the same exact fiber cardinality.
This records the normalization behind the right incidence estimate. -/
theorem raw_indicator_row_sum_eq_of_mem (C : AddSubgroup ((I ⊕ M) → V))
    (k : ℕ) (hk : k ≤ Fintype.card (I ⊕ M)) (hMDS : IsMDS C k)
    (y : I → V) (x₀ : M → V) (hx₀ : Sum.elim y x₀ ∈ C) :
    (∑ x : M → V, if Sum.elim y x ∈ C then (1 : ℝ) else 0) =
      (Fintype.card V : ℝ) ^ (k - min k (Fintype.card I)) := by
  let D := PaperMDSFiber.Fiber C (leftPositions (I := I) (M := M)) (Sum.elim y 0)
  have hcard : Fintype.card D = Fintype.card V ^ (k - min k (Fintype.card I)) := by
    by_cases hs : Fintype.card I ≤ k
    · simpa only [D, Nat.min_eq_right hs, leftPositions_card] using
        PaperMDSFiber.prescribed_card C k hk hMDS
          (leftPositions (I := I) (M := M)) (by simpa using hs) (Sum.elim y 0)
    · have hb := prescribed_card_le C k hk hMDS
        (leftPositions (I := I) (M := M)) (Sum.elim y 0)
      haveI : Nonempty D := ⟨rowFiberEquiv C y ⟨x₀, hx₀⟩⟩
      have hp : 0 < Fintype.card D := Fintype.card_pos
      simp only [leftPositions_card, Nat.min_eq_left (show k ≤ Fintype.card I by omega),
        Nat.sub_self, pow_zero] at hb ⊢
      change Fintype.card D ≤ 1 at hb
      omega
  rw [real_indicator_sum_card, Fintype.card_congr (rowFiberEquiv C y), hcard]
  norm_cast

def rightPositions : Finset (I ⊕ M) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

@[simp] theorem mem_rightPositions_inr (i : M) :
    Sum.inr i ∈ rightPositions (I := I) (M := M) := by simp [rightPositions]

@[simp] theorem not_mem_rightPositions_inl (i : I) :
    Sum.inl i ∉ rightPositions (I := I) (M := M) := by simp [rightPositions]

@[simp] theorem rightPositions_card :
    (rightPositions (I := I) (M := M)).card = Fintype.card M := by simp [rightPositions]

def columnFiberEquiv (C : AddSubgroup ((I ⊕ M) → V)) (x : M → V) :
    {y : I → V // Sum.elim y x ∈ C} ≃
      PaperMDSFiber.Fiber C (rightPositions (I := I) (M := M)) (Sum.elim 0 x) where
  toFun y := ⟨⟨Sum.elim y.val x, y.property⟩, by
    intro i hi
    cases i with
    | inl i => exact False.elim (not_mem_rightPositions_inl i hi)
    | inr i => rfl⟩
  invFun c := ⟨fun i => c.val.val (Sum.inl i), by
    have he : Sum.elim (fun i => c.val.val (Sum.inl i)) x = c.val.val := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (c.property (Sum.inr i) (mem_rightPositions_inr i)).symm
    rw [he]
    exact c.val.property⟩
  left_inv y := Subtype.ext rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (c.property (Sum.inr i) (mem_rightPositions_inr i)).symm

theorem raw_indicator_column_sum_le (C : AddSubgroup ((I ⊕ M) → V))
    (k : ℕ) (hk : k ≤ Fintype.card (I ⊕ M)) (hMDS : IsMDS C k) (x : M → V) :
    (∑ y : I → V, if Sum.elim y x ∈ C then (1 : ℝ) else 0) ≤
      (Fintype.card V : ℝ) ^ (k - min k (Fintype.card M)) := by
  rw [real_indicator_sum_card, Fintype.card_congr (columnFiberEquiv C x)]
  have h := prescribed_card_le C k hk hMDS
    (rightPositions (I := I) (M := M)) (Sum.elim 0 x)
  rw [rightPositions_card] at h
  exact_mod_cast h

/-- The right graph has injective middle restriction when `k ≤ |M|`.
The column factor remains the actual outside-fiber size, at every rank. -/
theorem transpose_rawGraphMatrix_energy (C : AddSubgroup ((I ⊕ M) → V))
    (k : ℕ) (hMDS : IsMDS C k) (hmid : k ≤ Fintype.card M)
    (c : ℝ) (f : (I → V) → ℝ) :
    (∑ x : M → V, action (fun x y => rawGraphMatrix C c y x) f x ^ 2) ≤
      (c ^ 2 * (Fintype.card V : ℝ) ^ (k - min k (Fintype.card I))) *
        ∑ y, f y ^ 2 := by
  have hk : k ≤ Fintype.card (I ⊕ M) := by
    simp only [Fintype.card_sum]
    omega
  let B : (M → V) → (I → V) → ℝ := fun x y => if Sum.elim y x ∈ C then 1 else 0
  have hB : ∀ x y, 0 ≤ B x y := by intro x y; dsimp [B]; split_ifs <;> norm_num
  have hr (x : M → V) : (∑ y, B x y) ≤ 1 := by
    simpa only [B, Nat.min_eq_left hmid, Nat.sub_self, pow_zero] using
      raw_indicator_column_sum_le C k hk hMDS x
  have hc (y : I → V) : (∑ x, B x y) ≤
      (Fintype.card V : ℝ) ^ (k - min k (Fintype.card I)) :=
    raw_indicator_row_sum_le C k hk hMDS y
  have he (x : M → V) : action (fun x y => rawGraphMatrix C c y x) f x =
      c * action B f x := by
    simp only [action, rawGraphMatrix, B, mul_assoc, ← Finset.mul_sum]
  simp_rw [he, mul_pow, ← Finset.mul_sum]
  have hb := rectangular_schur_energy B 1
    ((Fintype.card V : ℝ) ^ (k - min k (Fintype.card I))) (by norm_num) hB hr hc f
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_left hb (sq_nonneg c)

end AES8.PaperGraphResponseMatrix
