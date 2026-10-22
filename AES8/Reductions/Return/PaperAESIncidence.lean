import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Reductions.Return.PaperWholeGraphReturn
import AES8.Reductions.Return.PaperWordGraphCode
import AES8.Math.PaperEncoding
import AES8.Math.PaperFiberKernel
import AES8.Estimates.Word.SharpWordNorm

/-!
# Literal reduced-graph incidence and its outside encoder

Frozen paper: f902bb94, `16-graph-bounds.tex`, `lem:aesasm-incidence`.
The attained outside image and both coordinate maps are defined from the
actual code. The normalized identity is over either real or complex scalars;
the encoder estimate is first proved over the reals and then complexified.
MDS and the middle-size condition supply the information set, injective middle
restriction, and equal fibers. No norm inequality or physical identification
is assumed. Physical marked AES contraction is joined separately below.
Constructive proof validation only; no attacks, searches, or paper edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESIncidence
open AESMixing PaperMDSGram PaperGraphResponseMatrix PaperKernelBounds
open PaperMDSOverlap PaperFiberKernel
open PaperWordGraphCode

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {I M V : Type*} [Fintype I] [Fintype M] [Fintype V]
  [DecidableEq I] [DecidableEq M] [AddCommGroup V] [DecidableEq V]

def outsideSet (C : AddSubgroup ((I ⊕ M) → V)) : Finset (I → V) :=
  Finset.univ.filter (fun y => ∃ x : M → V, Sum.elim y x ∈ C)

@[simp] theorem mem_outsideSet (C : AddSubgroup ((I ⊕ M) → V)) (y : I → V) :
    y ∈ outsideSet C ↔ ∃ x : M → V, Sum.elim y x ∈ C := by
  simp [outsideSet]

def middle (C : AddSubgroup ((I ⊕ M) → V)) (c : C) : M → V :=
  fun j => c.val (Sum.inr j)

def outside (C : AddSubgroup ((I ⊕ M) → V)) (c : C) : outsideSet C :=
  ⟨fun i => c.val (Sum.inl i), mem_outsideSet C _ |>.mpr ⟨middle C c, by
    convert c.property using 1
    funext p
    cases p <;> rfl⟩⟩

theorem middle_injective (C : AddSubgroup ((I ⊕ M) → V)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ Fintype.card M) : Function.Injective (middle C) := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show s ≤ (Finset.univ : Finset M).card by simpa using hmid)
  have hb := restriction_bijective_of_card C s hC
    (⟨fun j : S => Sum.inr j.val, fun _ _ h => Subtype.ext (Sum.inr.inj h)⟩ : S ↪ I ⊕ M)
    (by simpa using hS)
  intro c d h
  apply hb.injective
  funext j
  exact congrFun h j.val

/-- The outside information set has precisely the rank printed in the paper. -/
theorem outside_information (C : AddSubgroup ((I ⊕ M) → V)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ Fintype.card M) :
    ∃ S : Finset I, S.card = min s (Fintype.card I) ∧
      Function.Bijective (PaperEncoding.informationProjection (outsideSet C) S) := by
  have hk : s ≤ Fintype.card (I ⊕ M) := by simp only [Fintype.card_sum]; omega
  by_cases hsmall : Fintype.card I ≤ s
  · have hall (y : I → V) : y ∈ outsideSet C := by
      have hc : Fintype.card {x : M → V // Sum.elim y x ∈ C} =
          Fintype.card V ^ (s - Fintype.card I) := by
        rw [Fintype.card_congr (rowFiberEquiv C y),
          PaperMDSFiber.prescribed_card C s hk hC
            (leftPositions (I := I) (M := M)) (by simpa using hsmall), leftPositions_card]
      obtain ⟨x⟩ := Fintype.card_pos_iff.mp (show
          0 < Fintype.card {x : M → V // Sum.elim y x ∈ C} by
        rw [hc]; exact pow_pos Fintype.card_pos _)
      exact (mem_outsideSet C y).mpr ⟨x.val, x.property⟩
    refine ⟨Finset.univ, by simp [Nat.min_eq_right hsmall], ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      funext i
      exact congrFun h ⟨i, Finset.mem_univ i⟩
    · intro u
      exact ⟨⟨fun i => u ⟨i, Finset.mem_univ i⟩, hall _⟩, rfl⟩
  · have hs : s ≤ Fintype.card I := by omega
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
      (show s ≤ (Finset.univ : Finset I).card by simpa using hs)
    have hb := restriction_bijective_of_card C s hC
      (⟨fun i : S => Sum.inl i.val, fun _ _ h => Subtype.ext (Sum.inl.inj h)⟩ : S ↪ I ⊕ M)
      (by simpa using hS)
    refine ⟨S, by simpa [Nat.min_eq_left hs] using hS, ?_, ?_⟩
    · intro y z h
      obtain ⟨x, hx⟩ := (mem_outsideSet C y.val).mp y.property
      obtain ⟨w, hw⟩ := (mem_outsideSet C z.val).mp z.property
      have he : (⟨Sum.elim y.val x, hx⟩ : C) = ⟨Sum.elim z.val w, hw⟩ :=
        hb.injective h
      apply Subtype.ext
      funext i
      exact congrArg (fun c : C => c.val (Sum.inl i)) he
    · intro u
      obtain ⟨c, hc⟩ := hb.surjective u
      exact ⟨outside C c, hc⟩

def outsideFiberEquiv (C : AddSubgroup ((I ⊕ M) → V)) (y : outsideSet C) :
    {c : C // outside C c = y} ≃ {x : M → V // Sum.elim y.val x ∈ C} where
  toFun c := ⟨middle C c.val, by
    convert c.val.property using 1
    funext p
    cases p with
    | inl i => exact congrFun (congrArg Subtype.val c.property).symm i
    | inr i => rfl⟩
  invFun x := ⟨⟨Sum.elim y.val x.val, x.property⟩, Subtype.ext rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    cases p with
    | inl i => exact congrFun (congrArg Subtype.val c.property).symm i
    | inr i => rfl
  right_inv x := Subtype.ext rfl

theorem outside_fiber_card (C : AddSubgroup ((I ⊕ M) → V)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ Fintype.card M) (y : outsideSet C) :
    Fintype.card {c : C // outside C c = y} =
      Fintype.card V ^ (s - min s (Fintype.card I)) := by
  obtain ⟨x, hx⟩ := (mem_outsideSet C y.val).mp y.property
  have h := raw_indicator_row_sum_eq_of_mem C s
    (by simp only [Fintype.card_sum]; omega) hC y.val x hx
  rw [real_indicator_sum_card] at h
  rw [Fintype.card_congr (outsideFiberEquiv C y)]
  exact_mod_cast h

section ScalarIdentity
variable {𝕜 : Type*} [RCLike 𝕜]

def rawKernel (C : AddSubgroup ((I ⊕ M) → V)) (y : I → V) (x : M → V) : 𝕜 :=
  if Sum.elim y x ∈ C then 1 else 0

def outsideInclusion (C : AddSubgroup ((I ⊕ M) → V)) :
    EuclideanSpace 𝕜 (outsideSet C) →L[𝕜] EuclideanSpace 𝕜 (I → V) :=
  kernelOperator (fun y b => if b.val = y then 1 else 0)

def middleInclusion (C : AddSubgroup ((I ⊕ M) → V)) :
    EuclideanSpace 𝕜 C →L[𝕜] EuclideanSpace 𝕜 (M → V) :=
  kernelOperator (fun x c => if middle C c = x then 1 else 0)

@[simp] theorem middleInclusion_adjoint_apply (C : AddSubgroup ((I ⊕ M) → V))
    (f : EuclideanSpace 𝕜 (M → V)) (c : C) :
    (middleInclusion C).adjoint f c = f (middle C c) := by
  rw [middleInclusion, kernelOperator_adjoint]
  simp [kernelOperator_apply, kernelAction, Matrix.conjTranspose_apply]

theorem outsideInclusion_apply (C : AddSubgroup ((I ⊕ M) → V))
    (g : EuclideanSpace 𝕜 (outsideSet C)) (y : I → V) :
    outsideInclusion C g y = if hy : y ∈ outsideSet C then g ⟨y, hy⟩ else 0 := by
  by_cases hy : y ∈ outsideSet C
  · rw [dif_pos hy]
    change (∑ b : outsideSet C, (if b.val = y then (1 : 𝕜) else 0) * g b) = _
    rw [Finset.sum_eq_single (⟨y, hy⟩ : outsideSet C)]
    · simp
    · intro b _ hb
      have hne : b.val ≠ y := fun he => hb (Subtype.ext he)
      simp [hne]
    · simp
  · rw [dif_neg hy]
    apply Finset.sum_eq_zero
    intro b _
    have hne : b.val ≠ y := by intro he; exact hy (he ▸ b.property)
    simp [hne]

theorem rawKernel_code_sum (C : AddSubgroup ((I ⊕ M) → V)) (y : I → V) (x : M → V) :
    rawKernel (𝕜 := 𝕜) C y x =
      ∑ c : C, if (outside C c).val = y ∧ middle C c = x then 1 else 0 := by
  by_cases hz : Sum.elim y x ∈ C
  · let c₀ : C := ⟨Sum.elim y x, hz⟩
    rw [rawKernel, if_pos hz, Finset.sum_eq_single c₀]
    · have hm : middle C c₀ = x := rfl
      simp [c₀, outside, hm]
    · intro c _ hc
      split_ifs with he
      · have hec : c = c₀ := by
          apply Subtype.ext
          funext p
          cases p with
          | inl i => exact congrFun he.1 i
          | inr j => exact congrFun he.2 j
        exact False.elim (hc hec)
      · rfl
    · simp
  · rw [rawKernel, if_neg hz]
    symm
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with he
    · have hec : Sum.elim y x = c.val := by
        funext p
        cases p with
        | inl i => exact (congrFun he.1 i).symm
        | inr j => exact (congrFun he.2 j).symm
      exact False.elim (hz (hec ▸ c.property))
    · rfl

theorem rawKernel_action (C : AddSubgroup ((I ⊕ M) → V))
    (f : (M → V) → 𝕜) (y : I → V) :
    kernelAction (rawKernel C) f y =
      ∑ c : C, if (outside C c).val = y then f (middle C c) else 0 := by
  unfold kernelAction
  simp_rw [rawKernel_code_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (outside C c).val = y
  · simp [hc, ite_mul]
  · simp [hc]

/-- The literal paper identity, as equality of actual real/complex operators.
`middleInclusion` is a coordinate inclusion when MDS gives middle injection. -/
theorem raw_incidence_identity (C : AddSubgroup ((I ⊕ M) → V))
    (a : ℕ) (ha : 0 < a) :
    kernelOperator (rawKernel (𝕜 := 𝕜) C) =
      (Real.sqrt (a : ℝ) : 𝕜) • (outsideInclusion C).comp
        ((fiberLift (outside C) a).adjoint.comp (middleInclusion C).adjoint) := by
  have hs : (Real.sqrt (a : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ha)))
  ext f y
  change kernelAction (rawKernel C) (fun x => f x) y =
    (Real.sqrt (a : ℝ) : 𝕜) * outsideInclusion C
      ((fiberLift (outside C) a).adjoint ((middleInclusion C).adjoint f)) y
  rw [rawKernel_action, outsideInclusion_apply]
  by_cases hy : y ∈ outsideSet C
  · rw [dif_pos hy, fiberLift_adjoint_apply]
    simp only [middleInclusion_adjoint_apply]
    have he (c : C) : outside C c = (⟨y, hy⟩ : outsideSet C) ↔
        (outside C c).val = y := Subtype.ext_iff
    simp_rw [he]
    field_simp
  · rw [dif_neg hy, mul_zero]
    apply Finset.sum_eq_zero
    intro c _
    have hn : (outside C c).val ≠ y := by
      intro he
      exact hy (he ▸ (outside C c).property)
    simp [hn]

/-- MDS supplies the exact normalization and the isometry hypothesis. -/
theorem mds_normalized_fiber_isometry (C : AddSubgroup ((I ⊕ M) → V))
    (s : ℕ) (hC : IsMDS C s) (hmid : s ≤ Fintype.card M)
    (f : EuclideanSpace 𝕜 (outsideSet C)) :
    ‖fiberLift (outside C) (Fintype.card V ^ (s - min s (Fintype.card I))) f‖ = ‖f‖ :=
  fiberLift_norm _ _ (pow_pos Fintype.card_pos _) (outside_fiber_card C s hC hmid) f

end ScalarIdentity

/-- Restriction along an injective coordinate map is a contraction. -/
theorem middleRestriction_norm (C : AddSubgroup ((I ⊕ M) → V))
    (hinj : Function.Injective (middle C)) :
    ‖(middleInclusion (𝕜 := ℝ) C).adjoint‖ ≤ 1 := by
  let T : C → (M → V) → ℝ := fun c x => if middle C c = x then 1 else 0
  have hcol (x : M → V) : (∑ c, T c x) ≤ 1 := by
    change (∑ c : C, if middle C c = x then (1 : ℝ) else 0) ≤ 1
    rw [real_indicator_sum_card]
    haveI : Subsingleton {c : C // middle C c = x} := ⟨fun a b =>
      Subtype.ext (hinj (a.property.trans b.property.symm))⟩
    have hc := Fintype.card_le_of_injective
      (fun _ : {c : C // middle C c = x} => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    have hc' : Fintype.card {c : C // middle C c = x} ≤ 1 := by simpa using hc
    exact_mod_cast hc'
  have hn := schur_operator_norm_sq T T 1 1 (by norm_num) (by norm_num)
    (fun c x => by dsimp [T]; split_ifs <;> norm_num)
    (fun c x => by dsimp [T]; split_ifs <;> simp)
    (fun c => by simp [T]) hcol
  have he : (middleInclusion (𝕜 := ℝ) C).adjoint = kernelOperator T := by
    ext f c
    simp [middleInclusion_adjoint_apply, kernelOperator_apply, kernelAction, T, ite_mul]
  rw [he]
  norm_num at hn
  nlinarith [norm_nonneg (kernelOperator T)]

theorem fiberAdjoint_norm (C : AddSubgroup ((I ⊕ M) → V)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ Fintype.card M) :
    ‖(fiberLift (𝕜 := ℝ) (outside C)
      (Fintype.card V ^ (s - min s (Fintype.card I)))).adjoint‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [mds_normalized_fiber_isometry C s hC hmid f, one_mul]

def outsideMappedMatrix (C : AddSubgroup ((I ⊕ M) → V)) (c : ℝ)
    (O : V → V → ℝ) : (I → V) → (M → V) → ℝ :=
  kernelCompose (coordinateKernel (fun _ : I => O)) (rawGraphMatrix C c)

theorem kernelOperator_comp {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq B] [DecidableEq D] (T : A → B → ℝ) (U : B → D → ℝ) :
    kernelOperator (kernelCompose T U) = (kernelOperator T).comp (kernelOperator U) := by
  ext f y
  simp only [kernelOperator_apply, ContinuousLinearMap.comp_apply, kernelAction,
    kernelCompose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem encoder_inclusion (C : AddSubgroup ((I ⊕ M) → V)) (O : V → V → ℝ) :
    (kernelOperator (coordinateKernel (fun _ : I => O))).comp
      (outsideInclusion C) = PaperEncoding.encoder (outsideSet C) (fun _ => O) := by
  ext f y
  change (∑ a : I → V, (∏ i, O (y i) (a i)) *
    ∑ b : outsideSet C, (if b.val = a then (1 : ℝ) else 0) * f b) =
      ∑ b : outsideSet C, (∏ i, O (y i) (b.val i)) * f b
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [mul_ite, ite_mul]

theorem coefficient_operator (C : AddSubgroup ((I ⊕ M) → V)) (c : ℝ) :
    kernelOperator (rawGraphMatrix C c) = c • kernelOperator (rawKernel C) := by
  ext f y
  change (∑ x, (c * if Sum.elim y x ∈ C then 1 else 0) * f x) =
    c * ∑ x, rawKernel (𝕜 := ℝ) C y x * f x
  simp only [rawKernel, mul_assoc, Finset.mul_sum]

/-- The outside word maps are exactly the information-set encoder. -/
theorem outsideMapped_factorization (C : AddSubgroup ((I ⊕ M) → V))
    (c : ℝ) (O : V → V → ℝ) (a : ℕ) (ha : 0 < a) :
    kernelOperator (outsideMappedMatrix C c O) =
      (c * Real.sqrt (a : ℝ)) • (PaperEncoding.encoder (outsideSet C) (fun _ => O)).comp
        ((fiberLift (outside C) a).adjoint.comp (middleInclusion C).adjoint) := by
  rw [outsideMappedMatrix, kernelOperator_comp, coefficient_operator,
    raw_incidence_identity C a ha]
  ext f y
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    smul_smul]
  have he := congrArg (fun T => T ((fiberLift (outside C) a).adjoint
    ((middleInclusion C).adjoint f))) (encoder_inclusion C O)
  simp only [ContinuousLinearMap.comp_apply] at he
  rw [he]
  rfl

/-- Generic displayed left factor, on the literal graph matrix. -/
theorem outsideMapped_norm (C : AddSubgroup ((I ⊕ M) → V)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ Fintype.card M)
    (c ν δ : ℝ) (hc : 0 ≤ c) (hν : 0 ≤ ν) (hδ : 0 ≤ δ)
    (O : V → V → ℝ) (hO : ‖kernelOperator O‖ ≤ ν)
    (hcol : ∀ x, ‖kernelOperator O (PaperEncoding.basisVector x)‖ ^ 2 ≤ δ) :
    ‖kernelOperator (outsideMappedMatrix C c O)‖ ≤
      (c * Real.sqrt ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card I)))) *
        (ν ^ min s (Fintype.card I) *
          Real.rpow δ (((Fintype.card I : ℝ) - (min s (Fintype.card I) : ℕ)) / 2)) := by
  obtain ⟨S, hS, hinfo⟩ := outside_information C s hC hmid
  have he := PaperEncoding.paper_encoding_norm (outsideSet C) S hinfo
    (fun _ : I => O) ν δ hν hδ (fun _ => hO) (fun _ => hcol)
  rw [hS] at he
  have hmiddle := middleRestriction_norm C (middle_injective C s hC hmid)
  have hfiber := fiberAdjoint_norm C s hC hmid
  rw [outsideMapped_factorization C c O
    (Fintype.card V ^ (s - min s (Fintype.card I)))
    (pow_pos (show 0 < Fintype.card V from Fintype.card_pos) _), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)), Nat.cast_pow]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (Real.sqrt_nonneg _))
  calc
    _ ≤ ‖PaperEncoding.encoder (outsideSet C) (fun _ => O)‖ *
        ‖(fiberLift (outside C) (Fintype.card V ^ (s - min s (Fintype.card I)))).adjoint.comp
          (middleInclusion C).adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖PaperEncoding.encoder (outsideSet C) (fun _ => O)‖ * (1 * 1) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hfiber hmiddle (norm_nonneg _) (by norm_num))
    _ ≤ _ := by simpa using he

def nu : ℝ := 52 / (5 * 65536)

theorem nu_nonneg : 0 ≤ nu := by norm_num [nu]

/-- Exact activity/fiber cancellation, with real subtraction in the exponent. -/
theorem incidence_coefficient (i m s : ℕ) :
    graphCoefficient i m s *
      Real.sqrt ((4294967296 : ℝ) ^ (s - min s i)) =
    Real.rpow (4294967296 : ℝ)
      (((i : ℝ) + (m : ℝ) - 4 - (min s i : ℕ)) / 2) := by
  have hq : (0 : ℝ) < 4294967296 := by norm_num
  have hs : (graphCoefficient i m s *
      Real.sqrt ((4294967296 : ℝ) ^ (s - min s i))) ^ 2 =
      (Real.rpow (4294967296 : ℝ)
        (((i : ℝ) + (m : ℝ) - 4 - (min s i : ℕ)) / 2)) ^ 2 := by
    rw [mul_pow, PaperWholeGraphReturn.graphCoefficient_square,
      Real.sq_sqrt (pow_nonneg hq.le _),
      PaperWholeGraphReturn.rpow_half_square _ _ hq.le,
      ← Real.rpow_natCast (4294967296 : ℝ) (s - min s i)]
    change (4294967296 : ℝ) ^ ((i : ℝ) + (m : ℝ) - 4 - (s : ℝ)) *
      (4294967296 : ℝ) ^ ((s - min s i : ℕ) : ℝ) =
      (4294967296 : ℝ) ^ ((i : ℝ) + (m : ℝ) - 4 - (min s i : ℕ))
    rw [← Real.rpow_add hq]
    congr 1
    rw [Nat.cast_sub (Nat.min_le_left _ _)]
    ring
  have hleft : 0 ≤ graphCoefficient i m s *
      Real.sqrt ((4294967296 : ℝ) ^ (s - min s i)) := by
    exact mul_nonneg (Real.rpow_nonneg hq.le _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.rpow (4294967296 : ℝ)
      (((i : ℝ) + (m : ℝ) - 4 - (min s i : ℕ)) / 2) := Real.rpow_nonneg hq.le _
  exact le_antisymm ((sq_le_sq₀ hleft hright).mp hs.le)
    ((sq_le_sq₀ hright hleft).mp hs.ge)

theorem word_sqrt_multiplicity (a : ℕ) :
    Real.sqrt ((4294967296 : ℝ) ^ a) =
      Real.rpow (4294967296 : ℝ) ((a : ℝ) / 2) := by
  have hleft := Real.sqrt_nonneg ((4294967296 : ℝ) ^ a)
  have hright : 0 ≤ Real.rpow (4294967296 : ℝ) ((a : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hs : Real.sqrt ((4294967296 : ℝ) ^ a) ^ 2 =
      Real.rpow (4294967296 : ℝ) ((a : ℝ) / 2) ^ 2 := by
    rw [Real.sq_sqrt (by positivity),
      PaperWholeGraphReturn.rpow_half_square _ _ (by norm_num)]
    change (4294967296 : ℝ) ^ a = (4294967296 : ℝ) ^ (a : ℝ)
    exact (Real.rpow_natCast (4294967296 : ℝ) a).symm
  exact le_antisymm ((sq_le_sq₀ hleft hright).mp hs.le)
    ((sq_le_sq₀ hright hleft).mp hs.ge)

/-- The paper's literal `q^(a/2) I J* I*` identity for either scalar field.
The MDS hypotheses making this normalization isometric are supplied separately
by `mds_normalized_fiber_isometry`; the algebraic identity needs no MDS premise. -/
theorem aes_raw_incidence_identity {𝕜 : Type*} [RCLike 𝕜] {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ) :
    kernelOperator (rawKernel (𝕜 := 𝕜) C) =
      (Real.rpow (4294967296 : ℝ) (((s - min s i : ℕ) : ℝ) / 2) : 𝕜) •
        (outsideInclusion C).comp
          ((fiberLift (outside C) (Fintype.card AES.Word ^ (s - min s i))).adjoint.comp
            (middleInclusion C).adjoint) := by
  have hc : Real.sqrt ((Fintype.card AES.Word ^ (s - min s i) : ℕ) : ℝ) =
      Real.rpow (4294967296 : ℝ) (((s - min s i : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_pow, AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat,
      word_sqrt_multiplicity]
  rw [← hc]
  exact raw_incidence_identity (𝕜 := 𝕜) C
    (Fintype.card AES.Word ^ (s - min s i))
    (pow_pos (show 0 < Fintype.card AES.Word from Fintype.card_pos) _)

def leftFactor (i m s : ℕ) : ℝ :=
  Real.rpow (4294967296 : ℝ) (((i : ℝ) + (m : ℝ) - 4 - (min s i : ℕ)) / 2) *
    (nu ^ min s i * Real.rpow PaperWordMixedGram.delta (((i : ℝ) - (min s i : ℕ)) / 2))

def rightFactor (j m t : ℕ) : ℝ :=
  Real.rpow (4294967296 : ℝ) (((j : ℝ) + (m : ℝ) - 4 - (min t j : ℕ)) / 2)

theorem leftFactor_nonneg (i m s : ℕ) : 0 ≤ leftFactor i m s := by
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (mul_nonneg (pow_nonneg nu_nonneg _) (Real.rpow_nonneg PaperWordMixedGram.delta_nonneg _))

/-- The actual ordinary/simultaneous-Fourier residual supplies the local caps. -/
theorem aes_left_incidence_norm {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ m) (adjoint fourier : Bool) :
    ‖kernelOperator (outsideMappedMatrix C (graphCoefficient i m s)
      (AESConcrete.WordFourierVariants.variant adjoint fourier))‖ ≤ leftFactor i m s := by
  have hnorm : ‖kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier)‖ ≤ nu := by
    have h := (SharpWordNorm.variant_operator_norm_lt adjoint fourier).le
    have hs : Real.sqrt ((2 : ℝ) ^ 32) = 65536 := by
      rw [show (2 : ℝ) ^ 32 = 65536 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hop : kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier) =
        AESConcrete.kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier) := by
      ext f y
      rfl
    rw [hop]
    simpa only [hs, nu] using h
  have hcol (x : AES.Word) :
      ‖kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier)
        (PaperEncoding.basisVector x)‖ ^ 2 ≤ PaperWordMixedGram.delta := by
    rw [PaperEncoding.basis_response_energy]
    exact (PaperAESSource.residualVariant_column_energy_lt_current adjoint fourier x).le.trans
      (by norm_num [PaperWordMixedGram.delta])
  have h := outsideMapped_norm C s hC (by simpa using hmid)
    (graphCoefficient i m s) nu PaperWordMixedGram.delta
    (Real.rpow_nonneg (by norm_num) _) nu_nonneg PaperWordMixedGram.delta_nonneg
    (AESConcrete.WordFourierVariants.variant adjoint fourier) hnorm hcol
  simp only [Fintype.card_fin, AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat] at h
  rw [incidence_coefficient] at h
  exact h

/-- Complex inputs retain all original signed cancellations. -/
theorem aes_left_incidence_complex_energy {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ m) (adjoint fourier : Bool)
    (f : (Fin m → AES.Word) → ℂ) :
    (∑ y, ‖kernelAction (fun y x =>
      (outsideMappedMatrix C (graphCoefficient i m s)
        (AESConcrete.WordFourierVariants.variant adjoint fourier) y x : ℂ)) f y‖ ^ 2) ≤
      leftFactor i m s ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
  apply PaperWholeGraphReturn.complex_energy_of_real
  intro g
  exact PaperEncoding.local_energy_of_norm _ _ (leftFactor_nonneg i m s)
    (aes_left_incidence_norm C s hC hmid adjoint fourier) g

theorem aes_left_incidence_complex_norm {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ m) (adjoint fourier : Bool) :
    ‖kernelOperator (fun y x =>
      (outsideMappedMatrix C (graphCoefficient i m s)
        (AESConcrete.WordFourierVariants.variant adjoint fourier) y x : ℂ))‖ ≤
      leftFactor i m s := by
  have hn := operator_norm_sq_le_of_energy _ (leftFactor i m s ^ 2) (sq_nonneg _)
    (aes_left_incidence_complex_energy C s hC hmid adjoint fourier)
  exact (sq_le_sq₀ (norm_nonneg _) (leftFactor_nonneg i m s)).mp hn

theorem aes_right_incidence_complex_energy {j m : ℕ}
    (C : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (t : ℕ)
    (hC : IsMDS C t) (hmid : t ≤ m) (f : (Fin j → AES.Word) → ℂ) :
    (∑ x, ‖kernelAction (fun x y => (rawGraphMatrix C (graphCoefficient j m t) y x : ℂ))
      f x‖ ^ 2) ≤ rightFactor j m t ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  apply PaperWholeGraphReturn.complex_energy_of_real
  intro g
  have h := transpose_rawGraphMatrix_energy C t hC (by simpa using hmid)
    (graphCoefficient j m t) g
  simp only [Fintype.card_fin, AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat] at h
  have he : graphCoefficient j m t ^ 2 * (4294967296 : ℝ) ^ (t - min t j) =
      rightFactor j m t ^ 2 := by
    unfold rightFactor
    rw [← incidence_coefficient j m t, mul_pow, Real.sq_sqrt (by positivity)]
  rw [he] at h
  exact h

/-- The displayed right factor bounds the actual complex right operator. -/
theorem aes_right_incidence_norm {j m : ℕ}
    (C : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (t : ℕ)
    (hC : IsMDS C t) (hmid : t ≤ m) :
    ‖kernelOperator (fun x y => (rawGraphMatrix C (graphCoefficient j m t) y x : ℂ))‖ ≤
      rightFactor j m t := by
  have hn := operator_norm_sq_le_of_energy _ (rightFactor j m t ^ 2) (sq_nonneg _)
    (aes_right_incidence_complex_energy C t hC hmid)
  have hp : 0 ≤ rightFactor j m t := Real.rpow_nonneg (by norm_num) _
  nlinarith [norm_nonneg (kernelOperator
    (fun x y => (rawGraphMatrix C (graphCoefficient j m t) y x : ℂ)))]

def markedIncidence {i m : ℕ} (B U : Finset Position) (e : B ≃ (Fin i ⊕ Fin m))
    (y : Fin i → AES.Word) (x : Fin m → AES.Word) : ℝ :=
  graphContraction B U (fun p => Sum.elim y x (e p))

/-- Explicit physical AES join: contract the actual word graph against the
zero/uniform activity frame, then relabel its marked positions. -/
theorem markedIncidence_eq {i m : ℕ} (B U : Finset Position)
    (e : B ≃ (Fin i ⊕ Fin m)) (hd : Disjoint B U) (s : ℕ)
    (hdim : (zeroPositions B U).card + s = 4) (hmid : s ≤ m) :
    markedIncidence B U e = rawGraphMatrix
      (relabelCode (markedCode B U) e) (graphCoefficient i m s) := by
  have hcard : B.card = i + m := by
    simpa using Fintype.card_congr e
  funext y x
  rw [markedIncidence, graphContraction_eq_graphCoefficient B U hd s hdim (by omega)]
  rw [hcard]
  simp only [rawGraphMatrix, graphCoefficient, relabel_mem_iff, Nat.cast_add]

/-- The left displayed factor now applies to a literal marked AES graph
contraction, with no graph-identification premise. -/
theorem marked_aes_left_incidence_norm {i m : ℕ} (B U : Finset Position)
    (e : B ≃ (Fin i ⊕ Fin m)) (hd : Disjoint B U) (s : ℕ)
    (hdim : (zeroPositions B U).card + s = 4) (hmid : s ≤ m)
    (adjoint fourier : Bool) :
    ‖kernelOperator (kernelCompose
      (coordinateKernel (fun _ : Fin i => AESConcrete.WordFourierVariants.variant adjoint fourier))
      (markedIncidence B U e))‖ ≤ leftFactor i m s := by
  rw [markedIncidence_eq B U e hd s hdim hmid]
  exact aes_left_incidence_norm _ s
    (relabel_isMDS _ e s (markedCode_isMDS B U s hdim)) hmid adjoint fourier

/-- The concrete marked left AES contraction also acts on arbitrary complex vectors. -/
theorem marked_aes_left_incidence_complex_norm {i m : ℕ} (B U : Finset Position)
    (e : B ≃ (Fin i ⊕ Fin m)) (hd : Disjoint B U) (s : ℕ)
    (hdim : (zeroPositions B U).card + s = 4) (hmid : s ≤ m)
    (adjoint fourier : Bool) :
    ‖kernelOperator (fun y x => ((kernelCompose
      (coordinateKernel (fun _ : Fin i => AESConcrete.WordFourierVariants.variant adjoint fourier))
      (markedIncidence B U e)) y x : ℂ))‖ ≤ leftFactor i m s := by
  rw [markedIncidence_eq B U e hd s hdim hmid]
  exact aes_left_incidence_complex_norm _ s
    (relabel_isMDS _ e s (markedCode_isMDS B U s hdim)) hmid adjoint fourier

theorem marked_aes_right_incidence_complex_norm {j m : ℕ} (B U : Finset Position)
    (e : B ≃ (Fin j ⊕ Fin m)) (hd : Disjoint B U) (t : ℕ)
    (hdim : (zeroPositions B U).card + t = 4) (hmid : t ≤ m) :
    ‖kernelOperator (fun x y => (markedIncidence B U e y x : ℂ))‖ ≤ rightFactor j m t := by
  rw [markedIncidence_eq B U e hd t hdim hmid]
  exact aes_right_incidence_norm _ t
    (relabel_isMDS _ e t (markedCode_isMDS B U t hdim)) hmid

end AES8.PaperAESIncidence
