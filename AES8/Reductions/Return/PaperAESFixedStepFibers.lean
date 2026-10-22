import AES8.Reductions.Return.PaperAESIncidence

/-!
# Two-sided fibers for a fixed-position step

Frozen paper f902bb94, `lem:aesasm-step`. The marked code dimension may
exceed either side's degree; no injective input projection is assumed.
MDS supplies both fiber factors and the outside information set. In
particular the input restriction contributes its genuine square-root fiber
multiplicity, rather than a separately assumed incidence cap.
Constructive proof validation only; no attacks or numerical searches.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESFixedStepFibers
open AESMixing PaperMDSGram PaperMDSFiber PaperMDSOverlap
open PaperGraphResponseMatrix PaperKernelBounds PaperFiberKernel PaperAESIncidence
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {I J V : Type*} [Fintype I] [Fintype J] [Fintype V]
  [DecidableEq I] [DecidableEq J] [AddCommGroup V] [DecidableEq V]

/-- The output information rank is valid without an injective opposite side. -/
theorem outside_information (C : AddSubgroup ((I ⊕ J) → V)) (s : ℕ)
    (hC : IsMDS C s) (htotal : s ≤ Fintype.card (I ⊕ J)) :
    ∃ S : Finset I, S.card = min s (Fintype.card I) ∧
      Function.Bijective (PaperEncoding.informationProjection (outsideSet C) S) := by
  by_cases hsmall : Fintype.card I ≤ s
  · have hall (y : I → V) : y ∈ outsideSet C := by
      have hc : Fintype.card {x : J → V // Sum.elim y x ∈ C} =
          Fintype.card V ^ (s - Fintype.card I) := by
        rw [Fintype.card_congr (rowFiberEquiv C y),
          PaperMDSFiber.prescribed_card C s htotal hC
            (leftPositions (I := I) (M := J)) (by simpa using hsmall), leftPositions_card]
      obtain ⟨x⟩ := Fintype.card_pos_iff.mp (show
          0 < Fintype.card {x : J → V // Sum.elim y x ∈ C} by
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
      (⟨fun i : S => Sum.inl i.val, fun _ _ h => Subtype.ext (Sum.inl.inj h)⟩ : S ↪ I ⊕ J)
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

/-- Every attained output label has its exact MDS fiber cardinality. -/
theorem outside_fiber_card (C : AddSubgroup ((I ⊕ J) → V)) (s : ℕ)
    (hC : IsMDS C s) (htotal : s ≤ Fintype.card (I ⊕ J)) (y : outsideSet C) :
    Fintype.card {c : C // outside C c = y} =
      Fintype.card V ^ (s - min s (Fintype.card I)) := by
  obtain ⟨x, hx⟩ := (mem_outsideSet C y.val).mp y.property
  have h := raw_indicator_row_sum_eq_of_mem C s htotal hC y.val x hx
  rw [real_indicator_sum_card] at h
  rw [Fintype.card_congr (PaperAESIncidence.outsideFiberEquiv C y)]
  exact_mod_cast h

/-- The input fiber consists of the actual codewords with that input label. -/
def middleFiberEquiv (C : AddSubgroup ((I ⊕ J) → V)) (x : J → V) :
    {c : C // middle C c = x} ≃ {y : I → V // Sum.elim y x ∈ C} where
  toFun c := ⟨fun i => c.val.val (Sum.inl i), by
    convert c.val.property using 1
    funext p
    cases p with
    | inl i => rfl
    | inr j => exact (congrFun c.property j).symm⟩
  invFun y := ⟨⟨Sum.elim y.val x, y.property⟩, rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    cases p with
    | inl i => rfl
    | inr j => exact (congrFun c.property j).symm
  right_inv _ := Subtype.ext rfl

/-- The input restriction has the square-root column-fiber norm, even when
its coordinate map is not injective and even if the input degree is zero. -/
theorem middleRestriction_norm (C : AddSubgroup ((I ⊕ J) → V)) (s : ℕ)
    (hC : IsMDS C s) (htotal : s ≤ Fintype.card (I ⊕ J)) :
    ‖(middleInclusion (𝕜 := ℝ) C).adjoint‖ ≤
      Real.sqrt ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card J))) := by
  let T : C → (J → V) → ℝ := fun c x => if middle C c = x then 1 else 0
  have hcol (x : J → V) : (∑ c, T c x) ≤
      (Fintype.card V : ℝ) ^ (s - min s (Fintype.card J)) := by
    change (∑ c : C, if middle C c = x then (1 : ℝ) else 0) ≤ _
    rw [real_indicator_sum_card, Fintype.card_congr (middleFiberEquiv C x)]
    have h := raw_indicator_column_sum_le C s htotal hC x
    rw [real_indicator_sum_card] at h
    exact h
  have hn := schur_operator_norm_sq T T 1
    ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card J)))
    (by norm_num) (by positivity)
    (fun c x => by dsimp [T]; split_ifs <;> norm_num)
    (fun c x => by dsimp [T]; split_ifs <;> simp)
    (fun c => by simp [T]) hcol
  have he : (middleInclusion (𝕜 := ℝ) C).adjoint = kernelOperator T := by
    ext f c
    simp [middleInclusion_adjoint_apply, kernelOperator_apply, kernelAction, T, ite_mul]
  rw [he]
  have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card V : ℝ) ^
    (s - min s (Fintype.card J)) by positivity)
  simp only [one_mul] at hn
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (by rw [hs]; exact hn)

theorem fiberAdjoint_norm (C : AddSubgroup ((I ⊕ J) → V)) (s : ℕ)
    (hC : IsMDS C s) (htotal : s ≤ Fintype.card (I ⊕ J)) :
    ‖(fiberLift (𝕜 := ℝ) (outside C)
      (Fintype.card V ^ (s - min s (Fintype.card I)))).adjoint‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [fiberLift_norm _ _ (pow_pos Fintype.card_pos _)
    (outside_fiber_card C s hC htotal) f, one_mul]

/-- Encoder and both fibers, on the actual rectangular incidence operator. -/
theorem outsideMapped_norm (C : AddSubgroup ((I ⊕ J) → V)) (s : ℕ)
    (hC : IsMDS C s) (htotal : s ≤ Fintype.card (I ⊕ J))
    (c ν δ : ℝ) (hc : 0 ≤ c) (hν : 0 ≤ ν) (hδ : 0 ≤ δ)
    (O : V → V → ℝ) (hO : ‖kernelOperator O‖ ≤ ν)
    (hcol : ∀ x, ‖kernelOperator O (PaperEncoding.basisVector x)‖ ^ 2 ≤ δ) :
    ‖kernelOperator (outsideMappedMatrix C c O)‖ ≤
      (c * Real.sqrt ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card I)))) *
        ((ν ^ min s (Fintype.card I) *
          Real.rpow δ (((Fintype.card I : ℝ) - (min s (Fintype.card I) : ℕ)) / 2)) *
        Real.sqrt ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card J)))) := by
  obtain ⟨S, hS, hinfo⟩ := outside_information C s hC htotal
  have he := PaperEncoding.paper_encoding_norm (outsideSet C) S hinfo
    (fun _ : I => O) ν δ hν hδ (fun _ => hO) (fun _ => hcol)
  rw [hS] at he
  have hmiddle := middleRestriction_norm C s hC htotal
  have hfiber := fiberAdjoint_norm C s hC htotal
  rw [outsideMapped_factorization C c O
    (Fintype.card V ^ (s - min s (Fintype.card I)))
    (pow_pos (show 0 < Fintype.card V from Fintype.card_pos) _), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)), Nat.cast_pow]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (Real.sqrt_nonneg _))
  calc
    _ ≤ ‖PaperEncoding.encoder (outsideSet C) (fun _ => O)‖ *
        ‖(fiberLift (outside C) (Fintype.card V ^ (s - min s (Fintype.card I)))).adjoint.comp
          (middleInclusion C).adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖PaperEncoding.encoder (outsideSet C) (fun _ => O)‖ *
        (1 * Real.sqrt ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card J)))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hfiber hmiddle (norm_nonneg _) (by norm_num))
    _ ≤ _ := by
      simpa only [one_mul, mul_assoc, Real.rpow_eq_pow] using
        mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg
          ((Fintype.card V : ℝ) ^ (s - min s (Fintype.card J))))

end AES8.PaperAESFixedStepFibers
