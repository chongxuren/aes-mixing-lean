import AESConcrete.RefinedStepZeros

/-!
# Completeness of the fourteen physical support types

The fourteen types omit exactly the all-zero-state projection. This file
separates that finite projection identity from norm caps and from the
experiment interface.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RefinedProjectionCompleteness
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (blockType)
open AESConcrete.DegreeCentering (distinguishedState)

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem refined_compose (z : V) (hn : 1 < Fintype.card V) (d a : Fin 5) :
    kernelCompose (refinedKernel z d a) (refinedKernel z d a) =
      refinedKernel z d a := by
  funext y x
  unfold refinedKernel kernelCompose
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have hterm (r : SupportIndex d.val) :
      (∑ v,
        (if AES.maskSize r.val.2 + a.val = 4 then supportIndexKernel z r y v else 0) *
        (if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel z p v x else 0)) =
        if r = p then
          (if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel z p y x else 0)
        else 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · by_cases hr : AES.maskSize r.val.2 + a.val = 4
      · simp only [hp, hr, if_true]
        change kernelCompose (supportIndexKernel z r) (supportIndexKernel z p) y x = _
        rw [supportIndexKernel_compose z hn]
        by_cases he : r = p
        · subst r
          simp
        · simp [he, Ne.symm he]
      · by_cases he : r = p
        · subst r
          exact (hr hp).elim
        · simp [hr, he]
    · simp [hp]
  simp_rw [hterm]
  simp

theorem refined_invalid (z : V) (d a : Fin 5) (h : a < d) :
    refinedKernel z d a = 0 := by
  funext y x
  apply Finset.sum_eq_zero
  intro p _
  have hs := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
  have hd := p.property.2
  have hn : ¬ AES.maskSize p.val.2 + a.val = 4 := by
    change a.val < d.val at h
    omega
  simp only [hn, if_false, Pi.zero_apply]

theorem refined_sum_active (z : V) (d : Fin 5) :
    (fun y x => ∑ a : Fin 5, refinedKernel z d a y x) = degreeKernel z d := by
  rw [← supportIndexKernel_sum z d]
  funext y x
  unfold refinedKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hs := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
  let active : Fin 5 := ⟨4 - AES.maskSize p.val.2, by omega⟩
  have hselect (a : Fin 5) : AES.maskSize p.val.2 + a.val = 4 ↔ a = active := by
    rw [Fin.ext_iff]
    change AES.maskSize p.val.2 + a.val = 4 ↔ a.val = 4 - AES.maskSize p.val.2
    omega
  simp_rw [hselect]
  simp

/-- This identity concerns only the fixed finite type list. -/
theorem type_sum (f : Fin 5 → Fin 5 → ℝ)
    (hz : ∀ d a, a < d → f d a = 0) :
    (∑ i : Fin 14, f (blockType i).1 (blockType i).2) + f 0 0 =
      ∑ d : Fin 5, ∑ a : Fin 5, f d a := by
  have h10 := hz 1 0 (by decide)
  have h20 := hz 2 0 (by decide)
  have h21 := hz 2 1 (by decide)
  have h30 := hz 3 0 (by decide)
  have h31 := hz 3 1 (by decide)
  have h32 := hz 3 2 (by decide)
  have h40 := hz 4 0 (by decide)
  have h41 := hz 4 1 (by decide)
  have h42 := hz 4 2 (by decide)
  have h43 := hz 4 3 (by decide)
  simp [Fin.sum_univ_succ, blockType, h10, h20, h21, h30, h31, h32,
    h40, h41, h42, h43]
  <;> ring

theorem degree_sum_identity (z : V) :
    (fun y x => ∑ d : Fin 5, degreeKernel z d y x) = identityKernel := by
  apply kernel_action_ext
  intro f
  rw [identityKernel_action]
  have hd := degreeComponent_decomposition z f
  funext y
  change (∑ x, (∑ d : Fin 5, degreeKernel z d y x) * f x) = f y
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simpa only [action, ← degreeKernel_action] using congrFun hd y

theorem fourteen_plus_omitted (z : V) :
    (fun y x => ∑ i : Fin 14,
      refinedKernel z (blockType i).1 (blockType i).2 y x) +
        refinedKernel z 0 0 = identityKernel := by
  have ht (y x : Fin 4 → V) := type_sum
    (fun d a => refinedKernel z d a y x)
    (fun d a h => congrFun (congrFun (refined_invalid z d a h) y) x)
  have hs (d : Fin 5) (y x : Fin 4 → V) :=
    congrFun (congrFun (refined_sum_active z d) y) x
  funext y x
  change (∑ i : Fin 14, refinedKernel z (blockType i).1 (blockType i).2 y x) +
    refinedKernel z 0 0 y x = identityKernel y x
  rw [ht]
  simp_rw [hs]
  exact congrFun (congrFun (degree_sum_identity z) y) x

private def omittedSupport : SupportIndex 0 := ⟨(0,15), by decide⟩

private theorem omitted_support_unique : ∀ p : SupportIndex 0,
    AES.maskSize p.val.2 = 4 ↔ p = omittedSupport := by decide

theorem zeroMatrix_tensor (z : V) (y x : Fin 4 → V) :
    (∏ i : Fin 4, zeroMatrix z (y i) (x i)) =
      zeroMatrix (distinguishedState z) y x := by
  by_cases hy : y = distinguishedState z
  · subst y
    by_cases hx : x = distinguishedState z
    · subst x
      simp [zeroMatrix, identityKernel, distinguishedState]
    · have hex : ∃ i, x i ≠ z := by
        by_contra hn
        push Not at hn
        exact hx (funext hn)
      obtain ⟨i, hi⟩ := hex
      simp only [zeroMatrix, identityKernel, hx, if_false, mul_zero]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  · have hex : ∃ i, y i ≠ z := by
      by_contra hn
      push Not at hn
      exact hy (funext hn)
    obtain ⟨i, hi⟩ := hex
    simp only [zeroMatrix, identityKernel, hy, if_false, zero_mul]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem refined_zero_zero (z : V) :
    refinedKernel z 0 0 = zeroMatrix (distinguishedState z) := by
  have h0 : AES.maskBit 0 = fun _ : Fin 4 => false := by decide
  have h15 : AES.maskBit 15 = fun _ : Fin 4 => true := by decide
  funext y x
  unfold refinedKernel
  simp only [Fin.val_zero, Nat.add_zero, omitted_support_unique]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change supportProduct z (AES.maskBit 0) (AES.maskBit 15) y x = _
  rw [h0, h15]
  simpa only [supportProduct, supportPiece, Bool.false_eq_true, if_false, if_true]
    using zeroMatrix_tensor z y x

theorem fourteen_plus_zero (z : V) :
    (fun y x => ∑ i : Fin 14,
      refinedKernel z (blockType i).1 (blockType i).2 y x) +
        zeroMatrix (distinguishedState z) = identityKernel := by
  rw [← refined_zero_zero]
  exact fourteen_plus_omitted z

private theorem mask_has_active : ∀ m : Fin 16, AES.maskSize m < 4 →
    ∃ i : Fin 4, AES.maskBit m i = false := by decide

theorem supportPiece_active_zero (z x : V) (marked : Bool) :
    supportPiece z marked false z x = 0 := by
  cases marked <;> by_cases hx : x = z <;>
    simp [supportPiece, residualProjection, constantMatrix, zeroMatrix,
      activityMatrix, identityKernel, hx, eq_comm] <;> exact Ne.symm hx

theorem refined_at_zero (z : V) (d a : Fin 5) (ha : a ≠ 0)
    (x : Fin 4 → V) : refinedKernel z d a (distinguishedState z) x = 0 := by
  unfold refinedKernel
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    have hpos : a.val ≠ 0 := by simpa using ha
    obtain ⟨i, hi⟩ := mask_has_active p.val.2 (by omega)
    unfold supportIndexKernel supportProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change supportPiece z (AES.maskBit p.val.1 i) (AES.maskBit p.val.2 i) z (x i) = 0
    rw [hi]
    exact supportPiece_active_zero z (x i) _
  · simp only [hp, if_false]

theorem refined_compose_zero (z : V) (d a : Fin 5) (ha : a ≠ 0) :
    kernelCompose (refinedKernel z d a) (zeroMatrix (distinguishedState z)) = 0 := by
  have hz (y : Fin 4 → V) : refinedKernel z d a y (distinguishedState z) = 0 := by
    rw [refinedKernel_symmetric]
    exact refined_at_zero z d a ha y
  funext y x
  simp [kernelCompose, zeroMatrix, identityKernel, hz]

private theorem blockType_active : ∀ i : Fin 14, (blockType i).2 ≠ 0 := by decide

theorem physical_projection_compose_zero (z : V) (i : Fin 14) :
    kernelCompose (refinedKernel z (blockType i).1 (blockType i).2)
      (zeroMatrix (distinguishedState z)) = 0 :=
  refined_compose_zero z _ _ (blockType_active i)

theorem wordStep_compose_zero :
    kernelCompose WordStepZeros.wordStepKernel
      (zeroMatrix (0 : AES.WordState)) = zeroMatrix 0 := by
  have hcol (y : AES.WordState) : WordStepZeros.wordStepKernel y 0 =
      if y = 0 then 1 else 0 := by
    unfold WordStepZeros.wordStepKernel
    rw [map_zero]
    exact AES.parallel_superbox_pointed.zero_column y
  funext y x
  simp [kernelCompose, zeroMatrix, identityKernel, hcol]

theorem centeredWordStep_compose_zero :
    kernelCompose CenteredWordStepZeros.centeredWordStepKernel
      (zeroMatrix (0 : AES.WordState)) = zeroMatrix 0 := by
  rw [CenteredWordStepZeros.centeredWordStepKernel,
    CenteredWordStepZeros.compose_sub_left, wordStep_compose_zero]
  have hu : kernelCompose (DegreeCentering.globalUniformKernel (0 : AES.Word))
      (zeroMatrix (0 : AES.WordState)) = 0 := by
    have hz : distinguishedState (0 : AES.Word) = (0 : AES.WordState) := rfl
    have hc (y : AES.WordState) : DegreeCentering.globalUniformKernel (0 : AES.Word) y 0 = 0 := by
      simp [DegreeCentering.globalUniformKernel, hz]
    funext y x
    simp [kernelCompose, zeroMatrix, identityKernel, hc]
  rw [hu, sub_zero]

theorem physical_remainder_invisible (i : Fin 14) :
    kernelCompose
      (refinedKernel (0 : AES.Word) (blockType i).1 (blockType i).2)
      (kernelCompose CenteredWordStepZeros.centeredWordStepKernel
        (zeroMatrix (0 : AES.WordState))) = 0 := by
  rw [centeredWordStep_compose_zero]
  exact physical_projection_compose_zero (0 : AES.Word) i

end AESConcrete.RefinedProjectionCompleteness
