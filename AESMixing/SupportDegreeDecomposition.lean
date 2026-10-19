import AESMixing.SupportIndex

/-! The support components indexed above sum to the actual degree
projection already used in the AES substitution and Gram estimates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem supportProduct_overlap_zero (z : V) (r out : Fin 16)
    (hr : ¬MaskDisjoint r out) :
    supportProduct z (maskBit out) (maskBit r) = (0 : (Fin 4 → V) → (Fin 4 → V) → ℝ) := by
  unfold MaskDisjoint at hr
  push Not at hr
  obtain ⟨i,hi,ho⟩ := hr
  funext y x
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [supportPiece,hi,ho]

theorem mask_degree_size : ∀ m : Fin 16, (degreeIndex (maskBit m)).val = maskSize m := by decide

theorem supportIndex_decomposition (z : V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (fun x => ∑ p : SupportIndex j.val, supportIndexComponent z p f x) =
      degreeComponent z j f := by
  funext x
  have hs : (∑ p : SupportIndex j.val, supportIndexComponent z p f x) =
      ∑ p : Fin 16 × Fin 16, if MaskDisjoint p.2 p.1 ∧ maskSize p.1 = j.val then
        action (supportProduct z (maskBit p.1) (maskBit p.2)) f x else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs,Fintype.sum_prod_type]
  have ht (out r : Fin 16) :
      (if MaskDisjoint r out ∧ maskSize out = j.val then
        action (supportProduct z (maskBit out) (maskBit r)) f x else 0) =
      if maskSize out = j.val then action (supportProduct z (maskBit out) (maskBit r)) f x else 0 := by
    by_cases hr : MaskDisjoint r out
    · simp [hr]
    · rw [supportProduct_overlap_zero z r out hr,zero_kernel_action]
      simp
  simp_rw [ht]
  have hp (out : Fin 16) :
      (∑ r : Fin 16, action (supportProduct z (maskBit out) (maskBit r)) f x) =
        action (productProjection z (maskBit out)) f x := by
    have h := congrFun (supportProduct_decomposition z (maskBit out) f) x
    rw [← maskBitsEquiv.sum_comp] at h
    exact h
  have hgroup (out : Fin 16) :
      (∑ r : Fin 16, if maskSize out = j.val then
        action (supportProduct z (maskBit out) (maskBit r)) f x else 0) =
      if degreeIndex (maskBit out) = j then action (productProjection z (maskBit out)) f x else 0 := by
    have he : degreeIndex (maskBit out) = j ↔ maskSize out = j.val := by
      rw [Fin.ext_iff,mask_degree_size]
    by_cases h : maskSize out = j.val <;> simp [he,h,hp]
  simp_rw [hgroup]
  unfold degreeComponent groupedFamily
  exact maskBitsEquiv.sum_comp (fun a : Fin 4 → Bool =>
    if degreeIndex a = j then action (productProjection z a) f x else 0)

theorem supportIndex_degree_energy (z : V) (hn : 1 < Fintype.card V)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x^2) =
      ∑ p : SupportIndex j.val, ∑ x, supportIndexComponent z p f x^2 := by
  rw [← supportIndex_decomposition z j f]
  exact supportIndex_energy z hn j.val f

end AESMixing
