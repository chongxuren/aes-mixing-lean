/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.SupportDegree
import AESPaper.BoundaryZeros

/-!
# Exact cross zeros of the fourteen support components

The new mask components lie in their named residual-degree spaces.  The
existing physical-boundary cancellation therefore gives the thirty-two
degree-zero/degree-one cross blocks for arbitrary joint real inputs.
`physicalWordStep` is identified both with the concrete word-step kernel and
with the grouped trajectory's `H Pi`, including its inverse law transport.

These are exact one-step identities.  They supply no nonzero transfer cap,
return cap, or complete recurrence estimate: high middle degrees may contribute
to a two-step return.  Raw-mask algebra avoids the separate support-index
interface.  Constructive proof work only; no predecessor or manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
-- Concrete AES finite types exceed this naming linter's recursion budget.
-- Kernel checking and proof elaboration stay enabled.
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.TransferZeros
open AESMixing AESMixing.AES
open AES8.SupportProfile AES8.SupportDegree

private theorem mask_degree_size : ∀ m : Fin 16,
    (AESMixing.degreeIndex (maskBit m)).val = maskSize m := by decide

private theorem mask_degree_eq (m : Fin 16) (j : Fin 5) :
    AESMixing.degreeIndex (maskBit m) = j ↔ maskSize m = j.val := by
  rw [Fin.ext_iff, mask_degree_size]

/-- Applying one raw support projection to another selects its own label. -/
theorem raw_raw (p q : Label) (f : SupportProfile.State → ℝ) :
    raw p (raw q f) = if p = q then raw p f else 0 := by
  have he : (maskBit p.1 = maskBit q.1 ∧ maskBit p.2 = maskBit q.2) ↔ p = q := by
    constructor
    · intro h
      exact Prod.ext (maskBits_injective h.1) (maskBits_injective h.2)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  unfold raw
  rw [← kernelCompose_action,
    supportProduct_mixed_compose (0 : AES.Word) SupportProfile.word_card_gt_one]
  by_cases hpq : p = q
  · subst q
    simp
  · simp only [he, hpq, if_false, zero_kernel_action]

/-- The selected coordinate retains exactly its own raw support pieces. -/
theorem raw_component (p : Label) (f : SupportProfile.State → ℝ) (c : Fin 14) :
    raw p (component f c) = if coord p = c.succ then raw p f else 0 := by
  change action (supportProduct (0 : AES.Word) (maskBit p.1) (maskBit p.2))
    (groupedFamily coord (fun q => raw q f) c.succ) = _
  rw [action_groupedFamily]
  change groupedFamily coord (fun q => raw p (raw q f)) c.succ = _
  funext x
  simp only [groupedFamily, ite_apply, Pi.zero_apply]
  have hterm (q : Label) :
      (if coord q = c.succ then raw p (raw q f) x else 0) =
        if q = p then (if coord p = c.succ then raw p f x else 0) else 0 := by
    by_cases hqp : q = p
    · subst q
      simp [raw_raw]
    · simp [raw_raw, hqp, Ne.symm hqp]
  simp_rw [hterm]
  simp

/-- Function-level degree decomposition by the same two raw masks. -/
theorem degree_eq_raw (f : SupportProfile.State → ℝ) (j : Fin 5) :
    degreeComponent (0 : AES.Word) j f = fun x =>
      ∑ p : Label, if maskSize p.1 = j.val then raw p f x else 0 := by
  funext x
  calc
    degreeComponent (0 : AES.Word) j f x =
        ∑ m : Fin 16, if AESMixing.degreeIndex (maskBit m) = j then
          action (productProjection (0 : AES.Word) (maskBit m)) f x else 0 :=
      (maskBitsEquiv.sum_comp (fun a : Fin 4 → Bool =>
        if AESMixing.degreeIndex a = j then
          action (productProjection (0 : AES.Word) a) f x else 0)).symm
    _ = ∑ p : Label, if maskSize p.1 = j.val then raw p f x else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : maskSize m = j.val
      · simp only [mask_degree_eq, hm, if_true]
        have hd := congrFun
          (supportProduct_decomposition (0 : AES.Word) (maskBit m) f) x
        rw [← maskBitsEquiv.sum_comp] at hd
        exact hd.symm
      · simp only [mask_degree_eq, hm, if_false, Finset.sum_const_zero]

/-- The actual mask component is fixed by its named whole-degree projection. -/
theorem degree_component (f : SupportProfile.State → ℝ) (c : Fin 14) :
    degreeComponent (0 : AES.Word) (degree c) (component f c) = component f c := by
  rw [degree_eq_raw]
  funext x
  change (∑ p : Label, if maskSize p.1 = (degree c).val then
      raw p (component f c) x else 0) =
    ∑ p : Label, if coord p = c.succ then raw p f x else 0
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Valid p
  · by_cases hc : coord p = c.succ
    · have hd : maskSize p.1 = (degree c).val := ((coord_type p c hp).mp hc).1
      simp [hd, hc, raw_component]
    · simp [hc, raw_component]
  · simp only [raw_invalid p hp f, raw_invalid p hp (component f c),
      Pi.zero_apply, ite_self]

/-- Abstract sum positivity avoids reducing a concrete finite state-space instance. -/
private theorem function_eq_zero_of_sum_sq_nonpos {I : Type*} [Fintype I]
    (v : I → ℝ) (h : (∑ x, v x ^ 2) ≤ 0) : v = 0 := by
  classical
  funext x
  have hx : v x ^ 2 ≤ ∑ y, v y ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  exact sq_eq_zero_iff.mp (le_antisymm (hx.trans h) (sq_nonneg _))

/-- A zero whole-degree projection forces each of its support components to zero. -/
theorem component_eq_zero_of_degree_eq_zero (f : SupportProfile.State → ℝ)
    (c : Fin 14) (h : degreeComponent (0 : AES.Word) (degree c) f = 0) :
    component f c = 0 := by
  have hs : (∑ x, component f c x ^ 2) ≤ 0 := by
    have he := component_energy_le_degree f c
    simpa only [h, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] using he
  -- Keep finite-sum unification abstract instead of expanding the AES universe.
  exact function_eq_zero_of_sum_sq_nonpos (component f c) hs

/-- The concrete physical word-step kernel acts on an arbitrary joint vector. -/
def physicalWordStep (f : SupportProfile.State → ℝ) : SupportProfile.State → ℝ :=
  action AESConcrete.WordStepZeros.wordStepKernel f

theorem physicalWordStep_eq_H_Pi (f : SupportProfile.State → ℝ) :
    physicalWordStep f = AESPaper.GroupedRecurrence.H (AESPaper.GroupedRecurrence.Pi f) :=
  (AESPaper.BoundaryZeros.H_Pi_eq_wordStep f).symm

theorem physicalWordStep_eq_step (f : SupportProfile.State → ℝ) :
    physicalWordStep f = AESPaper.GroupedRecurrence.step f := by
  -- Unfold only the execution adapter; do not delta-reduce the concrete channel.
  simpa only [AESPaper.GroupedRecurrence.step, Function.comp_apply] using
    physicalWordStep_eq_H_Pi f

/-- Exactly the degree-zero/degree-one ordered pairs in the fourteen-type order. -/
def crossPair (i j : Fin 14) : Prop :=
  (residualDegree i = 0 ∧ residualDegree j = 1) ∨
    (residualDegree i = 1 ∧ residualDegree j = 0)

instance (i j : Fin 14) : Decidable (crossPair i j) := by
  unfold crossPair
  infer_instance

/-- All thirty-two pairs belong to the low-input transfer family. -/
theorem crossPair_source_low (i j : Fin 14) (h : crossPair i j) :
    residualDegree j ≤ 2 := by
  rcases h with ⟨_, hj⟩ | ⟨_, hj⟩ <;> omega

/-- Exact zero blocks for the new support components and actual grouped step. -/
theorem component_step_cross_zero (f : SupportProfile.State → ℝ) (i j : Fin 14)
    (h : crossPair i j) :
    component (AESPaper.GroupedRecurrence.step (component f j)) i = 0 := by
  apply component_eq_zero_of_degree_eq_zero
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' : degree i = (0 : Fin 5) := Fin.ext hi
    have hj' : degree j = (1 : Fin 5) := Fin.ext hj
    have habs : degreeComponent (0 : AES.Word) 1 (component f j) = component f j := by
      simpa only [hj'] using degree_component f j
    rw [hi']
    simp only [AESPaper.GroupedRecurrence.step, Function.comp_apply]
    rw [← habs]
    exact AESPaper.BoundaryZeros.H_Pi_zero_one (component f j)
  · have hi' : degree i = (1 : Fin 5) := Fin.ext hi
    have hj' : degree j = (0 : Fin 5) := Fin.ext hj
    have habs : degreeComponent (0 : AES.Word) 0 (component f j) = component f j := by
      simpa only [hj'] using degree_component f j
    rw [hi']
    simp only [AESPaper.GroupedRecurrence.step, Function.comp_apply]
    rw [← habs]
    exact AESPaper.BoundaryZeros.H_Pi_one_zero (component f j)

/-- Kernel-action form of the same exact support-level cancellation. -/
theorem component_physicalWordStep_cross_zero (f : SupportProfile.State → ℝ)
    (i j : Fin 14) (h : crossPair i j) :
    component (physicalWordStep (component f j)) i = 0 := by
  rw [physicalWordStep_eq_step]
  exact component_step_cross_zero f i j h

/-- The corresponding counting-measure support-profile entry is exactly zero. -/
theorem profile_step_cross_zero (f : SupportProfile.State → ℝ) (i j : Fin 14)
    (h : crossPair i j) :
    SupportProfile.profile (AESPaper.GroupedRecurrence.step (component f j)) i = 0 := by
  unfold SupportProfile.profile
  rw [component_step_cross_zero f i j h]
  exact l2_zero

theorem crossPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => crossPair ij.1 ij.2)).card = 32 := by decide

end AES8.TransferZeros
