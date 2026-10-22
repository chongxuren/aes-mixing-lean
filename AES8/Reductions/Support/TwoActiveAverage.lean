/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.OneActiveAverage
import AES8.Reductions.Fibers.WordMixTwoZeroFiber

/-!
# Exact two-active nonzero averages and their signed boundary masses

Six degree-zero patterns have two literal zero blocks and two literal
constant-NONZERO blocks. Their counting energies are exact-support signed
masses squared divided by (q-1)^2. The patterns are orthogonal and sum to
profile component one.

The inverse boundary pullback is reindexed by FORWARD physical wordMix.
Signed inclusion-exclusion subtracts the two three-zero endpoint fibers and
adds the common zero point. No mass/norm bound, independence assumption or
AES endpoint is supplied here.  Constructive
proofs only; no attacks, proof bypasses or manuscript/predecessor edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.TwoActiveAverage
open AESMixing AESMixing.AES
open AES8.SupportProfile (Label raw)

-- Position pairs are 01,02,03,12,13,23; only these finite labels are decided.
def left : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def right : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
def inactiveMask : Fin 6 → Fin 16 := ![12, 10, 6, 9, 5, 3]
def patternLabel (t : Fin 6) : Label := (0, inactiveMask t)

theorem left_ne_right : ∀ t : Fin 6, left t ≠ right t := by decide
theorem inactiveMask_bit : ∀ (t : Fin 6) (i : Fin 4),
    maskBit (inactiveMask t) i = decide (i ≠ left t ∧ i ≠ right t) := by decide
theorem inactiveMask_size : ∀ t : Fin 6, maskSize (inactiveMask t) = 2 := by decide

def SelectedLabel (p : Label) : Prop := maskSize p.1 = 0 ∧ 4 - maskSize p.2 = 2
instance (p : Label) : Decidable (SelectedLabel p) := by unfold SelectedLabel; infer_instance

theorem patternLabel_selected : ∀ t : Fin 6, SelectedLabel (patternLabel t) := by decide
theorem patternLabel_injective : Function.Injective patternLabel := by decide

def patternLabelEquiv : Fin 6 ≃ {p : Label // SelectedLabel p} :=
  Equiv.ofBijective (fun t => ⟨patternLabel t, patternLabel_selected t⟩) (by decide)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def Q (t : Fin 6) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t))) f

def S (t : Fin 6) (x : Fin 4 → V) : Prop :=
  x (left t) ≠ 0 ∧ x (right t) ≠ 0 ∧
    ∀ i : Fin 4, i ≠ left t → i ≠ right t → x i = 0
instance (t : Fin 6) (x : Fin 4 → V) : Decidable (S t x) := by unfold S; infer_instance

def mass (t : Fin 6) (f : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ x, if S t x then f x else 0

/-- A full prescribed-zero event: no nonzero test is imposed outside r. -/
def Z (r : Fin 16) (x : Fin 4 → V) : Prop :=
  ∀ i : Fin 4, maskBit r i = true → x i = 0
instance (r : Fin 16) (x : Fin 4 → V) : Decidable (Z r x) := by unfold Z; infer_instance

def zeroMass (r : Fin 16) (f : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ x, if Z r x then f x else 0

theorem Z_inactive_iff (t : Fin 6) (x : Fin 4 → V) :
    Z (inactiveMask t) x ↔ ∀ i : Fin 4, i ≠ left t → i ≠ right t → x i = 0 := by
  constructor
  · intro h i hil hir
    exact h i (by rw [inactiveMask_bit]; exact decide_eq_true ⟨hil, hir⟩)
  · intro h i hi
    have hp : i ≠ left t ∧ i ≠ right t :=
      of_decide_eq_true ((inactiveMask_bit t i).symm.trans hi)
    exact h i hp.1 hp.2

theorem Z_single_iff (t : Fin 4) (x : Fin 4 → V) :
    Z (OneActiveAverage.inactiveMask t) x ↔ ∀ i : Fin 4, i ≠ t → x i = 0 := by
  constructor
  · intro h i hit
    exact h i (by rw [OneActiveAverage.inactiveMask_bit]; exact decide_eq_true hit)
  · intro h i hi
    exact h i (of_decide_eq_true ((OneActiveAverage.inactiveMask_bit t i).symm.trans hi))

theorem kernel_literal (t : Fin 6) (y x : Fin 4 → V) :
    supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)) y x =
      if S t y ∧ S t x then (ActivityAverageEnergy.denominator V)⁻¹ ^ 2 else 0 := by
  have hm : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
  by_cases hy : S t y
  · by_cases hx : S t x
    · rw [if_pos ⟨hy, hx⟩]
      have hp (i : Fin 4) :
          supportPiece (0 : V) (maskBit 0 i) (maskBit (inactiveMask t) i) (y i) (x i) =
            if i = left t ∨ i = right t then (ActivityAverageEnergy.denominator V)⁻¹ else 1 := by
        by_cases hi : i = left t ∨ i = right t
        · rcases hi with hil | hir
          · subst i
            simp [hm, inactiveMask_bit, supportPiece,
              ActivityAverageEnergy.constantMatrix_literal, hy.1, hx.1]
          · subst i
            simp [hm, inactiveMask_bit, supportPiece,
              ActivityAverageEnergy.constantMatrix_literal, hy.2.1, hx.2.1]
        · have hil : i ≠ left t := fun h => hi (Or.inl h)
          have hir : i ≠ right t := fun h => hi (Or.inr h)
          simp [hm, inactiveMask_bit, hi, hil, hir, supportPiece, zeroMatrix,
            identityKernel, hy.2.2 i hil hir, hx.2.2 i hil hir]
      unfold supportProduct
      simp_rw [hp]
      fin_cases t <;> simp [left, right, Fin.prod_univ_four, pow_two]
    · rw [if_neg (fun h => hx h.2)]
      unfold supportProduct
      by_cases hxl : x (left t) = 0
      · exact Finset.prod_eq_zero (Finset.mem_univ (left t)) (by
          simp [hm, inactiveMask_bit, supportPiece,
            ActivityAverageEnergy.constantMatrix_literal, hxl])
      · by_cases hxr : x (right t) = 0
        · exact Finset.prod_eq_zero (Finset.mem_univ (right t)) (by
            simp [hm, inactiveMask_bit, supportPiece,
              ActivityAverageEnergy.constantMatrix_literal, hxr])
        · have hex : ∃ i : Fin 4, i ≠ left t ∧ i ≠ right t ∧ x i ≠ 0 := by
            by_contra hn
            apply hx
            refine ⟨hxl, hxr, ?_⟩
            intro i hil hir
            by_contra hxi
            exact hn ⟨i, hil, hir, hxi⟩
          obtain ⟨i, hil, hir, hxi⟩ := hex
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by
            simp [hm, inactiveMask_bit, hil, hir, supportPiece, zeroMatrix, identityKernel, hxi])
  · rw [if_neg (fun h => hy h.1)]
    unfold supportProduct
    by_cases hyl : y (left t) = 0
    · exact Finset.prod_eq_zero (Finset.mem_univ (left t)) (by
        simp [hm, inactiveMask_bit, supportPiece,
          ActivityAverageEnergy.constantMatrix_literal, hyl])
    · by_cases hyr : y (right t) = 0
      · exact Finset.prod_eq_zero (Finset.mem_univ (right t)) (by
          simp [hm, inactiveMask_bit, supportPiece,
            ActivityAverageEnergy.constantMatrix_literal, hyr])
      · have hex : ∃ i : Fin 4, i ≠ left t ∧ i ≠ right t ∧ y i ≠ 0 := by
          by_contra hn
          apply hy
          refine ⟨hyl, hyr, ?_⟩
          intro i hil hir
          by_contra hyi
          exact hn ⟨i, hil, hir, hyi⟩
        obtain ⟨i, hil, hir, hyi⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by
          simp [hm, inactiveMask_bit, hil, hir, supportPiece, zeroMatrix, identityKernel, hyi])

/-- Symmetric idempotence gives the exact signed rank-one quadratic form. -/
theorem Q_energy (hn : 1 < Fintype.card V) (t : Fin 6) (f : (Fin 4 → V) → ℝ) :
    (∑ y, Q t f y ^ 2) = mass t f ^ 2 / ActivityAverageEnergy.denominator V ^ 2 := by
  have hi : kernelCompose
      (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)))
      (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t))) =
      supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)) := by
    rw [supportProduct_compose (0 : V) hn, if_pos rfl]
  rw [Q, ActivityAverageEnergy.symmetric_idempotent_energy _
    (supportProduct_symmetric (0 : V) _ _) hi]
  simp_rw [kernel_literal]
  have hp (x z : Fin 4 → V) :
      f x * f z * (if S t x ∧ S t z then (ActivityAverageEnergy.denominator V)⁻¹ ^ 2 else 0) =
      (ActivityAverageEnergy.denominator V)⁻¹ ^ 2 *
        ((if S t x then f x else 0) * (if S t z then f z else 0)) := by
    split_ifs <;> simp_all <;> ring
  simp_rw [hp]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, mass, div_eq_mul_inv, inv_pow, pow_two]
  ring

theorem Q_orthogonal (hn : 1 < Fintype.card V) (t u : Fin 6) (htu : t ≠ u)
    (f g : (Fin 4 → V) → ℝ) : (∑ y, Q t f y * Q u g y) = 0 := by
  apply supportProduct_mixed_orthogonal (0 : V) hn
  rintro ⟨hm, hi⟩
  apply htu
  apply patternLabel_injective
  exact Prod.ext (maskBits_injective hm) (maskBits_injective hi)

/-- Signed inclusion-exclusion. The two endpoint events intersect at zero. -/
theorem mass_eq_zero_masses (t : Fin 6) (f : (Fin 4 → V) → ℝ) :
    mass t f = zeroMass (inactiveMask t) f -
      zeroMass (OneActiveAverage.inactiveMask (left t)) f -
      zeroMass (OneActiveAverage.inactiveMask (right t)) f + f 0 := by
  have hp (x : Fin 4 → V) :
      (if S t x then f x else 0) =
      (if Z (inactiveMask t) x then f x else 0) -
      (if Z (OneActiveAverage.inactiveMask (left t)) x then f x else 0) -
      (if Z (OneActiveAverage.inactiveMask (right t)) x then f x else 0) +
      (if x = 0 then f 0 else 0) := by
    simp only [Z_inactive_iff, Z_single_iff]
    by_cases hz : ∀ i : Fin 4, i ≠ left t → i ≠ right t → x i = 0
    · by_cases hl : x (left t) = 0
      · by_cases hr : x (right t) = 0
        · have hx : x = 0 := by
            funext i
            by_cases hil : i = left t
            · subst i; exact hl
            · by_cases hir : i = right t
              · subst i; exact hr
              · exact hz i hil hir
          subst x
          simp [S]
        · -- The right-only event is the endpoint with left coordinate zero.
          have hzr : ∀ i : Fin 4, i ≠ right t → x i = 0 := by
            intro i hir
            by_cases hil : i = left t
            · subst i; exact hl
            · exact hz i hil hir
          have hnl : ¬ (∀ i : Fin 4, i ≠ left t → x i = 0) := by
            intro h
            exact hr (h (right t) (left_ne_right t).symm)
          have hns : ¬ S t x := fun h => h.1 hl
          have hx0 : x ≠ 0 := by
            intro h
            exact hr (congrFun h (right t))
          rw [if_neg hns, if_pos hz, if_neg hnl, if_pos hzr, if_neg hx0]
          ring
      · by_cases hr : x (right t) = 0
        · have hzl : ∀ i : Fin 4, i ≠ left t → x i = 0 := by
            intro i hil
            by_cases hir : i = right t
            · subst i; exact hr
            · exact hz i hil hir
          have hnr : ¬ (∀ i : Fin 4, i ≠ right t → x i = 0) := by
            intro h
            exact hl (h (left t) (left_ne_right t))
          have hns : ¬ S t x := fun h => h.2.1 hr
          have hx0 : x ≠ 0 := by
            intro h
            exact hl (congrFun h (left t))
          rw [if_neg hns, if_pos hz, if_pos hzl, if_neg hnr, if_neg hx0]
          ring
        · have hs : S t x := ⟨hl, hr, hz⟩
          have hnl : ¬ (∀ i : Fin 4, i ≠ left t → x i = 0) := by
            intro h
            exact hr (h (right t) (left_ne_right t).symm)
          have hnr : ¬ (∀ i : Fin 4, i ≠ right t → x i = 0) := by
            intro h
            exact hl (h (left t) (left_ne_right t))
          have hx0 : x ≠ 0 := by
            intro h
            exact hl (congrFun h (left t))
          rw [if_pos hs, if_pos hz, if_neg hnl, if_neg hnr, if_neg hx0]
          ring
    · have hns : ¬ S t x := fun h => hz h.2.2
      have hnl : ¬ (∀ i : Fin 4, i ≠ left t → x i = 0) := by
        intro h
        apply hz
        intro i hil _hir
        exact h i hil
      have hnr : ¬ (∀ i : Fin 4, i ≠ right t → x i = 0) := by
        intro h
        apply hz
        intro i _hil hir
        exact h i hir
      have hx0 : x ≠ 0 := by
        intro h
        apply hz
        intro i _hil _hir
        exact congrFun h i
      rw [if_neg hns, if_neg hz, if_neg hnl, if_neg hnr, if_neg hx0]
      ring
  calc
    _ = ∑ x : Fin 4 → V,
        ((if Z (inactiveMask t) x then f x else 0) -
        (if Z (OneActiveAverage.inactiveMask (left t)) x then f x else 0) -
        (if Z (OneActiveAverage.inactiveMask (right t)) x then f x else 0) +
        (if x = 0 then f 0 else 0)) := by
      unfold mass
      exact Finset.sum_congr rfl (fun x _ => hp x)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      change zeroMass (inactiveMask t) f -
        zeroMass (OneActiveAverage.inactiveMask (left t)) f -
        zeroMass (OneActiveAverage.inactiveMask (right t)) f +
        (∑ x : Fin 4 → V, if x = 0 then f 0 else 0) = _
      simp

end Generic

theorem component_one_eq_sum_Q (f : WordState → ℝ) :
    SupportProfile.component f 1 = fun y => ∑ t : Fin 6, Q t f y := by
  funext y
  rw [SupportProfile.component_eq_support_residual]
  change (∑ p : Label, if SelectedLabel p then raw p f y else 0) = _
  have hs : (∑ p : {p : Label // SelectedLabel p}, raw p.val f y) =
      ∑ p : Label, if SelectedLabel p then raw p f y else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs]
  exact (patternLabelEquiv.sum_comp (fun p => raw p.val f y)).symm

theorem component_one_energy (f : WordState → ℝ) :
    (∑ y, SupportProfile.component f 1 y ^ 2) =
      ∑ t : Fin 6, mass t f ^ 2 / ActivityAverageEnergy.denominator AES.Word ^ 2 := by
  rw [component_one_eq_sum_Q]
  rw [orthogonal_family_energy (fun t : Fin 6 => Q t f)
    (fun t u htu => Q_orthogonal SupportProfile.word_card_gt_one t u htu f f)]
  simp_rw [Q_energy SupportProfile.word_card_gt_one]

/-- Generic mask reindexing, with the physical forward diffusion explicit.
G is an affine-graph subtype for every mask; no size premise is needed here. -/
theorem boundary_zero_mass_eq_full_fiber (r : Fin 16) (f : WordState → ℝ) :
    zeroMass r (FirstHighSupportEvent.boundaryInput f) =
      ∑ g : WordMixTwoZeroFiber.G r, f g.val := by
  let e : WordState ≃ WordState := AESConcrete.WordCrossZero.wordMixAddEquiv.toEquiv
  have hsum : (∑ y : WordState, if Z r y then f (e.symm y) else 0) =
      ∑ y : WordState, if Z r (e y) then f y else 0 := by
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun y => if Z r y then f (e.symm y) else 0)).symm
  unfold zeroMass FirstHighSupportEvent.boundaryInput
  change (∑ y : WordState, if Z r y then f (e.symm y) else 0) = _
  rw [hsum]
  have hbits0 : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
  have hiff (y : WordState) :
      Z r (AESConcrete.WordCrossZero.wordMixAddEquiv y) ↔
      graphPrescribed WordMixTwoZeroFiber.L r 0 0 0 y := by
    constructor
    · intro hz
      constructor
      · exact hz
      · intro i hi
        exact Bool.noConfusion ((hbits0 i).symm.trans hi)
    · intro hg
      exact hg.1
  calc
    _ = ∑ y : WordState,
        if graphPrescribed WordMixTwoZeroFiber.L r 0 0 0 y then f y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      change (if Z r (AESConcrete.WordCrossZero.wordMixAddEquiv y) then f y else 0) = _
      simp only [hiff y]
    _ = _ := WordMixTwoZeroFiber.sum_zero_event r f

/-- Full signed inclusion-exclusion, before removing the common zero point. -/
theorem boundary_mass_eq_full_fibers_add_zero (f : WordState → ℝ) (t : Fin 6) :
    mass t (FirstHighSupportEvent.boundaryInput f) =
      (∑ g : WordMixTwoZeroFiber.G (inactiveMask t), f g.val) -
      (∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (left t)), f g.val) -
      (∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (right t)), f g.val) + f 0 := by
  have h := mass_eq_zero_masses t (FirstHighSupportEvent.boundaryInput f)
  rw [boundary_zero_mass_eq_full_fiber, boundary_zero_mass_eq_full_fiber,
    boundary_zero_mass_eq_full_fiber] at h
  have hz : FirstHighSupportEvent.boundaryInput f 0 = f 0 := by
    change f (AESConcrete.WordCrossZero.wordMixAddEquiv.symm 0) = f 0
    rw [map_zero]
  rw [hz] at h
  exact h

/-- The exact-support mass used downstream; the endpoint premise is explicit. -/
theorem boundary_mass_eq_full_fibers (f : WordState → ℝ) (hf : f 0 = 0) (t : Fin 6) :
    mass t (FirstHighSupportEvent.boundaryInput f) =
      (∑ g : WordMixTwoZeroFiber.G (inactiveMask t), f g.val) -
      (∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (left t)), f g.val) -
      (∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (right t)), f g.val) := by
  rw [boundary_mass_eq_full_fibers_add_zero, hf, _root_.add_zero]

end AES8.TwoActiveAverage
