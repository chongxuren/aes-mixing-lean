/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ActivityAverageEnergy
import AES8.Reductions.Fibers.WordMixThreeZeroFiber

/-!
# Rank-one nonzero activity averages for profile coordinate zero

Three zero blocks and one constant-NONZERO block yield one signed fiber
mass squared divided by q-1. Four orthogonal support patterns give the actual
component-zero energy. The boundary sum retains its nonzero active endpoint;
only a separately proved f(0)=0 may remove that endpoint restriction.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.OneActiveAverage
open AESMixing AESMixing.AES
open AES8.SupportProfile (Label raw)

def inactiveMask (t : Fin 4) : Fin 16 := maskComplement (ZeroOutsideProjection.singleMask t)
def patternLabel (t : Fin 4) : Label := (0, inactiveMask t)

theorem inactiveMask_bit : ∀ t i : Fin 4,
    maskBit (inactiveMask t) i = decide (i ≠ t) := by decide
theorem inactiveMask_size : ∀ t : Fin 4, maskSize (inactiveMask t) = 3 := by decide

def SelectedLabel (p : Label) : Prop := maskSize p.1 = 0 ∧ 4 - maskSize p.2 = 1
instance (p : Label) : Decidable (SelectedLabel p) := by unfold SelectedLabel; infer_instance
theorem patternLabel_selected : ∀ t : Fin 4, SelectedLabel (patternLabel t) := by decide
theorem patternLabel_injective : Function.Injective patternLabel := by decide
def patternLabelEquiv : Fin 4 ≃ {p : Label // SelectedLabel p} :=
  Equiv.ofBijective (fun t => ⟨patternLabel t, patternLabel_selected t⟩) (by decide)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def Q (t : Fin 4) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t))) f

def S (t : Fin 4) (x : Fin 4 → V) : Prop := x t ≠ 0 ∧ ∀ i : Fin 4, i ≠ t → x i = 0
instance (t : Fin 4) (x : Fin 4 → V) : Decidable (S t x) := by unfold S; infer_instance

def mass (t : Fin 4) (f : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ x, if S t x then f x else 0

theorem kernel_literal (t : Fin 4) (y x : Fin 4 → V) :
    supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)) y x =
      if S t y ∧ S t x then (ActivityAverageEnergy.denominator V)⁻¹ else 0 := by
  have hm : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
  by_cases hy : S t y
  · by_cases hx : S t x
    · rw [if_pos ⟨hy, hx⟩]
      unfold supportProduct
      calc
        _ = supportPiece (0 : V) (maskBit 0 t) (maskBit (inactiveMask t) t) (y t) (x t) := by
          apply Finset.prod_eq_single t
          · intro i _ hit
            simp [hm, inactiveMask_bit, hit, supportPiece, zeroMatrix, identityKernel,
              hy.2 i hit, hx.2 i hit]
          · simp
        _ = (ActivityAverageEnergy.denominator V)⁻¹ := by
          simp [hm, inactiveMask_bit, supportPiece,
            ActivityAverageEnergy.constantMatrix_literal, hy.1, hx.1]
    · rw [if_neg (fun h => hx h.2)]
      unfold S at hx
      push_neg at hx
      unfold supportProduct
      by_cases hxt : x t = 0
      · exact Finset.prod_eq_zero (Finset.mem_univ t) (by
          simp [hm, inactiveMask_bit, supportPiece, ActivityAverageEnergy.constantMatrix_literal, hxt])
      · obtain ⟨i, hit, hxi⟩ := hx hxt
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by
          simp [hm, inactiveMask_bit, supportPiece, zeroMatrix, identityKernel, hit, hxi])
  · rw [if_neg (fun h => hy h.1)]
    unfold S at hy
    push_neg at hy
    unfold supportProduct
    by_cases hyt : y t = 0
    · exact Finset.prod_eq_zero (Finset.mem_univ t) (by
        simp [hm, inactiveMask_bit, supportPiece, ActivityAverageEnergy.constantMatrix_literal, hyt])
    · obtain ⟨i, hit, hyi⟩ := hy hyt
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        simp [hm, inactiveMask_bit, supportPiece, zeroMatrix, identityKernel, hit, hyi])

/-- Symmetric-idempotent quadratic identity avoids counting support points. -/
theorem Q_energy (hn : 1 < Fintype.card V) (t : Fin 4) (f : (Fin 4 → V) → ℝ) :
    (∑ y, Q t f y ^ 2) = mass t f ^ 2 / ActivityAverageEnergy.denominator V := by
  have hi : kernelCompose
      (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)))
      (supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t))) =
      supportProduct (0 : V) (maskBit 0) (maskBit (inactiveMask t)) := by
    rw [supportProduct_compose (0 : V) hn, if_pos rfl]
  rw [Q, ActivityAverageEnergy.symmetric_idempotent_energy _
    (supportProduct_symmetric (0 : V) _ _) hi]
  simp_rw [kernel_literal]
  have hp (x z : Fin 4 → V) :
      f x * f z * (if S t x ∧ S t z then (ActivityAverageEnergy.denominator V)⁻¹ else 0) =
      (ActivityAverageEnergy.denominator V)⁻¹ *
        ((if S t x then f x else 0) * (if S t z then f z else 0)) := by
    split_ifs <;> simp_all <;> ring
  simp_rw [hp]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, mass, div_eq_mul_inv, pow_two]
  ring

theorem Q_orthogonal (hn : 1 < Fintype.card V) (t u : Fin 4) (htu : t ≠ u)
    (f g : (Fin 4 → V) → ℝ) : (∑ y, Q t f y * Q u g y) = 0 := by
  apply supportProduct_mixed_orthogonal (0 : V) hn
  rintro ⟨hm, hi⟩
  apply htu
  apply patternLabel_injective
  exact Prod.ext (maskBits_injective hm) (maskBits_injective hi)

end Generic

theorem component_zero_eq_sum_Q (f : WordState → ℝ) :
    SupportProfile.component f 0 = fun y => ∑ t : Fin 4, Q t f y := by
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

theorem component_zero_energy (f : WordState → ℝ) :
    (∑ y, SupportProfile.component f 0 y ^ 2) =
      ∑ t : Fin 4, mass t f ^ 2 / ActivityAverageEnergy.denominator AES.Word := by
  rw [component_zero_eq_sum_Q]
  rw [orthogonal_family_energy (fun t : Fin 4 => Q t f)
    (fun t u htu => Q_orthogonal SupportProfile.word_card_gt_one t u htu f f)]
  simp_rw [Q_energy SupportProfile.word_card_gt_one]

theorem boundary_mass_eq_full_fiber (f : WordState → ℝ) (hf : f 0 = 0) (t : Fin 4) :
    mass t (FirstHighSupportEvent.boundaryInput f) =
      ∑ g : WordMixThreeZeroFiber.G (inactiveMask t), f g.val := by
  let e : WordState ≃ WordState := AESConcrete.WordCrossZero.wordMixAddEquiv.toEquiv
  have hsum : (∑ y : WordState, if S t y then f (e.symm y) else 0) =
      ∑ y : WordState, if S t (e y) then f y else 0 := by
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun y => if S t y then f (e.symm y) else 0)).symm
  unfold mass FirstHighSupportEvent.boundaryInput
  change (∑ y : WordState, if S t y then f (e.symm y) else 0) = _
  rw [hsum]
  -- Keep the equivalence intact: broad simp unfolds its forward AES diffusion
  -- before the matching graph and support hypotheses can be used.
  have hbits0 : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
  have hp (y : WordState) :
      (if S t (AESConcrete.WordCrossZero.wordMixAddEquiv y) then f y else 0) =
      if graphPrescribed WordMixThreeZeroFiber.L (inactiveMask t) 0 0 0 y then f y else 0 := by
    by_cases hg : graphPrescribed WordMixThreeZeroFiber.L (inactiveMask t) 0 0 0 y
    · have hz : ∀ i : Fin 4, i ≠ t → AESConcrete.WordCrossZero.wordMixAddEquiv y i = 0 := by
        intro i hit
        exact hg.1 i (by
          rw [inactiveMask_bit]
          exact decide_eq_true hit)
      by_cases ht : AESConcrete.WordCrossZero.wordMixAddEquiv y t = 0
      · have hy : y = 0 := by
          apply AESConcrete.WordCrossZero.wordMixAddEquiv.injective
          have hL0 : AESConcrete.WordCrossZero.wordMixAddEquiv 0 = 0 := map_zero _
          rw [hL0]
          funext i
          by_cases hit : i = t
          · subst i; exact ht
          · exact hz i hit
        rw [hy, hf]
        simp only [ite_self]
      · rw [if_pos (show S t (AESConcrete.WordCrossZero.wordMixAddEquiv y) from ⟨ht, hz⟩),
          if_pos hg]
    · have hn : ¬ S t (AESConcrete.WordCrossZero.wordMixAddEquiv y) := by
        intro hs
        apply hg
        constructor
        · intro i hi
          have hit : i ≠ t := of_decide_eq_true ((inactiveMask_bit t i).symm.trans hi)
          exact hs.2 i hit
        · intro i hi
          exact Bool.noConfusion ((hbits0 i).symm.trans hi)
      rw [if_neg hn, if_neg hg]
  calc
    _ = ∑ y : WordState,
        if graphPrescribed WordMixThreeZeroFiber.L (inactiveMask t) 0 0 0 y then f y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      exact hp y
    _ = _ := WordMixThreeZeroFiber.sum_zero_event _ f

end AES8.OneActiveAverage
