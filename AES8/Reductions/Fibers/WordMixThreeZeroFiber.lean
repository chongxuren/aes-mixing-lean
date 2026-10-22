/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberCollision
import AES8.Estimates.FirstHigh.FirstHighSupportEvent
import AESConcrete.WordCrossZero

/-!
# One information coordinate on a literal three-zero wordMix fiber

 Every named input coordinate labels
the whole fiber bijectively. Only four POSITION labels and their masks are
enumerated.
Constructive proof work only; no attacks or predecessor/manuscript edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixThreeZeroFiber
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision

abbrev L := wordMixAddEquiv.toAddMonoidHom
abbrev G (r : Fin 16) := AffineGraph L r 0 (0 : WordState) 0

def singleMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]
def zeroMask : Fin 4 → Fin 16 := ![7, 11, 13, 14]

theorem singleMask_mem : ∀ t i : Fin 4,
    maskBit (singleMask t) i = true ↔ i = t := by decide
theorem singleMask_size : ∀ t : Fin 4, maskSize (singleMask t) = 1 := by decide
theorem zeroMask_size : ∀ j : Fin 4, maskSize (zeroMask j) = 3 := by decide
private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide
private theorem empty_disjoint : ∀ r : Fin 16, MaskDisjoint 0 r := by decide

def selectedIndex (t : Fin 4) : ObservedIndex 0 (singleMask t) :=
  Sum.inr ⟨t, (singleMask_mem t t).mpr rfl⟩

private theorem observedIndex_eq : ∀ t : Fin 4,
    ∀ i : ObservedIndex 0 (singleMask t), i = selectedIndex t := by decide

def valueEquiv (t : Fin 4) : (ObservedIndex 0 (singleMask t) → AES.Word) ≃ AES.Word where
  toFun f := f (selectedIndex t)
  invFun x := fun _ => x
  left_inv f := by
    funext i
    rw [observedIndex_eq t i]
  right_inv x := rfl

/-- The forward map is literally g.val t, on every complete three-zero fiber. -/
def coordinateEquiv (r : Fin 16) (hr : maskSize r = 3) (t : Fin 4) : G r ≃ AES.Word :=
  (informationEquiv L wordMixAddEquiv_zeroMDS r 0 0 (singleMask t) 0 0
    (disjoint_empty r) (empty_disjoint (singleMask t))
    (by rw [hr, singleMask_size]; decide)).trans (valueEquiv t)

@[simp] theorem coordinateEquiv_apply (r : Fin 16) (hr : maskSize r = 3)
    (t : Fin 4) (g : G r) : coordinateEquiv r hr t g = g.val t := rfl

theorem coordinate_bijective (r : Fin 16) (hr : maskSize r = 3) (t : Fin 4) :
    Function.Bijective (fun g : G r => g.val t) :=
  (coordinateEquiv r hr t).bijective

theorem sum_coordinate (r : Fin 16) (hr : maskSize r = 3) (t : Fin 4)
    (f : AES.Word → ℝ) : (∑ g : G r, f (g.val t)) = ∑ x, f x :=
  (coordinateEquiv r hr t).sum_comp f

theorem sum_zero_event (r : Fin 16) (F : WordState → ℝ) :
    (∑ y : WordState, if graphPrescribed L r 0 0 0 y then F y else 0) =
      ∑ g : G r, F g.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

private theorem zeroMask_of_one_false : ∀ bits : Fin 4 → Bool,
    (Finset.univ.filter (fun i => bits i = false)).card = 1 →
      ∃ j : Fin 4, ∀ i : Fin 4, maskBit (zeroMask j) i = true → bits i = true := by decide

theorem activeCount_one_has_zeroMask (y : WordState) (hy : SupportProfile.activeCount y = 1) :
    ∃ j : Fin 4, ∀ i : Fin 4, maskBit (zeroMask j) i = true → y i = 0 := by
  have hf : Finset.univ.filter (fun i : Fin 4 => decide (y i = 0) = false) =
      Finset.univ.filter (fun i : Fin 4 => y i ≠ 0) := by
    ext i
    simp
  have hc : (Finset.univ.filter (fun i : Fin 4 => decide (y i = 0) = false)).card = 1 := by
    rw [hf]
    exact hy
  obtain ⟨j, hj⟩ := zeroMask_of_one_false (fun i => decide (y i = 0)) hc
  exact ⟨j, fun i hi => of_decide_eq_true (hj i hi)⟩

/-- This is a nonnegative energy cover; no signed sum or source law is changed. -/
theorem support_one_energy_le_zero_fibers (f : WordState → ℝ) :
    FirstHighSupportEvent.boundaryEventEnergy 1 f ≤
      ∑ j : Fin 4, ∑ g : G (zeroMask j), f g.val ^ 2 := by
  unfold FirstHighSupportEvent.boundaryEventEnergy
  have hp (y : WordState) :
      (if SupportProfile.activeCount (wordMixAddEquiv y) = 1 then f y ^ 2 else 0) ≤
        ∑ j : Fin 4, if graphPrescribed L (zeroMask j) 0 0 0 y then f y ^ 2 else 0 := by
    by_cases hy : SupportProfile.activeCount (wordMixAddEquiv y) = 1
    · rw [if_pos hy]
      obtain ⟨j, hj⟩ := activeCount_one_has_zeroMask (wordMixAddEquiv y) hy
      have hg : graphPrescribed L (zeroMask j) 0 0 0 y := by
        constructor
        · exact hj
        · intro i hi
          have hz : maskBit (0 : Fin 16) i = false := by fin_cases i <;> decide
          rw [hz] at hi
          contradiction
      calc
        _ = (if graphPrescribed L (zeroMask j) 0 0 0 y then f y ^ 2 else 0) := by rw [if_pos hg]
        _ ≤ ∑ t : Fin 4, if graphPrescribed L (zeroMask t) 0 0 0 y then f y ^ 2 else 0 :=
          Finset.single_le_sum (f := fun t : Fin 4 =>
            if graphPrescribed L (zeroMask t) 0 0 0 y then f y ^ 2 else 0)
            (fun t _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
            (Finset.mem_univ j)
    · rw [if_neg hy]
      exact Finset.sum_nonneg
        (fun t _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
  calc
    _ ≤ ∑ y : WordState, ∑ j : Fin 4,
        if graphPrescribed L (zeroMask j) 0 0 0 y then f y ^ 2 else 0 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = ∑ j : Fin 4, ∑ y : WordState,
        if graphPrescribed L (zeroMask j) 0 0 0 y then f y ^ 2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_zero_event (zeroMask j) (fun y => f y ^ 2)

end AES8.WordMixThreeZeroFiber
