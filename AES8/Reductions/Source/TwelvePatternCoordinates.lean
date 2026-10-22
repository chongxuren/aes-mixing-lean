/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.WordMixTwoZeroFiber

/-!
# Literal residual information coordinates for the four component-twelve patterns

Each position order puts the constant coordinate first, two residual
information coordinates next, and the bounded residual entry last. The
information bijections on a literal two-zero wordMix fiber are constructed
from the existing one-copy MDS theorem. All finite decisions enumerate only
four position labels and four-bit masks, never words or states.

-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section

namespace AES8.TwelvePatternCoordinates
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision

def positionOrder : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 2, 3], ![2, 0, 1, 3], ![3, 0, 1, 2]]

theorem positionOrder_bijective : ∀ j : Fin 4, Function.Bijective (positionOrder j) := by decide

def order (j : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (positionOrder j) (positionOrder_bijective j)

theorem order_zero : ∀ j : Fin 4, order j 0 = j := by decide

theorem order_ne_zero : ∀ j i : Fin 4, i ≠ 0 → order j i ≠ j := by decide

private def inputMask : Fin 4 → Fin 16 := ![6, 5, 3, 3]

private theorem inputMask_size : ∀ j : Fin 4, maskSize (inputMask j) = 2 := by decide
private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide
private theorem empty_disjoint : ∀ r : Fin 16, MaskDisjoint 0 r := by decide

private def indices (j : Fin 4) : Fin 2 → ObservedIndex 0 (inputMask j) :=
  ![Sum.inr ⟨order j 1, by fin_cases j <;> decide⟩,
    Sum.inr ⟨order j 2, by fin_cases j <;> decide⟩]

private theorem indices_bijective : ∀ j : Fin 4, Function.Bijective (indices j) := by decide

private def indexEquiv (j : Fin 4) : Fin 2 ≃ ObservedIndex 0 (inputMask j) :=
  Equiv.ofBijective (indices j) (indices_bijective j)

private def tupleLabelEquiv {I : Type*} (e : Fin 2 ≃ I) (V : Type*) :
    (I → V) ≃ V × V where
  toFun f := (f (e 0), f (e 1))
  invFun p i := ![p.1, p.2] (e.symm i)
  left_inv f := by
    funext i
    change ![f (e 0), f (e 1)] (e.symm i) = f i
    have he (j : Fin 2) : ![f (e 0), f (e 1)] j = f (e j) := by
      fin_cases j <;> rfl
    rw [he, e.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨a, b⟩
    change (![a, b] (e.symm (e 0)), ![a, b] (e.symm (e 1))) = (a, b)
    simp only [e.symm_apply_apply]
    rfl

def informationEquiv (r : Fin 16) (hr : maskSize r = 2) (j : Fin 4) :
    WordMixTwoZeroFiber.G r ≃ AES.Word × AES.Word :=
  (MDSFiberCollision.informationEquiv WordMixTwoZeroFiber.L wordMixAddEquiv_zeroMDS
    r 0 0 (inputMask j) 0 0 (disjoint_empty r) (empty_disjoint (inputMask j))
    (by rw [hr, inputMask_size]; decide)).trans (tupleLabelEquiv (indexEquiv j) AES.Word)

@[simp] theorem informationEquiv_apply (r : Fin 16) (hr : maskSize r = 2)
    (j : Fin 4) (g : WordMixTwoZeroFiber.G r) :
    informationEquiv r hr j g = (g.val (order j 1), g.val (order j 2)) := rfl

theorem residual_coords_bijective (r : Fin 16) (hr : maskSize r = 2) (j : Fin 4) :
    Function.Bijective (fun g : WordMixTwoZeroFiber.G r =>
      (g.val (order j 1), g.val (order j 2))) :=
  (informationEquiv r hr j).bijective

end AES8.TwelvePatternCoordinates
