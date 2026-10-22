/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.WordMixTwoZeroFiber
import AES8.Reductions.Support.ZeroOutsideProjection

/-! Any two distinct input coordinates label a complete two-output-zero
physical wordMix fiber. Only finite POSITION labels are enumerated.  Constructive only; no attacks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section

namespace AES8.WordMixTwoZeroPairInfo
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision
open AES8.WordMixTwoZeroFiber (G L)
open AES8.ZeroOutsideProjection (singleMask)

def pairMask (i j : Fin 4) : Fin 16 := maskUnion (singleMask i) (singleMask j)

theorem pairMask_left : ∀ i j : Fin 4, maskBit (pairMask i j) i = true := by decide
theorem pairMask_right : ∀ i j : Fin 4, maskBit (pairMask i j) j = true := by decide
theorem pairMask_size : ∀ i j : Fin 4, i ≠ j → maskSize (pairMask i j) = 2 := by decide
private theorem empty_disjoint : ∀ r : Fin 16, MaskDisjoint 0 r := by decide
private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide

def indices (i j : Fin 4) : Fin 2 → ObservedIndex 0 (pairMask i j) :=
  ![Sum.inr ⟨i, pairMask_left i j⟩, Sum.inr ⟨j, pairMask_right i j⟩]

theorem indices_bijective : ∀ i j : Fin 4, i ≠ j → Function.Bijective (indices i j) := by decide

def indexEquiv (i j : Fin 4) (hij : i ≠ j) : Fin 2 ≃ ObservedIndex 0 (pairMask i j) :=
  Equiv.ofBijective (indices i j) (indices_bijective i j hij)

def tupleEquiv {I : Type*} (e : Fin 2 ≃ I) (V : Type*) : (I → V) ≃ V × V where
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

def pairEquiv (r : Fin 16) (hr : maskSize r = 2) (i j : Fin 4) (hij : i ≠ j) :
    G r ≃ AES.Word × AES.Word :=
  (informationEquiv WordMixTwoZeroFiber.L wordMixAddEquiv_zeroMDS r 0 0 (pairMask i j) 0 0
    (disjoint_empty r) (empty_disjoint (pairMask i j))
    (by rw [hr, pairMask_size i j hij]; decide)).trans
      (tupleEquiv (indexEquiv i j hij) AES.Word)

@[simp] theorem pairEquiv_apply (r : Fin 16) (hr : maskSize r = 2)
    (i j : Fin 4) (hij : i ≠ j) (g : G r) : pairEquiv r hr i j hij g = (g.val i, g.val j) := rfl

theorem coords_bijective (r : Fin 16) (hr : maskSize r = 2)
    (i j : Fin 4) (hij : i ≠ j) :
    Function.Bijective (fun g : G r => (g.val i, g.val j)) :=
  (pairEquiv r hr i j hij).bijective

end AES8.WordMixTwoZeroPairInfo
