/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberCollision
import AESConcrete.WordCrossZero

/-!
# Two information input coordinates on a literal two-zero wordMix fiber

The prescribed output mask has exactly two positions. No input coordinate is
fixed. The literal input coordinates 0,1 label the complete physical forward
wordMix fiber by the existing one-copy MDS information theorem.
This geometry supplies no moment, profile bound or AES endpoint.
Constructive work only;
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace AES8.WordMixTwoZeroFiber
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision

abbrev L := wordMixAddEquiv.toAddMonoidHom

/-- Exactly the literal prescribed-zero output graph; no input is fixed. -/
abbrev G (r : Fin 16) := AffineGraph L r 0 (0 : WordState) 0

private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide
private theorem empty_disjoint : ∀ r : Fin 16, MaskDisjoint 0 r := by decide

private def indices01 : Fin 2 → ObservedIndex 0 3 :=
  ![Sum.inr ⟨0, by decide⟩, Sum.inr ⟨1, by decide⟩]

private theorem indices01_bijective : Function.Bijective indices01 := by decide

private def indexEquiv01 : Fin 2 ≃ ObservedIndex 0 3 :=
  Equiv.ofBijective indices01 indices01_bijective

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

def equiv01 (r : Fin 16) (hr : maskSize r = 2) : G r ≃ AES.Word × AES.Word :=
  (informationEquiv L wordMixAddEquiv_zeroMDS r 0 0 3 0 0
    (disjoint_empty r) (empty_disjoint 3) (by rw [hr]; decide)).trans
      (tupleLabelEquiv indexEquiv01 AES.Word)

@[simp] theorem equiv01_apply (r : Fin 16) (hr : maskSize r = 2) (g : G r) :
    equiv01 r hr g = (g.val 0, g.val 1) := rfl

theorem coords01_bijective (r : Fin 16) (hr : maskSize r = 2) :
    Function.Bijective (fun g : G r => (g.val 0, g.val 1)) :=
  (equiv01 r hr).bijective

/-- Reindex the actual two-zero event, without a sign hypothesis on F. -/
theorem sum_zero_event (r : Fin 16) (F : WordState → ℝ) :
    (∑ y : WordState, if graphPrescribed L r 0 0 0 y then F y else 0) =
      ∑ g : G r, F g.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end AES8.WordMixTwoZeroFiber
