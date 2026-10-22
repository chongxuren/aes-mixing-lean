/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.WordMixTwoZeroFiber
import AES8.Reductions.Support.ZeroOutsideProjection

/-!
# One information coordinate after two output zeros and one input zero

The domain remains the literal physical forward wordMix fiber. A third,
input-side, coordinate is prescribed to zero. Any other input coordinate
is then an information label, by the existing one-copy MDS theorem.
No larger paired-code MDS claim or probability premise occurs.

Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.WordMixTwoZeroPinnedFiber
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision
open AES8.WordMixTwoZeroFiber (G)

private abbrev diffusion := AES8.WordMixTwoZeroFiber.L
open AES8.ZeroOutsideProjection (singleMask singleMask_bit_iff)

abbrev H (r : Fin 16) (j : Fin 4) := {g : G r // g.val j = 0}

private theorem singleMask_size : ∀ j : Fin 4, maskSize (singleMask j) = 1 := by decide
private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide
private theorem emptyMask_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide

private theorem single_disjoint (j i : Fin 4) (hij : i ≠ j) :
    MaskDisjoint (singleMask j) (singleMask i) := by
  intro k hj hi
  have hkj : k = j := (singleMask_bit_iff j k).mp hj
  have hki : k = i := (singleMask_bit_iff i k).mp hi
  exact hij (hki.symm.trans hkj)

def graphEquiv (r : Fin 16) (j : Fin 4) :
    H r j ≃ AffineGraph diffusion r (singleMask j) (0 : WordState) 0 where
  toFun g := ⟨g.val.val, by
    constructor
    · exact g.val.property.1
    · intro i hi
      have hij : i = j := (singleMask_bit_iff j i).mp hi
      subst i
      exact g.property⟩
  invFun g := ⟨⟨g.val, by
    constructor
    · exact g.property.1
    · intro i hi
      rw [emptyMask_bit] at hi
      exact Bool.noConfusion hi⟩,
    g.property.2 j ((singleMask_bit_iff j j).mpr rfl)⟩
  left_inv g := Subtype.ext (Subtype.ext rfl)
  right_inv g := Subtype.ext rfl

private def soleIndex (i : Fin 4) : ObservedIndex 0 (singleMask i) :=
  Sum.inr ⟨i, (singleMask_bit_iff i i).mpr rfl⟩

private theorem index_eq_sole (i : Fin 4) (v : ObservedIndex 0 (singleMask i)) :
    v = soleIndex i := by
  cases v with
  | inl v =>
    have h := v.property
    rw [emptyMask_bit] at h
    exact Bool.noConfusion h
  | inr v =>
    congr 1
    exact Subtype.ext ((singleMask_bit_iff i v.val).mp v.property)

private def evaluationEquiv (i : Fin 4) :
    (ObservedIndex 0 (singleMask i) → AES.Word) ≃ AES.Word where
  toFun f := f (soleIndex i)
  invFun x := fun _ => x
  left_inv f := by
    funext v
    rw [index_eq_sole i v]
  right_inv x := rfl

def coordinateEquiv (r : Fin 16) (hr : maskSize r = 2) (j i : Fin 4) (hij : i ≠ j) :
    H r j ≃ AES.Word :=
  (graphEquiv r j).trans
    ((informationEquiv diffusion wordMixAddEquiv_zeroMDS
      r (singleMask j) 0 (singleMask i) 0 0 (disjoint_empty r)
      (single_disjoint j i hij)
      (by rw [hr, singleMask_size, singleMask_size]; decide)).trans (evaluationEquiv i))

@[simp] theorem coordinateEquiv_apply (r : Fin 16) (hr : maskSize r = 2)
    (j i : Fin 4) (hij : i ≠ j) (g : H r j) :
    coordinateEquiv r hr j i hij g = g.val.val i := rfl

theorem coordinate_bijective (r : Fin 16) (hr : maskSize r = 2)
    (j i : Fin 4) (hij : i ≠ j) :
    Function.Bijective (fun g : H r j => g.val.val i) :=
  (coordinateEquiv r hr j i hij).bijective

theorem sum_input_zero (r : Fin 16) (j : Fin 4) (F : G r → ℝ) :
    (∑ g : G r, if g.val j = 0 then F g else 0) = ∑ h : H r j, F h.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem sum_coordinate (r : Fin 16) (hr : maskSize r = 2)
    (j i : Fin 4) (hij : i ≠ j) (F : AES.Word → ℝ) :
    (∑ h : H r j, F (h.val.val i)) = ∑ x : AES.Word, F x :=
  Equiv.sum_comp (coordinateEquiv r hr j i hij) F

end AES8.WordMixTwoZeroPinnedFiber
