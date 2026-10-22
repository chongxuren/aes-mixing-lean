/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberCollision
import AESConcrete.WordCrossZero

/-!
# Three-coordinate information sets on an actual wordMix zero fiber

Fix one output coordinate of the physical AES word diffusion to zero. Each
of the input triples `(y0,y2,y3)` and `(y1,y2,y3)` labels that entire fiber
bijectively. The bijections use the existing word-alphabet MDS information
theorem and have literal coordinate projections as their forward maps.
Exact sum reindexing is supplied for arbitrary signed functions.

No byte-alphabet substitution, numerical moment estimate, attack, active
source edit, or full first-high/return estimate is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace AES8.WordMixEventFiber
open AESMixing AESMixing.AES
open AESConcrete.WordCrossZero
open AES8.MDSFiberCollision

/-- The actual physical output-zero event, with the full input retained. -/
abbrev G (c : Fin 4) := {y : WordState // wordMixAddEquiv y c = 0}

abbrev Triple := AES.Word × (AES.Word × AES.Word)

private def singleMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]

private theorem singleMask_mem : ∀ c i : Fin 4,
    maskBit (singleMask c) i = true ↔ i = c := by decide

private theorem singleMask_size : ∀ c : Fin 4,
    maskSize (singleMask c) = 1 := by decide

private theorem emptyMask_mem : ∀ i : Fin 4,
    maskBit (0 : Fin 16) i = false := by decide

private theorem disjoint_empty : ∀ r : Fin 16, MaskDisjoint r 0 := by decide
private theorem empty_disjoint : ∀ r : Fin 16, MaskDisjoint 0 r := by decide

private abbrev L := wordMixAddEquiv.toAddMonoidHom

/-- The literal event is exactly the prescribed-coordinate affine graph.
The only prescribed output is c; no input coordinate is fixed here. -/
private def graphEquiv (c : Fin 4) :
    G c ≃ AffineGraph L (singleMask c) 0 (0 : WordState) 0 where
  toFun y := ⟨y.val, by
    constructor
    · intro i hi
      have hic : i = c := (singleMask_mem c i).mp hi
      subst i
      exact y.property
    · intro i hi
      rw [emptyMask_mem] at hi
      contradiction⟩
  invFun y := ⟨y.val, y.property.1 c ((singleMask_mem c c).mpr rfl)⟩
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

-- These maps enumerate three POSITION labels only. Their finite proofs
-- never enumerate words, states, diffusion values, or source functions.
private def indices023 : Fin 3 → ObservedIndex 0 13 :=
  ![Sum.inr ⟨0, by decide⟩, Sum.inr ⟨2, by decide⟩, Sum.inr ⟨3, by decide⟩]

private def indices123 : Fin 3 → ObservedIndex 0 14 :=
  ![Sum.inr ⟨1, by decide⟩, Sum.inr ⟨2, by decide⟩, Sum.inr ⟨3, by decide⟩]

private theorem indices023_bijective : Function.Bijective indices023 := by decide
private theorem indices123_bijective : Function.Bijective indices123 := by decide

private def indexEquiv023 : Fin 3 ≃ ObservedIndex 0 13 :=
  Equiv.ofBijective indices023 indices023_bijective

private def indexEquiv123 : Fin 3 ≃ ObservedIndex 0 14 :=
  Equiv.ofBijective indices123 indices123_bijective

/-- Evaluation at the three named indices, packaged in the requested tuple. -/
private def tupleLabelEquiv {I : Type*} (e : Fin 3 ≃ I) (V : Type*) :
    (I → V) ≃ (V × (V × V)) where
  toFun f := (f (e 0), (f (e 1), f (e 2)))
  invFun p i := ![p.1, p.2.1, p.2.2] (e.symm i)
  left_inv f := by
    funext i
    change ![f (e 0), f (e 1), f (e 2)] (e.symm i) = f i
    have he (j : Fin 3) : ![f (e 0), f (e 1), f (e 2)] j = f (e j) := by
      fin_cases j <;> rfl
    rw [he, e.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨a, b, d⟩
    change
      (![a, b, d] (e.symm (e 0)),
        (![a, b, d] (e.symm (e 1)), ![a, b, d] (e.symm (e 2)))) = (a, (b, d))
    simp only [e.symm_apply_apply]
    rfl

/-- Input coordinates 0,2,3 identify every actual output-zero fiber point. -/
def equiv023 (c : Fin 4) : G c ≃ Triple :=
  (graphEquiv c).trans
    ((informationEquiv L wordMixAddEquiv_zeroMDS
      (singleMask c) 0 0 13 0 0 (disjoint_empty (singleMask c))
      (empty_disjoint 13) (by rw [singleMask_size]; decide)).trans
        (tupleLabelEquiv indexEquiv023 AES.Word))

/-- Input coordinates 1,2,3 give the alternative information labeling. -/
def equiv123 (c : Fin 4) : G c ≃ Triple :=
  (graphEquiv c).trans
    ((informationEquiv L wordMixAddEquiv_zeroMDS
      (singleMask c) 0 0 14 0 0 (disjoint_empty (singleMask c))
      (empty_disjoint 14) (by rw [singleMask_size]; decide)).trans
        (tupleLabelEquiv indexEquiv123 AES.Word))

@[simp] theorem equiv023_apply (c : Fin 4) (y : G c) :
    equiv023 c y = (y.val 0, (y.val 2, y.val 3)) := rfl

@[simp] theorem equiv123_apply (c : Fin 4) (y : G c) :
    equiv123 c y = (y.val 1, (y.val 2, y.val 3)) := rfl

theorem coords023_bijective (c : Fin 4) :
    Function.Bijective (fun y : G c => (y.val 0, (y.val 2, y.val 3))) :=
  (equiv023 c).bijective

theorem coords123_bijective (c : Fin 4) :
    Function.Bijective (fun y : G c => (y.val 1, (y.val 2, y.val 3))) :=
  (equiv123 c).bijective

theorem equiv023_symm_coordinates (c : Fin 4) (p : Triple) :
    ((equiv023 c).symm p).val 0 = p.1 ∧
      ((equiv023 c).symm p).val 2 = p.2.1 ∧
        ((equiv023 c).symm p).val 3 = p.2.2 := by
  have h := (equiv023 c).apply_symm_apply p
  exact ⟨congrArg Prod.fst h, congrArg (fun t : Triple => t.2.1) h,
    congrArg (fun t : Triple => t.2.2) h⟩

theorem equiv123_symm_coordinates (c : Fin 4) (p : Triple) :
    ((equiv123 c).symm p).val 1 = p.1 ∧
      ((equiv123 c).symm p).val 2 = p.2.1 ∧
        ((equiv123 c).symm p).val 3 = p.2.2 := by
  have h := (equiv123 c).apply_symm_apply p
  exact ⟨congrArg Prod.fst h, congrArg (fun t : Triple => t.2.1) h,
    congrArg (fun t : Triple => t.2.2) h⟩

/-- Exact conditional-sum restriction, with no sign hypothesis on F. -/
theorem sum_zero_event (c : Fin 4) (F : WordState → ℝ) :
    (∑ y : WordState, if wordMixAddEquiv y c = 0 then F y else 0) =
      ∑ g : G c, F g.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem sum_fiber023 (c : Fin 4) (F : WordState → ℝ) :
    (∑ g : G c, F g.val) =
      ∑ p : Triple, F ((equiv023 c).symm p).val :=
  ((equiv023 c).symm.sum_comp (fun g : G c => F g.val)).symm

theorem sum_fiber123 (c : Fin 4) (F : WordState → ℝ) :
    (∑ g : G c, F g.val) =
      ∑ p : Triple, F ((equiv123 c).symm p).val :=
  ((equiv123 c).symm.sum_comp (fun g : G c => F g.val)).symm

theorem sum_zero_event_eq023 (c : Fin 4) (F : WordState → ℝ) :
    (∑ y : WordState, if wordMixAddEquiv y c = 0 then F y else 0) =
      ∑ p : Triple, F ((equiv023 c).symm p).val := by
  rw [sum_zero_event, sum_fiber023]

theorem sum_zero_event_eq123 (c : Fin 4) (F : WordState → ℝ) :
    (∑ y : WordState, if wordMixAddEquiv y c = 0 then F y else 0) =
      ∑ p : Triple, F ((equiv123 c).symm p).val := by
  rw [sum_zero_event, sum_fiber123]

end AES8.WordMixEventFiber
