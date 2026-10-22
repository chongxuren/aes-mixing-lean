/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.FiberIncidence

/-!
# Reparametrizing normalized finite-fiber overlaps

Finite equivalences change information-coordinate labels without changing the
actual normalized overlap.  All identities are direct finite-sum identities:
there are no equal-fiber, positivity, kernel, or operator-bound hypotheses.
These helpers separate the coordinate transport from the collision estimates.

Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace AES8.PaperFiberTransport
open AESMixing AES8.FiberIncidence

section OneFiber
variable {C C' O : Type*} [Fintype C] [Fintype C'] [Fintype O] [DecidableEq O]

/-- A raw outside-fiber sum is invariant under a finite source equivalence. -/
theorem rawFiberSum_reparam (e : C' ≃ C) (outside : C → O) (g : C → ℝ) :
    rawFiberSum (outside ∘ e) (g ∘ e) = rawFiberSum outside g := by
  funext o
  unfold rawFiberSum
  simp only [Function.comp_apply]
  exact e.sum_comp (fun c => if outside c = o then g c else 0)

/-- Normalized pullback commutes with a finite source equivalence. -/
theorem normalizedLift_reparam (e : C' ≃ C) (outside : C → O) (m : ℕ)
    (f : O → ℝ) :
    normalizedLift (outside ∘ e) m f = (normalizedLift outside m f) ∘ e := rfl

/-- Normalized fiber summation is invariant under a finite source equivalence. -/
theorem normalizedAdjoint_reparam (e : C' ≃ C) (outside : C → O) (m : ℕ)
    (g : C → ℝ) :
    normalizedAdjoint (outside ∘ e) m (g ∘ e) = normalizedAdjoint outside m g := by
  funext o
  change rawFiberSum (outside ∘ e) (g ∘ e) o / Real.sqrt (m : ℝ) =
    rawFiberSum outside g o / Real.sqrt (m : ℝ)
  rw [rawFiberSum_reparam]

end OneFiber

section Kernel
variable {L L' R R' OL OR : Type*}
  [Fintype L] [Fintype L'] [Fintype R] [Fintype R']
  [Fintype OL] [Fintype OR] [DecidableEq OL] [DecidableEq OR]

/-- Both finite kernel indices can be changed by equivalences. -/
theorem action_reparam (eL : L' ≃ L) (eR : R' ≃ R)
    (K : L → R → ℝ) (g : R → ℝ) :
    action (fun y x => K (eL y) (eR x)) (g ∘ eR) = (action K g) ∘ eL := by
  funext y
  unfold action
  simp only [Function.comp_apply]
  exact eR.sum_comp (fun x => K (eL y) x * g x)

/-- The actual `J_L^* K J_R` is unchanged after choosing information-coordinate
equivalences on both codeword spaces.  The outside labels stay literal. -/
theorem normalizedOverlap_reparam (eL : L' ≃ L) (eR : R' ≃ R)
    (outsideL : L → OL) (outsideR : R → OR) (mL mR : ℕ)
    (K : L → R → ℝ) (f : OR → ℝ) :
    normalizedAdjoint (outsideL ∘ eL) mL
        (action (fun y x => K (eL y) (eR x))
          (normalizedLift (outsideR ∘ eR) mR f)) =
      normalizedAdjoint outsideL mL (action K (normalizedLift outsideR mR f)) := by
  rw [normalizedLift_reparam, action_reparam]
  exact normalizedAdjoint_reparam eL outsideL mL
    (action K (normalizedLift outsideR mR f))

end Kernel
end AES8.PaperFiberTransport
