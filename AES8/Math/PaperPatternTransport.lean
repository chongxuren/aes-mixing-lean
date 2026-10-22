import AESConcrete.MarkedDegreeHilbertSchmidt
import AESPaper.ByteCoordinateTransport

/-!
# Exact fixed-pattern transport under a coordinate permutation

Module role: reusable counting-measure kernel and Hilbert--Schmidt transport.
The kernel and alphabet are arbitrary; no AES numerical estimate is used.
The legacy generic pattern-block definitions have a broadly packaged import,
but no numerical theorem from that package is invoked. Masks are transported
explicitly, with no binomial coefficient or additional normalization.
Constructive mathematics only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

noncomputable section
open scoped BigOperators

namespace AES8.PaperPatternTransport
open AESMixing
open AESConcrete.MarkedDegreeHilbertSchmidt (patternBlock)
open AESConcrete.HilbertSchmidtEnergy (hs hs_sq hs_nonneg)
open AESPaper.ByteCoordinateTransport (reindexEquiv)

/-- Simultaneous relabeling preserves the counting-coordinate composition exactly. -/
theorem compose_reindex {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A B : Y → Y → ℝ) :
    kernelCompose (reindexKernel e A) (reindexKernel e B) =
      reindexKernel e (kernelCompose A B) := by
  funext y x
  exact e.sum_comp (fun z => A (e y) z * B z (e x))

/-- Hilbert--Schmidt norm is invariant under a counting-coordinate bijection. -/
theorem hs_reindex {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (K : Y → Y → ℝ) : hs (reindexKernel e K) = hs K := by
  apply (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).mp
  rw [hs_sq, hs_sq]
  change (∑ y, ∑ x, K (e y) (e x) ^ 2) = _
  calc
    _ = ∑ y : X, ∑ x : Y, K (e y) x ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact e.sum_comp (fun x => K (e y) x ^ 2)
    _ = _ := e.sum_comp (fun y => ∑ x, K y x ^ 2)

section Patterns
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pulling back both kernel labels transports the flag by the inverse position map. -/
theorem projection_reindex (z : V) (p : Equiv.Perm (Fin 4)) (a : Fin 4 → Bool) :
    reindexKernel (reindexEquiv p : Equiv.Perm (Fin 4 → V)) (productProjection z a) =
      productProjection z (reindexEquiv p.symm a) := by
  funext y x
  simpa only [reindexKernel, productProjection, reindexEquiv,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
    Equiv.prod_comp p (fun i => degreePiece z (a (p.symm i)) (y i) (x i))

/-- A fixed-pattern block transports with both flags and the full joint kernel. -/
theorem pattern_reindex (z : V) (p : Equiv.Perm (Fin 4))
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (a b : Fin 4 → Bool) :
    patternBlock z (reindexKernel (reindexEquiv p) K) a b =
      reindexKernel (reindexEquiv p)
        (patternBlock z K (reindexEquiv p a) (reindexEquiv p b)) := by
  have hp (c : Fin 4 → Bool) :
      reindexKernel (reindexEquiv p : Equiv.Perm (Fin 4 → V))
        (productProjection z (reindexEquiv p c)) = productProjection z c := by
    rw [projection_reindex]
    congr 1
    funext i
    exact congrArg c (p.apply_symm_apply i)
  symm
  rw [patternBlock, ← compose_reindex, ← compose_reindex, hp, hp]
  rfl

/-- The exact fixed-pattern HS transport has coefficient one. -/
theorem pattern_hs_reindex (z : V) (p : Equiv.Perm (Fin 4))
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (a b : Fin 4 → Bool) :
    hs (patternBlock z (reindexKernel (reindexEquiv p) K) a b) =
      hs (patternBlock z K (reindexEquiv p a) (reindexEquiv p b)) := by
  rw [pattern_reindex, hs_reindex]

end Patterns
end AES8.PaperPatternTransport
