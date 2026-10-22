import AES8.Reductions.Support.PaperSupportCoordinates
import AES8.Math.PaperKernelReindex

/-!
# Fixed support blocks as literal compressed operators

This joins the raw physical support tensors to the residual-coordinate kernel
obtained by compressing their normalized outside factors. The comparison uses
the projected input norm and applies to arbitrary signed joint functions.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportCompression
open AESMixing PaperSupportProjection PaperSupportCoordinates
open PaperTensorCompression PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def coordinateKernel (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n)
    (y : (Residual p → V) × (Outside p → V))
    (x : (Residual q → V) × (Outside q → V)) : ℝ :=
  K ((split p).symm y) ((split q).symm x)

def blockKernel (z : V) (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n) :=
  kernelCompose (residualKernel z p)
    (kernelCompose (compressed (coordinateKernel K p q) (outsideUnit z p) (outsideUnit z q))
      (residualKernel z q))

def inputVector (z : V) (q : Label n) (f : (Fin n → V) → ℝ) : (Residual q → V) → ℝ :=
  action (residualKernel z q) (collapse (outsideUnit z q) (fun x => f ((split q).symm x)))

theorem l2_reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    l2 (fun x => f (e x)) = l2 f := by
  apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  simp only [l2_sq]
  exact e.sum_comp (fun x => f x ^ 2)

theorem raw_norm (z : V) (hq : 1 < Fintype.card V) (p : Label n)
    (hp : Valid p) (f : (Fin n → V) → ℝ) : l2 (raw z p f) = l2 (inputVector z p f) := by
  rw [← l2_reindex (split p).symm (raw z p f), raw_action_split z hq p hp,
    embed_l2 _ (outside_unit_energy z hq p)]
  rfl

theorem coordinate_action (K : (Fin n → V) → (Fin n → V) → ℝ)
    (p q : Label n) (f : (Fin n → V) → ℝ) :
    (fun y => action K f ((split p).symm y)) =
      kernelAction (coordinateKernel K p q) (fun x => f ((split q).symm x)) := by
  funext y
  unfold action kernelAction coordinateKernel
  exact ((split q).symm.sum_comp (fun x => K ((split p).symm y) x * f x)).symm

/-- The raw block and compressed block are the same operation in the split
coordinates, including the residual projections on both sides. -/
theorem block_action (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n)
    (hp : Valid p) (hvalid : Valid q) (f : (Fin n → V) → ℝ) :
    (fun y => raw z p (action K (raw z q f)) ((split p).symm y)) =
      embed (outsideUnit z p) (action (blockKernel z K p q) (inputVector z q f)) := by
  have h := raw_action_split z hq p hp (action K (raw z q f))
  rw [coordinate_action K p q (raw z q f), raw_action_split z hq q hvalid] at h
  rw [compressed_action] at h
  have hg : action (residualKernel z q) (inputVector z q f) = inputVector z q f :=
    residual_idempotent z hq q _
  have haction : action (blockKernel z K p q) (inputVector z q f) =
      action (residualKernel z p)
        (kernelAction (compressed (coordinateKernel K p q) (outsideUnit z p) (outsideUnit z q))
          (inputVector z q f)) := by
    rw [blockKernel, kernelCompose_action, kernelCompose_action, hg]
    rfl
  rw [haction]
  exact h

/-- A cap on the literal compressed kernel gives the per-position hypothesis
needed by orthogonal support assembly, with no additional multiplicity. -/
theorem raw_block_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ) (p q : Label n)
    (hp : Valid p) (hvalid : Valid q) (c : ℝ)
    (hK : ‖kernelOperator (blockKernel z K p q)‖ ≤ c) (f : (Fin n → V) → ℝ) :
    l2 (raw z p (action K (raw z q f))) ≤ c * l2 (raw z q f) := by
  rw [← l2_reindex (split p).symm (raw z p (action K (raw z q f))),
    block_action z hq K p q hp hvalid, embed_l2 _ (outside_unit_energy z hq p),
    raw_norm z hq q hvalid, l2_eq_norm, l2_eq_norm]
  let g : EuclideanSpace ℝ (Residual q → V) := WithLp.toLp 2 (inputVector z q f)
  change ‖kernelOperator (blockKernel z K p q) g‖ ≤ c * ‖g‖
  exact ((kernelOperator (blockKernel z K p q)).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg g))

end AES8.PaperSupportCompression
