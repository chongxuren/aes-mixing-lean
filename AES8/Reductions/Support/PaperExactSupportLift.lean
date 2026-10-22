import AES8.Reductions.Support.PaperSupportOutside
import AES8.Reductions.Support.PaperFixedSupportBlockLift

/-!
# Exact-support lifting on the paper's literal projections

The sole analytic hypothesis bounds every residual-sandwiched zero/full frame
block at its physical positions. Outside expansion and orthogonal assembly
supply the binomial sum, normalization, and support multiplicities.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperExactSupportLift
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportCompression
open PaperSupportOutside PaperSupportBlockLift PaperActivityExpansion WordActivityFrame
open PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V]

def fixedBound (V : Type*) [Fintype V] (i t j u : ℕ) (G : ℕ → ℕ → ℝ) : ℝ :=
  Real.sqrt (eta V) ^ (t-i + (u-j)) * supportSum (t-i) (u-j) (xi V) G

theorem fixedBound_nonneg (i t j u : ℕ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ a b, 0 ≤ G a b) : 0 ≤ fixedBound V i t j u G := by
  unfold fixedBound supportSum
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg _ (hG a b)
  unfold xi
  positivity

/-- Every graph cap is quantified over the actual valid physical masks. -/
theorem grouped_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i t j u : Fin 5)
    (G : ℕ → ℕ → ℝ) (hG0 : ∀ a b, 0 ≤ G a b)
    (hG : ∀ (p : BlockLabel 4 i.val t.val) (q : BlockLabel 4 j.val u.val)
      (s : Finset (Active p.val)) (r : Finset (Active q.val)),
      ‖kernelOperator (frameKernel z K p.val q.val s r)‖ ≤ G s.card r.card)
    (f : (Fin 4 → V) → ℝ) :
    l2 (component z (action K (component z f j.val u.val)) i.val t.val) ≤
      (fixedBound V i.val t.val j.val u.val G *
        Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
          (Nat.choose 4 u.val * Nat.choose u.val j.val))) *
        l2 (component z f j.val u.val) := by
  apply four_word_norm_le z hq K f i t j u _ (fixedBound_nonneg _ _ _ _ G hG0)
  intro p q
  apply raw_block_norm_le z hq K p.val q.val p.property.1 q.property.1
  have h := block_norm_le z hq K p.val q.val G (hG p q)
  simpa only [active_card p.val p.property.1, active_card q.val q.property.1,
    p.property.2.1, p.property.2.2, q.property.2.1, q.property.2.2, fixedBound] using h

/-- A fixed input support leaves only the input residual-position count. -/
theorem fixed_input_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i t j : Fin 5) (mask : Fin 4 → Bool)
    (G : ℕ → ℕ → ℝ) (hG0 : ∀ a b, 0 ≤ G a b)
    (hG : ∀ (p : BlockLabel 4 i.val t.val)
      (q : PaperFixedSupportBlockLift.FixedLabel j.val mask)
      (s : Finset (Active p.val)) (r : Finset (Active (q.val,mask))),
      ‖kernelOperator (frameKernel z K p.val (q.val,mask) s r)‖ ≤ G s.card r.card)
    (f : (Fin 4 → V) → ℝ) :
    l2 (component z (action K (PaperFixedSupportBlockLift.fixedComponent z f j.val mask))
      i.val t.val) ≤
      (fixedBound V i.val t.val j.val (supportCount mask) G *
        Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
          Nat.choose (supportCount mask) j.val)) *
        l2 (PaperFixedSupportBlockLift.fixedComponent z f j.val mask) := by
  apply PaperFixedSupportBlockLift.four_word_norm_le z hq K f i t j mask _
    (fixedBound_nonneg _ _ _ _ G hG0)
  intro p q
  apply raw_block_norm_le z hq K p.val (q.val,mask) p.property.1 q.property.1
  have h := block_norm_le z hq K p.val (q.val,mask) G (hG p q)
  simpa only [active_card p.val p.property.1, active_card (q.val,mask) q.property.1,
    p.property.2.1, p.property.2.2, q.property.2, fixedBound] using h

end AES8.PaperExactSupportLift
