import AESConcrete.MarkedBlockVectorization

/-!
# Centering of every nonempty marked word block

A residual mark on either side annihilates the whole-word activity kernel.
The all-activity block is intentionally excluded and needs its own centered
trace. This is an exact kernel identity, not an energy bound. Constructive
mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedBlockCentering
open AESMixing AESConcrete.MarkedBlockVectorization
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordOrientationClosure (wordKernel)

section Generic
variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

theorem activity_pattern_zero (hV : 1 < Fintype.card V)
    (a : Fin 4 → Bool) (k : Fin 4) (hk : a k = true) :
    kernelCompose (activityMatrix (0 : Fin 4 → V)) (productProjection 0 a) = 0 := by
  funext y x
  have h := congrFun (congrFun
    (ActivityWordKernel.pattern_word_activity_zero hV a k hk) x) y
  change (∑ v : Fin 4 → V,
    productProjection 0 a x v * activityMatrix (0 : Fin 4 → V) v y) = 0 at h
  change (∑ v : Fin 4 → V,
    activityMatrix (0 : Fin 4 → V) y v * productProjection 0 a v x) = 0
  calc
    _ = ∑ v : Fin 4 → V,
        productProjection 0 a x v * activityMatrix (0 : Fin 4 → V) v y := by
      apply Finset.sum_congr rfl
      intro v _
      rw [activityMatrix_symmetric (0 : Fin 4 → V) y v,
        productProjection_symmetric (0 : V) a v x]
      ring
    _ = 0 := h

theorem centered_pattern_right (hV : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (a : Fin 4 → Bool) (k : Fin 4) (hk : a k = true) :
    kernelCompose (residualMatrix K 0) (productProjection 0 a) =
      kernelCompose K (productProjection 0 a) := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action]
  change action (K - activityMatrix (0 : Fin 4 → V))
    (action (productProjection 0 a) f) = _
  rw [kernel_action_sub,
    ← kernelCompose_action (activityMatrix (0 : Fin 4 → V)) (productProjection 0 a) f,
    activity_pattern_zero hV a k hk]
  simp only [zero_kernel_action, sub_zero]

theorem centered_marked_kernel (hV : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
      (kernelCompose (residualMatrix K 0) (productProjection 0 (fun i => m (Sum.inr i)))) =
      kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
        (kernelCompose K (productProjection 0 (fun i => m (Sum.inr i)))) := by
  obtain ⟨p,hp⟩ := hm
  cases p with
  | inl i =>
    apply kernel_action_ext
    intro f
    simpa only [kernelCompose_action] using
      ActivityWordKernel.centered_pattern_action hV K (fun j => m (Sum.inl j)) i hp
        (action (productProjection 0 (fun j => m (Sum.inr j))) f)
  | inr i => rw [centered_pattern_right hV K (fun j => m (Sum.inr j)) i hp]

end Generic

/-- Every nonempty physical marking is a block of the actual centered word. -/
theorem actual_centered_vectorizedBlock_matrix
    (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (hm : ∃ p, m p = true) (y a : Word) :
    vectorizedBlock (channel left) (channel right) (byteDiffusionHom inverse) m
      (Sum.elim y a) =
      kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
        (kernelCompose (residualMatrix (wordKernel left right inverse) 0)
          (productProjection 0 (fun i => m (Sum.inr i)))) y a := by
  rw [centered_marked_kernel (by norm_num [BinaryWord.card]) _ m hm]
  exact actual_vectorizedBlock_matrix left right inverse m y a

end AESConcrete.MarkedBlockCentering
