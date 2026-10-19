import AESPaper.OneSourceLaw
import AESPaper.Profile

/-!
# Residual-position projections retain the actual common source

Projection acts on each output coordinate of a tensor response. This does
not split the source weights into independent factors. The exact energy
identity below is the link from the actual four-round law to its signed
common-source Gram sums, before any numerical majorization.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.OneSourceProjection
open AESMixing AESConcrete
open AESConcrete.WordColumnGram

section Generic
variable {I V X : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V] [Fintype X]

/-- Output projection changes the channel factors, keeping the source label. -/
theorem project_tensorResponse (z : V) (b : I → Bool)
    (T : I → V → V → ℝ) (coords : X → I → V) (mu : X → ℝ) :
    action (productProjection z b) (tensorResponse T coords mu) =
      tensorResponse (fun i => kernelCompose (degreePiece z (b i)) (T i)) coords mu := by
  have hc (y : I → V) (x : X) :
      kernelCompose (productProjection z b) (tensorColumn T coords) y x =
        tensorColumn (fun i => kernelCompose (degreePiece z (b i)) (T i)) coords y x := by
    unfold kernelCompose productProjection tensorColumn
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => degreePiece z (b i) (y i) v *
      T i v (coords x i))).symm
  change action (productProjection z b) (action (tensorColumn T coords) mu) = _
  rw [← kernelCompose_action]
  funext y
  simp only [action, hc, tensorResponse]

/-- General pointed channels have the same activity/residual decomposition. -/
theorem pointed_degree_left (D : V → V → ℝ) (z : V)
    (h : PointedBistochastic D z) (b : Bool) :
    kernelCompose (degreePiece z b) D =
      if b then residualMatrix D z else activityMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  cases b
  · change action (activityMatrix z) (action D f) = action (activityMatrix z) f
    rw [activityMatrix_action, h.average_action, activityMatrix_action]
  · change action (residualProjection z) (action D f) = action (D-activityMatrix z) f
    rw [residualProjection_action, wordResidual, h.average_action,
      kernel_action_sub, activityMatrix_action]

end Generic

/-- The actual output factor selected by one residual-position bit. -/
def piece (b : Bool) : AES.Word → AES.Word → ℝ :=
  if b then residualMatrix AES.wordSuperboxKernel 0 else activityMatrix 0

theorem projected_law (b : Fin 4 → Bool) (k : Fin 4) (a : AES.Word) :
    action (productProjection (0 : AES.Word) b) (OneSourceLaw.law k a) =
      tensorResponse (fun i => piece (b i))
        (fun x c => BoundarySourceCoordinates.outputEquiv k c x) (StartingWord.wordLaw a) := by
  rw [OneSourceLaw.law, project_tensorResponse]
  simp only [pointed_degree_left AES.wordSuperboxKernel 0 AES.word_superbox_pointed, piece]

/-- Exact pattern energy; source weights remain inside the double sum. -/
theorem projected_law_energy (b : Fin 4 → Bool) (k : Fin 4) (a : AES.Word) :
    (∑ y, action (productProjection (0 : AES.Word) b) (OneSourceLaw.law k a) y ^ 2) =
      ∑ x, ∑ z, StartingWord.wordLaw a x * StartingWord.wordLaw a z *
        ∏ i, gram (piece (b i)) (BoundarySourceCoordinates.outputEquiv k i x)
          (BoundarySourceCoordinates.outputEquiv k i z) := by
  rw [projected_law, tensorResponse_energy]

/-- Orthogonality groups precisely the genuine residual-position patterns. -/
theorem degree_law_energy (j : Fin 5) (k : Fin 4) (a : AES.Word) :
    (∑ y, degreeComponent (0 : AES.Word) j (OneSourceLaw.law k a) y ^ 2) =
      ∑ b : Fin 4 → Bool, if degreeIndex b = j then
        (∑ x, ∑ z, StartingWord.wordLaw a x * StartingWord.wordLaw a z *
          ∏ i, gram (piece (b i)) (BoundarySourceCoordinates.outputEquiv k i x)
            (BoundarySourceCoordinates.outputEquiv k i z)) else 0 := by
  rw [degreeComponent_energy (0 : AES.Word) ProfileSpace.word_card_gt_one]
  simp only [projected_law_energy]

end AESPaper.OneSourceProjection
