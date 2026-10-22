import AES8.Reductions.Graph.PaperSlopeLinearGraph

/-! Invertibility of the original diffusion follows from its output
information set. This leaf keeps the geometric MDS premise as the only input. -/
noncomputable section
namespace AES8.PaperSlopeGraphInvertible
open PaperSlopeLinearGraph
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem linear_bijective_of_graph_mds
    (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L).toAddSubgroup 4) :
    Function.Bijective L := by
  let outputs : Fin 4 ↪ Fin 8 := ⟨outputPos,outputPos_injective⟩
  have hb := PaperMDSGram.restriction_bijective_of_embedding
    (graphCode L).toAddSubgroup 4 hL outputs
  have hg := hb.comp (graphEquiv L).bijective
  change Function.Bijective
    (fun x : Fin 4 → F => fun i : Fin 4 => graphWord L x (outputPos i)) at hg
  simpa only [graphWord_output] using hg

def diffusionEquiv (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L).toAddSubgroup 4) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
  LinearEquiv.ofBijective L (linear_bijective_of_graph_mds L hL)

@[simp] theorem diffusionEquiv_toLinearMap
    (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L).toAddSubgroup 4) :
    (diffusionEquiv L hL).toLinearMap = L := rfl

end AES8.PaperSlopeGraphInvertible
