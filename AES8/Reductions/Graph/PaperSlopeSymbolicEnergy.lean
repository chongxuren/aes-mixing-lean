import AES8.Reductions.Graph.PaperSlopeSymbolicGraph
import AES8.Reductions.Graph.PaperSlopePhysicalEnergy

/-! The symbolic geometric certificate supplies both physical hypotheses of
the exact energy identity. The parameter and its degree remain arbitrary. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeSymbolicEnergy
open PaperSlopeSymbolicGraph PaperSlopeCoincidenceMatrix
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

theorem degree2_energy_scaledGram (a : F)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (hq : Fintype.card F = 256)
    (u : Interior → ℝ) :
    (256 : ℝ)^2 * (∑ x : Fin 4 → F,
      AESMixing.degreeComponent 0 2
        (PaperSlopePhysicalEnergy.signedDiffusion (diffusionEquiv a ha) u) x^2) =
      PaperSlopeClassGram.scaledGram u := by
  exact PaperSlopePhysicalEnergy.degree2_energy_scaledGram
    (diffusionEquiv a ha) (diffusionEquiv_isMDS a ha) hq
    (diffusionEquiv_sameSlopeClasses a ha) u

end AES8.PaperSlopeSymbolicEnergy
