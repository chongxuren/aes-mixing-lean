import AES8.Reductions.Graph.PaperMarkedContractionEnergy
import AESConcrete.ActualMarkedFrameBound

/-!
# Survivor-frame energy from the printed-route contractions

Module role: instantiate the original inverse-frame row inequality using the
owned contraction bound. The exact vanishing and centered-block identities
are reused, as are the survivor set and its scalar row sum. This leaf does not
perform the unsigned cube count or the signed three-mark sum. Source candidate
only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperMarkedFrameEnergy
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ActualMarkedContractionEnergy (dimension)
open AESConcrete.ActualMarkedFrameBound
  (survives survivorBound centeredPattern actual_centeredPattern_hs_square)
open AESConcrete.HilbertSchmidtEnergy (hs)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000

/-- This is an actual finite survivor sum. No code-energy or endpoint
vanishing premise remains in the concrete theorem. -/
theorem actual_vectorizedBlock_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    (4294967296 : ℝ) * (∑ v : GraphPosition → BinaryWord 8,
      vectorizedBlock (channel left) (channel right) (byteDiffusionHom inverse) m v ^ 2) ≤
      survivorBound m := by
  apply InverseFrameEnergy.fullResponse_restricted_le_rows
    (by norm_num [BinaryWord.card]) m (markedLeg (channel left) (channel right) m)
    (graphCoordinate (byteDiffusionHom inverse)) (4294967296 : ℝ) (by norm_num)
    (survives m)
  · intro s hs y
    exact ActualMarkedContractionEnergy.actual_contracted_zero_outside_surviving
      left right inverse m s hm hs y
  · intro s
    have hd : 0 < dimension m s.val := s.property.1
    have hdim : AES.maskSize (outputZeros m s.val) + AES.maskSize (inputZeros m s.val) +
        dimension m s.val = 4 := by
      dsimp only [dimension] at hd ⊢
      omega
    exact AES8.PaperMarkedContractionEnergy.actual_contracted_energy_le
      left right inverse m s.val (dimension m s.val) (Fintype.card (Marked m))
      rfl hdim (Nat.le_of_lt s.property.2)


/-- The printed-route code energies, exact adjoints, normalizers and
vanishing endpoints have been discharged before the finite geometric sum. -/
theorem actual_centeredPattern_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m) ^ 2 ≤ survivorBound m := by
  rw [actual_centeredPattern_hs_square left right inverse m hm]
  exact actual_vectorizedBlock_energy_le left right inverse m hm


#print axioms actual_vectorizedBlock_energy_le
#print axioms actual_centeredPattern_energy_le
end AES8.PaperMarkedFrameEnergy
