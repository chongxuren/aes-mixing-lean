import AESConcrete.InverseFrameEnergy
import AESConcrete.ActualMarkedContractionEnergy
import AESConcrete.MarkedBlockCentering
import AESConcrete.HilbertSchmidtEnergy

/-!
# Actual centered marked blocks bounded by their survivor frame rows

The actual MDS code moments and endpoint vanishings instantiate the generic
inverse-frame row bound. Every residual mark is a physical input or output
position, and input residuals retain their adjoint orientation. The final
finite survivor row sum is explicit; its geometric counts and the sharper
signed degree-three aggregate remain separate. Constructive mathematics
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActualMarkedFrameBound
open AESMixing
open AESConcrete.ActivityFrame
open AESConcrete.MarkedBlockVectorization
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActualMarkedContractionEnergy (dimension zeta)
open AESConcrete.HilbertSchmidtEnergy (hs hs_sq)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def survives (m : GraphPosition → Bool) (s : Activity m → Bool) : Prop :=
  0 < dimension m s ∧ dimension m s < Fintype.card (Marked m)

abbrev Surviving (m : GraphPosition → Bool) := {s : Activity m → Bool // survives m s}

def survivorBound (m : GraphPosition → Bool) : ℝ :=
  ∑ s : Surviving m, zeta (Fintype.card (Marked m)) (dimension m s.val) *
    ∑ t : Surviving m, |frameInverse s.val t.val|

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
    exact ActualMarkedContractionEnergy.actual_contracted_energy_le
      left right inverse m s.val (dimension m s.val) (Fintype.card (Marked m))
      rfl hdim (Nat.le_of_lt s.property.2)

def centeredPattern (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) : AES.Word → AES.Word → ℝ :=
  kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
    (kernelCompose (residualMatrix (wordKernel left right inverse) 0)
      (productProjection 0 (fun i => m (Sum.inr i))))

theorem actual_centeredPattern_hs_square (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    hs (centeredPattern left right inverse m) ^ 2 =
      ∑ v : GraphPosition → BinaryWord 8,
        vectorizedBlock (channel left) (channel right) (byteDiffusionHom inverse) m v ^ 2 := by
  have h := markedBlock_hilbertSchmidt_square (channel_resources left)
    (channel_resources right) (actualDiffusionEquiv inverse) m
  simp only [actualDiffusionEquiv_hom, actualDiffusionEquiv_perm, markedBlock] at h
  rw [hs_sq]
  unfold centeredPattern
  rw [MarkedBlockCentering.centered_marked_kernel (by norm_num [BinaryWord.card]) _ m hm]
  simp only [wordKernel]
  exact h

/-- All substitutions, actual MDS moments, adjoints, normalizers and
vanishing endpoints have been discharged before the finite geometric sum. -/
theorem actual_centeredPattern_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m) ^ 2 ≤ survivorBound m := by
  rw [actual_centeredPattern_hs_square left right inverse m hm]
  exact actual_vectorizedBlock_energy_le left right inverse m hm

end AESConcrete.ActualMarkedFrameBound
