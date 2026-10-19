import AESConcrete.ActualMarkedFrameBound

/-!
# Exact signed survivor expression for the actual centered marked block

The physical input adjoints and graph source are retained in each contraction.
Only zero contractions are removed. This identity exposes the signed frame
coefficients before any bound is applied; it does not assert the missing
three-mark overlap estimates. Constructive mathematics only; no attacks.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualSignedFrame
open AESMixing
open ByteOrientations (Orientation channel)
open MarkedBlockVectorization
open ShortenedLineResponse (byteDiffusionHom)
open ActualMarkedFrameBound (centeredPattern survives Surviving)
open ActivityFrame (frameInverse)
open HilbertSchmidtEnergy (hs)

attribute [local instance] Classical.propDecidable

def response (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) : (Marked m → BinaryWord 8) → ℝ :=
  contractedResponse m (markedLeg (channel left) (channel right) m)
    (graphCoordinate (byteDiffusionHom inverse)) s

def scaledPair (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s t : Activity m → Bool) : ℝ :=
  (4294967296 : ℝ) * ∑ y : Marked m → BinaryWord 8,
    response left right inverse m s y * response left right inverse m t y

theorem centered_energy_signed (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 =
      ∑ s : Surviving m, ∑ t : Surviving m,
        frameInverse s.val t.val * scaledPair left right inverse m s.val t.val := by
  rw [ActualMarkedFrameBound.actual_centeredPattern_hs_square left right inverse m hm]
  simp only [vectorizedBlock]
  rw [fullResponse_energy (by norm_num [BinaryWord.card])]
  have hz (s : Activity m → Bool) (h : ¬ survives m s) (y : Marked m → BinaryWord 8) :
      response left right inverse m s y = 0 :=
    ActualMarkedContractionEnergy.actual_contracted_zero_outside_surviving
      left right inverse m s hm h y
  change (4294967296 : ℝ) *
    (∑ s : Activity m → Bool, ∑ t : Activity m → Bool,
      frameInverse s t * InverseFrameEnergy.inner
        (response left right inverse m s) (response left right inverse m t)) = _
  rw [InverseFrameEnergy.quadratic_restrict frameInverse
    (response left right inverse m) (survives m) hz]
  simp only [Finset.mul_sum, scaledPair, InverseFrameEnergy.inner]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem centered_energy_le_signed_caps (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hm : ∃ p, m p = true)
    (cap : Surviving m → Surviving m → ℝ)
    (hcap : ∀ s t, frameInverse s.val t.val *
      scaledPair left right inverse m s.val t.val ≤ cap s t) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 ≤
      ∑ s : Surviving m, ∑ t : Surviving m, cap s t := by
  rw [centered_energy_signed left right inverse m hm]
  exact Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => hcap s t))

end AESConcrete.ActualSignedFrame
