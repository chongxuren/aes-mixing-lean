import AESConcrete.ActualDegreeThreeGram
import AESConcrete.ActivityEffectiveMetric

/-!
# Frame synthesis and actual degree-three energy

These identities pass between arbitrary frame coefficients, their actual
word vectors, and the compressed Gram quadratic. The empty/full rows are
removed only after their actual vanishing theorem. Every degree-zero input
has the normalized frame reconstruction below. No spectral bound is assumed
or asserted in this algebraic bridge. Constructive mathematics only.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.DegreeThreeFrameEnergy
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ActivityFrame
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActualDegreeThreeGram
open AESConcrete.ActivityEffectiveMetric (Interior qForm)

set_option maxRecDepth 100000

def frameSynthesis (u : Fin 16 → ℝ) (x : Fin 4 → Byte) : ℝ :=
  ∑ A : Fin 16, frameColumn (maskBit A) x * u A

def outputSynthesis (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ)
    (y : Fin 4 → Byte) : ℝ :=
  ∑ A : Fin 16, degreeComponent 0 3 (wordVector left right inverse A) y * u A

theorem action_synthesis {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (F : I → X → ℝ) (u : I → ℝ) (y : Y) :
    action K (fun x => ∑ i, F i x*u i) y = ∑ i, action K (F i) y*u i := by
  unfold action
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem outputSynthesis_eq (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    outputSynthesis left right inverse u =
      degreeComponent 0 3
        (action (residualMatrix (wordKernel left right inverse) 0) (frameSynthesis u)) := by
  rw [← degreeKernel_action, ← kernelCompose_action]
  funext y
  rw [show frameSynthesis u = fun x => ∑ A, frameColumn (maskBit A) x*u A from rfl,
    action_synthesis]
  unfold outputSynthesis
  apply Finset.sum_congr rfl
  intro A _
  rw [kernelCompose_action, degreeKernel_action]
  rfl

theorem outputSynthesis_energy (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    (4294967296 : ℝ) * ∑ y, (outputSynthesis left right inverse u y)^2 =
      qForm u (degreeThreeGram left right inverse) := by
  unfold outputSynthesis
  rw [gram_quadratic]
  simp only [qForm, degreeThreeGram, gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem degreeThreeGram_interior (left right : Orientation) (inverse : Bool) (u : Fin 16 → ℝ) :
    qForm u (degreeThreeGram left right inverse) =
      qForm (fun A : Interior => u A.val)
        (fun A B => degreeThreeGram left right inverse A.val B.val) := by
  have hz0 (B : Fin 16) : degreeThreeGram left right inverse 0 B = 0 :=
    degreeThreeGram_endpoint_row_zero left right inverse 0 B (Or.inl (by decide))
  have hz15 (B : Fin 16) : degreeThreeGram left right inverse 15 B = 0 :=
    degreeThreeGram_endpoint_row_zero left right inverse 15 B (Or.inr (by decide))
  have hz0r (A : Fin 16) : degreeThreeGram left right inverse A 0 = 0 := by
    rw [degreeThreeGram_symmetric, hz0]
  have hz15r (A : Fin 16) : degreeThreeGram left right inverse A 15 = 0 := by
    rw [degreeThreeGram_symmetric, hz15]
  unfold qForm
  rw [ActivityEffectiveMetric.sum_split]
  simp only [hz0, hz15, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [ActivityEffectiveMetric.sum_split]
  simp only [hz0r, hz15r, mul_zero, zero_add]

def normalizedCoefficients (f : (Fin 4 → Byte) → ℝ) (A : Fin 16) : ℝ :=
  (16 : ℝ)^maskSize A * activityCoefficient A f

theorem normalized_reconstruction (f : (Fin 4 → Byte) → ℝ) :
    degreeComponent 0 0 f = frameSynthesis (normalizedCoefficients f) := by
  rw [degree_zero_reconstruction]
  funext x
  unfold frameSynthesis normalizedCoefficients
  apply Finset.sum_congr rfl
  intro A _
  rw [frameColumn_activity]
  have hn : (16 : ℝ)^maskSize A ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem frameSynthesis_energy (u : Fin 16 → ℝ) :
    (∑ x, (frameSynthesis u x)^2) = ActivityEffectiveMetric.fullEnergy u :=
  ActivityEffectiveMetric.actual_frame_energy u

end AESConcrete.DegreeThreeFrameEnergy
