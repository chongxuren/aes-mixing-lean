import AESPaper.RectangularFourier
import AESPaper.WordCodeFourier
import AESPaper.WordMarkedSplit
import AESPaper.WordDualNormalization

/-!
# Physical rectangular operator transport to the actual word annihilator
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordOperatorDuality
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros uniformCount sourceCoordinates)
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked join)
open AESPaper.RectangularFourier (EnergyBound fourierTransform)
open AESPaper.WordMarkedCode (markedCode)
attribute [local instance] Classical.propDecidable

/-- Reshape only along the proved physical output/input tuple equivalence. -/
def reshape (m : GraphPosition → Bool) (v : (Marked m → AES.Word) → ℝ) :
    (OutputMarked m → AES.Word) → (InputMarked m → AES.Word) → ℝ :=
  fun y x => v (join m y x)

theorem reshape_fourier (m : GraphPosition → Bool) (v : (Marked m → AES.Word) → ℝ) :
    reshape m (action (pairingFourier (WordFourierCore.wordPairing.product (Marked m))) v) =
      fourierTransform WordFourierCore.wordPairing (reshape m v) := by
  funext y x
  exact WordMarkedSplit.fourier_join m WordFourierCore.wordPairing v y x

/-- Exact operator-bound equivalence; this is not merely total vector energy. -/
theorem physical_fourier_bound_iff (m : GraphPosition → Bool)
    (v : (Marked m → AES.Word) → ℝ) (c : ℝ) :
    EnergyBound (reshape m
      (action (pairingFourier (WordFourierCore.wordPairing.product (Marked m))) v)) c ↔
      EnergyBound (reshape m v) c := by
  rw [reshape_fourier]
  exact RectangularFourier.energyBound_fourierTransform_iff
    WordFourierCore.wordPairing word_add_self (reshape m v) c

/-- Every bound on the actual normalized source is equivalent to the same
rectangular bound on its actual annihilator with Fourier flags toggled. -/
theorem actual_variant_bound_iff (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (adjoint fourier : Marked m → Bool) (c : ℝ) :
    EnergyBound (reshape m (MixedCodeMoment.normalizedResponse
      (fun p => variant (adjoint p) (fourier p))
      (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s))) c ↔
    EnergyBound (reshape m (MixedCodeMoment.normalizedResponse
      (fun p => variant (adjoint p) (!(fourier p)))
      (fun a : (WordFourierCore.wordPairing.product (Marked m)).annihilator
        (markedCode m s) => a.val))) c := by
  have h := physical_fourier_bound_iff m
    (MixedCodeMoment.normalizedResponse (fun p => variant (adjoint p) (fourier p))
      (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s)) c
  rw [WordCodeFourier.actual_variant_source_fourier_normalized m s hhigh] at h
  exact h.symm

theorem action_scale {X Y : Type*} [Fintype X] (K : Y → X → ℝ)
    (a : ℝ) (f : X → ℝ) :
    action K (fun x => a * f x) = fun y => a * action K f y := by
  funext y
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Raw dual enumeration, with the exact physical input transpose retained. -/
def dualRawResponse (m : GraphPosition → Bool) (s : Activity m → Bool)
    (y : Marked m → AES.Word) : ℝ :=
  ∑ a : (WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s),
    ∏ p : Marked m, variant (WordShorteningBridge.inputAdjoint m p) true (y p) (a.val p)

/-- The actual contracted matrix transforms to a raw dual sum with exactly
1/65536 per physical zero coordinate. No desired operator bound is assumed. -/
theorem boundary_fourier_raw (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) :
    action (pairingFourier (WordFourierCore.wordPairing.product (Marked m)))
      (WordMarkedResponse.boundaryContractedResponse m s) =
      fun y => (1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) +
        AES.maskSize (inputZeros m s))) * dualRawResponse m s y := by
  let a : ℝ := Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) /
    (65536 : ℝ)^uniformCount s
  have hh : 4 ≤ AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + Fintype.card (Marked m) := by omega
  have hv : WordMarkedResponse.boundaryContractedResponse m s =
      fun y => a * MixedCodeMoment.normalizedResponse
        (fun p => variant (WordShorteningBridge.inputAdjoint m p) false)
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y := by
    funext y
    rw [WordMarkedResponse.boundaryContractedResponse_normalized,
      WordShorteningBridge.wordMarkedLeg_eq_variant]
  rw [hv, action_scale,
    WordCodeFourier.actual_variant_source_fourier_normalized m s hh]
  funext y
  change a * (dualRawResponse m s y /
      Real.sqrt (Fintype.card ((WordFourierCore.wordPairing.product (Marked m)).annihilator
        (markedCode m s)))) = _
  rw [← mul_div_assoc, ← div_mul_eq_mul_div]
  rw [show a / Real.sqrt (Fintype.card
      ((WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s))) =
      1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s)) from
    WordDualNormalization.actual_dual_normalization m s d hd hle]

/-- The physical contraction and explicitly scaled raw annihilator response
have exactly the same arbitrary-signed-input operator-bound predicate. -/
theorem boundary_raw_dual_bound_iff (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) (c : ℝ) :
    EnergyBound (reshape m (WordMarkedResponse.boundaryContractedResponse m s)) c ↔
    EnergyBound (reshape m (fun y =>
      (1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) *
        dualRawResponse m s y)) c := by
  have h := physical_fourier_bound_iff m (WordMarkedResponse.boundaryContractedResponse m s) c
  rw [boundary_fourier_raw m s d hd hle] at h
  exact h.symm

end AESPaper.WordOperatorDuality
