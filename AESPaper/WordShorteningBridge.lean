import AESPaper.WordMarkedResponse
import AESPaper.WordMarkedMoment

/-!
# Actual low-dimensional contracted word response

The supplied index equivalence partitions the marked physical positions into
two sets of source dimension and a remainder. Their actual information-set
properties follow from ZeroMDS in WordMarkedMoment; no response-energy or
independence hypothesis is introduced here. The size equation is retained
explicitly before simplifying the natural subtraction in the graph count.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordShorteningBridge
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros uniformCount)
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WordMarkedResponse (wordMarkedLeg boundaryContractedResponse)

/-- Actual output legs use R and actual input legs use its transpose. -/
def inputAdjoint (m : GraphPosition → Bool) (p : Marked m) : Bool :=
  Sum.elim (fun _ : Fin 4 => false) (fun _ : Fin 4 => true) p.val

/-- Match the actual vectorized residual legs to the checked word variants. -/
theorem wordMarkedLeg_eq_variant (m : GraphPosition → Bool) :
    wordMarkedLeg m = fun p => variant (inputAdjoint m p) false := by
  funext p y x
  rcases p with ⟨p, hp⟩
  cases p <;> rfl

section LowDimension
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Moment bound for the exact residual legs of the actual sandwich graph. -/
theorem boundary_normalized_low_energy_le
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse (wordMarkedLeg m)
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (WordMarkedMoment.tau ^ 2 / WordMarkedMoment.q) ^ Fintype.card I *
        WordMarkedMoment.delta ^ Fintype.card J := by
  rw [wordMarkedLeg_eq_variant]
  exact WordMarkedMoment.actual_normalized_low_energy_le m s
    (inputAdjoint m) (fun _ => false) idx hsize

/-- The dimension is identified by an exact size equation before eliminating
natural subtraction. No signed or negative dimension is silently truncated. -/
theorem boundary_normalization_square_of_size
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    (Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) /
      (65536 : ℝ) ^ uniformCount s) ^ 2 =
      WordMarkedMoment.q ^ Fintype.card I / WordMarkedMoment.q ^ uniformCount s := by
  have hd : 4 - (AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s)) =
      Fintype.card I := by omega
  have hn := WordMarkedResponse.boundary_normalization_square m s
  rw [hd] at hn
  exact hn

/-- Counting-energy bound for one actual activity contraction. The coefficient
includes every 1/65536 uniform leg and the actual shortened-source size. -/
theorem boundary_contracted_low_energy_le
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    (∑ y : Marked m → AES.Word, boundaryContractedResponse m s y ^ 2) ≤
      (WordMarkedMoment.q ^ Fintype.card I / WordMarkedMoment.q ^ uniformCount s) *
        ((WordMarkedMoment.tau ^ 2 / WordMarkedMoment.q) ^ Fintype.card I *
          WordMarkedMoment.delta ^ Fintype.card J) := by
  let n : ℝ := Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) /
    (65536 : ℝ) ^ uniformCount s
  have he : (∑ y : Marked m → AES.Word, boundaryContractedResponse m s y ^ 2) =
      n ^ 2 * ∑ y : Marked m → AES.Word,
        MixedCodeMoment.normalizedResponse (wordMarkedLeg m)
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2 := by
    simp_rw [WordMarkedResponse.boundaryContractedResponse_normalized, mul_pow]
    rw [← Finset.mul_sum]
  have hn : n ^ 2 =
      WordMarkedMoment.q ^ Fintype.card I / WordMarkedMoment.q ^ uniformCount s :=
    boundary_normalization_square_of_size m s hsize
  rw [he, ← hn]
  exact mul_le_mul_of_nonneg_left
    (boundary_normalized_low_energy_le m s idx hsize) (sq_nonneg n)

end LowDimension
end AESPaper.WordShorteningBridge
