import AESPaper.WordMarkedDual
import AESPaper.WordMarkedUniform
import AESPaper.WordShorteningBridge
import AESConcrete.MarkedBlockScale

/-!
# Complete primal/dual per-choice word moment estimate

The final normalization scale is derived from the eight physical positions.
These are counting-energy bounds for one activity choice; weighted line and
plane operator improvements, activity arrays and full H Pi H Pi assembly remain
separate obligations. Input residuals keep their transpose.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.WordMarkedEnergy
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros uniformCount)
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WordMarkedMoment (q tau delta)
open AESPaper.WordMarkedResponse (wordMarkedLeg boundaryContractedResponse)
attribute [local instance] Classical.propDecidable

section Partition
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Both physical branches, preserving arbitrary per-leg Fourier/transpose flags. -/
theorem actual_normalized_energy_min
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool) (idx : CodePosition I J ≃ Marked m)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) (hI : Fintype.card I = min d (ell-d)) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse
        (fun p => variant (adjoint p) (fourier p))
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (tau ^ 2 / q) ^ min d (ell-d) * delta ^ (ell-2*min d (ell-d)) := by
  have hc := Fintype.card_congr idx
  simp only [CodePosition, Fintype.card_sum] at hc
  have hJ : Fintype.card J = ell-2*min d (ell-d) := by omega
  have hb :
      (∑ y : Marked m → AES.Word,
        MixedCodeMoment.normalizedResponse
          (fun p => variant (adjoint p) (fourier p))
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
        (tau ^ 2 / q) ^ Fintype.card I * delta ^ Fintype.card J := by
    by_cases hd : d ≤ ell-d
    · have hm : min d (ell-d) = d := min_eq_left hd
      exact WordMarkedMoment.actual_normalized_low_energy_le m s adjoint fourier idx (by omega)
    · have hm : min d (ell-d) = ell-d := min_eq_right (by omega)
      exact WordMarkedDual.actual_normalized_high_energy_le m s adjoint fourier idx (by omega)
  simpa only [hI, hJ] using hb

end Partition

/-- The partition exists by cardinality; MDS, not cardinality alone, proves
that its physical coordinate restrictions are information sets. -/
theorem actual_normalized_energy_bound
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse
        (fun p => variant (adjoint p) (fourier p))
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (tau ^ 2 / q) ^ min d (ell-d) * delta ^ (ell-2*min d (ell-d)) := by
  let dstar := min d (ell-d)
  let rest := ell-2*dstar
  have htwo : 2*dstar ≤ ell := by
    have hl := min_le_left d (ell-d)
    have hr := min_le_right d (ell-d)
    dsimp only [dstar]
    omega
  let idx : CodePosition (Fin dstar) (Fin rest) ≃ Marked m :=
    Fintype.equivOfCardEq (by
      simp only [CodePosition, Fintype.card_sum, Fintype.card_fin]
      rw [hlen]
      dsimp only [rest]
      omega)
  exact actual_normalized_energy_min m s adjoint fourier idx d ell hlen hdim hdle
    (by simp only [Fintype.card_fin, dstar])

/-- Specialization to actual graph legs, ordinary on outputs and transposed
on inputs, with no assumed information-set partition. -/
theorem boundary_normalized_energy_bound
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse (wordMarkedLeg m)
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (tau ^ 2 / q) ^ min d (ell-d) * delta ^ (ell-2*min d (ell-d)) := by
  rw [WordShorteningBridge.wordMarkedLeg_eq_variant]
  exact actual_normalized_energy_bound m s (WordShorteningBridge.inputAdjoint m)
    (fun _ => false) d ell hlen hdim hdle

/-- Word normalization: the eight positions give d+4=ell+t exactly. -/
theorem boundary_normalization_scale
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) ≤ 4) :
    q ^ 4 * (Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) /
      (65536 : ℝ) ^ uniformCount s) ^ 2 = q ^ Fintype.card (Marked m) := by
  rw [WordMarkedResponse.boundary_normalization_square]
  change q ^ 4 * (q ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))) /
    q ^ uniformCount s) = q ^ Fintype.card (Marked m)
  rw [← mul_div_assoc]
  apply (div_eq_iff (pow_ne_zero _ (by norm_num [q] : q ≠ 0))).mpr
  rw [← pow_add, ← pow_add]
  congr 1
  have h := MarkedBlockScale.dimension_balance m s hz
  omega

/-- Exact scale times the complete per-choice mixed-moment bound. -/
theorem boundary_contracted_energy_scaled
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    q ^ 4 * (∑ y : Marked m → AES.Word, boundaryContractedResponse m s y ^ 2) ≤
      q ^ ell * ((tau ^ 2 / q) ^ min d (ell-d) * delta ^ (ell-2*min d (ell-d))) := by
  let n : ℝ := Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) /
    (65536 : ℝ) ^ uniformCount s
  have he : (∑ y : Marked m → AES.Word, boundaryContractedResponse m s y ^ 2) =
      n ^ 2 * ∑ y : Marked m → AES.Word,
        MixedCodeMoment.normalizedResponse (wordMarkedLeg m)
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2 := by
    simp_rw [WordMarkedResponse.boundaryContractedResponse_normalized, mul_pow]
    rw [← Finset.mul_sum]
  have hn : q ^ 4 * n ^ 2 = q ^ ell := by
    rw [← hlen]
    exact boundary_normalization_scale m s (by omega)
  rw [he, ← mul_assoc, hn]
  exact mul_le_mul_of_nonneg_left
    (boundary_normalized_energy_bound m s d ell hlen hdim hdle)
    (pow_nonneg (by norm_num [q] : 0 ≤ q) ell)

/-- Source dimension with literal natural subtraction; high-zero cases are
handled by actual vanishing rather than by a fictitious positive dimension. -/
def dimension (m : GraphPosition → Bool) (s : Activity m → Bool) : ℕ :=
  4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))

/-- Both nonsurviving endpoints use actual cancellation, including the
uniform-image endpoint and more than four prescribed physical zeros. -/
theorem boundary_contracted_zero_outside_surviving
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hout : ¬ (0 < dimension m s ∧ dimension m s < Fintype.card (Marked m)))
    (y : Marked m → AES.Word) : boundaryContractedResponse m s y = 0 := by
  by_cases hz : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s)
  · exact WordMarkedResponse.boundaryContractedResponse_zero_of_high_zeros m s hm hz y
  · apply WordMarkedUniform.boundaryContractedResponse_zero_of_uniform_image m s hm _ y
    dsimp only [dimension] at hout
    omega

/-- Complete per-choice bound for a nonempty residual marking. Outside the
surviving range the exact response is zero. -/
theorem boundary_contracted_energy_piecewise
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true) :
    q ^ 4 * (∑ y : Marked m → AES.Word, boundaryContractedResponse m s y ^ 2) ≤
      if 0 < dimension m s ∧ dimension m s < Fintype.card (Marked m) then
        q ^ Fintype.card (Marked m) *
          ((tau ^ 2 / q) ^ min (dimension m s) (Fintype.card (Marked m)-dimension m s) *
            delta ^ (Fintype.card (Marked m)-
              2*min (dimension m s) (Fintype.card (Marked m)-dimension m s)))
      else 0 := by
  split_ifs with hs
  · apply boundary_contracted_energy_scaled m s (dimension m s)
      (Fintype.card (Marked m)) rfl _ (by omega)
    dsimp only [dimension] at hs ⊢
    omega
  · have hz := boundary_contracted_zero_outside_surviving m s hm hs
    simp only [hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero, le_refl]

end AESPaper.WordMarkedEnergy
