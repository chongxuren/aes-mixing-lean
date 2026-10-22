import AES8.Reductions.Support.PaperPhysicalOutput

/-!
# Fixed output arithmetic for the paper's alternating profiles

The integer vectors are Table (parity-envelopes) of frozen paper f902bb94.
The common diagonal is the unchanged table (scales), retained as AES8.d.
The conservative historical output functional upper-bounds the literal current
quadrature functional. These comparisons prove outputs of the two fixed boxes;
they assert no invariant-map test and no actual AES profile bound.
-/

noncomputable section
namespace AES8.PaperOutputEnvelopes

/-- Even profile, in the exact fourteen-type order. -/
def evenEnvelope : Profile := ![342,45,39,39,133,74,81,39,37,163,97,37,316,179]
/-- Odd profile, in the same type order. -/
def oddEnvelope : Profile := ![76,130,30,30,528,64,49,44,48,51,56,29,73,90]

theorem even_nonneg (i : Fin 14) : 0 ≤ evenEnvelope i := by
  fin_cases i <;> norm_num [evenEnvelope]
theorem odd_nonneg (i : Fin 14) : 0 ≤ oddEnvelope i := by
  fin_cases i <;> norm_num [oddEnvelope]

theorem even_partial_lt : outputLinear (scale 1000 evenEnvelope) < 2 := by
  norm_num [outputLinear, physical, scale, d, evenEnvelope, vec14_apply]
theorem odd_partial_lt : outputLinear (scale 1000 oddEnvelope) < 2 := by
  norm_num [outputLinear, physical, scale, d, oddEnvelope, vec14_apply]

theorem even_all_active_lt : outputSquared (scale 1000 evenEnvelope) < (110 : ℝ) ^ 2 := by
  norm_num [outputSquared, physical, scale, d, evenEnvelope, vec14_apply]
theorem odd_all_active_lt : outputSquared (scale 1000 oddEnvelope) < (110 : ℝ) ^ 2 := by
  norm_num [outputSquared, physical, scale, d, oddEnvelope, vec14_apply]

theorem legacy_even_lt : AES8.Phi (scale 1000 evenEnvelope) < 112 := by
  have hs : Real.sqrt (outputSquared (scale 1000 evenEnvelope)) < 110 :=
    (Real.sqrt_lt (by unfold outputSquared; positivity) (by norm_num)).mpr even_all_active_lt
  unfold AES8.Phi
  linarith [even_partial_lt]

theorem legacy_odd_lt : AES8.Phi (scale 1000 oddEnvelope) < 112 := by
  have hs : Real.sqrt (outputSquared (scale 1000 oddEnvelope)) < 110 :=
    (Real.sqrt_lt (by unfold outputSquared; positivity) (by norm_num)).mpr odd_all_active_lt
  unfold AES8.Phi
  linarith [odd_partial_lt]

theorem even_output_lt : PaperPhysicalOutput.Phi (scale 1000 evenEnvelope) < 112 :=
  (PaperPhysicalOutput.Phi_le_legacy _ (fun i =>
    mul_nonneg (by norm_num) (even_nonneg i))).trans_lt legacy_even_lt

theorem odd_output_lt : PaperPhysicalOutput.Phi (scale 1000 oddEnvelope) < 112 :=
  (PaperPhysicalOutput.Phi_le_legacy _ (fun i =>
    mul_nonneg (by norm_num) (odd_nonneg i))).trans_lt legacy_odd_lt

/-- Arbitrary nonnegative profiles lying in either fixed box satisfy the
current output cap. The recurrence must separately prove box membership. -/
theorem output_lt_of_box (z : Profile) (hz : ∀ i, 0 ≤ z i)
    (hbox : z ≤ scale 1000 evenEnvelope ∨ z ≤ scale 1000 oddEnvelope) :
    PaperPhysicalOutput.Phi z < 112 := by
  apply (PaperPhysicalOutput.Phi_le_legacy z hz).trans_lt
  rcases hbox with h | h
  · exact (AES8.Phi_mono hz h).trans_lt legacy_even_lt
  · exact (AES8.Phi_mono hz h).trans_lt legacy_odd_lt

end AES8.PaperOutputEnvelopes
