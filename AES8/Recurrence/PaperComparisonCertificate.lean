import AES8.Recurrence.PaperComparisonChecks
import AES8.Recurrence.PaperComparisonReal

/-! Public rational and real certificate interface for the four frozen image tests.
The physical block estimates and the real-power/monomial correspondence remain
separate from this finite rational certificate. -/
namespace AES8.PaperComparison

 theorem margin_lt (i : Fin 14) : ratioPermille i / 1000 < (99:ℚ)/100 := by
  have h := ratioPermille_lt i
  linarith

 theorem ratio_le_one (i : Fin 14) : ratioPermille i / 1000 ≤ 1 := by
  have h := margin_lt i
  linarith

 theorem startup_even_bound (i : Fin 14) : startup2 i ≤ evenEnvelope i := by
  exact (startup_even_test i).trans (by
    simpa using mul_le_mul_of_nonneg_right (ratio_le_one i) (envelopes_pos i).1.le)
 theorem startup_odd_bound (i : Fin 14) : startup3 i ≤ oddEnvelope i := by
  exact (startup_odd_test i).trans (by
    simpa using mul_le_mul_of_nonneg_right (ratio_le_one i) (envelopes_pos i).2.le)
 theorem invariant_even_bound (i : Fin 14) : invariantEven i ≤ evenEnvelope i := by
  exact (invariant_even_test i).trans (by
    simpa using mul_le_mul_of_nonneg_right (ratio_le_one i) (envelopes_pos i).1.le)
 theorem invariant_odd_bound (i : Fin 14) : invariantOdd i ≤ oddEnvelope i := by
  exact (invariant_odd_test i).trans (by
    simpa using mul_le_mul_of_nonneg_right (ratio_le_one i) (envelopes_pos i).2.le)

 theorem startup1_real : realProfile startup1 =
    realMv realStep (realProfile startup0) + realProfile firstReturn := by
  ext i
  simp [startup1, realProfile, realMv, mv, realStep]
 theorem startup2_real : realProfile startup2 =
    realMv realStep (realProfile startup1) + realMv realReturn (realProfile startup0) := by
  ext i
  simp [startup2, realProfile, realMv, mv, realStep, realReturn]
 theorem startup3_real : realProfile startup3 =
    realMv realStep (realProfile startup2) + realMv realReturn (realProfile startup1) := by
  ext i
  simp [startup3, realProfile, realMv, mv, realStep, realReturn]

 theorem startup_even_bound_real :
    realProfile startup2 ≤ PaperOutputEnvelopes.evenEnvelope := by
  rw [← real_even_eq]
  intro i
  change (startup2 i : ℝ) ≤ (evenEnvelope i : ℝ)
  exact_mod_cast startup_even_bound i
 theorem startup_odd_bound_real :
    realProfile startup3 ≤ PaperOutputEnvelopes.oddEnvelope := by
  rw [← real_odd_eq]
  intro i
  change (startup3 i : ℝ) ≤ (oddEnvelope i : ℝ)
  exact_mod_cast startup_odd_bound i

 theorem invariant_even_bound_real :
    (fun i => realMv realStep PaperOutputEnvelopes.oddEnvelope i +
      realMv realReturn PaperOutputEnvelopes.evenEnvelope i) ≤
        PaperOutputEnvelopes.evenEnvelope := by
  intro i
  have h : (invariantEven i : ℝ) ≤ (evenEnvelope i : ℝ) := by
    exact_mod_cast invariant_even_bound i
  rw [← real_even_eq, ← real_odd_eq]
  simpa [invariantEven, realProfile, realMv, mv, realStep, realReturn] using h

 theorem invariant_odd_bound_real :
    (fun i => realMv realStep PaperOutputEnvelopes.evenEnvelope i +
      realMv realReturn PaperOutputEnvelopes.oddEnvelope i) ≤
        PaperOutputEnvelopes.oddEnvelope := by
  intro i
  have h : (invariantOdd i : ℝ) ≤ (oddEnvelope i : ℝ) := by
    exact_mod_cast invariant_odd_bound i
  rw [← real_even_eq, ← real_odd_eq]
  simpa [invariantOdd, realProfile, realMv, mv, realStep, realReturn] using h

end AES8.PaperComparison
