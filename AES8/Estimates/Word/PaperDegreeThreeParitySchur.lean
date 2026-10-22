import AES8.Estimates.Word.PaperDegreeThreePrintedMetric
import AES8.Estimates.Word.PaperDegreeThreeParityResponse

/-! The actual parity slack margins and the final two-block positivity argument.
The proof uses the completed-square/Cauchy--Schwarz form of the Schur criterion;
it assumes no desired positivity or spectral comparison. Every actual physical
orientation is instantiated from its already proved Gram entry intervals. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParitySchur
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric AESConcrete.ActivityGramDominance
open PaperDegreeThreeParityCounts PaperDegreeThreeEndpointMetric
open PaperDegreeThreeParityResponse
set_option autoImplicit false
set_option maxRecDepth 100000

def slack (G : Fin 16 → Fin 16 → ℝ) (A B : Fin 16) : ℝ :=
  comparisonLambda*effectiveMetric A B-G A B

theorem slack_symmetric (G : Fin 16 → Fin 16 → ℝ) (hsym : ∀ A B, G A B = G B A)
    (A B : Fin 16) : slack G A B = slack G B A := by
  unfold slack
  rw [DampedDegreeThree.effectiveMetric_symmetric, hsym]

theorem slack_quadratic (G : Fin 16 → Fin 16 → ℝ) (u : Fin 16 → ℝ) :
    qForm u (slack G) = comparisonLambda*qForm u effectiveMetric - qForm u G := by
  unfold qForm
  simp only [slack, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem odd_slack_strict (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (u : Fin 16 → ℝ)
    (hu : ∀ A, ¬ IsOdd A → u A = 0) (hne : u ≠ 0) :
    6*(∑ A : Fin 16, (u A)^2) < qForm u (slack G) := by
  have hm := PaperDegreeThreePrintedMetric.odd_metric_strict u hu hne
  have hg := supported_quadratic_le IsOdd G hsym ((1024/255 : ℝ)*(9/8))
    (by norm_num) (fun A => ((PaperDegreeThreePrintedDeductions.odd_rows_printed G hG A).trans
      (mul_lt_mul_of_pos_left PaperDegreeThreePrintedDeductions.printed_brackets.2.2.1 (by norm_num))).le) u hu
  have hl : 0 < comparisonLambda := by norm_num [comparisonLambda]
  have hmul := mul_lt_mul_of_pos_left hm hl
  have hc : (6 : ℝ) < comparisonLambda*(31/32) - (1024/255)*(9/8) := by
    norm_num [comparisonLambda]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  rw [slack_quadratic]
  nlinarith

theorem even_slack_strict (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (u : Fin 16 → ℝ)
    (hu : ∀ A, ¬ IsEven A → u A = 0) (hne : u ≠ 0) :
    (3/2 : ℝ)*(∑ A : Fin 16, (u A)^2) < qForm u (slack G) := by
  have hm := PaperDegreeThreePrintedMetric.even_metric_strict u hu hne
  have hg := supported_quadratic_le IsEven G hsym ((1024/255 : ℝ)*(229/100))
    (by norm_num) (fun A => ((PaperDegreeThreePrintedDeductions.even_rows_printed G hG A).trans
      (mul_lt_mul_of_pos_left PaperDegreeThreePrintedDeductions.printed_brackets.2.2.2 (by norm_num))).le) u hu
  have hl : 0 < comparisonLambda := by norm_num [comparisonLambda]
  have hmul := mul_lt_mul_of_pos_left hm hl
  have hc : (3/2 : ℝ) < comparisonLambda*(63/64) - (1024/255)*(229/100) := by
    norm_num [comparisonLambda]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  rw [slack_quadratic]
  nlinarith

def mixed (G : Fin 16 → Fin 16 → ℝ) (u v : Fin 16 → ℝ) : ℝ :=
  ∑ A : Odd, ∑ B : Even, u A.val*v B.val*slack G A.val B.val

theorem mixed_sq_le (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (u v : Fin 16 → ℝ) :
    (mixed G u v)^2 ≤ (25/3 : ℝ)*(∑ A : Odd, (u A.val)^2)*
      (∑ B : Even, (v B.val)^2) := by
  let C := crossKernel G
  let f : Even → ℝ := fun B => v B.val
  have hp := cross_row_arithmetic.2.2.2.1
  have hpcap := cross_row_arithmetic.2.2.2.2
  have he := NormalizedSchur.signed_schur_energy C (fun A B => |C A B|)
    (3*crossPairCap) (4*crossPairCap) (by positivity) (fun _ _ => abs_nonneg _)
    (fun _ _ => le_rfl) (cross_rows G hG) (cross_columns G hG hsym) f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun A : Odd => u A.val) (action C f)
  have hid : (∑ A : Odd, u A.val*action C f A) = mixed G u v := by
    unfold action mixed
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    dsimp [C, f, crossKernel, residualEntry, slack]
    ring
  rw [hid] at hcs
  have hu : 0 ≤ ∑ A : Odd, (u A.val)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : 0 ≤ ∑ B : Even, (v B.val)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left he hu
  have hcap : (3*crossPairCap)*(4*crossPairCap) ≤ (25/3 : ℝ) := by nlinarith
  have hf := mul_le_mul_of_nonneg_right hcap (mul_nonneg hu hv)
  nlinarith

/-- Completed-square form of the final Schur test. The constants correspond
exactly to diagonal margins 6,3/2 and squared cross norm at most 25/3. -/
theorem two_block_positive (x y a b c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hdiag : 6*x+(3/2)*y < a+b) (hcross : c^2 ≤ (25/3)*x*y) :
    0 < a+b+2*c := by
  by_contra h
  have hsum : 0 ≤ 6*x+(3/2)*y := by positivity
  have hc : 6*x+(3/2)*y < -2*c := by linarith
  have hc0 : 0 ≤ -2*c := by linarith
  have hs := (sq_lt_sq₀ hsum hc0).mpr hc
  nlinarith [sq_nonneg (6*x-(3/2)*y), mul_nonneg hx hy]

def oddPart (u : Fin 16 → ℝ) (A : Fin 16) : ℝ := if IsOdd A then u A else 0
def evenPart (u : Fin 16 → ℝ) (A : Fin 16) : ℝ := if IsEven A then u A else 0

theorem oddPart_supported (u : Fin 16 → ℝ) : ∀ A, ¬ IsOdd A → oddPart u A = 0 := by
  intro A hA; exact if_neg hA

theorem evenPart_supported (u : Fin 16 → ℝ) : ∀ A, ¬ IsEven A → evenPart u A = 0 := by
  intro A hA; exact if_neg hA

theorem oddPart_energy (u : Fin 16 → ℝ) :
    (∑ A : Fin 16, (oddPart u A)^2) = ∑ A : Odd, (u A.val)^2 := by
  rw [sum_subtype IsOdd (fun A => (u A)^2)]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : IsOdd A <;> simp [oddPart, hA]

theorem evenPart_energy (u : Fin 16 → ℝ) :
    (∑ A : Fin 16, (evenPart u A)^2) = ∑ A : Even, (u A.val)^2 := by
  rw [sum_subtype IsEven (fun A => (u A)^2)]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : IsEven A <;> simp [evenPart, hA]

theorem parts_sum (u : Fin 16 → ℝ) (h0 : u 0 = 0) (h15 : u 15 = 0) :
    u = fun A => oddPart u A + evenPart u A := by
  funext A
  fin_cases A <;> norm_num [oddPart, evenPart, IsOdd, IsEven,
    mask_size_numeric, bitCount, h0, h15]
  all_goals exact h15

def bilinear (u v : Fin 16 → ℝ) (K : Fin 16 → Fin 16 → ℝ) : ℝ :=
  ∑ A : Fin 16, ∑ B : Fin 16, u A*v B*K A B

theorem bilinear_swap (u v : Fin 16 → ℝ) (K : Fin 16 → Fin 16 → ℝ)
    (hsym : ∀ A B, K A B = K B A) : bilinear v u K = bilinear u v K := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [hsym B A]
  ring

theorem qForm_add (u v : Fin 16 → ℝ) (K : Fin 16 → Fin 16 → ℝ)
    (hsym : ∀ A B, K A B = K B A) :
    qForm (fun A => u A+v A) K = qForm u K+qForm v K+2*bilinear u v K := by
  have he (A B : Fin 16) : (u A+v A)*(u B+v B)*K A B =
      u A*u B*K A B + v A*v B*K A B + u A*v B*K A B + v A*u B*K A B := by ring
  unfold qForm
  simp_rw [he, Finset.sum_add_distrib]
  change qForm u K + qForm v K + bilinear u v K + bilinear v u K = _
  rw [bilinear_swap u v K hsym]
  unfold qForm
  ring

theorem bilinear_parts (G : Fin 16 → Fin 16 → ℝ) (u : Fin 16 → ℝ) :
    bilinear (oddPart u) (evenPart u) (slack G) = mixed G u u := by
  have hin (A : Fin 16) :
      (∑ B : Fin 16, oddPart u A*evenPart u B*slack G A B) =
      if IsOdd A then ∑ B : Even, u A*u B.val*slack G A B.val else 0 := by
    by_cases hA : IsOdd A
    · rw [if_pos hA, sum_subtype IsEven (fun B => u A*u B*slack G A B)]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : IsEven B <;> simp [oddPart, evenPart, hA, hB]
    · simp [oddPart, hA]
  unfold bilinear mixed
  simp_rw [hin]
  rw [sum_subtype IsOdd (fun A => ∑ B : Even, u A*u B.val*slack G A B.val)]

theorem slack_parity_positive (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (u : Fin 16 → ℝ)
    (h0 : u 0 = 0) (h15 : u 15 = 0) (hne : u ≠ 0) : 0 < qForm u (slack G) := by
  let o := oddPart u
  let e := evenPart u
  let x : ℝ := ∑ A : Odd, (u A.val)^2
  let y : ℝ := ∑ A : Even, (u A.val)^2
  have hx : 0 ≤ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : 0 ≤ y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hox : (∑ A : Fin 16, (o A)^2) = x := oddPart_energy u
  have hey : (∑ A : Fin 16, (e A)^2) = y := evenPart_energy u
  have hod : 6*x ≤ qForm o (slack G) := by
    by_cases ho : o = 0
    · simp [← hox, ho, qForm]
    · have h := odd_slack_strict G hG hsym o (oddPart_supported u) ho
      rw [hox] at h
      exact h.le
  have hed : (3/2)*y ≤ qForm e (slack G) := by
    by_cases he : e = 0
    · simp [← hey, he, qForm]
    · have h := even_slack_strict G hG hsym e (evenPart_supported u) he
      rw [hey] at h
      exact h.le
  have hdiag : 6*x+(3/2)*y < qForm o (slack G)+qForm e (slack G) := by
    by_cases ho : o = 0
    · have he : e ≠ 0 := by
        intro he
        apply hne
        have h := parts_sum u h0 h15
        change u = fun A => o A+e A at h
        apply h.trans
        funext A
        rw [ho, he]
        simp
      have h := even_slack_strict G hG hsym e (evenPart_supported u) he
      rw [hey] at h
      linarith
    · have h := odd_slack_strict G hG hsym o (oddPart_supported u) ho
      rw [hox] at h
      linarith
  have hc : (mixed G u u)^2 ≤ (25/3)*x*y := mixed_sq_le G hG hsym u u
  have hp := two_block_positive x y (qForm o (slack G)) (qForm e (slack G))
    (mixed G u u) hx hy hdiag hc
  have heq : qForm u (slack G) = qForm o (slack G)+qForm e (slack G)+2*mixed G u u := by
    conv_lhs => rw [parts_sum u h0 h15]
    rw [qForm_add _ _ _ (slack_symmetric G hsym), bilinear_parts]
  rwa [← heq] at hp

theorem actual_slack_parity_positive (left right : ByteOrientations.Orientation)
    (inverse : Bool) (u : Fin 16 → ℝ) (h0 : u 0 = 0) (h15 : u 15 = 0)
    (hne : u ≠ 0) :
    0 < qForm u (slack (ActualDegreeThreeGram.degreeThreeGram left right inverse)) :=
  slack_parity_positive _ (PaperDegreeThreeGramPrinted.actual_entry_bounds left right inverse)
    (ActualDegreeThreeGram.degreeThreeGram_symmetric left right inverse) u h0 h15 hne

end AES8.PaperDegreeThreeParitySchur
