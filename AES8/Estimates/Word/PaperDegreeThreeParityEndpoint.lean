import AES8.Estimates.Word.PaperDegreeThreeParitySchur
import AESConcrete.ReverseDegreeThree

/-! A uniform positive margin from the actual parity proof.
The explicit weakening to 1/12 turns the two-block inequalities into a
uniform energy inequality. A finite absolute-row cap then gives a smaller
Gram scalar and hence the strict physical operator endpoint. This leaf does
not import the historical weighted-row strict endpoint.
Constructive proof preparation only; no attacks or manuscript/vendor edits. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParityEndpoint
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ActivityEffectiveMetric
open AESConcrete.ActivityGramDominance
open AESConcrete.ActualDegreeThreeGram
open AESConcrete.DegreeThreeFrameEnergy
open PaperDegreeThreeParityCounts PaperDegreeThreeEndpointMetric
open PaperDegreeThreeParitySchur
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Uniform weakening of the paper's margins; 1/12 is below the smaller
eigenvalue of the scalar two-by-two comparison. -/
theorem two_block_margin (x y a b c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hdiag : 6*x+(3/2)*y ≤ a+b) (hcross : c^2 ≤ (25/3)*x*y) :
    (1/12 : ℝ)*(x+y) ≤ a+b+2*c := by
  by_contra h
  have hneg : a+b+2*c < (1/12)*(x+y) := lt_of_not_ge h
  have hc : (71/12 : ℝ)*x+(17/12)*y < -2*c := by linarith
  have hp : 0 ≤ (71/12 : ℝ)*x+(17/12)*y := by positivity
  have hc0 : 0 ≤ -2*c := by linarith
  have hs := (sq_lt_sq₀ hp hc0).mpr hc
  nlinarith [sq_nonneg ((71/12 : ℝ)*x-(17/12)*y), mul_nonneg hx hy]

theorem slack_parity_margin (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (u : Fin 16 → ℝ)
    (h0 : u 0 = 0) (h15 : u 15 = 0) :
    (1/12 : ℝ)*(∑ A : Fin 16, (u A)^2) ≤ qForm u (slack G) := by
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
  have heq : qForm u (slack G) = qForm o (slack G)+qForm e (slack G)+2*mixed G u u := by
    conv_lhs => rw [parts_sum u h0 h15]
    rw [qForm_add _ _ _ (slack_symmetric G hsym), bilinear_parts]
  have henergy : (∑ A : Fin 16, (u A)^2) = x+y := by
    have h := parts_sum u h0 h15
    change (∑ A : Fin 16, (u A)^2) =
      (∑ A : Odd, (u A.val)^2)+(∑ A : Even, (u A.val)^2)
    rw [sum_subtype IsOdd (fun A => (u A)^2),
      sum_subtype IsEven (fun A => (u A)^2)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _
    have ha := congrFun h A
    by_cases ho : IsOdd A <;> by_cases he : IsEven A
    · rcases ho with ho | ho <;> have he' : maskSize A = 2 := he <;> omega
    · simp [ho, he]
    · simp [ho, he]
    · have hz : u A = 0 := by simpa [oddPart, evenPart, ho, he] using ha
      simp [ho, he, hz]
  rw [henergy, heq]
  exact two_block_margin x y _ _ _ hx hy (by linarith)
    (mixed_sq_le G hG hsym u u)

def interiorPart (u : Fin 16 → ℝ) (A : Fin 16) : ℝ :=
  if A = 0 ∨ A = 15 then 0 else u A

theorem interiorPart_zero (u : Fin 16 → ℝ) : interiorPart u 0 = 0 := by
  simp [interiorPart]

theorem interiorPart_full (u : Fin 16 → ℝ) : interiorPart u 15 = 0 := by
  simp [interiorPart]

theorem qForm_interiorPart (u : Fin 16 → ℝ) (K : Fin 16 → Fin 16 → ℝ) :
    qForm (interiorPart u) K =
      qForm (fun A : Interior => u A.val) (fun A B => K A.val B.val) := by
  have hi (A : Interior) : interiorPart u A.val = u A.val := by
    simp [interiorPart, A.property.1, A.property.2]
  unfold qForm
  rw [sum_split]
  simp only [interiorPart_zero, interiorPart_full, zero_mul, Finset.sum_const_zero,
    zero_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [sum_split]
  simp only [interiorPart_zero, interiorPart_full, mul_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro B _
  rw [hi, hi]

def metricCap : ℝ := ∑ A : Fin 16, ∑ B : Fin 16, |effectiveMetric A B|

theorem metricCap_nonneg : 0 ≤ metricCap :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem metric_quadratic_upper (u : Fin 16 → ℝ) :
    qForm u effectiveMetric ≤ metricCap * ∑ A : Fin 16, (u A)^2 := by
  apply PaperSymmetricRowQuadratic.quadratic_le effectiveMetric
    DampedDegreeThree.effectiveMetric_symmetric metricCap
  intro A
  exact Finset.single_le_sum
    (fun B (_ : B ∈ (Finset.univ : Finset (Fin 16))) =>
      Finset.sum_nonneg (fun C _ => abs_nonneg (effectiveMetric B C)))
    (Finset.mem_univ A)

/-- A parity-derived uniform scalar below the printed Gram coefficient. -/
theorem exists_strict_gram_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 < c ∧ c < comparisonLambda ∧ ∀ u : Fin 16 → ℝ,
      qForm u (degreeThreeGram left right inverse) ≤ c * fullEnergy u := by
  let eps : ℝ := 1/(24*(metricCap+1))
  have hcap := metricCap_nonneg
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsbudget : eps*(metricCap+1) = 1/24 := by
    dsimp [eps]
    field_simp [show metricCap+1 ≠ 0 from ne_of_gt (by linarith)]
  have hepsterm := mul_nonneg heps.le hcap
  have hepstop : eps ≤ 1/24 := by nlinarith
  have hepscap : eps*metricCap ≤ 1/12 := by nlinarith
  have hc : 0 < comparisonLambda-eps := by
    norm_num [comparisonLambda] at *
    linarith
  refine ⟨comparisonLambda-eps, hc, by linarith, ?_⟩
  intro u
  let v := interiorPart u
  let energy : ℝ := ∑ A : Fin 16, (v A)^2
  have hp := slack_parity_margin (degreeThreeGram left right inverse)
    (PaperDegreeThreeGramPrinted.actual_entry_bounds left right inverse)
    (degreeThreeGram_symmetric left right inverse) v
    (interiorPart_zero u) (interiorPart_full u)
  have hupper := metric_quadratic_upper v
  have hmul := mul_le_mul_of_nonneg_left hupper heps.le
  have hsmall := mul_le_mul_of_nonneg_right hepscap
    (Finset.sum_nonneg (fun A (_ : A ∈ (Finset.univ : Finset (Fin 16))) =>
      sq_nonneg (v A)))
  rw [slack_quadratic] at hp
  have hgram : qForm v (degreeThreeGram left right inverse) ≤
      (comparisonLambda-eps)*qForm v effectiveMetric := by nlinarith
  have hvG : qForm v (degreeThreeGram left right inverse) =
      qForm u (degreeThreeGram left right inverse) := by
    calc
      _ = qForm (fun A : Interior => u A.val)
          (fun A B => degreeThreeGram left right inverse A.val B.val) :=
        qForm_interiorPart u _
      _ = _ := (PaperDegreeThreeGramPrinted.degreeThreeGram_interior left right inverse u).symm
  have hvH : qForm v effectiveMetric = effectiveEnergy u := qForm_interiorPart u _
  rw [hvG, hvH] at hgram
  exact hgram.trans (mul_le_mul_of_nonneg_left (effectiveEnergy_le_fullEnergy u) hc.le)

theorem exists_frame_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧ ∀ u : Fin 16 → ℝ,
      (∑ y, (outputSynthesis left right inverse u y)^2) ≤
        c^2 * ∑ x, (frameSynthesis u x)^2 := by
  obtain ⟨a, ha, halt, hgram⟩ := exists_strict_gram_scalar left right inverse
  let c : ℝ := Real.sqrt a / 65536
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg a) (by norm_num)
  have hroot : Real.sqrt a < (33 / 10 : ℝ) := by
    have hs := Real.sq_sqrt ha.le
    have hn := Real.sqrt_nonneg a
    norm_num [comparisonLambda] at halt
    nlinarith
  have hcap : c < 33 / (10 * 65536) := by
    dsimp [c]
    have h := div_lt_div_of_pos_right hroot (by norm_num : (0 : ℝ) < 65536)
    norm_num at h ⊢
    exact h
  have hc2 : c^2 = a / 4294967296 := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt ha.le]
    norm_num
  refine ⟨c, hc, hcap, ?_⟩
  intro u
  have h := hgram u
  rw [← outputSynthesis_energy, ← frameSynthesis_energy] at h
  rw [hc2]
  nlinarith

theorem exists_forward_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧
      ∀ f : (Fin 4 → Byte) → ℝ,
      (∑ y, (action (DampedDegreeThree.forwardBlockKernel left right inverse) f y)^2) ≤
        c^2 * ∑ x, (f x)^2 := by
  obtain ⟨c, hc, hcap, hframe⟩ := exists_frame_energy_scalar left right inverse
  refine ⟨c, hc, hcap, ?_⟩
  intro f
  have h := hframe (normalizedCoefficients f)
  simp only [outputSynthesis_eq, ← normalized_reconstruction] at h
  simp only [DampedDegreeThree.forwardBlockKernel, kernelCompose_action, degreeKernel_action]
  exact h.trans (mul_le_mul_of_nonneg_left
    (degreeComponent_energy_le (0 : Byte) (by norm_num [BinaryWord.card]) 0 f)
    (sq_nonneg c))

theorem forward_operator_norm_lt (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (DampedDegreeThree.forwardBlockKernel left right inverse)‖ <
      (33 / (10 * 65536) : ℝ) := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_forward_energy_scalar left right inverse
  exact (kernelOperator_norm_le _ hc henergy).trans_lt hcap

theorem exists_reverse_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧
      ∀ f : (Fin 4 → Byte) → ℝ,
      (∑ y, (action (ReverseDegreeThree.reverseBlockKernel left right inverse) f y)^2) ≤
        c^2 * ∑ x, (f x)^2 := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_forward_energy_scalar
    (ReverseDegreeThree.transposeOrientation right)
    (ReverseDegreeThree.transposeOrientation left) (!inverse)
  exact ⟨c, hc, hcap, adjoint_energy_le _ _ c
    (ReverseDegreeThree.forward_reverse_adjoint left right inverse) henergy⟩

theorem reverse_operator_norm_lt (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (ReverseDegreeThree.reverseBlockKernel left right inverse)‖ <
      (33 / (10 * 65536) : ℝ) := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_reverse_energy_scalar left right inverse
  exact (kernelOperator_norm_le _ hc henergy).trans_lt hcap

end AES8.PaperDegreeThreeParityEndpoint
