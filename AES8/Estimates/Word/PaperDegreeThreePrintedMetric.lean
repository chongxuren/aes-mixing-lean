import AES8.Estimates.Word.PaperDegreeThreePrintedDeductions

/-! The printed degree-three metric lower bounds, using the endpoint
coupling-times-inverse operator bound. The older absolute-row calculation
remains independent; only its metric definitions and exact identities are used. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreePrintedMetric
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric
open PaperDegreeThreeParityCounts PaperDegreeThreeTensorSpectrum
open PaperDegreeThreeEndpointMetric
set_option autoImplicit false
set_option maxRecDepth 100000

theorem quadratic_le_norm {I : Type*} [Fintype I] [DecidableEq I]
    (K : I → I → ℝ) (cap : ℝ) (hc : 0 ≤ cap)
    (hnorm : ‖PaperKernelBounds.kernelOperator K‖ ≤ cap) (f : I → ℝ) :
    qForm f K ≤ cap * ∑ i, f i ^ 2 := by
  let v : EuclideanSpace ℝ I := WithLp.toLp 2 f
  have hn := (PaperKernelBounds.kernelOperator K).le_opNorm v
  have hb : ‖PaperKernelBounds.kernelOperator K v‖ ≤ cap * ‖v‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg v))).mpr hb
  have he : (∑ i, action K f i ^ 2) ≤ cap ^ 2 * ∑ i, f i ^ 2 := by
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq,
      PaperKernelBounds.kernelOperator_apply, PaperKernelBounds.kernelAction,
      Real.norm_eq_abs, sq_abs, v, action] using hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (action K f)
  have hid : (∑ i, f i * action K f i) = qForm f K := by
    unfold action qForm
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid] at hcs
  have hf : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left he hf
  have hp : 0 ≤ cap * ∑ i, f i ^ 2 := mul_nonneg hc hf
  nlinarith

theorem supported_quadratic_norm (P : Fin 16 → Prop) [DecidablePred P]
    (K : Fin 16 → Fin 16 → ℝ) (cap : ℝ) (hc : 0 ≤ cap)
    (hn : ‖PaperKernelBounds.kernelOperator (fun a b : {a // P a} => K a.val b.val)‖ ≤ cap)
    (u : Fin 16 → ℝ) (hu : ∀ a, ¬ P a → u a = 0) :
    qForm u K ≤ cap * ∑ a, u a ^ 2 := by
  have hsum (f : Fin 16 → ℝ) (hf : ∀ a, ¬ P a → f a = 0) :
      (∑ a : {a // P a}, f a.val) = ∑ a, f a := by
    rw [sum_subtype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : P a <;> simp [ha, hf a]
  have hq : qForm (fun a : {a // P a} => u a.val)
      (fun a b => K a.val b.val) = qForm u K := by
    unfold qForm
    rw [hsum (fun a => ∑ b : {a // P a}, u a * u b.val * K a b.val)
      (by intro a ha; simp [hu a ha])]
    apply Finset.sum_congr rfl
    intro a _
    exact hsum (fun b => u a * u b * K a b) (by intro b hb; simp [hu b hb])
  have he : (∑ a : {a // P a}, u a.val ^ 2) = ∑ a, u a ^ 2 :=
    hsum (fun a => u a ^ 2) (by intro a ha; simp [hu a ha])
  have h := quadratic_le_norm (fun a b : {a // P a} => K a.val b.val) cap hc hn
    (fun a => u a.val)
  rwa [hq, he] at h

theorem odd_metric_lower (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsOdd A → u A = 0) :
    ((1-xi^2)^2 - oddCorrectionCap) * ∑ A : Fin 16, (u A)^2 ≤
      qForm u effectiveMetric := by
  have hp : ∀ A, maskSize A % 2 ≠ 1 → u A = 0 := by
    intro A hA
    apply hu A
    intro ha
    rcases ha with ha | ha <;> simp [ha] at hA
  have ht := supported_quadratic_lower u 1 hp
  have hc := supported_quadratic_norm IsOdd correction
    oddCorrectionCap (by norm_num [oddCorrectionCap, xi])
    PaperDegreeThreePrintedDeductions.odd_correction_norm u hu
  rw [correction_quadratic_sub]
  nlinarith

theorem even_metric_lower (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsEven A → u A = 0) :
    ((1-xi^2)^2 - evenCorrectionCap) * ∑ A : Fin 16, (u A)^2 ≤
      qForm u effectiveMetric := by
  have hp : ∀ A, maskSize A % 2 ≠ 0 → u A = 0 := by
    intro A hA
    apply hu A
    intro ha
    simp [IsEven] at ha
    simp [ha] at hA
  have ht := supported_quadratic_lower u 0 hp
  have hc := supported_quadratic_norm IsEven correction
    evenCorrectionCap (by norm_num [evenCorrectionCap, xi])
    PaperDegreeThreePrintedDeductions.even_correction_norm u hu
  rw [correction_quadratic_sub]
  nlinarith

/-- Strict Loewner lower bound on the actual odd principal metric block. -/
theorem odd_metric_strict (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsOdd A → u A = 0)
    (hne : u ≠ 0) : (31/32 : ℝ) * ∑ A : Fin 16, (u A)^2 < qForm u effectiveMetric := by
  have h := odd_metric_lower u hu
  have hc : (31/32 : ℝ) < (1-xi^2)^2 - oddCorrectionCap := by
    norm_num [xi, oddCorrectionCap]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  exact hp.trans_le h

/-- Strict Loewner lower bound on the actual size-two principal metric block. -/
theorem even_metric_strict (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsEven A → u A = 0)
    (hne : u ≠ 0) : (63/64 : ℝ) * ∑ A : Fin 16, (u A)^2 < qForm u effectiveMetric := by
  have h := even_metric_lower u hu
  have hc : (63/64 : ℝ) < (1-xi^2)^2 - evenCorrectionCap := by
    norm_num [xi, evenCorrectionCap]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  exact hp.trans_le h


end AES8.PaperDegreeThreePrintedMetric
