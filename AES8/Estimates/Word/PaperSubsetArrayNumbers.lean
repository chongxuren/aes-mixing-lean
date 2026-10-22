import AES8.Estimates.Word.PaperSubsetSupportNorms

/-! Exact printed square-root constants and rational rounding, independently
of any actual AES support-matrix sandwich identity. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSubsetArrayConsumers
open AESMixing PaperKernelBounds PaperActivityArrayBlocks PaperSubsetSupportBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

theorem printed11_nonneg : 0≤printed11 := by unfold printed11; positivity
theorem printed12_nonneg : 0≤printed12 := by unfold printed12; positivity
theorem printed22_nonneg : 0≤printed22 := by unfold printed22; positivity

/-- The first displayed printed constant is exact, not merely a rounding. -/
theorem printed11_eq : printed11 = (4/1125:ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤(16/15:ℝ)^3)
  unfold printed11
  nlinarith only [hs]

/-- Squared form of sqrt(24(8+2sqrt13)) (16/15)^(5/2) / 256. -/
theorem printed12_sq : printed12^2 =
    24*(8+2*Real.sqrt 13)*(16/15:ℝ)^5/256^2 := by
  have h6 := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hf := Real.sq_sqrt (by norm_num : (0:ℝ)≤(16/15:ℝ)^3)
  have ha := Real.sq_sqrt (by positivity : (0:ℝ)≤8+2*Real.sqrt 13)
  calc
    printed12^2 = (4*Real.sqrt (6:ℝ)^2*Real.sqrt ((16/15:ℝ)^3)^2*
        Real.sqrt (8+2*Real.sqrt 13)^2*(16/15:ℝ)^2)/256^2 := by
      unfold printed12
      ring
    _ = _ := by
      rw [h6, hf, ha]
      norm_num
      ring

/-- Exact printed square-root form, with half-integer powers written as sqrt. -/
theorem printed12_eq : printed12 =
    Real.sqrt (24*(8+2*Real.sqrt 13))*Real.sqrt ((16/15:ℝ)^5)/256 := by
  have h1 := Real.sq_sqrt (by positivity : (0:ℝ)≤24*(8+2*Real.sqrt 13))
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤(16/15:ℝ)^5)
  have hp : 0≤Real.sqrt (24*(8+2*Real.sqrt 13))*Real.sqrt ((16/15:ℝ)^5)/256 := by positivity
  have he : (Real.sqrt (24*(8+2*Real.sqrt 13))*Real.sqrt ((16/15:ℝ)^5)/256)^2 =
      24*(8+2*Real.sqrt 13)*(16/15:ℝ)^5/256^2 := by
    rw [div_pow, mul_pow, h1, h2]
  nlinarith only [printed12_sq, printed12_nonneg, hp, he]

theorem printed12_le : printed12 ≤ (64/729:ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
  have hsn := Real.sqrt_nonneg (13:ℝ)
  have hsbound : Real.sqrt (13:ℝ) ≤ 361/100 := by nlinarith
  have hsq : printed12^2 ≤ (64/729:ℝ)^2 := by
    rw [printed12_sq]
    norm_num
    nlinarith only [hsbound]
  exact (sq_le_sq₀ printed12_nonneg (by norm_num)).mp hsq

/-- Same third displayed constant, simplified without decimal approximation. -/
theorem printed22_eq : printed22 = (3+Real.sqrt 4097)/75 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤(1/256:ℝ)^2+16*(1/16:ℝ)^2)
  have ht := Real.sq_sqrt (by norm_num : (0:ℝ)≤4097)
  have hsn := Real.sqrt_nonneg ((1/256:ℝ)^2+16*(1/16:ℝ)^2)
  have htn := Real.sqrt_nonneg (4097:ℝ)
  have he : Real.sqrt ((1/256:ℝ)^2+16*(1/16:ℝ)^2) = Real.sqrt 4097/256 := by
    nlinarith only [hs, ht, hsn, htn]
  unfold printed22
  rw [he]
  ring

theorem printed22_lt : printed22 < (9/10:ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤4097)
  have hsn := Real.sqrt_nonneg (4097:ℝ)
  rw [printed22_eq]
  nlinarith


end AES8.PaperSubsetArrayConsumers
