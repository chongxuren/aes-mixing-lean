import AESConcrete.WeightedResponse

/-!
# Two signed responses with distinct common normalizers

Generic norm inequalities. The input normalizer D belongs to both responses;
the output normalizer d belongs to their difference. Norm caps are added
before squaring. The exact response identity and actual AES energy hypotheses
must be supplied by separate geometric proofs.

Constructive fixed AES10/14/16 research only.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoResponseEnergy
open AESMixing

variable {Y Z : Type*} [Fintype Y] [Fintype Z]

theorem sub_div_l2_le (W W0 : Y → ℝ) (h : Z → ℝ)
    (a b D d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hW : (∑ y, W y ^ 2) ≤ (a / D) ^ 2 * ∑ z, h z ^ 2)
    (hW0 : (∑ y, W0 y ^ 2) ≤ (b / D) ^ 2 * ∑ z, h z ^ 2) :
    l2 (fun y => (W y - W0 y) / d) ≤ ((a + b) / (D * d)) * l2 h := by
  rw [WeightedResponse.l2_div, abs_of_nonneg hd]
  calc
    _ ≤ (l2 W + l2 W0) / d :=
      div_le_div_of_nonneg_right (WeightedResponse.l2_sub_le W W0) hd
    _ ≤ ((a / D) * l2 h + (b / D) * l2 h) / d :=
      div_le_div_of_nonneg_right
        (add_le_add (l2_le_of_energy W h (a / D) (div_nonneg ha hD) hW)
          (l2_le_of_energy W0 h (b / D) (div_nonneg hb hD) hW0)) hd
    _ = _ := by ring

theorem sub_div_energy_le (W W0 : Y → ℝ) (h : Z → ℝ)
    (a b D d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hW : (∑ y, W y ^ 2) ≤ (a / D) ^ 2 * ∑ z, h z ^ 2)
    (hW0 : (∑ y, W0 y ^ 2) ≤ (b / D) ^ 2 * ∑ z, h z ^ 2) :
    (∑ y, ((W y - W0 y) / d) ^ 2) ≤
      ((a + b) ^ 2 / (D ^ 2 * d ^ 2)) * ∑ z, h z ^ 2 := by
  have hl := sub_div_l2_le W W0 h a b D d ha hb hD hd hW hW0
  have hc : 0 ≤ (a + b) / (D * d) :=
    div_nonneg (add_nonneg ha hb) (mul_nonneg hD hd)
  have hs := (sq_le_sq₀ (l2_nonneg (fun y => (W y - W0 y) / d))
    (mul_nonneg hc (l2_nonneg h))).mpr hl
  simpa only [mul_pow, div_pow, l2_sq] using hs

end AESConcrete.OmittedUniformTwoResponseEnergy
