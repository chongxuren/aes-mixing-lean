/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Word.ScaledEnergy
import AES8.Reductions.Source.ThreeZeroMass
import AES8.Reductions.Support.OneActiveAverage
import AES8.Estimates.FirstHigh.ActualFourMoment
import AES8.Estimates.FirstHigh.ActualNineMoment

/-! Actual coordinate-zero moments from signed three-zero fiber masses.
Only original source laws are conditioned.   -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ActualZeroMoment
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.TwelveConditionalResponse
open AES8.TwelvePatternCoordinates (order order_zero order_ne_zero)
open AES8.OneSourceEventMoment (atomCap traceCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.TwoZeroTwelveMoment (constantCap)
open AES8.FirstHighSupportEvent (boundaryInput)

def thirteenMassCap : ℝ := atomCap * entryCap ^ 2 * traceCap
def twelvePatternMassCap : ℝ := atomCap * constantCap * entryCap * traceCap
def thirteenBudget : ℝ := 4 * thirteenMassCap ^ 2 / (q - 1)
def twelveBudget : ℝ := 64 * twelvePatternMassCap ^ 2 / (q - 1)

section GenericMixture
variable {I : Type*} [Fintype I]
theorem abs_probability_sum_le (eta v : I → ℝ) (A : ℝ)
    (heta : ∀ i, 0 ≤ eta i) (htotal : (∑ i, eta i) = 1) (hv : ∀ i, |v i| ≤ A) :
    |∑ i, eta i * v i| ≤ A := by
  calc
    _ ≤ ∑ i, |eta i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, eta i * |v i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (heta i)]
    _ ≤ ∑ i, eta i * A := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (heta i))
    _ = A := by rw [← Finset.sum_mul, htotal, _root_.one_mul]
end GenericMixture

theorem conditional_thirteen_mass_le (r : Fin 16) (hr : maskSize r = 3)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    |∑ g : WordMixThreeZeroFiber.G r, conditionalResponse b k w g.val| ≤ thirteenMassCap := by
  have h := ThreeZeroMass.four_residual_mass_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun i => affineEquiv k w i) (fun g : WordMixThreeZeroFiber.G r => g.val)
    (wordLaw (sourceInput b k))
    (WordMixThreeZeroFiber.coordinate_bijective r hr 0)
    (WordMixThreeZeroFiber.coordinate_bijective r hr 1)
    atomCap entryCap traceCap (by norm_num [atomCap, q]) (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun _ y x => TwoZeroThirteenMoment.residual_entry_le y x)
    (fun _ => OneSourceEventMoment.residual_trace_le)
  change |∑ g : WordMixThreeZeroFiber.G r, conditionalResponse b k w g.val| ≤ thirteenMassCap at h
  exact h

theorem conditional_twelve_pattern_mass_le (r : Fin 16) (hr : maskSize r = 3)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (w : OtherAssignments k) (j : Fin 4) :
    |∑ g : WordMixThreeZeroFiber.G r, conditionalPattern b k w j g.val| ≤ twelvePatternMassCap := by
  have h := ThreeZeroMass.three_residual_constant_mass_le
    (fun i => patternChannel j (order j i)) (fun i => affineEquiv k w (order j i))
    (fun g : WordMixThreeZeroFiber.G r => fun i => g.val (order j i)) (wordLaw (sourceInput b k))
    (WordMixThreeZeroFiber.coordinate_bijective r hr (order j 1))
    (WordMixThreeZeroFiber.coordinate_bijective r hr (order j 2))
    atomCap constantCap entryCap traceCap (by norm_num [atomCap, q])
    (by norm_num [constantCap, q]) (by norm_num [entryCap, q]) (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun y x => by
      simpa only [order_zero, patternChannel, if_pos rfl, ite_true] using
        TwoZeroTwelveMoment.constant_entry_le y x)
    (fun y x => by
      simpa only [patternChannel, if_neg (order_ne_zero j 3 (by decide))] using
        TwoZeroThirteenMoment.residual_entry_le y x)
    (by simpa only [patternChannel, if_neg (order_ne_zero j 1 (by decide))] using
      OneSourceEventMoment.residual_trace_le)
    (by simpa only [patternChannel, if_neg (order_ne_zero j 2 (by decide))] using
      OneSourceEventMoment.residual_trace_le)
  have heq : (∑ g : WordMixThreeZeroFiber.G r, conditionalPattern b k w j g.val) =
      ∑ g : WordMixThreeZeroFiber.G r, ZeroFiberResponseEnergy.response
        (fun i => patternChannel j (order j i)) (fun i => affineEquiv k w (order j i))
        (fun g : WordMixThreeZeroFiber.G r => fun i => g.val (order j i))
        (wordLaw (sourceInput b k)) g := by
    apply Finset.sum_congr rfl
    intro g _
    exact TwoZeroTwelveMoment.conditionalPattern_eq_response (fun g : WordMixThreeZeroFiber.G r => g.val)
      b k w j g
  rw [heq]
  exact h

theorem actual_thirteen_mass_le (r : Fin 16) (hr : maskSize r = 3) (b : AES.State) (hb : b ≠ 0) :
    |∑ g : WordMixThreeZeroFiber.G r, component (error 1 b) 13 g.val| ≤ thirteenMassCap := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  rw [actual_component_thirteen_eq_probability_mixture b k]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  exact abs_probability_sum_le (conditionWeight b k)
    (fun w => ∑ g : WordMixThreeZeroFiber.G r, conditionalResponse b k w g.val)
    thirteenMassCap (conditionWeight_nonnegative b k) (conditionWeight_total b k)
    (fun w => conditional_thirteen_mass_le r hr b k hk w)

theorem actual_twelve_mass_le (r : Fin 16) (hr : maskSize r = 3) (b : AES.State) (hb : b ≠ 0) :
    |∑ g : WordMixThreeZeroFiber.G r, component (error 1 b) 12 g.val| ≤ 4 * twelvePatternMassCap := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  rw [actual_component_twelve_eq_probability_mixture b k]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  apply abs_probability_sum_le (conditionWeight b k) _ (4 * twelvePatternMassCap)
    (conditionWeight_nonnegative b k) (conditionWeight_total b k)
  intro w
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin 4, |∑ g : WordMixThreeZeroFiber.G r, conditionalPattern b k w j g.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, twelvePatternMassCap := Finset.sum_le_sum
      (fun j _ => conditional_twelve_pattern_mass_le r hr b k hk w j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

theorem actual_thirteen_projected_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 13)) 0 y ^ 2) ≤ thirteenBudget := by
  rw [OneActiveAverage.component_zero_energy]
  have hd : ActivityAverageEnergy.denominator AES.Word = q - 1 := by
    unfold ActivityAverageEnergy.denominator
    rw [AES.word_card]
    norm_num [q]
  simp_rw [hd, OneActiveAverage.boundary_mass_eq_full_fiber _ (SupportProfile.component_at_zero _ 13)]
  calc
    _ ≤ ∑ _t : Fin 4, thirteenMassCap ^ 2 / (q - 1) := by
      apply Finset.sum_le_sum
      intro t _
      apply div_le_div_of_nonneg_right _ (by norm_num [q])
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _)
        (actual_thirteen_mass_le _ (OneActiveAverage.inactiveMask_size t) b hb) 2)
    _ = thirteenBudget := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, thirteenBudget]; ring

theorem actual_twelve_projected_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 12)) 0 y ^ 2) ≤ twelveBudget := by
  rw [OneActiveAverage.component_zero_energy]
  have hd : ActivityAverageEnergy.denominator AES.Word = q - 1 := by
    unfold ActivityAverageEnergy.denominator
    rw [AES.word_card]
    norm_num [q]
  simp_rw [hd, OneActiveAverage.boundary_mass_eq_full_fiber _ (SupportProfile.component_at_zero _ 12)]
  calc
    _ ≤ ∑ _t : Fin 4, (4 * twelvePatternMassCap) ^ 2 / (q - 1) := by
      apply Finset.sum_le_sum
      intro t _
      apply div_le_div_of_nonneg_right _ (by norm_num [q])
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _)
        (actual_twelve_mass_le _ (OneActiveAverage.inactiveMask_size t) b hb) 2)
    _ = twelveBudget := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, twelveBudget]; ring

theorem exact_thirteen_budget : q ^ 5 * thirteenBudget =
    (4626176256000000 : ℝ) / (q ^ 3 * (q - 1)) := by
  norm_num [thirteenBudget, thirteenMassCap, atomCap, entryCap, traceCap, q]
theorem exact_twelve_budget : q ^ 5 * twelveBudget =
    (185047050240000 : ℝ) / (q * (q - 1) ^ 3) := by
  norm_num [twelveBudget, twelvePatternMassCap, atomCap, constantCap, entryCap, traceCap, q]

theorem thirteen_budget_le : q ^ 5 * thirteenBudget ≤ (1 / 100000000000 : ℝ) ^ 2 := by
  rw [exact_thirteen_budget]
  norm_num [q]
theorem twelve_budget_le : q ^ 5 * twelveBudget ≤ (1 / 100000000000 : ℝ) ^ 2 := by
  rw [exact_twelve_budget]
  norm_num [q]

theorem actual_thirteen_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 13)) 0) ≤ 1 / 100000000000 := by
  exact ScaledEnergy.aes_scaled_l2_le _ _ _ (by norm_num)
    (actual_thirteen_projected_energy_le b hb) thirteen_budget_le

theorem actual_twelve_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 12)) 0) ≤ 1 / 100000000000 := by
  exact ScaledEnergy.aes_scaled_l2_le _ _ _ (by norm_num)
    (actual_twelve_projected_energy_le b hb) twelve_budget_le

end AES8.ActualZeroMoment
