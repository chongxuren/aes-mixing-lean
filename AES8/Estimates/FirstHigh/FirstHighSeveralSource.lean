/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Transfer.LowTransfer
import AESPaper.SeveralSourcePositiveProfile

/-!
# First high remainder at outputs eleven and twelve for several sources

The literal-pattern degree-energy budgets are sharper than the universal
initializer at degrees three and four. For actual inputs with at least two
active first-layer source words, they bound the scaled high-component lengths
by `11/1000`, `11/1000`, and `1/400`. The admitted centered physical step caps
then fit the existing first-high allowances at output coordinates 11 and 12.

The source-count hypothesis is essential to this argument. The one-source
cases, outputs 0 through 10, and the full `PhysicalCaps.firstHigh` field remain
separate obligations. No assumed missing analytic estimate, local execution,
attack, manuscript edit, or predecessor edit is used here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.FirstHighSeveralSource
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AES8.SupportEvolution (highPart)

section ActualInput

/-- The exact degree-three scalar budget is needed; its older coarse cap is
insufficient for the length `11/1000`. -/
theorem degree_three_budget_le :
    AESPaper.MixedDegreeBudgets.degreeBudget (3 : Fin 5) ≤ (11 / 1000 : ℝ)^2 := by
  rw [AESPaper.MixedDegreeBudgets.degreeBudget_eq_cast,
    AESPaper.MixedDegreeBudgets.rationalDegreeBudget_values]
  change ((112764087178354773 / 960767920282009600000 : ℚ) : ℝ) ≤ (11 / 1000 : ℝ)^2
  norm_num

theorem degree_four_budget_le :
    AESPaper.MixedDegreeBudgets.degreeBudget (4 : Fin 5) ≤ (1 / 400 : ℝ)^2 := by
  rw [AESPaper.MixedDegreeBudgets.degreeBudget_eq_cast,
    AESPaper.MixedDegreeBudgets.rationalDegreeBudget_values]
  change ((15752961 / 2684354560000 : ℚ) : ℝ) ≤ (1 / 400 : ℝ)^2
  norm_num

/-- Convert the actual positive-degree energy to the same counting length
used by `SupportProfile`; this retains the exact factor `q^5 = (2^80)^2`. -/
theorem scaled_degree_le (a : AES.State) (ha : 2 ≤ activeSourceCount a)
    (j : Fin 5) (hj : j ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hbudget : AESPaper.MixedDegreeBudgets.degreeBudget j ≤ c^2) :
    (2 : ℝ) ^ (80 : ℕ) * l2 (degreeComponent (0 : AES.Word) j (error 1 a)) ≤ c := by
  have he := AESPaper.SeveralSourcePositiveProfile.degree_scaled_energy_le a ha j hj
  rw [← AESPaper.SeveralSourcePositiveProfile.actual_positive_degree a j hj] at he
  have hs : ((2 : ℝ) ^ (80 : ℕ) *
      l2 (degreeComponent (0 : AES.Word) j (error 1 a)))^2 =
      AESPaper.StartingWord.q^5 *
        (∑ y, degreeComponent (0 : AES.Word) j (error 1 a) y^2) := by
    rw [mul_pow, l2_sq]
    norm_num [AESPaper.StartingWord.q]
  exact (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) hc).mp
    (hs.trans_le (he.trans hbudget))

theorem scaled_degree_three_le (a : AES.State) (ha : 2 ≤ activeSourceCount a) :
    (2 : ℝ) ^ (80 : ℕ) *
      l2 (degreeComponent (0 : AES.Word) (3 : Fin 5) (error 1 a)) ≤ 11 / 1000 :=
  scaled_degree_le a ha (3 : Fin 5) (by decide) (by norm_num) degree_three_budget_le

theorem scaled_degree_four_le (a : AES.State) (ha : 2 ≤ activeSourceCount a) :
    (2 : ℝ) ^ (80 : ℕ) *
      l2 (degreeComponent (0 : AES.Word) (4 : Fin 5) (error 1 a)) ≤ 1 / 400 :=
  scaled_degree_le a ha (4 : Fin 5) (by decide) (by norm_num) degree_four_budget_le

/-- Length allowances for the actual high support coordinates, in order 11,12,13. -/
def highBudget (c : Fin 3) : ℝ := if c.val = 2 then 1 / 400 else 11 / 1000

/-- Support refinement only reduces the counting length. -/
theorem high_component_scaled_le (a : AES.State) (ha : 2 ≤ activeSourceCount a)
    (c : Fin 3) :
    (2 : ℝ) ^ (80 : ℕ) *
      SupportProfile.profile (error 1 a) (Fin.natAdd 11 c) ≤ highBudget c := by
  have hr := SupportDegree.profile_le_degree (error 1 a) (Fin.natAdd 11 c)
  have hd : SupportDegree.degree (Fin.natAdd 11 c) =
      (if c.val = 2 then (4 : Fin 5) else (3 : Fin 5)) := by
    fin_cases c <;> rfl
  rw [hd] at hr
  unfold highBudget
  by_cases hc : c.val = 2
  · simp only [hc, if_true] at hr ⊢
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
      (scaled_degree_four_le a ha)
  · simp only [hc, if_false] at hr ⊢
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
      (scaled_degree_three_le a ha)

end ActualInput

section AdmittedStep

/-- The admitted coefficient bounds exactly the centered block used here. -/
theorem old_operator_cap (i j : Fin 14) :
    ‖LegacyTransfer.euclideanBlock i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  exact AESConcrete.AllStepCaps.physical_step_cap i j

theorem old_coefficient_nonneg (i j : Fin 14) :
    0 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L i j :=
  (norm_nonneg _).trans (old_operator_cap i j)

/-- Keep the centering on each source component when applying the admitted caps. -/
theorem highPart_profile_le (f : WordState → ℝ) (i : Fin 14) :
    SupportProfile.profile (TransferAssembly.centeredStep (highPart f)) i ≤
      ∑ c : Fin 3,
        (AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.natAdd 11 c)) *
          SupportProfile.profile f (Fin.natAdd 11 c) := by
  have hs : TransferAssembly.centeredStep (highPart f) =
      fun x => ∑ c : Fin 3,
        TransferAssembly.centeredStep
          (SupportProfile.component f (Fin.natAdd 11 c)) x := by
    unfold highPart
    exact TransferAssembly.centeredStep_sum _
  rw [hs]
  exact (TransferAssembly.profile_sum_le _ i).trans (Finset.sum_le_sum
    (fun c _ => LegacyTransfer.profile_le_of_operator_cap f i (Fin.natAdd 11 c)
      (old_operator_cap i (Fin.natAdd 11 c))))

/-- The analytic reduction is valid for every output coordinate. Its scalar
right side fits the fixed allowance only in the two rows proved below. -/
theorem normalized_highPart_profile_le (a : AES.State)
    (ha : 2 ≤ activeSourceCount a) (i : Fin 14) :
    NormalizedProfile.factor 1 *
      SupportProfile.profile (TransferAssembly.centeredStep (highPart (error 1 a))) i ≤
      (101 / 128 : ℝ) *
        ∑ c : Fin 3, AESRound.Certificate.L i (Fin.natAdd 11 c) * highBudget c := by
  have hscaled : (2 : ℝ) ^ (80 : ℕ) *
      SupportProfile.profile (TransferAssembly.centeredStep (highPart (error 1 a))) i ≤
      ∑ c : Fin 3,
        (AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.natAdd 11 c)) *
          highBudget c := by
    calc
      _ ≤ (2 : ℝ) ^ (80 : ℕ) *
          (∑ c : Fin 3,
            (AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.natAdd 11 c)) *
              SupportProfile.profile (error 1 a) (Fin.natAdd 11 c)) :=
        mul_le_mul_of_nonneg_left (highPart_profile_le (error 1 a) i) (by positivity)
      _ = ∑ c : Fin 3,
          (AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.natAdd 11 c)) *
            ((2 : ℝ) ^ (80 : ℕ) *
              SupportProfile.profile (error 1 a) (Fin.natAdd 11 c)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun c _ =>
        mul_le_mul_of_nonneg_left (high_component_scaled_le a ha c)
          (old_coefficient_nonneg i (Fin.natAdd 11 c)))
  have hf : NormalizedProfile.factor 1 =
      (2 : ℝ) ^ (80 : ℕ) * (2 : ℝ) ^ (41 : ℕ) := by
    norm_num [NormalizedProfile.factor, omega41]
  have hl : (2 : ℝ) ^ (41 : ℕ) * AESRound.Terminal.lambda = 101 / 128 := by
    norm_num [AESRound.Terminal.lambda]
  calc
    _ = (2 : ℝ) ^ (41 : ℕ) *
        ((2 : ℝ) ^ (80 : ℕ) *
          SupportProfile.profile
            (TransferAssembly.centeredStep (highPart (error 1 a))) i) := by
      rw [hf]
      ring
    _ ≤ (2 : ℝ) ^ (41 : ℕ) *
        (∑ c : Fin 3,
          (AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.natAdd 11 c)) *
            highBudget c) := mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = ∑ c : Fin 3,
        ((2 : ℝ) ^ (41 : ℕ) * AESRound.Terminal.lambda) *
          AESRound.Certificate.L i (Fin.natAdd 11 c) * highBudget c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [hl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

end AdmittedStep

section FixedAllowances

/-- These scalar checks use the authoritative admitted old L entries and the
current fixed d and g. They change no comparison coefficient or allowance. -/
theorem firstHigh_eleven_scalar :
    (101 / 128 : ℝ) *
      (∑ c : Fin 3, AESRound.Certificate.L (11 : Fin 14) (Fin.natAdd 11 c) *
        highBudget c) ≤ (1000 * g (11 : Fin 14)) * d (11 : Fin 14) := by
  norm_num [Fin.sum_univ_succ, AESRound.Certificate.L, highBudget, g, d, vec14_apply,
    Fin.natAdd]

theorem firstHigh_twelve_scalar :
    (101 / 128 : ℝ) *
      (∑ c : Fin 3, AESRound.Certificate.L (12 : Fin 14) (Fin.natAdd 11 c) *
        highBudget c) ≤ (1000 * g (12 : Fin 14)) * d (12 : Fin 14) := by
  norm_num [Fin.sum_univ_succ, AESRound.Certificate.L, highBudget, g, d, vec14_apply,
    Fin.natAdd]

/-- Coordinate eleven of the exact first-high interface, restricted to actual
inputs with at least two active source words. -/
theorem firstHigh_eleven_of_several (a : AES.State)
    (ha : 2 ≤ activeSourceCount a) :
    SupportProfile.profile
        (TransferAssembly.centeredStep (highPart (error 1 a))) (11 : Fin 14) ≤
      (d (11 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (11 : Fin 14)) := by
  have hbound := (normalized_highPart_profile_le a ha (11 : Fin 14)).trans
    firstHigh_eleven_scalar
  calc
    _ ≤ ((1000 * g (11 : Fin 14)) * d (11 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      calc
        _ = NormalizedProfile.factor 1 *
            SupportProfile.profile
              (TransferAssembly.centeredStep (highPart (error 1 a))) (11 : Fin 14) :=
          _root_.mul_comm _ _
        _ ≤ _ := hbound
    _ = _ := by ring

/-- Coordinate twelve has the same explicit several-source restriction. -/
theorem firstHigh_twelve_of_several (a : AES.State)
    (ha : 2 ≤ activeSourceCount a) :
    SupportProfile.profile
        (TransferAssembly.centeredStep (highPart (error 1 a))) (12 : Fin 14) ≤
      (d (12 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (12 : Fin 14)) := by
  have hbound := (normalized_highPart_profile_le a ha (12 : Fin 14)).trans
    firstHigh_twelve_scalar
  calc
    _ ≤ ((1000 * g (12 : Fin 14)) * d (12 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      calc
        _ = NormalizedProfile.factor 1 *
            SupportProfile.profile
              (TransferAssembly.centeredStep (highPart (error 1 a))) (12 : Fin 14) :=
          _root_.mul_comm _ _
        _ ≤ _ := hbound
    _ = _ := by ring

end FixedAllowances
end AES8.FirstHighSeveralSource
