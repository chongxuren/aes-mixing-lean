import AESPaper.MixedTermBounds
import AESPaper.MixedDegreeBudgets

/-!
# Actual positive-degree J/Z/R terms satisfy their scalar budgets

Each ternary pattern is identified with a residual mask and its disjoint
bias set before any actual-source estimate is applied. The pure degree-one
case uses the checked single-coordinate marginal estimate; pure higher
degrees use two residual contractions; mixed patterns use their signed
joint-event response estimate. The hypothesis counts actual active sources.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActualMixedPatternBounds
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (residual)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESPaper.TernaryDegree (residualIndex)
open AESPaper.MixedDegreeBudgets (biasCount budget)

def biasSet (a : Fin 4 → Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter (fun i : Fin 4 => a i = 1)

theorem biasSet_card (a : Fin 4 → Fin 3) : (biasSet a).card = biasCount a := rfl

theorem biasSet_eq_empty (a : Fin 4 → Fin 3) (hz : biasCount a = 0) :
    biasSet a = ∅ := by
  apply Finset.card_eq_zero.mp
  exact hz

/-- The exact residual mask is selected internally, including its size. -/
theorem residual_mask_exists (a : Fin 4 → Fin 3) : ∃ out : Fin 16,
    (∀ i : Fin 4, maskBit out i = true ↔ a i = 2) ∧
      maskSize out = (residualIndex a).val := by
  obtain ⟨out, hout, hsize⟩ := ActualZeroEvents.set_mask_exists
    (Finset.univ.filter (fun i : Fin 4 => a i = 2))
  refine ⟨out, ?_, ?_⟩
  · intro i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hout i
  · rw [hsize]
    exact (TernaryDegree.residualIndex_val a).symm

theorem bias_residual_disjoint (a : Fin 4 → Fin 3) (out : Fin 16)
    (hout : ∀ i : Fin 4, maskBit out i = true ↔ a i = 2) :
    MixedTensorEnergy.Disjoint out (biasSet a) := by
  intro i hi
  have h1 : a i = 1 := by simpa only [biasSet, Finset.mem_filter,
    Finset.mem_univ, true_and] using hi
  have hn : ¬maskBit out i = true := by
    intro hm
    have h2 := (hout i).mp hm
    rw [h1] at h2
    exact (by decide : (1 : Fin 3) ≠ 2) h2
  cases hm : maskBit out i
  · rfl
  · exact (hn hm).elim

/-- The formal ternary channel is the literal mask/bias kernel, coordinate by
coordinate. This is an exact identity, before an energy bound. -/
theorem channel_eq_kernel (a : Fin 4 → Fin 3) (out : Fin 16)
    (hout : ∀ i : Fin 4, maskBit out i = true ↔ a i = 2) :
    BiasStartup.channel a =
      MixedTensorEnergy.kernel (0 : AES.Word) out (biasSet a) residual := by
  funext y x
  change (∏ i : Fin 4,
    UniformBias.channelPiece AES.wordSuperboxKernel (0 : AES.Word)
      (a i) (y i) (x i)) =
    ∏ i : Fin 4, if maskBit out i = true then residual (y i) (x i)
      else if i ∈ biasSet a then UniformBias.biasKernel (0 : AES.Word) (y i) (x i)
      else UniformBias.uniformKernel (y i) (x i)
  apply Finset.prod_congr rfl
  intro i _
  have hs : i ∈ biasSet a ↔ a i = 1 := by simp [biasSet]
  simp only [hout i, hs]
  generalize ha : a i = t
  fin_cases t <;> simp [UniformBias.channelPiece, WordRestrictedResponse.residual]

/-- Among the 81 literal patterns, the pure degree-one patterns are exactly
the four checked single-R patterns. This certificate involves labels only. -/
theorem pure_one_eq_singleR : ∀ a : Fin 4 → Fin 3,
    residualIndex a = 1 → biasCount a = 0 →
      ∃ c : Fin 4, a = BiasStartup.singleR c := by
  decide

theorem singleR_scaled_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (c : Fin 4) :
    q ^ 5 * (∑ y, action (BiasStartup.channel (BiasStartup.singleR c))
      (BiasStartup.inputLaw b) y ^ 2) ≤ 441 / 100 := by
  rw [BiasStartup.singleR_channel]
  apply SingleResidualJ.scaled_energy_le
  simpa only [BiasStartup.inputLaw, ManySourceLaw.wordMarginal] using
    ManySourceBounds.marginal_energy_le b hb c

theorem scaled_four_denominator (c : ℝ) :
    q ^ 5 * (c / q ^ 4) = q * c := by
  field_simp [ResponseScalarBounds.q_ne_zero]
  <;> ring

/-- Actual per-pattern budget domination. Positive degree counts only R,
and the source-count premise is distinct from that output degree. -/
theorem pattern_energy_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (a : Fin 4 → Fin 3) (hr : residualIndex a ≠ 0) :
    q ^ 5 * (∑ y, action (BiasStartup.channel a) (BiasStartup.inputLaw b) y ^ 2) ≤
      budget a := by
  have hq : 0 ≤ q ^ 5 := pow_nonneg ResponseScalarBounds.q_positive.le _
  by_cases hz : biasCount a = 0
  · by_cases h1 : residualIndex a = 1
    · obtain ⟨c, hc⟩ := pure_one_eq_singleR a h1 hz
      rw [MixedDegreeBudgets.budget_pure_one a h1 hz, hc]
      exact singleR_scaled_energy_le b hb c
    · have hr0 : (residualIndex a).val ≠ 0 := by
        intro h
        exact hr (Fin.ext h)
      have hr1 : (residualIndex a).val ≠ 1 := by
        intro h
        exact h1 (Fin.ext h)
      have hr2 : 2 ≤ (residualIndex a).val := by omega
      obtain ⟨out, hout, hsize⟩ := residual_mask_exists a
      have hout2 : 2 ≤ maskSize out := by omega
      have henergy := MixedTermBounds.pure_residual_energy_le b hb out hout2
      rw [MixedDegreeBudgets.budget_pure_many a hr2 hz,
        channel_eq_kernel a out hout, biasSet_eq_empty a hz]
      calc
        _ ≤ q ^ 5 * ((6 / 5 : ℝ) ^ 4 * nu ^ 4 / q ^ 4) :=
          mul_le_mul_of_nonneg_left henergy hq
        _ = _ := by rw [scaled_four_denominator]; ring
  · obtain ⟨out, hout, hsize⟩ := residual_mask_exists a
    have hd := bias_residual_disjoint a out hout
    have hr0 : (residualIndex a).val ≠ 0 := by
      intro h
      exact hr (Fin.ext h)
    have hj : 0 < maskSize out := by omega
    have henergy := MixedTermBounds.mixed_energy_le b (by omega) out (biasSet a) hd hj
    rw [MixedDegreeBudgets.budget_mixed a hr hz, channel_eq_kernel a out hout]
    calc
      _ ≤ q ^ 5 * ((6 / 5 : ℝ) ^ 4 * nu ^ 2 *
          (441 / (q - 1)) ^ (biasSet a).card / q ^ 4) :=
        mul_le_mul_of_nonneg_left henergy hq
      _ = _ := by
        rw [scaled_four_denominator, biasSet_card]
        unfold MixedDegreeBudgets.B
        ring

end AESPaper.ActualMixedPatternBounds
