import AESPaper.ActualZeroEvents
import AESPaper.PureBiasBounds
import AESMixing.IncidenceCounting

/-!
# Actual pure J/Z startup terms beyond the single-bias patterns

A subset of bias positions identifies a literal ternary pattern with no R
labels. The actual boundary law is nonnegative, and its unnormalized joint
zero-event bounds instantiate the generic pure-bias estimate. Distinct subsets
give orthogonal actual terms, so the multiple-bias sum has exactly the sum of
their energies. A finite cardinality sum and exact rational arithmetic supply the stated
scaled budget. The singleton budget is inherited from the checked single-Z
result.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace AESPaper.PureBiasStartup
open AESMixing AESConcrete
open AESPaper.StartingWord (q)
open AESPaper.ManySourceBounds (activeSourceCount)

/-- Bias at S, with full uniform at every other word coordinate. -/
def purePattern (S : Finset (Fin 4)) : Fin 4 → Fin 3 :=
  fun i => if i ∈ S then 1 else 0

theorem purePattern_injective : Function.Injective purePattern := by
  intro S T h
  apply Finset.ext
  intro i
  constructor
  · intro hi
    by_contra hn
    have he := congrFun h i
    simp only [purePattern, if_pos hi, if_neg hn] at he
    norm_num at he
  · intro hi
    by_contra hn
    have he := congrFun h i
    simp only [purePattern, if_neg hn, if_pos hi] at he
    norm_num at he

/-- Z factors do not count as residual-word degree. -/
theorem purePattern_residualIndex : ∀ S : Finset (Fin 4),
    TernaryDegree.residualIndex (purePattern S) = 0 := by decide

theorem purePattern_singleton (c : Fin 4) : purePattern {c} = BiasStartup.singleZ c := by
  funext i
  simp only [purePattern, Finset.mem_singleton, BiasStartup.singleZ]

theorem pure_channel (S : Finset (Fin 4)) :
    BiasStartup.channel (purePattern S) = BiasTensorEnergy.kernel (0 : AES.Word) S := by
  funext y x
  change (∏ i, UniformBias.channelPiece AES.wordSuperboxKernel (0 : AES.Word)
    (purePattern S i) (y i) (x i)) =
    ∏ i, if i ∈ S then UniformBias.biasKernel (0 : AES.Word) (y i) (x i)
      else UniformBias.uniformKernel (y i) (x i)
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [purePattern, hi, UniformBias.channelPiece]

theorem input_nonnegative (b : AES.State) (x : AES.WordState) :
    0 ≤ BiasStartup.inputLaw b x := by
  rw [BiasStartup.inputLaw, GroupedRecurrence.Pi_apply, StartingWord.grouped_initial_product]
  exact Finset.prod_nonneg (fun i _ => StartingWord.wordLaw_nonnegative _ _)

/-- Every joint zero-event cap is supplied by the actual source/boundary proof. -/
theorem per_subset_energy_le (b : AES.State) (hb : 0 < activeSourceCount b)
    (S : Finset (Fin 4)) :
    (∑ y, BiasStartup.term b (purePattern S) y ^ 2) ≤
      (1/q^4) * (441/(q-1)) ^ S.card := by
  have he (D : Finset (Fin 4)) (_hD : D ⊆ S) :
      BiasTensorEnergy.jointZeroMass (0 : AES.Word) (BiasStartup.inputLaw b) D ≤
        (20/(Fintype.card AES.Word : ℝ)) ^ D.card := by
    simpa only [ActualZeroEvents.zeroMass, StartingWord.q_eq_word_card] using
      ActualZeroEvents.actual_zeroMass_le b hb D
  have h := PureBiasBounds.energy_le (0 : AES.Word) AES.word_card_gt_one S
    (BiasStartup.inputLaw b) (input_nonnegative b) he
  simpa only [BiasStartup.term, ← pure_channel S, ← StartingWord.q_eq_word_card] using h

theorem orthogonal (b : AES.State) (S T : Finset (Fin 4)) (hST : S ≠ T) :
    (∑ y, BiasStartup.term b (purePattern S) y *
      BiasStartup.term b (purePattern T) y) = 0 :=
  BiasStartup.orthogonal b _ _ (fun h => hST (purePattern_injective h))

/-- Sum of precisely the patterns having at least two bias coordinates. -/
def multipleBias (b : AES.State) (y : AES.WordState) : ℝ :=
  ∑ S : Finset (Fin 4), if 2 ≤ S.card then BiasStartup.term b (purePattern S) y else 0

theorem multiple_sum_energy (b : AES.State) :
    (∑ y, multipleBias b y ^ 2) = ∑ S : Finset (Fin 4), if 2 ≤ S.card then
      (∑ y, BiasStartup.term b (purePattern S) y ^ 2) else 0 := by
  have ho (S T : Finset (Fin 4)) (hST : S ≠ T) :
      (∑ y, (if 2 ≤ S.card then BiasStartup.term b (purePattern S) y else 0) *
        (if 2 ≤ T.card then BiasStartup.term b (purePattern T) y else 0)) = 0 := by
    by_cases hS : 2 ≤ S.card <;> by_cases hT : 2 ≤ T.card <;>
      simp only [hS, hT, if_true, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
    exact orthogonal b S T hST
  have h := orthogonal_family_energy
    (fun (S : Finset (Fin 4)) y => if 2 ≤ S.card then BiasStartup.term b (purePattern S) y else 0) ho
  unfold multipleBias
  rw [h]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : 2 ≤ S.card <;> simp [hS]

/-- The finite subset sum is reduced by cardinality before rational arithmetic. -/
theorem numeric_multiple_bound_real :
    q^5 * (∑ S : Finset (Fin 4), if 2 ≤ S.card then
      (1/q^4) * (441/(q-1)) ^ S.card else 0) < 855/1000000 := by
  have h := powerset_size_sum (Finset.univ : Finset (Fin 4))
    (fun n => if 2 ≤ n then (1/q^4) * (441/(q-1))^n else 0)
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  norm_num [Finset.sum_range_succ, Nat.choose, q]

theorem multiple_total_scaled_energy_lt (b : AES.State) (hb : 0 < activeSourceCount b) :
    q^5 * (∑ S : Finset (Fin 4), if 2 ≤ S.card then
      (∑ y, BiasStartup.term b (purePattern S) y ^ 2) else 0) < 855/1000000 := by
  have hs : (∑ S : Finset (Fin 4), if 2 ≤ S.card then
      (∑ y, BiasStartup.term b (purePattern S) y ^ 2) else 0) ≤
      ∑ S : Finset (Fin 4), if 2 ≤ S.card then
        (1/q^4) * (441/(q-1)) ^ S.card else 0 := by
    apply Finset.sum_le_sum
    intro S _
    by_cases hS : 2 ≤ S.card
    · simp only [if_pos hS]
      exact per_subset_energy_le b hb S
    · simp [hS]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hs (by norm_num [q])) numeric_multiple_bound_real

/-- This is the energy of the actual sum vector, not merely a list of caps. -/
theorem multiple_sum_scaled_energy_lt (b : AES.State) (hb : 0 < activeSourceCount b) :
    q^5 * (∑ y, multipleBias b y ^ 2) < 855/1000000 := by
  rw [multiple_sum_energy]
  exact multiple_total_scaled_energy_lt b hb

/-- Singleton subsets are exactly the four previously bounded single-Z terms. -/
theorem singleton_sum_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, (∑ c : Fin 4, BiasStartup.term b (purePattern {c}) y) ^ 2) <
      1000001/250000 := by
  simpa only [purePattern_singleton] using BiasStartup.singleZ_sum_scaled_energy_lt b hb

end AESPaper.PureBiasStartup
