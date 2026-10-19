import AESMixing.AdaptiveView

/-! One fresh common round key acts on a retained pair experiment. The
pointwise identity below derives the difference-chain update from the joint
pair law, including the uniform first output. No independence of two oracle
evaluations is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def keyedPairKernel (s : Equiv.Perm V) (y u : V × V) : ℝ :=
  (∑ key, if s u.1 + key = y.1 ∧ s u.2 + key = y.2 then (1 : ℝ) else 0) /
    Fintype.card V

theorem keyedPairKernel_formula (s : Equiv.Perm V) (y u : V × V) :
    keyedPairKernel s y u =
      (if s u.2 - s u.1 = y.2 - y.1 then (1 : ℝ) else 0) / Fintype.card V := by
  have hy : y.1 + (y.2 - y.1) = y.2 := by simp
  simpa only [keyedPairKernel, hy] using
    output_key_pair (s u.1) (s u.2) y.1 (y.2 - y.1)

theorem keyedPair_difference (s : Equiv.Perm V) (p : V → ℝ) :
    action (keyedPairKernel s) (pairFromDifference p) =
      pairFromDifference (action (differenceChannel s) p) := by
  funext y
  have hc := Equiv.sum_comp (pairCoordinates (V := V)).symm
    (fun u => keyedPairKernel s y u * pairFromDifference p u)
  change (∑ u : V × V, keyedPairKernel s y (u.1, u.1 + u.2) *
      pairFromDifference p (u.1, u.1 + u.2)) =
    (∑ u, keyedPairKernel s y u * pairFromDifference p u) at hc
  rw [action, ← hc, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [keyedPairKernel_formula, pairFromDifference, add_sub_cancel_left]
  have hp (d : V) :
      (∑ x, ((if s (x + d) - s x = y.2 - y.1 then (1 : ℝ) else 0) /
        Fintype.card V) * (p d / Fintype.card V)) =
      differenceChannel s (y.2 - y.1) d * p d / Fintype.card V := by
    rw [← Finset.sum_mul, ← Finset.sum_div]
    unfold differenceChannel difference
    ring
  simp_rw [hp]
  rw [← Finset.sum_div]
  rfl

theorem pair_difference_step_tv (s : Equiv.Perm V) (p q : V → ℝ) :
    tv (action (keyedPairKernel s) (pairFromDifference p))
      (action (keyedPairKernel s) (pairFromDifference q)) ≤ tv p q := by
  rw [keyedPair_difference, keyedPair_difference, tv_pairFromDifference]
  exact tv_action_le _ (differenceChannel_nonneg s) (differenceChannel_column s) p q

theorem retained_pair_fresh_key {K : Type*} [Fintype K]
    (E : K → V → V) (weight : K → ℝ) (s : Equiv.Perm V) (x x' : V) :
    retainedPairLaw (fun k : K × V => fun z => s (E k.1 z) + k.2)
      (fun k => weight k.1 / Fintype.card V) x x' =
    action (keyedPairKernel s) (retainedPairLaw E weight x x') := by
  funext y
  have hind (k : K) (u : V × V) :
      (E k x = u.1 ∧ E k x' = u.2) ↔ (E k x, E k x') = u := by
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  simp only [retainedPairLaw, action]
  rw [Fintype.sum_prod_type]
  conv_rhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hind, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp only [keyedPairKernel, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro key _
  by_cases h : s (E k x) + key = y.1 ∧ s (E k x') + key = y.2
  · simp [h]
    ring
  · simp [h]

theorem retained_pair_difference_step {K : Type*} [Fintype K]
    (E : K → V → V) (weight : K → ℝ) (s : Equiv.Perm V)
    (x x' : V) (p : V → ℝ)
    (h : retainedPairLaw E weight x x' = pairFromDifference p) :
    retainedPairLaw (fun k : K × V => fun z => s (E k.1 z) + k.2)
      (fun k => weight k.1 / Fintype.card V) x x' =
    pairFromDifference (action (differenceChannel s) p) := by
  rw [retained_pair_fresh_key, h, keyedPair_difference]

end AESMixing
