import AESMixing.TupleKeys
import AESMixing.PhysicalLayers

/-! Exact identification of the physical AES retained-key pair experiment
with its Markov difference law, at every number of rounds. This does not
assume or conclude a mixing rate. The final layer omits MixColumns. -/
noncomputable section
open scoped BigOperators
namespace AESMixing.AES

def ordinaryPrefix (n : ℕ) (keys : Fin (n+1) → State) (x : State) : State :=
  ordinaryRounds n keys (x + keys 0)

theorem ordinaryPrefix_zero : ordinaryPrefix 0 =
    fun keys : Fin 1 → State => fun x => x + keys 0 := rfl

theorem ordinaryPrefix_succ (n : ℕ) : ordinaryPrefix (n+1) =
    fun keys : Fin (n+2) → State => fun x =>
      ordinaryLayer (ordinaryPrefix n (Fin.init keys) x) + keys (Fin.last (n+1)) := rfl

def ordinaryDifferenceLaw : ℕ → State → State → ℝ
  | 0, a => differencePoint a
  | n+1, a => action (differenceChannel ordinaryLayer) (ordinaryDifferenceLaw n a)

def physicalDifferenceLaw : ℕ → State → State → ℝ
  | 0, a => differencePoint a
  | n+1, a => action (differenceChannel finalLayer) (ordinaryDifferenceLaw n a)

theorem ordinaryPrefix_pair (n : ℕ) (x x' : State) :
    retainedPairLaw (ordinaryPrefix n) (uniformKeyWeight (n+1)) x x' =
      pairFromDifference (ordinaryDifferenceLaw n (x'-x)) := by
  induction n with
  | zero => exact retained_whitening x x'
  | succ n ih =>
    rw [ordinaryPrefix_succ, retained_tuple_step, ih, keyedPair_difference]
    rfl

theorem encrypt_final_tuple (n : ℕ) : encrypt (n+1) =
    fun keys : Fin (n+2) → State => fun x =>
      finalLayer (ordinaryPrefix n (Fin.init keys) x) + keys (Fin.last (n+1)) := rfl

theorem encrypt_pair_difference (r : ℕ) (x x' : State) :
    retainedPairLaw (encrypt r) (uniformKeyWeight (r+1)) x x' =
      pairFromDifference (physicalDifferenceLaw r (x'-x)) := by
  cases r with
  | zero => exact retained_whitening x x'
  | succ n =>
    rw [encrypt_final_tuple, retained_tuple_step, ordinaryPrefix_pair, keyedPair_difference]
    rfl

theorem pairLaw_retained (r : ℕ) (x x' : State) :
    pairLaw r x x' = retainedPairLaw (encrypt r) (uniformKeyWeight (r+1)) x x' := by
  funext y
  simp only [pairLaw, retainedPairLaw, uniformKeyWeight, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, one_div_mul_eq_div, Finset.sum_div]

theorem pairLaw_difference (r : ℕ) (x x' : State) :
    pairLaw r x x' = pairFromDifference (physicalDifferenceLaw r (x'-x)) := by
  rw [pairLaw_retained, encrypt_pair_difference]

theorem randomPermutationPair_difference :
    randomPermutationPair = pairFromDifference (uniformExcept (0 : State)) := by
  funext y
  have he : y.2-y.1 = 0 ↔ y.1 = y.2 := sub_eq_zero.trans eq_comm
  simp only [randomPermutationPair, pairFromDifference, uniformExcept, he,
    state_card, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : y.1 = y.2
  · simp [h]
  · simp only [h, if_false]
    ring

theorem physical_pair_tv (r : ℕ) (x x' : State) :
    tv (pairLaw r x x') randomPermutationPair =
      tv (physicalDifferenceLaw r (x'-x)) (uniformExcept (0 : State)) := by
  rw [pairLaw_difference, randomPermutationPair_difference, tv_pairFromDifference]

end AESMixing.AES
