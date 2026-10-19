import AESMixing.BinaryWord
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.BigOperators

/-! The paper's physical cipher experiment: independently uniform keys are
sampled as one tuple and reused for both evaluations. No key schedule is used.
This module specifies the target; it does not assert the mixing theorem. -/
namespace AESMixing.AES
open scoped BigOperators Matrix

abbrev State := Fin 4 → Fin 4 → BinaryWord 8

theorem state_card : Fintype.card State = 2 ^ 128 := by
  norm_num [State, Fintype.card_fun, BinaryWord.card]

def subBytes (x : State) : State := fun row col => BinaryWord.sboxPerm (x row col)

def shiftRows (x : State) : State := fun row col => x row (col + row)

def invShiftRows (x : State) : State := fun row col => x row (col - row)

def mixEntry : Fin 4 → Fin 4 → Byte :=
  !![2,3,1,1; 1,2,3,1; 1,1,2,3; 3,1,1,2]

def mixColumns (x : State) : State := fun row col =>
  ∑ i, (⟨mul (mixEntry row i) (x i col).bits⟩ : BinaryWord 8)

def round (x key : State) : State := mixColumns (shiftRows (subBytes x)) + key
def finalRound (x key : State) : State := shiftRows (subBytes x) + key

/-- Ordinary rounds 1 through n, after the input whitening has been applied. -/
def ordinaryRounds : (n : ℕ) → (Fin (n + 1) → State) → State → State
  | 0, _, x => x
  | n + 1, keys, x => round
      (ordinaryRounds n (fun i => keys i.castSucc) x) (keys (Fin.last (n + 1)))

/-- r substitution layers, with no MixColumns in the last layer.
The r=0 convention is whitening only and is irrelevant to the theorem r≥4. -/
def encrypt : (r : ℕ) → (Fin (r + 1) → State) → State → State
  | 0, keys, x => x + keys 0
  | n + 1, keys, x => finalRound
      (ordinaryRounds n (fun i => keys i.castSucc) (x + keys 0))
      (keys (Fin.last (n + 1)))

noncomputable def pairLaw (r : ℕ) (x x' : State) (y : State × State) : ℝ :=
  (∑ keys : Fin (r + 1) → State,
    if encrypt r keys x = y.1 ∧ encrypt r keys x' = y.2 then (1 : ℝ) else 0) /
      Fintype.card (Fin (r + 1) → State)

/-- Output pair law of a uniform random permutation on two distinct inputs. -/
noncomputable def randomPermutationPair (y : State × State) : ℝ :=
  if y.1 = y.2 then 0 else 1 / ((2 : ℝ)^128 * ((2 : ℝ)^128 - 1))

noncomputable def epsilon (r : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun inputs : State × State =>
    if inputs.1 = inputs.2 then 0 else tv (pairLaw r inputs.1 inputs.2) randomPermutationPair)

theorem pairLaw_nonnegative (r : ℕ) (x x' : State) (y : State × State) :
    0 ≤ pairLaw r x x' y := by
  unfold pairLaw
  positivity

theorem pairLaw_total (r : ℕ) (x x' : State) :
    (∑ y, pairLaw r x x' y) = 1 := by
  have hpoint (keys : Fin (r + 1) → State) :
      (∑ y : State × State,
        if encrypt r keys x = y.1 ∧ encrypt r keys x' = y.2 then (1 : ℝ) else 0) = 1 := by
    have hc (y : State × State) :
        (encrypt r keys x = y.1 ∧ encrypt r keys x' = y.2) ↔
          (encrypt r keys x, encrypt r keys x') = y := by
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    simp_rw [hc]
    simp
  unfold pairLaw
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hpoint]
  simp

end AESMixing.AES
