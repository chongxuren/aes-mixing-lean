import AESMixing.MDSCertificate
import Mathlib.Data.Fintype.EquivFin

/-! Connect the binary-basis certificates to the physical AES specification.
Multiplication order is justified explicitly; no field instance is assumed. -/
namespace AESMixing.AES
open scoped BigOperators

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem mul_small_comm_fin (c : Fin 4) (x : Fin 256) :
    mul (BitVec.ofNat 8 c.val) (BitVec.ofFin x) =
      mul (BitVec.ofFin x) (BitVec.ofNat 8 c.val) := by
  fin_cases c <;> fin_cases x <;> decide

theorem mixEntry_comm (i j : Fin 4) (x : Byte) :
    mul (mixEntry i j) x = mul x (mixEntry i j) := by
  have h : mixEntry i j = 1 ∨ mixEntry i j = 2 ∨ mixEntry i j = 3 := by
    fin_cases i <;> fin_cases j <;> decide
  rcases h with h | h | h
  · rw [h]; exact mul_small_comm_fin 1 x.toFin
  · rw [h]; exact mul_small_comm_fin 2 x.toFin
  · rw [h]; exact mul_small_comm_fin 3 x.toFin

theorem mixColumns_column (x : State) (col : Fin 4) :
    (fun row => mixColumns x row col) = columnMatrix mixEntry (fun row => x row col) := by
  funext row
  unfold mixColumns columnMatrix scale
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  exact BinaryWord.ext (mixEntry_comm row i (x i col).bits)

theorem projectMask_full (x : Fin 4 → BinaryWord 8) : projectMask 15 x = x := by
  have h : ∀ i : Fin 4, maskBit 15 i = true := by decide
  funext i
  simp [projectMask, h]

theorem mixColumn_left_inverse : Function.LeftInverse
    (columnMatrix (minorInverse 15 15)) (columnMatrix mixEntry) := by
  intro x
  simpa only [projectMask_full] using mds_reconstruction 15 15 rfl x

theorem mixColumn_injective : Function.Injective (columnMatrix mixEntry) :=
  mixColumn_left_inverse.injective

theorem mixColumns_injective : Function.Injective mixColumns := by
  intro x y h
  funext row col
  have hc : columnMatrix mixEntry (fun r => x r col) =
      columnMatrix mixEntry (fun r => y r col) := by
    rw [← mixColumns_column, ← mixColumns_column, h]
  exact congrFun (mixColumn_injective hc) row

theorem physical_mixColumns_mds_zero (r c : Fin 16) (h : maskSize r = maskSize c)
    (x : State) (col : Fin 4) (hs : projectMask c (fun row => x row col) = fun row => x row col)
    (hz : projectMask r (fun row => mixColumns x row col) = 0) :
    (fun row => x row col) = 0 := by
  rw [mixColumns_column] at hz
  exact mixColumns_mds_zero r c h _ hs hz

theorem invShiftRows_left_inverse : Function.LeftInverse invShiftRows shiftRows := by
  intro x
  funext row col
  change x row (col - row + row) = x row col
  have h : col - row + row = col := by fin_cases col <;> fin_cases row <;> decide
  rw [h]

theorem shiftRows_injective : Function.Injective shiftRows :=
  invShiftRows_left_inverse.injective

theorem subBytes_injective : Function.Injective subBytes := by
  intro x y h
  funext row col
  exact BinaryWord.sboxPerm.injective (congrFun (congrFun h row) col)

theorem round_injective (key : State) : Function.Injective (fun x => round x key) := by
  intro x y h
  exact subBytes_injective (shiftRows_injective (mixColumns_injective (add_right_cancel h)))

theorem finalRound_injective (key : State) : Function.Injective (fun x => finalRound x key) := by
  intro x y h
  exact subBytes_injective (shiftRows_injective (add_right_cancel h))

theorem ordinaryRounds_injective (n : ℕ) (keys : Fin (n + 1) → State) :
    Function.Injective (ordinaryRounds n keys) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    intro x y h
    exact ih _ (round_injective _ h)

theorem encrypt_injective (r : ℕ) (keys : Fin (r + 1) → State) :
    Function.Injective (encrypt r keys) := by
  cases r with
  | zero => intro x y h; exact add_right_cancel h
  | succ n =>
    intro x y h
    exact add_right_cancel (ordinaryRounds_injective n _ (finalRound_injective _ h))

theorem encrypt_bijective (r : ℕ) (keys : Fin (r + 1) → State) :
    Function.Bijective (encrypt r keys) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨encrypt_injective r keys, rfl⟩

noncomputable def encryptPerm (r : ℕ) (keys : Fin (r + 1) → State) : Equiv.Perm State :=
  Equiv.ofBijective (encrypt r keys) (encrypt_bijective r keys)

theorem pairLaw_diagonal (r : ℕ) (x x' y : State) (h : x ≠ x') :
    pairLaw r x x' (y, y) = 0 := by
  have hn (keys : Fin (r + 1) → State) :
      ¬ (encrypt r keys x = y ∧ encrypt r keys x' = y) := by
    rintro ⟨h1, h2⟩
    exact h (encrypt_injective r keys (h1.trans h2.symm))
  simp [pairLaw, hn]

end AESMixing.AES
