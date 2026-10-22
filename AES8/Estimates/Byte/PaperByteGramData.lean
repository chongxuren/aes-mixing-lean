import AES8.Model.PaperByteTrace
import AESConcrete.ByteGramResources
import Mathlib.Tactic.FinCases
import AES8.Estimates.Byte.PaperCitedByteBounds
import AES8.Estimates.Byte.PaperByteGramPrinted

/-! Literal trace-character, Kloosterman and off-diagonal multiplicity
statements for the paper's byte Gram data. Existing exact Gram resources
are reused; the zero term of the Walsh sum is removed explicitly. -/
-- The Kloosterman estimate is our deduction from the exact cited Walsh
-- interface; the existing concrete provider preserves the public statement.
noncomputable section
open scoped BigOperators
namespace AES8.PaperByteGramData
open AESMixing PaperByteTrace AESConcrete.ByteGramCore
open AESConcrete.ByteGramDiagonal AESConcrete.ByteGramFourier AESConcrete.ByteGramResources
open AESConcrete.ByteOrientations (Orientation channel)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable
abbrev Byte := BinaryWord 8

def kloosterman (z : Byte) : ℝ :=
  ∑ x : {x : Byte // x ≠ 0}, traceCharacter (x.val + z/x.val)

theorem kloosterman_eq_walsh (z : Byte) :
    kloosterman z = fieldWalsh byteCharacter (fun x => x⁻¹) 1 z - 1 := by
  unfold fieldWalsh
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun x : Byte => byteCharacter (1*x+z*x⁻¹)) 0]
  simp only [mul_zero, inv_zero, add_zero, byteCharacter_zero, one_mul]
  unfold kloosterman
  simp only [traceCharacter_eq, div_eq_mul_inv]
  ring

theorem kloosterman_bounds_of_walsh (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (z : Byte) : -33 ≤ kloosterman z ∧ kloosterman z ≤ 31 := by
  rw [kloosterman_eq_walsh]
  have h := hWalsh 1 z one_ne_zero
  constructor <;> nlinarith

theorem kloosterman_bounds (z : Byte) : -33 ≤ kloosterman z ∧ kloosterman z ≤ 31 :=
  kloosterman_bounds_of_walsh PaperCitedByteBounds.concreteWalshBound z

/-- The Gram formula uses the explicitly defined absolute field trace. -/
theorem gram_trace_formula (x y : Byte) (hx : x ≠ 0) (hy : y ≠ 0) :
    inversionGram x y =
      ((256+4)/256^2 : ℝ) * (if x=y then 1 else 0) +
      (2/256^2 : ℝ) * (traceCharacter (x/y) + traceCharacter (y/x)) -
      1/(256*255) := by
  simp only [traceCharacter_eq]
  convert inversion_gram_nonzero x y hx hy using 1 <;> norm_num

/-- An exact ratio count, including the zero and diagonal exclusions. -/
def numeratorCount (v : ℤ) : ℕ :=
  ∑ c : Fin 256, if c ≠ 0 ∧ c ≠ 1 ∧
    AESConcrete.ByteGramFinite.numerator (BitVec.ofFin c) = v then 1 else 0

theorem numerator_counts : numeratorCount 191 = 70 ∧ numeratorCount (-64) = 112 ∧
    numeratorCount (-319) = 72 := by decide

def rowCount (x : Byte) (v : ℤ) : ℕ :=
  ∑ y : Byte, if y ≠ 0 ∧ y ≠ x ∧
    inversionGram x y = (v : ℝ)/4177920 then 1 else 0

theorem rowCount_eq (x : Byte) (hx : x ≠ 0) (v : ℤ) :
    rowCount x v = numeratorCount v := by
  unfold rowCount
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ x hx)]
  change (∑ c : Byte, if x*c ≠ 0 ∧ x*c ≠ x ∧
    inversionGram x (x*c) = (v : ℝ)/4177920 then 1 else 0) = numeratorCount v
  have hterm (c : Byte) :
      (if x*c ≠ 0 ∧ x*c ≠ x ∧ inversionGram x (x*c) = (v : ℝ)/4177920 then (1 : ℕ) else 0) =
      if c ≠ 0 ∧ c ≠ 1 ∧ AESConcrete.ByteGramFinite.numerator c.bits = v then 1 else 0 := by
    rw [inversion_gram_ratio]
    have hratio : x*c/x = c := by field_simp
    rw [hratio]
    have hzero : x*c ≠ 0 ↔ c ≠ 0 := by simp [hx]
    have hone : x*c ≠ x ↔ c ≠ 1 := by
      constructor
      · intro h hc; apply h; rw [hc, mul_one]
      · intro h hh; apply h; apply mul_left_cancel₀ hx; simpa using hh
    have heq : (AESConcrete.ByteGramFinite.numerator c.bits : ℝ)/4177920 =
        (v : ℝ)/4177920 ↔ AESConcrete.ByteGramFinite.numerator c.bits = v := by
      constructor
      · intro h
        have hh : (AESConcrete.ByteGramFinite.numerator c.bits : ℝ) = (v : ℝ) := by linarith
        exact_mod_cast hh
      · intro h; rw [h]
    simp only [hzero, hone, heq]
  simp_rw [hterm]
  rw [← Equiv.sum_comp (BinaryWord.equivFin 8).symm]
  unfold numeratorCount
  apply Finset.sum_congr rfl
  intro c _
  have h0 : (BinaryWord.equivFin 8).symm c = (0 : Byte) ↔ c = 0 := by
    exact Equiv.symm_apply_eq (BinaryWord.equivFin 8)
  have h1 : (BinaryWord.equivFin 8).symm c = (1 : Byte) ↔ c = 1 := by
    exact Equiv.symm_apply_eq (BinaryWord.equivFin 8)
  change (if (BinaryWord.equivFin 8).symm c ≠ 0 ∧ (BinaryWord.equivFin 8).symm c ≠ 1 ∧
    AESConcrete.ByteGramFinite.numerator (BitVec.ofFin c) = v then (1 : ℕ) else 0) = _
  simp only [ne_eq, h0, h1]

theorem row_multiplicities (x : Byte) (hx : x ≠ 0) :
    rowCount x 191 = 70 ∧ rowCount x (-64) = 252-2*70 ∧ rowCount x (-319) = 70+2 := by
  simp only [rowCount_eq x hx]
  exact numerator_counts

theorem actual_diagonal (o : Orientation) (x : Byte) (hx : x ≠ 0) :
    residualGram (channel o) x x = 16766/4177920 := by
  rw [actual_gram_diagonal, if_neg hx]
  norm_num

/-- All actual Gram resources are attached to the same orientation family. -/
-- The moment now consumes the printed Walsh/Kloosterman/count argument.
-- The stronger exact finite multiplicities above are extra facts, not premises.
theorem actual_resources (o : Orientation) :
    (∀ x, residualGram (channel o) 0 x = 0 ∧ residualGram (channel o) x 0 = 0) ∧
    (∀ x, x ≠ 0 → residualGram (channel o) x x = 16766/4177920) ∧
    (∀ x y, x ≠ y → -(319/4177920 : ℝ) ≤ residualGram (channel o) x y ∧
      residualGram (channel o) x y ≤ 191/4177920) ∧
    (∑ x, ∑ y, residualGram (channel o) x y^2) ≤ 571447/(2 : ℝ)^27 :=
  ⟨fun x => ⟨actual_gram_zero_row o x, actual_gram_zero_column o x⟩,
    actual_diagonal o, actual_gram_offdiagonal o,
    PaperByteGramPrinted.actual_gram_square_moment_le o⟩

end AES8.PaperByteGramData
