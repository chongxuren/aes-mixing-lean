import AESConcrete.ActivityFrame
import AESMixing.Generated.GramLDL_F0
import AESMixing.Generated.GramLDL_I0
import AESMixing.CenteredActivityGram
import Mathlib.Data.Rat.BigOperators

/-!
# Exact rational inverse-frame activity traces

These are finite scalar evaluations of the source-bound raw activity Gram
numerators. The actual AES trace correspondence is supplied separately.
The invariant correction is subtracted exactly once. No floating point,
native_decide, external oracle or assumed numerical certificate is used.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityTraceNumbers
open AESMixing AESMixing.AES

set_option maxRecDepth 100000

def inverseEntry (a b : Fin 16) : ℚ :=
  ∏ i : Fin 4, (256 / 255 : ℚ) * if maskBit a i = maskBit b i then 1 else -(1/16)

def traceEntry (N : Fin 16 → Fin 16 → ℤ) (a b : Fin 16) : ℚ :=
  inverseEntry a b * ((N a b : ℚ)/255^4 - GramNumeric.F0.fixed a b) /
    (16^maskSize a * 16^maskSize b)

theorem maskBit_arithmetic : ∀ (a : Fin 16) (i : Fin 4),
    maskBit a i = decide (a.val / 2^i.val % 2 = 1) := by decide

theorem forward_trace_number :
    (∑ a : Fin 16, ∑ b : Fin 16, traceEntry GramNumeric.F0.numerator a b) =
      (68*256^2+264*256+68 : ℚ)/255^6 := by
  simp only [traceEntry, inverseEntry, GramNumeric.F0.fixed]
  simp_rw [maskBit_arithmetic, GramNumeric.F0.maskSize_table]
  norm_num [GramNumeric.F0.numerator, Fin.sum_univ_succ, Fin.prod_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem inverse_trace_number :
    (∑ a : Fin 16, ∑ b : Fin 16, traceEntry GramNumeric.I0.numerator a b) =
      (68*256^2+264*256+68 : ℚ)/255^6 := by
  simp only [traceEntry, inverseEntry, GramNumeric.F0.fixed]
  simp_rw [maskBit_arithmetic, GramNumeric.F0.maskSize_table]
  norm_num [GramNumeric.I0.numerator, Fin.sum_univ_succ, Fin.prod_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem inverseEntry_cast (a b : Fin 16) : (inverseEntry a b : ℝ) =
    ActivityFrame.frameInverse (maskBit a) (maskBit b) := by
  simp only [inverseEntry, ActivityFrame.frameInverse, ActivityFrame.byteInverse]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem traceEntry_cast (N : Fin 16 → Fin 16 → ℤ) (a b : Fin 16) :
    (traceEntry N a b : ℝ) =
      ActivityFrame.frameInverse (maskBit a) (maskBit b) *
        ((N a b : ℝ)/255^4 - invariantActivityGram 256 a b) /
        (16^maskSize a *16^maskSize b) := by
  simp only [traceEntry]
  push_cast
  rw [inverseEntry_cast]
  simp only [GramNumeric.F0.fixed, invariantActivityGram]
  push_cast
  rfl

end AESConcrete.ActivityTraceNumbers
