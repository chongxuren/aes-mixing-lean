import AESMixing.ByteProfile
import AESMixing.ByteWalshCertificate
import Mathlib.Tactic.NormNum

/-!
# Finite one-variable AES byte Gram arithmetic

Generated on the formal TS1000 Slurm node.  The Python arithmetic is diagnostic;
every displayed finite fact is checked below by ordinary kernel-producing
`decide`.  There is no native_decide, assumed table, or actual-channel estimate
in this module.  The separate ByteGramResources wrapper owns the bridge to the
actual inversion/AES Gram operators and all orientation/conjugacy arguments.

User scope: constructive proof support only; no attacks or manuscript edits.
The numerator is centered by the nonzero-byte activity projection.  Its
denominator is 4177920; the diagonal is 16766 at byte one.  The off-diagonal
profile uses nonzero multiplicative ratios other than one.
-/

namespace AESConcrete.ByteGramFinite
open scoped BigOperators

-- Set these before all finite reductions, including numerator_twice at byte one.
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev Byte := AESMixing.AES.Byte

def traceSign (c : Byte) : ℤ :=
  if AESMixing.AES.traceBit c then -1 else 1

def numerator (c : Byte) : ℤ :=
  if c = 0 then 0 else if c = 1 then 16766 else
    -319 + 255 *
      ((if AESMixing.AES.traceBit c then 0 else 1) +
       (if AESMixing.AES.traceBit (AESMixing.AES.invLookup c) then 0 else 1))

def numeratorFin (c : Fin 256) : ℤ := numerator (BitVec.ofFin c)

theorem numerator_zero : numerator 0 = 0 := by decide

theorem numerator_one : numerator 1 = 16766 := by decide

theorem numerator_offdiagonal_values (c : Byte) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    numerator c = -319 ∨ numerator c = -64 ∨ numerator c = 191 := by
  cases ht : AESMixing.AES.traceBit c <;>
    cases hi : AESMixing.AES.traceBit (AESMixing.AES.invLookup c) <;>
    norm_num [numerator, hc0, hc1, ht, hi]

/-- Integer form of -64 + (255/2)(chi(c)+chi(c^-1)) plus the diagonal
correction; it avoids rounding or an integer division by two. -/
theorem numerator_twice (c : Byte) (hc0 : c ≠ 0) :
    2 * numerator c = -128 + 255 *
      (traceSign c + traceSign (AESMixing.AES.invLookup c)) +
      33150 * (if c = 1 then 1 else 0) := by
  by_cases hc1 : c = 1
  · subst c
    decide
  · cases ht : AESMixing.AES.traceBit c <;>
      cases hi : AESMixing.AES.traceBit (AESMixing.AES.invLookup c) <;>
      norm_num [numerator, traceSign, hc0, hc1, ht, hi]

/-- Both traces vanish: positive off-diagonal numerator 191. -/
theorem trace_pair_false_false :
    (∑ c : Fin 256, if c ≠ 0 ∧ c ≠ 1 ∧
      AESMixing.AES.traceBit (BitVec.ofFin c) = false ∧
      AESMixing.AES.traceBit (AESMixing.AES.invLookup (BitVec.ofFin c)) = false
      then (1 : ℕ) else 0) = 70 := by decide

/-- Exactly one trace vanishes: off-diagonal numerator -64. -/
theorem trace_pair_mixed :
    (∑ c : Fin 256, if c ≠ 0 ∧ c ≠ 1 ∧
      AESMixing.AES.traceBit (BitVec.ofFin c) ≠
        AESMixing.AES.traceBit (AESMixing.AES.invLookup (BitVec.ofFin c))
      then (1 : ℕ) else 0) = 112 := by decide

/-- Both traces are one: negative off-diagonal numerator -319. -/
theorem trace_pair_true_true :
    (∑ c : Fin 256, if c ≠ 0 ∧ c ≠ 1 ∧
      AESMixing.AES.traceBit (BitVec.ofFin c) = true ∧
      AESMixing.AES.traceBit (AESMixing.AES.invLookup (BitVec.ofFin c)) = true
      then (1 : ℕ) else 0) = 72 := by decide

theorem numerator_sum_zero : (∑ c : Fin 256, numeratorFin c) = 0 := by decide

theorem numerator_square_sum :
    (∑ c : Fin 256, numeratorFin c ^ 2) =
      (16766 : ℤ)^2 + 70 * 191^2 + 112 * 64^2 + 72 * 319^2 := by decide

theorem numerator_abs_cube_sum :
    (∑ c : Fin 256, (numeratorFin c).natAbs ^ 3) =
      16766^3 + 70 * 191^3 + 112 * 64^3 + 72 * 319^3 := by decide

/-- The existing checked Walsh table fixes the Kloosterman coefficient at one.
No new Walsh table is asserted. -/
theorem kloosterman_one : AESMixing.AES.inversionWalshOne 1 = 32 := by
  rw [← AESMixing.AES.inversionWalshLookup_correct (1 : Byte)]
  decide

/-- Exact unnormalized mixed row coefficient at the extremal ratio one.
The actual GF entry additionally divides by 16 * 4177920. -/
theorem mixed_one :
    (∑ c : Fin 256, numeratorFin c * traceSign (BitVec.ofFin c)) = 53104 := by decide

/-- Scalar normalization only.  The wrapper separately proves that the
ordered-pair Gram square sum is 255 copies of this finite row. -/
theorem square_moment_normalization :
    (255 : ℚ) * (16766^2 + 70 * 191^2 + 112 * 64^2 + 72 * 319^2) /
      4177920^2 = 571447 / 2^27 := by norm_num

theorem mixed_cap_normalization :
    (53104 : ℚ) / (16 * 4177920) = 13276 / (4 * 4177920) := by norm_num

end AESConcrete.ByteGramFinite
