import AESConcrete.WordFourierCore

/-!
# Absolute trace on the concrete AES polynomial field

The absolute trace is the standard eight-term Frobenius sum, valued in the
ambient byte field. Its concrete value is exactly zero or one according to
the existing two-bit `AES.traceBit`. Thus the character, multiplication
pairing and normalized byte/word Fourier kernels have their literal trace
formulas on the original physical labels.

The only finite certificate evaluates this fixed semantics on all 256 bytes
with ordinary kernel `decide`. No search, `native_decide`, legacy edits or
manuscript edits are used. A separate Mathlib `Algebra.trace` scalar-space
interface is not constructed here; the explicit Frobenius formula is the
finite-field absolute trace used by the paper.
-/

noncomputable section
open scoped BigOperators

namespace AES8.ByteTrace
open AESMixing

abbrev Byte := BinaryWord 8
abbrev Word := Fin 4 → Byte

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- The absolute trace F_256/F_2, represented in the ambient AES byte field. -/
def absoluteTrace (x : Byte) : Byte := ∑ i : Fin 8, x ^ (2 ^ i.val)

-- Editorial: repeated squaring keeps the finite semantic certificate small;
-- the abstract power identity below connects it to the displayed trace sum.
private def squarePower : ℕ → Byte → Byte
  | 0, x => x
  | n + 1, x => squarePower n x * squarePower n x

private theorem squarePower_eq_pow (n : ℕ) (x : Byte) :
    squarePower n x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp [squarePower]
  | succ n ih =>
    rw [squarePower, ih, ← pow_add]
    congr 1
    simp [pow_succ, Nat.mul_two]

private def concreteTrace (x : AES.Byte) : AES.Byte :=
  let x2 := AES.mul x x
  let x4 := AES.mul x2 x2
  let x8 := AES.mul x4 x4
  let x16 := AES.mul x8 x8
  let x32 := AES.mul x16 x16
  let x64 := AES.mul x32 x32
  let x128 := AES.mul x64 x64
  x ^^^ (x2 ^^^ (x4 ^^^ (x8 ^^^ (x16 ^^^ (x32 ^^^ (x64 ^^^ (x128 ^^^ 0)))))))

private theorem sum_fin_zero (f : Fin 0 → Byte) : (∑ i, f i) = 0 := by simp

private theorem absoluteTrace_bits (x : Byte) :
    (absoluteTrace x).bits = concreteTrace x.bits := by
  unfold absoluteTrace
  simp only [← squarePower_eq_pow, Fin.sum_univ_succ, sum_fin_zero]
  rfl

-- User-authorized exact semantics check; this is not a numerical search.
private theorem concreteTrace_certificate (x : Fin 256) :
    concreteTrace (BitVec.ofFin x) =
      if AES.traceBit (BitVec.ofFin x) then 1 else 0 := by
  fin_cases x <;> decide

/-- The implemented bit parity is exactly the absolute/Frobenius trace. -/
theorem absoluteTrace_eq_traceBit (x : Byte) :
    absoluteTrace x = if AES.traceBit x.bits then 1 else 0 := by
  apply BinaryWord.ext
  rw [absoluteTrace_bits]
  have h := concreteTrace_certificate x.bits.toFin
  cases ht : AES.traceBit x.bits
  · simp only [ht, Bool.false_eq_true, if_false] at h ⊢
    change concreteTrace x.bits = (0 : AES.Byte)
    exact h
  · simp only [ht, if_true] at h ⊢
    change concreteTrace x.bits = (1 : AES.Byte)
    exact h

theorem absoluteTrace_zero_or_one (x : Byte) :
    absoluteTrace x = 0 ∨ absoluteTrace x = 1 := by
  rw [absoluteTrace_eq_traceBit]
  cases AES.traceBit x.bits <;> simp

/-- The existing character is precisely the sign of the absolute trace. -/
theorem byteCharacter_eq_trace (x : Byte) :
    byteCharacter x = if absoluteTrace x = 0 then 1 else -1 := by
  rw [absoluteTrace_eq_traceBit]
  cases ht : AES.traceBit x.bits <;> simp [byteCharacter, ht]

theorem bytePairing_eq_trace (x y : Byte) :
    bytePairing.value x y = if absoluteTrace (x * y) = 0 then 1 else -1 :=
  byteCharacter_eq_trace (x * y)

/-- The byte Fourier kernel uses the trace pairing with counting normalization. -/
theorem byteFourier_eq_trace (x y : Byte) :
    byteFourierMatrix x y =
      (if absoluteTrace (x * y) = 0 then 1 else -1) / 16 := by
  exact congrArg (fun z : ℝ => z / 16) (byteCharacter_eq_trace (x * y))

theorem wordPairing_eq_trace (x y : Word) :
    AESConcrete.WordFourierCore.wordPairing.value x y =
      ∏ i : Fin 4, (if absoluteTrace (x i * y i) = 0 then (1 : ℝ) else -1) := by
  change (∏ i : Fin 4, byteCharacter (x i * y i)) = _
  apply Finset.prod_congr rfl
  intro i _
  exact byteCharacter_eq_trace (x i * y i)

/-- Literal bytewise trace formula for the existing normalized word transform. -/
theorem wordFourier_eq_trace (x y : Word) :
    AESConcrete.WordFourierCore.wordFourier x y =
      (∏ i : Fin 4, (if absoluteTrace (x i * y i) = 0 then (1 : ℝ) else -1)) /
        65536 := by
  rw [AESConcrete.WordFourierCore.wordFourier_coefficient, wordPairing_eq_trace]

end AES8.ByteTrace
