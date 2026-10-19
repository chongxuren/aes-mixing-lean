import AESPaper.WordMarkedEnergy

/-!
# Exact normalization of the actual marked code and its annihilator
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AESPaper.WordDualNormalization
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros uniformCount)
open AESPaper.WordMarkedMoment (Source)
open AESPaper.WordMarkedCode (markedCode)
attribute [local instance] Classical.propDecidable

theorem source_card_of_dimension (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4) :
    Fintype.card (Source m s) = (2^32 : ℕ)^d := by
  have h := WordMarkedResponse.boundary_source_card m s
  have he : 4 - (AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s)) = d := by omega
  simpa only [he] using h

theorem code_card_of_dimension (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) :
    Fintype.card (markedCode m s) = (2^32 : ℕ)^d := by
  have hh : 4 ≤ AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + Fintype.card (Marked m) := by omega
  rw [← Fintype.card_congr (WordMarkedCode.sourceCodeEquiv m s hh)]
  exact source_card_of_dimension m s d hd

theorem dual_card_of_dimension (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) :
    Fintype.card ((WordFourierCore.wordPairing.product (Marked m)).annihilator
      (markedCode m s)) = (2^32 : ℕ)^(Fintype.card (Marked m)-d) := by
  have h := (WordFourierCore.wordPairing.product (Marked m)).annihilator_card
    (markedCode m s)
  rw [code_card_of_dimension m s d hd hle, Fintype.card_fun,
    AES.word_card_exact] at h
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2^32 : ℕ)^d)
  rw [h, ← pow_add, Nat.sub_add_cancel hle]
  norm_num

theorem source_sqrt_card (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4) :
    Real.sqrt (Fintype.card (Source m s)) = (65536 : ℝ)^d := by
  rw [source_card_of_dimension m s d hd]
  push_cast
  rw [show (4294967296 : ℝ) = 65536^2 by norm_num, pow_right_comm,
    Real.sqrt_sq (by positivity)]

theorem dual_sqrt_card (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) :
    Real.sqrt (Fintype.card ((WordFourierCore.wordPairing.product (Marked m)).annihilator
      (markedCode m s))) = (65536 : ℝ)^(Fintype.card (Marked m)-d) := by
  rw [dual_card_of_dimension m s d hd hle]
  push_cast
  rw [show (4294967296 : ℝ) = 65536^2 by norm_num, pow_right_comm,
    Real.sqrt_sq (by positivity)]

/-- Generic scalar identity used when returning the dual unit code to its
raw enumeration. Both physical count equations are explicit premises. -/
theorem dual_power_ratio (ell d z t : ℕ) (hd : z+d=4)
    (hcount : ell+t+z=8) (hle : d ≤ ell) :
    ((65536 : ℝ)^d / 65536^t) / 65536^(ell-d) = 1 / 65536^z := by
  have he : t+(ell-d)=d+z := by omega
  rw [div_div, ← pow_add, he, pow_add]
  field_simp

/-- Actual frame contraction divided by the dual unit-source normalization
has exactly one inverse square-root alphabet factor per zero coordinate. -/
theorem actual_dual_normalization (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) +
      AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m)) :
    (Real.sqrt (Fintype.card (Source m s)) / (65536 : ℝ)^uniformCount s) /
        Real.sqrt (Fintype.card ((WordFourierCore.wordPairing.product (Marked m)).annihilator
          (markedCode m s))) =
      1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) +
        AES.maskSize (inputZeros m s)) := by
  rw [source_sqrt_card m s d hd, dual_sqrt_card m s d hd hle]
  exact dual_power_ratio _ d _ _ hd (MarkedBlockScale.count_balance m s) hle

end AESPaper.WordDualNormalization
