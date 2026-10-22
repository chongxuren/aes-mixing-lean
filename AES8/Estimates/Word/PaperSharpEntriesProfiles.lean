import AES8.Estimates.Word.PaperSharpEntriesFinite
import AES8.Estimates.Word.PaperSharpEntriesGraphReduction
import AES8.Estimates.Word.PaperWordEntryBounds

/-!
# Exact AES channel profiles and transport of finite raw predicates

The integer profile specifications are imported from the finite-certificate
interface. This file proves their actual ordinary and trace-Fourier row/column
meaning, and converts raw byte inequalities into the four required pair caps.
Final word bounds are conditional only on the named finite raw predicates;
their certification is a separate obligation owned by the certificate worker.
Draft only. Constructive mathematics only; no attacks or local execution.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesProfiles
open AESMixing
open AESConcrete.ByteOrientations (channel)
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesProfileReparam
open AES8.PaperSharpEntriesGraphReduction

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem ordinary_column (a v : Byte) (ha : a ≠ 0) :
    channel .ordinary v a = rhoOrd (a * ordinaryMap v) := by
  change aesByteChannel v a = _
  rw [aesByteChannel_affine, inversion_channel_scale a _ ha, rhoOrd_spec]
  rfl

theorem ordinary_row (b v : Byte) (hb : b ≠ 0) :
    channel .ordinary b v = rhoOrd (ordinaryMap b * v) := by
  change aesByteChannel b v = _
  rw [aesByteChannel_affine, inversion_channel_symmetric]
  change differenceChannel invPermutation v (ordinaryMap b) =
    rhoOrd (ordinaryMap b * v)
  rw [inversion_channel_scale _ _ (map_ne_zero ordinaryMap b hb), rhoOrd_spec]

theorem fourier_column (a v : Byte) (ha : a ≠ 0) :
    channel .fourier v a = rhoFourier (a * fourierMap v) := by
  change aesSquaredWalshChannel v a = _
  rw [aesSquaredWalshChannel, aes_walsh_square,
    inversion_walsh_scale byteCharacter a _ ha, rhoFourier_spec]
  rfl

theorem fourier_row (b v : Byte) (hb : b ≠ 0) :
    channel .fourier b v = rhoFourier (fourierMap b * v) := by
  change aesSquaredWalshChannel b v = _
  rw [aesSquaredWalshChannel, aes_walsh_square, inversion_walsh_symmetric]
  change fieldWalsh byteCharacter (fun x => x⁻¹) (fourierMap b) v ^ 2 / 65536 =
    rhoFourier (fourierMap b * v)
  rw [inversion_walsh_scale byteCharacter _ _ (map_ne_zero fourierMap b hb),
    rhoFourier_spec]

theorem ordinary_pairCap (raw : OrdinaryRawBound) (r : ℕ)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    PairCap rhoOrd ordinaryMap r (5-r) ((111 : ℝ) / 2^35) := by
  intro alpha beta gamma ha hb
  rw [ordinary_normalization alpha beta gamma r (by omega)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast raw alpha beta gamma r ha hb hr1 hr4

theorem ordinary_required_caps (raw : OrdinaryRawBound) :
    RequiredPairCaps rhoOrd ordinaryMap ((111 : ℝ) / 2^35) where
  balanced23 := ordinary_pairCap raw 2 (by omega) (by omega)
  balanced32 := ordinary_pairCap raw 3 (by omega) (by omega)
  homogeneous14 := by
    intro alpha beta ha hb
    simpa only [add_zero] using ordinary_pairCap raw 1 (by omega) (by omega)
      alpha beta 0 ha hb
  homogeneous41 := by
    intro alpha beta ha hb
    simpa only [add_zero] using ordinary_pairCap raw 4 (by omega) (by omega)
      alpha beta 0 ha hb

theorem fourier_balanced_pairCap (raw : FourierRawBound fourierMap) (r : ℕ)
    (hr : r = 2 ∨ r = 3) :
    PairCap rhoFourier fourierMap r (5-r) ((7247757311 : ℝ) / 2^60) := by
  intro alpha beta gamma ha hb
  rw [fourier_normalization fourierMap alpha beta gamma r (by omega)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast raw.1 alpha beta gamma r ha hb hr

theorem fourier_homogeneous_pairCap (raw : FourierRawBound fourierMap) (r : ℕ)
    (hr : r = 1 ∨ r = 4) :
    HomogeneousPairCap rhoFourier fourierMap r (5-r)
      ((7247757311 : ℝ) / 2^60) := by
  intro alpha beta ha hb
  have he := fourier_normalization fourierMap alpha beta 0 r (by omega)
  simp only [add_zero] at he
  rw [he]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast raw.2 alpha beta r ha hb hr

theorem fourier_required_caps (raw : FourierRawBound fourierMap) :
    RequiredPairCaps rhoFourier fourierMap ((7247757311 : ℝ) / 2^60) where
  balanced23 := fourier_balanced_pairCap raw 2 (Or.inl rfl)
  balanced32 := fourier_balanced_pairCap raw 3 (Or.inr rfl)
  homogeneous14 := fourier_homogeneous_pairCap raw 1 (Or.inl rfl)
  homogeneous41 := fourier_homogeneous_pairCap raw 4 (Or.inr rfl)

/-- The ordinary source/full cap now has exactly the declared finite byte
obligation as a premise, rather than an assumed word-entry estimate. -/
theorem ordinary_word_entry_lt_fourteen (raw : OrdinaryRawBound) (inverse : Bool)
    (a b : AESConcrete.WordColumnGram.Word) (ha : a ≠ 0) :
    AESConcrete.WordOrientationClosure.wordKernel .ordinary .ordinary inverse b a <
      (14 / 2^32 : ℝ) := by
  exact (word_entry_le_of_pairCaps .ordinary inverse rhoOrd ordinaryMap
    ordinary_row ordinary_column ((111 : ℝ) / 2^35) (by norm_num)
    (ordinary_required_caps raw) a b ha).trans_lt ordinary_cap_lt_fourteen

/-- Both diffusion directions are retained so the whole-word Fourier
relabeling can consume this byte/graph result without changing its measure. -/
theorem fourier_word_entry_lt_twenty_seven (raw : FourierRawBound fourierMap)
    (inverse : Bool) (a b : AESConcrete.WordColumnGram.Word) (ha : a ≠ 0) :
    AESConcrete.WordOrientationClosure.wordKernel .fourier .fourier inverse b a <
      (27 / 2^32 : ℝ) := by
  exact (word_entry_le_of_pairCaps .fourier inverse rhoFourier fourierMap
    fourier_row fourier_column ((7247757311 : ℝ) / 2^60) (by norm_num)
    (fourier_required_caps raw) a b ha).trans_lt fourier_cap_lt_twenty_seven

/-- Preserve the alternative finite route as an adapter to the common source
interface. The current cited-result endpoint does not depend on this adapter. -/
theorem ordinary_bound (raw : OrdinaryRawBound) : PaperWordEntryBounds.OrdinaryBound := by
  intro a b ha
  simpa only [AESConcrete.WordOrientationClosure.ordinary_word_kernel] using
    ordinary_word_entry_lt_fourteen raw false a b ha

end AES8.PaperSharpEntriesProfiles
