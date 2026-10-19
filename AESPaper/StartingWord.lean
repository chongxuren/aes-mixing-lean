import AESPaper.GroupedRecurrence
import AESConcrete.ActualWordEntry

/-!
# Concrete first-word estimates for the v9 four-round initialization

`wordLaw a` is the actual forward AES word channel column. The full-column
collision bound is assembled before residual centering: adding the rounded
residual cap to `1/(q-1)` would lose the strict `17/(15q)` bound. The point
bound specializes the checked shortened-MDS graph argument to ordinary byte
channels and retains their exact fifth moment `79/(4q)`, instead of the
larger bound shared with Fourier orientations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.StartingWord
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.WordEntryGraph (Active leg)
open AESConcrete.ByteFifthMoments (ddtMoment)
attribute [local instance] Classical.propDecidable

/-- Exact 32-bit word alphabet size used throughout the paper. -/
def q : ℝ := 2^32

theorem q_eq_word_card : q = Fintype.card AES.Word := by
  rw [AESConcrete.AES.word_card_exact]
  norm_num [q]

/-- The first superbox response of one actual word difference. -/
def wordLaw (a : AES.Word) : AES.Word → ℝ := fun b => AES.wordSuperboxKernel b a

theorem wordLaw_nonnegative (a b : AES.Word) : 0 ≤ wordLaw a b :=
  AES.word_superbox_pointed.nonnegative b a

theorem wordLaw_total (a : AES.Word) : (∑ b, wordLaw a b) = 1 :=
  AES.word_superbox_pointed.column_sum a

theorem wordLaw_zero (a : AES.Word) (ha : a ≠ 0) : wordLaw a 0 = 0 := by
  exact (AES.word_superbox_pointed.zero_row a).trans (if_neg ha)

-- The 16 four-byte zero masks are checked exhaustively by kernel reduction.
theorem one_active_choice : ∀ z : Fin 16, AES.maskSize z = 3 →
    ∃ k : Fin 4, ∀ i : Fin 4, AES.maskBit z i = true ↔ i ≠ k := by decide

/-- Join the sharp full-column estimates over the actual input zero mask.
This retains the strict pre-centering bound in every checked orientation. -/
theorem full_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : Word) (ha0 : a ≠ 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) <
      (17/(15*4294967296) : ℝ) := by
  let z := inputZeroMask a
  have ha : ∀ i : Fin 4, a i = 0 ↔ AES.maskBit z i = true :=
    fun i => (inputZeroMask_bit a i).symm
  have hz := AllColumnBound.inputZeroMask_size_lt_four a ha0
  by_cases hsmall : AES.maskSize z ≤ 2
  · exact MultibyteColumnBound.full_column_energy_lt left right inverse a z
      (4-AES.maskSize z) (by omega) (by omega) ha
  · have hthree : AES.maskSize z = 3 := by dsimp [z] at *; omega
    obtain ⟨k,hk⟩ := one_active_choice z hthree
    have hs : ∀ i, i ≠ k → a i = 0 := fun i hi => (ha i).mpr ((hk i).mpr hi)
    have hak : a k ≠ 0 := fun h => ((hk k).mp ((ha k).mp h)) rfl
    exact SingleByteColumnBound.full_column_energy_lt left right inverse a k hs hak

/-- v9 `eq:word-collisions`, collision part, for the actual forward word law. -/
theorem wordLaw_collision_lt (a : AES.Word) (ha : a ≠ 0) :
    (∑ b, wordLaw a b ^ 2) < 17/(15*q) := by
  have h := full_column_energy_lt .ordinary .ordinary false a ha
  rw [WordOrientationClosure.ordinary_word_kernel] at h
  simpa only [wordLaw, q, show (2 : ℝ)^32 = 4294967296 by norm_num] using h

/-- The convenient larger collision resource in the several-source proof. -/
theorem wordLaw_collision_lt_six_fifths (a : AES.Word) (ha : a ≠ 0) :
    (∑ b, wordLaw a b ^ 2) < 6/(5*q) := by
  apply (wordLaw_collision_lt a ha).trans
  norm_num [q]

/-- Exact ordinary-byte fifth moments are smaller than the uniform bound
used in `ActualWordEntry` for all Fourier orientations simultaneously. -/
theorem ordinary_active_leg_fifth (a b : Word) (p : Active a b) :
    (∑ v : Byte, leg .ordinary .ordinary a b p.val v ^ 5) = ddtMoment := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i =>
    have hb : b i ≠ 0 := fun h => hp ((inputZeroMask_bit b i).mpr h)
    exact ByteFifthMoments.aes_row_fifth (b i) hb
  | inr i =>
    have ha : a i ≠ 0 := fun h => hp ((inputZeroMask_bit a i).mpr h)
    exact ByteFifthMoments.aes_column_fifth (a i) ha

/-- Actual shortened-graph factorization and fifth-moment Holder give a
uniform forward atom cap `79/(4q)`. No word-level probability bound is assumed. -/
theorem wordLaw_point_le_fifth (a b : AES.Word) (ha : a ≠ 0) :
    wordLaw a b ≤ ddtMoment := by
  change wordKernel .ordinary .ordinary false b a ≤ ddtMoment
  rw [WordEntryGraph.actual_shortened_formula]
  change MDSFiveFactorEntry.graphResponse (byteDiffusionHom false)
    (inputZeroMask b) (inputZeroMask a)
    (fun p => leg .ordinary .ordinary a b p.val) ≤ ddtMoment
  by_cases hz : AES.maskSize (inputZeroMask b) + AES.maskSize (inputZeroMask a) ≤ 3
  · exact MDSFiveFactorEntry.graphResponse_le_fifth
      (byteDiffusionHom false) (byteDiffusionHom_zeroMDS false)
      (inputZeroMask b) (inputZeroMask a) hz
      (fun p => leg .ordinary .ordinary a b p.val)
      (fun p v => WordEntryGraph.leg_nonneg .ordinary .ordinary a b p.val v)
      (fun p => WordEntryGraph.leg_mass .ordinary .ordinary a b p.val)
      ddtMoment (fun p => (ordinary_active_leg_fifth a b p).le)
  · obtain ⟨p⟩ := WordEntryGraph.active_nonempty_of_input_ne_zero a b ha
    rw [MDSFiveFactorEntry.graphResponse_zero_of_high_zeros
      (byteDiffusionHom false) (byteDiffusionHom_zeroMDS false)
      (inputZeroMask b) (inputZeroMask a) (by omega)
      (fun p => leg .ordinary .ordinary a b p.val) p
      (WordEntryGraph.active_leg_zero .ordinary .ordinary a b p)]
    norm_num [ddtMoment]

/-- v9 `eq:word-collisions`, point-probability part, with the sharper
checked ordinary fifth moment in the preceding theorem. -/
theorem wordLaw_point_lt (a b : AES.Word) (ha : a ≠ 0) :
    wordLaw a b < 20/q := by
  apply (wordLaw_point_le_fifth a b ha).trans_lt
  norm_num [ddtMoment, q]

theorem wordLaw_abs_point_lt (a b : AES.Word) (ha : a ≠ 0) :
    |wordLaw a b| < 20/q := by
  rw [abs_of_nonneg (wordLaw_nonnegative a b)]
  exact wordLaw_point_lt a b ha

/-- The exact centering subtraction is retained for later source estimates. -/
theorem residual_column_energy_lt_sharp (a : AES.Word) (ha : a ≠ 0) :
    (∑ b, residualMatrix AES.wordSuperboxKernel 0 b a ^ 2) <
      17/(15*q) - 1/(q-1) := by
  rw [pointed_residual_column_energy_exact AES.word_superbox_pointed
    AESConcrete.AES.word_card_gt_one a ha, ← q_eq_word_card]
  exact sub_lt_sub_right (wordLaw_collision_lt a ha) _

/-- Physical input coordinates after initial ShiftRows, before the first
parallel word response. This is not the raw physical column split of `a`. -/
def sourceInput (a : AES.State) : AES.WordState :=
  AES.transposeState.symm (AES.shiftRows a)

/-- The four actual first-layer word laws factor because the input is fixed.
This does not assume independence after the boundary permutation. -/
theorem grouped_initial_product (a : AES.State) (x : AES.WordState) :
    GroupedLaw.groupedLaw 0 a x = ∏ i, wordLaw (sourceInput a i) (x i) := by
  rw [GroupedRecurrence.groupedLaw_initial]
  change action AES.parallelSuperboxKernel (differencePoint (sourceInput a)) x = _
  simp [action, differencePoint, mul_ite, AES.parallelSuperboxKernel,
    coordinateKernel, wordLaw]

end AESPaper.StartingWord
