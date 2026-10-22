import AES8.Reductions.Source.PaperAESSourceActivity
import AES8.Reductions.Source.PaperAESSourceMarkedEnergy

/-!
# The current Section 11 column bound for at least two active bytes

Fixed rational checks are separated from the structural source reductions.
The actual activity estimate, marked-position estimate and exact orthogonal
degree decomposition then prove the stated full-column bound and its exact
centering. This does not redo the separate one-active-byte estimate or the
whole-word Fourier/orientation correspondence. No numerical search is used.
Constructive verification only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESSource
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)

def markedMajorant : ℝ := 4*X + 6*X^2*(1+Y)^2 + 12*C*X*(1+C+Y)^2

theorem activity_scalar_lt : PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) <
    (51 / 50 : ℝ) := by
  norm_num [PaperActivityMajorization.allCaps]

theorem marked_scalar_lt : markedMajorant < (1 / 12 : ℝ) := by
  norm_num [markedMajorant, X, Y, C]

theorem word_normalization_lt : (256 / 255 : ℝ)^4 < 51 / 50 := by norm_num

theorem current_column_scalar_lt :
    (PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant) / 255^4 <
      (17 / (15 * 4294967296) : ℝ) := by
  have hn : (4294967296 : ℝ) / 255^4 < 51 / 50 := by
    convert word_normalization_lt using 1
    norm_num
  have hp : 0 ≤ PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant := by
    obtain ⟨hx,hy,hc,_⟩ := marked_scalars
    unfold PaperActivityMajorization.allCaps markedMajorant
    positivity
  have hs : (4294967296 : ℝ) / 255^4 *
      (PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant) < 17 / 15 := by
    calc
      _ ≤ (51 / 50) *
          (PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant) :=
        mul_le_mul_of_nonneg_right hn.le hp
      _ < (51 / 50 : ℝ) * (51 / 50 + 1 / 12) :=
        mul_lt_mul_of_pos_left (add_lt_add activity_scalar_lt marked_scalar_lt) (by norm_num)
      _ < _ := by norm_num
  calc
    _ = ((4294967296 : ℝ) / 255^4 *
        (PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant)) /
          4294967296 := by ring
    _ < (17 / 15 : ℝ) / 4294967296 :=
      div_lt_div_of_pos_right hs (by norm_num)
    _ = _ := by ring

/-- The complete degree energy is the activity part plus all strictly
positive residual degrees. This is an exact identity before any estimate. -/
theorem column_energy_eq_activity_add_positive
    (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) =
      (∑ y : Word, degreeComponent (0 : Byte) 0
        (fun v => wordKernel left right inverse v a) y ^ 2) +
      ∑ j : Fin 5, if 0 < j.val then
        ∑ y : Word, degreeComponent (0 : Byte) j
          (fun v => wordKernel left right inverse v a) y ^ 2 else 0 := by
  rw [← degreeComponent_pythagoras (0 : Byte) (by norm_num [Byte, BinaryWord.card])]
  simp [Fin.sum_univ_succ]

/-- The full physical word column obtained through the current source,
activity and marked-position routes, still with symbolic scalar expressions. -/
theorem multibyte_column_energy_le_current
    (left right : Orientation) (inverse : Bool) (a : Word)
    (ht : 2 ≤ (active a).card) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) ≤
      (PaperActivityMajorization.allCaps (1 / 64) (65 / 8192) + markedMajorant) / 255^4 := by
  rw [column_energy_eq_activity_add_positive]
  have h0 := activity_energy_le_allCaps left right inverse a (nonzero_of_two_active a ht)
  have hp := positive_residual_energy_le_marked left right inverse a ht
  exact (add_le_add h0 hp).trans_eq (by unfold markedMajorant; ring)

theorem multibyte_column_energy_lt_current
    (left right : Orientation) (inverse : Bool) (a : Word)
    (ht : 2 ≤ (active a).card) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) <
      (17 / (15 * 4294967296) : ℝ) :=
  (multibyte_column_energy_le_current left right inverse a ht).trans_lt current_column_scalar_lt

/-- Exact subtraction of the uniform nonzero component gives the residual
column estimate; no stronger full-column claim is assumed. -/
theorem multibyte_residual_column_energy_lt_current
    (left right : Orientation) (inverse : Bool) (a : Word)
    (ht : 2 ≤ (active a).card) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) := by
  rw [AESConcrete.pointed_residual_column_energy_exact (word_kernel_pointed left right inverse)
    AESConcrete.AES.word_card_gt_one a (nonzero_of_two_active a ht),
    AESConcrete.AES.word_card_exact]
  have h := multibyte_column_energy_lt_current left right inverse a ht
  norm_num at h ⊢
  linarith

end AES8.PaperAESSource
