import AESConcrete.MultibyteColumnBound
import AESConcrete.SingleByteColumnBound

/-!
# Uniform concrete AES word residual column bound

The input zero mask is constructed from the actual input word. Zero columns,
single-active-byte columns and multibyte columns are joined without an
assumed support choice or numeric resource. All four explicit byte-channel
orientations on each side and both diffusion directions are covered.

Constructive mathematics only; no attacks or manuscript edits. This is one
operator resource for the still separate complete AES mixing theorem.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.AllColumnBound
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel)

def inputZeroMask (a : Word) : Fin 16 :=
  maskBitsEquiv.symm (fun i => decide (a i = 0))

theorem inputZeroMask_bit (a : Word) (i : Fin 4) :
    maskBit (inputZeroMask a) i = true ↔ a i = 0 := by
  have h := congrFun (maskBitsEquiv.apply_symm_apply (fun i => decide (a i = 0))) i
  change maskBit (inputZeroMask a) i = decide (a i = 0) at h
  rw [h]
  simp

private theorem full_mask_bits : ∀ z : Fin 16, maskSize z = 4 →
    ∀ i : Fin 4, maskBit z i = true := by decide

private theorem one_active_choice : ∀ z : Fin 16, maskSize z = 3 →
    ∃ k : Fin 4, ∀ i : Fin 4, maskBit z i = true ↔ i ≠ k := by decide

theorem inputZeroMask_size_lt_four (a : Word) (ha : a ≠ 0) :
    maskSize (inputZeroMask a) < 4 := by
  have hle := AESMixing.maskSize_le_four (inputZeroMask a)
  by_contra hn
  have he : maskSize (inputZeroMask a) = 4 := by omega
  apply ha
  funext i
  exact (inputZeroMask_bit a i).mp (full_mask_bits (inputZeroMask a) he i)

/-- The column resource is now unconditional on the actual input word. -/
theorem residual_column_energy_lt (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a^2) <
      (2/(15*4294967296) : ℝ) := by
  by_cases ha0 : a = 0
  · subst a
    rw [SingleByteColumnBound.residual_zero_column_energy]
    norm_num
  · let z := inputZeroMask a
    have ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true :=
      fun i => (inputZeroMask_bit a i).symm
    have hz := inputZeroMask_size_lt_four a ha0
    by_cases hsmall : maskSize z ≤ 2
    · exact MultibyteColumnBound.residual_column_energy_lt left right inverse a z (4-maskSize z)
        (by omega) (by omega) ha
    · have hthree : maskSize z = 3 := by dsimp [z] at *; omega
      obtain ⟨k,hk⟩ := one_active_choice z hthree
      have hs : ∀ i, i ≠ k → a i = 0 := fun i hi => (ha i).mpr ((hk i).mpr hi)
      have hak : a k ≠ 0 := fun h => ((hk k).mp ((ha k).mp h)) rfl
      exact SingleByteColumnBound.residual_column_energy_lt left right inverse a k hs hak

theorem actual_word_residual_column_energy_lt (a : Word) :
    (∑ y : Word, residualMatrix AES.wordSuperboxKernel 0 y a^2) <
      (2/(15*4294967296) : ℝ) :=
  residual_column_energy_lt .ordinary .ordinary false a

end AESConcrete.AllColumnBound
