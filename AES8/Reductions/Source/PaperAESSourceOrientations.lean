import AES8.Reductions.Source.PaperAESSourceColumn
import AES8.Math.PaperEncoding
import AESConcrete.SingleByteColumnBound
import AESConcrete.WordFourierVariants

/-!
# Current-paper source columns in the four physical word orientations

The support split joins the current Section 11 multibyte argument to the
actual common-source single-byte argument. Exact transpose and tensor-Fourier
identities then identify the four matrices in the column assertion of
`lem:resources`: R, R*, F R F and F R* F. Coordinate reversal is retained
as a physical permutation, and column energy is reindexed through it.

The legacy orientation definitions and exact identities are reused, but no
legacy multibyte or all-column numerical bound is used. This file proves only
the column resource; the norm, Gram moment and complete mixing theorem remain
separate. Constructive verification only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000

namespace AES8.PaperAESSource
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.WordFourierCore (wordConjugate)
open AESConcrete.WordFourierDiffusion (wordReverse)
open AESConcrete.WordFourierClosure (reverseKernel wordKernel_fourier residual_fourier)
open AESConcrete.WordFourierVariants (baseOrientation baseResidual variant baseResidual_eq)

/-- The sole active position is selected from the actual physical input,
rather than supplied as an independent support assumption. -/
theorem single_active_of_not_two (a : Word) (ha : a ≠ 0)
    (ht : ¬ 2 ≤ (active a).card) :
    ∃ k : Fin 4, (∀ i, i ≠ k → a i = 0) ∧ a k ≠ 0 := by
  have hc : (active a).card = 1 := by
    have hp := (active_nonempty a ha).card_pos
    omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    by_contra hn
    have hm := (mem_active a i).mpr hn
    rw [hk] at hm
    exact hi (Finset.mem_singleton.mp hm)
  · apply (mem_active a k).mp
    rw [hk]
    exact Finset.mem_singleton_self k

/-- Every nonzero physical column satisfies the current full-channel cap,
using the single-byte or current multibyte proof according to its support. -/
theorem all_nonzero_column_energy_lt_current
    (left right : Orientation) (inverse : Bool) (a : Word) (ha : a ≠ 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) <
      (17 / (15 * 4294967296) : ℝ) := by
  by_cases ht : 2 ≤ (active a).card
  · exact multibyte_column_energy_lt_current left right inverse a ht
  · obtain ⟨k, hs, hk⟩ := single_active_of_not_two a ha ht
    exact AESConcrete.SingleByteColumnBound.full_column_energy_lt
      left right inverse a k hs hk

/-- Exact centering gives a sharper intermediate expression before the
paper's uniform residual-column allowance is applied. -/
theorem all_nonzero_residual_column_energy_lt_centered_current
    (left right : Orientation) (inverse : Bool) (a : Word) (ha : a ≠ 0) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a ^ 2) <
      (17 / (15 * 4294967296) - 1 / 4294967295 : ℝ) := by
  rw [AESConcrete.pointed_residual_column_energy_exact
    (word_kernel_pointed left right inverse) AESConcrete.AES.word_card_gt_one a ha,
    AESConcrete.AES.word_card_exact]
  have h := sub_lt_sub_right
    (all_nonzero_column_energy_lt_current left right inverse a ha) (1 / 4294967295 : ℝ)
  norm_num at h ⊢
  exact h

/-- The current Section 11 route proves the resource without a target cap
premise; the distinguished zero column is handled by pointedness. -/
theorem all_residual_column_energy_lt_current
    (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) := by
  by_cases ha : a = 0
  · subst a
    rw [AESConcrete.SingleByteColumnBound.residual_zero_column_energy]
    norm_num
  · exact (all_nonzero_residual_column_energy_lt_centered_current
      left right inverse a ha).trans (by norm_num)

/-- The full ordinary channel and its actual adjoint. -/
def baseWordChannel (adjoint : Bool) : Word → Word → ℝ :=
  if adjoint then fun y x => AES.wordSuperboxKernel x y else AES.wordSuperboxKernel

/-- The full-channel counterparts of the four paper residual matrices. -/
def fullWordVariant (adjoint fourier : Bool) : Word → Word → ℝ :=
  if fourier then wordConjugate (baseWordChannel adjoint) else baseWordChannel adjoint

theorem baseWordChannel_eq (adjoint : Bool) :
    baseWordChannel adjoint = wordKernel (baseOrientation adjoint)
      (baseOrientation adjoint) adjoint := by
  cases adjoint
  · rfl
  · exact AESConcrete.ReverseDegreeThree.wordKernel_transpose .ordinary .ordinary false

/-- Fourier duality changes the byte channel and diffusion direction, and
uses an explicit reversal of both physical word labels. -/
def sourceOrientation (adjoint fourier : Bool) : Orientation :=
  if fourier then AESConcrete.FourierLineOverlap.fourierMate (baseOrientation adjoint)
  else baseOrientation adjoint

def sourceInverse (adjoint fourier : Bool) : Bool :=
  if fourier then !adjoint else adjoint

def sourceRelabel (fourier : Bool) : Equiv.Perm Word :=
  if fourier then wordReverse else Equiv.refl Word

@[simp] theorem sourceRelabel_zero (fourier : Bool) : sourceRelabel fourier 0 = 0 := by
  cases fourier <;> rfl

theorem sourceRelabel_nonzero (fourier : Bool) (a : Word) (ha : a ≠ 0) :
    sourceRelabel fourier a ≠ 0 := by
  intro h
  apply ha
  exact (sourceRelabel fourier).injective (h.trans (sourceRelabel_zero fourier).symm)

/-- Exact physical matrix correspondence, including the full adjoint and
the inverse-transpose diffusion hidden by Fourier duality. -/
theorem fullWordVariant_physical (adjoint fourier : Bool) (y a : Word) :
    fullWordVariant adjoint fourier y a =
      wordKernel (sourceOrientation adjoint fourier) (sourceOrientation adjoint fourier)
        (sourceInverse adjoint fourier) (sourceRelabel fourier y) (sourceRelabel fourier a) := by
  unfold fullWordVariant
  rw [baseWordChannel_eq]
  cases fourier
  · rfl
  · rw [if_pos rfl, wordKernel_fourier]
    rfl

/-- The residual correspondence uses the exact Fourier image of the word
activity projection, rather than entrywise invariance under an orthogonal map. -/
theorem residualVariant_physical (adjoint fourier : Bool) (y a : Word) :
    variant adjoint fourier y a =
      residualMatrix
        (wordKernel (sourceOrientation adjoint fourier) (sourceOrientation adjoint fourier)
          (sourceInverse adjoint fourier)) 0
        (sourceRelabel fourier y) (sourceRelabel fourier a) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · rfl
  · rw [if_pos rfl, residual_fourier]
    rfl

theorem fullWordVariant_column_energy_exact (adjoint fourier : Bool) (a : Word) :
    (∑ y : Word, fullWordVariant adjoint fourier y a ^ 2) =
      ∑ y : Word, wordKernel (sourceOrientation adjoint fourier)
        (sourceOrientation adjoint fourier) (sourceInverse adjoint fourier)
        y (sourceRelabel fourier a) ^ 2 := by
  simp_rw [fullWordVariant_physical]
  exact Equiv.sum_comp (sourceRelabel fourier) (fun y =>
    wordKernel (sourceOrientation adjoint fourier) (sourceOrientation adjoint fourier)
      (sourceInverse adjoint fourier) y (sourceRelabel fourier a) ^ 2)

theorem residualVariant_column_energy_exact (adjoint fourier : Bool) (a : Word) :
    (∑ y : Word, variant adjoint fourier y a ^ 2) =
      ∑ y : Word, residualMatrix
        (wordKernel (sourceOrientation adjoint fourier) (sourceOrientation adjoint fourier)
          (sourceInverse adjoint fourier)) 0 y (sourceRelabel fourier a) ^ 2 := by
  simp_rw [residualVariant_physical]
  exact Equiv.sum_comp (sourceRelabel fourier) (fun y =>
    residualMatrix
      (wordKernel (sourceOrientation adjoint fourier) (sourceOrientation adjoint fourier)
        (sourceInverse adjoint fourier)) 0 y (sourceRelabel fourier a) ^ 2)

/-- The exact all-nonzero full-column statement at the end of Section 11,
for ordinary, adjoint, simultaneous Fourier and Fourier-adjoint channels. -/
theorem fullWordVariant_nonzero_column_energy_lt_current
    (adjoint fourier : Bool) (a : Word) (ha : a ≠ 0) :
    (∑ y : Word, fullWordVariant adjoint fourier y a ^ 2) <
      (17 / (15 * 4294967296) : ℝ) := by
  rw [fullWordVariant_column_energy_exact]
  exact all_nonzero_column_energy_lt_current _ _ _ _ (sourceRelabel_nonzero fourier a ha)

/-- The column assertion of frozen-paper `lem:resources`, for the literal
four residual matrices. Its proof uses the current multibyte source route. -/
theorem residualVariant_column_energy_lt_current (adjoint fourier : Bool) (a : Word) :
    (∑ y : Word, variant adjoint fourier y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) := by
  rw [residualVariant_column_energy_exact]
  exact all_residual_column_energy_lt_current _ _ _ _

/-- The same resource in the counting-measure Euclidean basis convention
used by the paper's Hilbert encoding and graph interfaces. -/
theorem residualVariant_basis_norm_sq_lt_current (adjoint fourier : Bool) (a : Word) :
    ‖PaperKernelBounds.kernelOperator (variant adjoint fourier)
      (PaperEncoding.basisVector a)‖ ^ 2 < (2 / (15 * 4294967296) : ℝ) := by
  rw [PaperEncoding.basis_response_energy]
  exact residualVariant_column_energy_lt_current adjoint fourier a

end AES8.PaperAESSource
