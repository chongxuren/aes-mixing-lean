import AESConcrete.WordFourierClosure
import AESConcrete.ActualWordEntry
import AESConcrete.ActualWordMoments
import AESConcrete.SharpDampedWordNorm

/-!
# Bounds for the identified whole-word Fourier matrices

Exact simultaneous coordinate relabeling transfers the existing ordinary
entry, column, Hilbert--Schmidt and second Gram moment bounds. The operator
bound is transferred for arbitrary joint inputs. No pointwise invariance
under an unspecified orthogonal transformation is used.
The one-sided mixed entry bound and full round theorem remain separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordFourierBounds
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierCore
open AESConcrete.WordFourierDiffusion (wordReverse wordReverse_self)
open AESConcrete.WordFourierClosure (reverseKernel residual_fourier)
set_option maxRecDepth 100000

theorem reverse_column_energy (T : AES.Word → AES.Word → ℝ) (a : AES.Word) :
    (∑ y, reverseKernel T y a ^ 2) = ∑ y, T y (wordReverse a) ^ 2 :=
  Equiv.sum_comp wordReverse (fun y => T y (wordReverse a) ^ 2)

theorem reverse_trace (T : AES.Word → AES.Word → ℝ) :
    (∑ y, ∑ x, reverseKernel T y x ^ 2) = ∑ y, ∑ x, T y x ^ 2 := by
  change (∑ y, ∑ x, T (wordReverse y) (wordReverse x) ^ 2) = _
  calc
    _ = ∑ y, ∑ x, T (wordReverse y) x ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact Equiv.sum_comp wordReverse (fun x => T (wordReverse y) x ^ 2)
    _ = _ := Equiv.sum_comp wordReverse (fun y => ∑ x, T y x ^ 2)

theorem reverse_gram (T : AES.Word → AES.Word → ℝ) (x z : AES.Word) :
    (∑ y, reverseKernel T y x * reverseKernel T y z) =
      ∑ y, T y (wordReverse x) * T y (wordReverse z) :=
  Equiv.sum_comp wordReverse (fun y => T y (wordReverse x) * T y (wordReverse z))

theorem reverse_gram_moment (T : AES.Word → AES.Word → ℝ) :
    (∑ x, ∑ z, (∑ y, reverseKernel T y x * reverseKernel T y z)^2) =
      ∑ x, ∑ z, (∑ y, T y x * T y z)^2 := by
  simp_rw [reverse_gram]
  calc
    _ = ∑ x, ∑ z, (∑ y, T y (wordReverse x) * T y z)^2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Equiv.sum_comp wordReverse (fun z => (∑ y, T y (wordReverse x) * T y z)^2)
    _ = _ := Equiv.sum_comp wordReverse (fun x => ∑ z, (∑ y, T y x * T y z)^2)

theorem reverse_action (T : AES.Word → AES.Word → ℝ) (f : AES.Word → ℝ)
    (y : AES.Word) :
    action (reverseKernel T) f y = action T (fun x => f (wordReverse x)) (wordReverse y) := by
  have h := Equiv.sum_comp wordReverse (fun x => T (wordReverse y) x * f (wordReverse x))
  simpa only [wordReverse_self, action, reverseKernel] using h

theorem reverse_energy (T : AES.Word → AES.Word → ℝ) (f : AES.Word → ℝ) :
    (∑ y, action (reverseKernel T) f y ^ 2) =
      ∑ y, action T (fun x => f (wordReverse x)) y ^ 2 := by
  simp_rw [reverse_action]
  exact Equiv.sum_comp wordReverse
    (fun y => action T (fun x => f (wordReverse x)) y ^ 2)

theorem fourier_residual_entry_lt (left right : Orientation) (inverse : Bool)
    (a b : AES.Word) :
    |wordConjugate (residualMatrix (wordKernel left right inverse) 0) b a| <
      (46 / 4294967296 : ℝ) := by
  rw [residual_fourier]
  exact ActualWordEntry.residual_entry_lt _ _ _ (wordReverse a) (wordReverse b)

theorem fourier_residual_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : AES.Word) :
    (∑ y, wordConjugate (residualMatrix (wordKernel left right inverse) 0) y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) := by
  rw [residual_fourier, reverse_column_energy]
  exact AllColumnBound.residual_column_energy_lt _ _ _ (wordReverse a)

theorem fourier_residual_trace_lt (left right : Orientation) (inverse : Bool) :
    (∑ y, ∑ x, wordConjugate (residualMatrix (wordKernel left right inverse) 0) y x ^ 2) <
      (4251 / 4294967296 : ℝ) := by
  rw [residual_fourier, reverse_trace]
  exact ActualWordMoments.actual_trace_bound _ _ _

theorem fourier_residual_gram_moment_lt (left right : Orientation) (inverse : Bool) :
    (∑ x, ∑ z, (∑ y,
      wordConjugate (residualMatrix (wordKernel left right inverse) 0) y x *
      wordConjugate (residualMatrix (wordKernel left right inverse) 0) y z)^2) <
      (300 / 4294967296 : ℝ)^2 := by
  rw [residual_fourier, reverse_gram_moment]
  exact ActualWordMoments.actual_gram_moment_bound _ _ _

theorem fourier_residual_energy_le (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ y, action (wordConjugate (residualMatrix (wordKernel left right inverse) 0)) f y ^ 2) ≤
      (21 / 131072 : ℝ)^2 * ∑ x, f x ^ 2 := by
  rw [residual_fourier, reverse_energy]
  have h := SharpDampedWordNorm.word_kernel_residual_energy
    (FourierLineOverlap.fourierMate left) (FourierLineOverlap.fourierMate right) (!inverse)
    (fun x => f (wordReverse x))
  have hnorm : (∑ x, f (wordReverse x) ^ 2) = ∑ x, f x ^ 2 :=
    Equiv.sum_comp wordReverse (fun x => f x ^ 2)
  rw [hnorm] at h
  exact h

theorem fourier_residual_operator_norm_le (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (wordConjugate (residualMatrix (wordKernel left right inverse) 0))‖ ≤
      (21 / 131072 : ℝ) :=
  kernelOperator_norm_le _ (by norm_num) (fourier_residual_energy_le left right inverse)

theorem actual_fourier_residual_entry_lt (a b : AES.Word) :
    |wordConjugate (residualMatrix AES.wordSuperboxKernel 0) b a| <
      (46 / 4294967296 : ℝ) :=
  fourier_residual_entry_lt .ordinary .ordinary false a b

end AESConcrete.WordFourierBounds
