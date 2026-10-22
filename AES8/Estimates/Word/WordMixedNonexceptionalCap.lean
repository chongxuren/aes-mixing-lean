import AES8.Estimates.Word.WordMixedSingleMaskCap
import AESConcrete.WordMixedCentering
import AES8.Estimates.Word.OneSidedWordEnergy

/-!
# Actual nonexceptional one-sided residual entries

The only excluded entries have precisely one active byte in both physical
word labels. Every other nonzero pair uses one of the two independently
derived raw mixed-word bounds. The actual global word activity correction
and its zero-axis cancellations give the residual cap 1152/q. This supplies
no exceptional-block fourth sums.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixedNonexceptionalCap
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.WordFourierCore (wordFourier)
open AESConcrete.WordMixedCentering
open AES8.WordMixedPairCap
open AES8.WordMixedSingleMaskCap
open AES8.OneSidedWordEnergy (rightMixed)

def OneActive (a : Word) : Prop := ∃ k : Fin 4, a k ≠ 0 ∧ ∀ i, i ≠ k → a i = 0

/-- A nonzero word either has one active byte or contains two distinct
active physical byte positions. No finite word enumeration is used. -/
theorem one_or_pair (a : Word) (ha : a ≠ 0) :
    OneActive a ∨ ∃ i j : Fin 4, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0 := by
  by_cases hp : ∃ i j : Fin 4, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0
  · exact Or.inr hp
  · have hex : ∃ k : Fin 4, a k ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (funext h)
    obtain ⟨k, hk⟩ := hex
    refine Or.inl ⟨k, hk, ?_⟩
    intro i hik
    by_contra hi
    exact hp ⟨k, i, hik.symm, hk, hi⟩

theorem raw_mixed_le (left right : Orientation) (inverse : Bool) (a b : Word)
    (ha : a ≠ 0) (hb : b ≠ 0) (hnonexception : ¬ (OneActive a ∧ OneActive b)) :
    |kernelCompose (wordKernel left right inverse) wordFourier b a| ≤
      (1144 / 4294967296 : ℝ) := by
  rcases one_or_pair a ha with haOne | ⟨i, j, hij, hi, hj⟩
  · rcases one_or_pair b hb with hbOne | ⟨i, j, hij, hi, hj⟩
    · exact (hnonexception ⟨haOne, hbOne⟩).elim
    · obtain ⟨k, hak, ha⟩ := haOne
      exact (full_mixed_single_mask_le left right inverse a b k ha hak i j hij hi hj).trans
        (by norm_num)
  · exact (full_mixed_le_pair left right inverse a b hb i j hij hi hj).trans (by norm_num)

/-- The activity term is the actual global zero/nonzero-word projection;
no tensor-byte activity replacement is used. -/
theorem residual_mixed_lt (left right : Orientation) (inverse : Bool) (a b : Word)
    (hnonexception : ¬ (OneActive a ∧ OneActive b)) :
    |kernelCompose (residualMatrix (wordKernel left right inverse) 0) wordFourier b a| <
      (1152 / 4294967296 : ℝ) := by
  have hpoint := word_kernel_pointed left right inverse
  by_cases ha : a = 0
  · subst a
    rw [residual_fourier_zero_column _ hpoint, abs_zero]
    norm_num
  by_cases hb : b = 0
  · subst b
    rw [residual_fourier_zero_row _ hpoint, abs_zero]
    norm_num
  rw [residual_right_fourier, activity_right_fourier a b ha hb]
  calc
    _ ≤ |kernelCompose (wordKernel left right inverse) wordFourier b a| +
        |-(1 / (65536 * 4294967295) : ℝ)| := abs_sub _ _
    _ ≤ (1144 / 4294967296 : ℝ) + |-(1 / (65536 * 4294967295) : ℝ)| :=
      add_le_add (raw_mixed_le left right inverse a b ha hb hnonexception) le_rfl
    _ < _ := by norm_num

/-- The actual R F and R^T F retain their literal physical labels. -/
theorem rightMixed_lt (adjoint : Bool) (a b : Word)
    (hnonexception : ¬ (OneActive a ∧ OneActive b)) :
    |rightMixed adjoint b a| < (1152 / 4294967296 : ℝ) := by
  unfold rightMixed
  rw [AESConcrete.WordFourierVariants.baseResidual_eq]
  exact residual_mixed_lt _ _ _ a b hnonexception

end AES8.WordMixedNonexceptionalCap
