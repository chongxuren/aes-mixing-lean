import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Estimates.Word.OneSidedWordEnergy
import AES8.Estimates.Word.PaperWordTwoSwapsVariants
import AES8.Math.PaperMDSGram
import AESMixing.FourierGram

/-!
# Mixed Fourier word resources for the whole-graph estimate

The two Fourier choices are independent.  Left multiplication preserves the
Gram matrix itself; right multiplication preserves its squared-entry sum.
The same statements apply to the transpose needed by matrix vectorization.
No new numerical calculation, attack, or manuscript change is used here.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperWordMixedGram
open AESMixing AESConcrete
open AESConcrete.WordFourierCore AESConcrete.WordFourierVariants

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Literal independent left and right normalized Fourier multiplication. -/
def mixed (adjoint eL eR : Bool) : AES.Word → AES.Word → ℝ :=
  let R := if eR then kernelCompose (baseResidual adjoint) wordFourier
    else baseResidual adjoint
  if eL then kernelCompose wordFourier R else R

theorem left_fourier_gram (T : AES.Word → AES.Word → ℝ) (x z : AES.Word) :
    gram (kernelCompose wordFourier T) x z = gram T x z := by
  exact pairingFourier_inner WordFourierCore.wordPairing word_add_self
    (fun y => T y x) (fun y => T y z)

theorem left_fourier_moment (T : AES.Word → AES.Word → ℝ) :
    (∑ xz : AES.Word × AES.Word,
      gram (kernelCompose wordFourier T) xz.1 xz.2 ^ 2) =
      ∑ xz : AES.Word × AES.Word, gram T xz.1 xz.2 ^ 2 := by
  simp_rw [left_fourier_gram]

theorem right_fourier_moment (T : AES.Word → AES.Word → ℝ) :
    (∑ xz : AES.Word × AES.Word,
      gram (kernelCompose T wordFourier) xz.1 xz.2 ^ 2) =
      ∑ xz : AES.Word × AES.Word, gram T xz.1 xz.2 ^ 2 := by
  have h := fourierConjugate_gram_moment WordFourierCore.wordPairing word_add_self T
  change (∑ xz : AES.Word × AES.Word,
    gram (kernelCompose wordFourier (kernelCompose T wordFourier)) xz.1 xz.2 ^ 2) = _ at h
  simpa only [left_fourier_gram] using h

theorem mixed_moment_eq (adjoint eL eR : Bool) :
    (∑ xz : AES.Word × AES.Word, gram (mixed adjoint eL eR) xz.1 xz.2 ^ 2) =
      ∑ xz : AES.Word × AES.Word, gram (baseResidual adjoint) xz.1 xz.2 ^ 2 := by
  cases eL <;> cases eR <;>
    simp only [mixed, Bool.false_eq_true, if_false, if_true,
      left_fourier_moment, right_fourier_moment]

theorem mixed_moment_lt (adjoint eL eR : Bool) :
    (∑ xz : AES.Word × AES.Word, gram (mixed adjoint eL eR) xz.1 xz.2 ^ 2) <
      (300 / 4294967296 : ℝ) ^ 2 := by
  rw [mixed_moment_eq, Fintype.sum_prod_type]
  exact PaperWordTwoSwapsVariants.variant_gram_moment_lt adjoint false

theorem wordConjugate_transpose (T : AES.Word → AES.Word → ℝ) :
    wordConjugate (fun y x => T x y) = fun y x => wordConjugate T x y := by
  funext a b
  unfold wordConjugate fourierConjugate kernelCompose
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [pairingFourier_symmetric WordFourierCore.wordPairing a x,
    pairingFourier_symmetric WordFourierCore.wordPairing y b]
  ring

theorem mixed_row_energy_lt (adjoint eL eR : Bool) (y : AES.Word) :
    (∑ x, mixed adjoint eL eR y x ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
  have hbase (a : Bool) (z : AES.Word) :
      (∑ x, baseResidual a z x ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
    have h := PaperAESSource.residualVariant_column_energy_lt_current (!a) false z
    simpa only [variant, Bool.false_eq_true, if_false,
      OneSidedWordEnergy.baseResidual_transpose] using h
  cases eL <;> cases eR
  · exact hbase adjoint y
  · rw [show mixed adjoint false true = OneSidedWordEnergy.rightMixed adjoint from rfl,
      OneSidedWordEnergy.row_energy_eq]
    exact hbase adjoint y
  · have he (x : AES.Word) : mixed adjoint true false y x =
        OneSidedWordEnergy.rightMixed (!adjoint) x y := by
      unfold mixed OneSidedWordEnergy.rightMixed kernelCompose
      simp only [Bool.false_eq_true, if_false, if_true,
        OneSidedWordEnergy.baseResidual_transpose]
      apply Finset.sum_congr rfl
      intro z _
      rw [wordFourier_symmetric y z]
      ring
    simp_rw [he]
    exact OneSidedWordEnergy.column_energy_lt (!adjoint) y
  · have he (x : AES.Word) : mixed adjoint true true y x = variant (!adjoint) true x y := by
      have ht : baseResidual (!adjoint) = fun y x => baseResidual adjoint x y := by
        funext a b
        exact OneSidedWordEnergy.baseResidual_transpose adjoint a b
      change wordConjugate (baseResidual adjoint) y x =
        wordConjugate (baseResidual (!adjoint)) x y
      rw [ht, wordConjugate_transpose]
    simp_rw [he]
    exact PaperAESSource.residualVariant_column_energy_lt_current (!adjoint) true y

theorem transpose_moment_eq {V : Type*} [Fintype V] (T : V → V → ℝ) :
    (∑ xz : V × V, gram (fun y x => T x y) xz.1 xz.2 ^ 2) =
      ∑ xz : V × V, gram T xz.1 xz.2 ^ 2 := by
  have hex (S : V → V → ℝ) :
      (∑ xz : V × V, gram S xz.1 xz.2 ^ 2) =
        ∑ xz : V × V, ∑ ab : V × V,
          (S ab.1 xz.1 * S ab.1 xz.2) * (S ab.2 xz.1 * S ab.2 xz.2) := by
    simp only [gram, pow_two, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hex, hex T, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xz _
  apply Finset.sum_congr rfl
  intro ab _
  ring

def tau : ℝ := 300 / 4294967296
def delta : ℝ := (183 / 500 : ℝ) ^ 2 / 4294967296

theorem delta_nonneg : 0 ≤ delta := by norm_num [delta]

theorem mixed_gram_diagonal_le (adjoint eL eR : Bool) (x : AES.Word) :
    gram (mixed adjoint eL eR) x x ≤ delta := by
  have he : gram (mixed adjoint eL eR) x x = gram (variant adjoint eR) x x := by
    cases eL <;> cases eR <;>
      simp only [mixed, variant, Bool.false_eq_true, if_false, if_true,
        wordConjugate, fourierConjugate, left_fourier_gram]
    all_goals change (gram (kernelCompose (baseResidual adjoint) wordFourier) x x =
      gram (kernelCompose wordFourier (kernelCompose (baseResidual adjoint) wordFourier)) x x)
    all_goals rw [left_fourier_gram]
  rw [he, gram_diagonal]
  exact (PaperAESSource.residualVariant_column_energy_lt_current adjoint eR x).le.trans (by norm_num [delta])

theorem mixed_transpose_diagonal_le (adjoint eL eR : Bool) (x : AES.Word) :
    gram (fun y x => mixed adjoint eL eR x y) x x ≤ delta := by
  rw [gram_diagonal]
  exact (mixed_row_energy_lt adjoint eL eR x).le.trans (by norm_num [delta])

theorem mixed_transpose_moment_le (adjoint eL eR : Bool) :
    (∑ xz : AES.Word × AES.Word,
      gram (fun y x => mixed adjoint eL eR x y) xz.1 xz.2 ^ 2) ≤ tau ^ 2 := by
  rw [transpose_moment_eq]
  exact (mixed_moment_lt adjoint eL eR).le

end AES8.PaperWordMixedGram
