import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Estimates.Word.PaperWordMixedGram
import AES8.Estimates.Word.SharpWordNorm
import AES8.Estimates.Word.OrdinaryResidualEntry
import AES8.Math.PaperThinLines
import AES8.Estimates.Word.PaperWordTraceVariants

/-!
# Actual AES resources for the normalized middle overlap

Frozen paper f902bb94, Section 16. The left and right Fourier bits are
independent. Column estimates use the current source proof, including its
physical orientation and coordinate-reversal identities. Parseval transfers
these to mixed matrices without an entrywise Fourier-invariance premise.
No target overlap estimate or matrix-membership premise is assumed.

The printed 27/q entry resource is proved here for ordinary residuals only.
The simultaneous-Fourier 27/q and mixed fourth-moment resources are separate
obligations; this module does not silently replace them by the legacy 46/q.
Constructive proof checking only; no attacks, searches or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapResources
open AESMixing AESConcrete PaperWordMixedGram
open AESConcrete.WordFourierCore AESConcrete.WordFourierVariants

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def q : ℕ := 4294967296
def nu : ℝ := 52 / (5 * 65536)
def delta : ℝ := (183 / 500 : ℝ) ^ 2 / q
def total : ℝ := (326 / 5 : ℝ) ^ 2 / q
def entry : ℝ := 27 / q

theorem q_pos : 0 < q := by norm_num [q]
theorem nu_nonneg : 0 ≤ nu := by norm_num [nu]
theorem delta_nonneg : 0 ≤ delta := by norm_num [delta, q]
theorem total_nonneg : 0 ≤ total := by norm_num [total, q]
theorem entry_nonneg : 0 ≤ entry := by norm_num [entry, q]

theorem mixed_column_energy (adjoint eL eR : Bool) (x : AES.Word) :
    (∑ y, mixed adjoint eL eR y x ^ 2) ≤ delta := by
  have he : gram (mixed adjoint eL eR) x x = gram (variant adjoint eR) x x := by
    cases eL <;> cases eR <;>
      simp only [mixed, variant, Bool.false_eq_true, if_false, if_true,
        wordConjugate, fourierConjugate, left_fourier_gram]
    all_goals change (gram (kernelCompose (baseResidual adjoint) wordFourier) x x =
      gram (kernelCompose wordFourier (kernelCompose (baseResidual adjoint) wordFourier)) x x)
    all_goals rw [left_fourier_gram]
  rw [← gram_diagonal, he, gram_diagonal]
  exact (PaperAESSource.residualVariant_column_energy_lt_current adjoint eR x).le.trans
    (by norm_num [delta, q])

theorem mixed_row_energy (adjoint eL eR : Bool) (y : AES.Word) :
    (∑ x, mixed adjoint eL eR y x ^ 2) ≤ delta := by
  have hbase (a : Bool) (z : AES.Word) :
      (∑ x, baseResidual a z x ^ 2) ≤ delta := by
    have h := PaperAESSource.residualVariant_column_energy_lt_current (!a) false z
    have hh : (∑ x, baseResidual a z x ^ 2) ≤ (2 / (15 * 4294967296) : ℝ) := by
      simpa only [variant, Bool.false_eq_true, if_false,
        OneSidedWordEnergy.baseResidual_transpose] using h.le
    exact hh.trans (by norm_num [delta, q])
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
    rw [OneSidedWordEnergy.column_energy_eq]
    exact (PaperAESSource.residualVariant_column_energy_lt_current (!adjoint) true y).le.trans
      (by norm_num [delta, q])
  · have he (x : AES.Word) : mixed adjoint true true y x = variant (!adjoint) true x y := by
      have ht : baseResidual (!adjoint) = fun y x => baseResidual adjoint x y := by
        funext a b
        exact OneSidedWordEnergy.baseResidual_transpose adjoint a b
      change wordConjugate (baseResidual adjoint) y x =
        wordConjugate (baseResidual (!adjoint)) x y
      rw [ht, wordConjugate_transpose]
    simp_rw [he]
    exact (PaperAESSource.residualVariant_column_energy_lt_current (!adjoint) true y).le.trans
      (by norm_num [delta, q])

theorem left_fourier_column_energy (T : AES.Word → AES.Word → ℝ) (x : AES.Word) :
    (∑ y, kernelCompose wordFourier T y x ^ 2) = ∑ y, T y x ^ 2 := by
  simpa only [gram_diagonal] using left_fourier_gram T x x

theorem right_fourier_row_energy (T : AES.Word → AES.Word → ℝ) (y : AES.Word) :
    (∑ x, kernelCompose T wordFourier y x ^ 2) = ∑ x, T y x ^ 2 := by
  have he (x : AES.Word) : kernelCompose T wordFourier y x =
      action wordFourier (fun z => T y z) x := by
    unfold kernelCompose action
    apply Finset.sum_congr rfl
    intro z _
    rw [wordFourier_symmetric z x]
    ring
  simp_rw [he]
  exact wordFourier_energy _

-- Route dependency: the trace premise uses the owned physical degree-HS assembly.
theorem mixed_total_energy (adjoint eL eR : Bool) :
    (∑ y, ∑ x, mixed adjoint eL eR y x ^ 2) ≤ total := by
  have hbase : (∑ y, ∑ x, baseResidual adjoint y x ^ 2) ≤ total :=
    (PaperWordTraceVariants.variant_trace_lt adjoint false).le.trans (by norm_num [total, q])
  cases eL <;> cases eR
  · exact hbase
  · simpa only [mixed, Bool.false_eq_true, if_false, if_true,
      right_fourier_row_energy] using hbase
  · simp only [mixed, Bool.false_eq_true, if_false, if_true]
    rw [Finset.sum_comm]
    simp_rw [left_fourier_column_energy]
    rw [Finset.sum_comm]
    exact hbase
  · simp only [mixed, Bool.false_eq_true, if_false, if_true]
    rw [Finset.sum_comm]
    simp_rw [left_fourier_column_energy]
    rw [Finset.sum_comm]
    simp_rw [right_fourier_row_energy]
    exact hbase

theorem mixed_energy (adjoint eL eR : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (mixed adjoint eL eR) f y ^ 2) ≤ nu ^ 2 * ∑ x, f x ^ 2 := by
  have hbase (g : AES.Word → ℝ) :
      (∑ y, action (baseResidual adjoint) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2 := by
    have h := SharpWordNorm.variant_energy adjoint false g
    exact h.trans (mul_le_mul_of_nonneg_right
      (by norm_num [SharpWordNorm.rho, nu])
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  cases eL <;> cases eR
  · exact hbase f
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action]
    have h := hbase (action wordFourier f)
    rw [wordFourier_energy] at h
    exact h
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action,
      wordFourier_energy]
    exact hbase f
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action,
      wordFourier_energy]
    have h := hbase (action wordFourier f)
    rw [wordFourier_energy] at h
    exact h

/-- The current ordinary entry proof is stronger than the printed allowance. -/
theorem ordinary_entry (adjoint : Bool) (y x : AES.Word) :
    |mixed adjoint false false y x| ≤ entry := by
  cases adjoint
  · exact (OrdinaryResidualEntry.actual_word_residual_entry_lt x y).le.trans
      (by norm_num [entry, q])
  · exact (OrdinaryResidualEntry.actual_word_residual_entry_lt y x).le.trans
      (by norm_num [entry, q])

/-- Entry caps imply exactly the fourth resources, without sign restrictions. -/
theorem ordinary_entry_moments (n : ℕ) (adjoint : Bool) :
    PaperThinLines.EntryMoments (fun _ : Fin n => mixed adjoint false false)
      delta total entry entry := by
  have hfourth (u : AES.Word → ℝ) (B : ℝ)
      (hentry : ∀ x, |u x| ≤ entry) (hsecond : (∑ x, u x ^ 2) ≤ B) :
      (∑ x, ‖u x‖ ^ 4) ≤ entry ^ 2 * B := by
    calc
      _ ≤ ∑ x, entry ^ 2 * u x ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        have hx := (sq_le_sq₀ (abs_nonneg (u x)) entry_nonneg).mpr (hentry x)
        have hm := mul_le_mul_of_nonneg_right hx (sq_nonneg (u x))
        calc
          ‖u x‖ ^ 4 = u x ^ 2 * u x ^ 2 := by
            rw [show 4 = 2 * 2 from rfl, pow_mul, Real.norm_eq_abs, sq_abs, pow_two]
          _ ≤ _ := by simpa only [sq_abs] using hm
      _ = entry ^ 2 * ∑ x, u x ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (sq_nonneg entry)
  refine ⟨delta_nonneg, total_nonneg, entry_nonneg, entry_nonneg,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ y
    simpa only [Real.norm_eq_abs, sq_abs] using mixed_row_energy adjoint false false y
  · intro _ x
    simpa only [Real.norm_eq_abs, sq_abs] using mixed_column_energy adjoint false false x
  · intro _
    simpa only [Real.norm_eq_abs, sq_abs] using mixed_total_energy adjoint false false
  · intro _ y
    exact hfourth _ delta (ordinary_entry adjoint y) (mixed_row_energy adjoint false false y)
  · intro _ x
    exact hfourth _ delta (fun y => ordinary_entry adjoint y x)
      (mixed_column_energy adjoint false false x)
  · intro _
    calc
      _ ≤ ∑ y, entry ^ 2 * ∑ x, mixed adjoint false false y x ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        exact hfourth _ _ (ordinary_entry adjoint y) le_rfl
      _ = entry ^ 2 * ∑ y, ∑ x, mixed adjoint false false y x ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (mixed_total_energy adjoint false false)
        (sq_nonneg entry)

end AES8.PaperAESOverlapResources
