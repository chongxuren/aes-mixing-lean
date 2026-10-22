/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwoZeroMass
import AES8.Reductions.Fibers.WordMixTwoZeroPairInfo
import AES8.Historical.TwoActiveScalars
import AES8.Estimates.FirstHigh.TwoZeroElevenMoment
import AESMixing.ProjectionGram

/-!
# Actual signed masses on literal two-output-zero fibers

All response legs retain the same conditioned original source word. The
incoming-twelve constant channel is its literal symmetric idempotent block.
No current-boundary independence, source splitting or absolute Gram kernel
is assumed.
Constructive work only; no attacks or predecessor/manuscript changes.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ActualTwoActiveMass
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.TwelveConditionalResponse
open AES8.TwelvePatternCoordinates (order order_zero order_ne_zero)
open AES8.OneSourceEventMoment (atomCap columnCap traceCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.TwoZeroTwelveMoment (constantCap)
open AES8.TwoActiveScalars

/-- Projector Gram identity supplies the full constant-column energy. -/
theorem constant_column_le (x : AES.Word) :
    (∑ y, constantMatrix (0 : AES.Word) y x ^ 2) ≤ constantCap := by
  let C := constantMatrix (0 : AES.Word)
  have hs : ∀ y z, C y z = C z y := by
    intro y z
    simpa only [C, supportPiece, Bool.false_eq_true, if_false, if_true] using (supportPiece_symmetric (0 : AES.Word) false false y z)
  have hi : kernelCompose C C = C := by
    simpa only [C, supportPiece, Bool.false_eq_true, if_false, if_true] using
      (supportPiece_compose (0 : AES.Word) SupportProfile.word_card_gt_one false false false)
  have hg : (∑ y, C y x ^ 2) = C x x := by
    simpa only [gram, pow_two] using projection_gram C hs hi x x
  rw [show (∑ y, constantMatrix (0 : AES.Word) y x ^ 2) = C x x from hg]
  exact (le_abs_self _).trans (TwoZeroTwelveMoment.constant_entry_le x x)

theorem conditional_thirteen_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    |∑ g : WordMixTwoZeroFiber.G r, conditionalResponse b k w g.val| ≤ thirteenFullMassCap := by
  have h := TwoZeroMass.four_residual_mass_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun i => affineEquiv k w i) (fun g : WordMixTwoZeroFiber.G r => g.val)
    (wordLaw (sourceInput b k))
    (WordMixTwoZeroPairInfo.coords_bijective r hr 0 1 (by decide))
    (WordMixTwoZeroPairInfo.coords_bijective r hr 2 3 (by decide))
    atomCap columnCap traceCap (by norm_num [atomCap, q])
    (by norm_num [columnCap, q]) (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun _ x => OneSourceEventMoment.residual_column_le x)
    (fun _ => OneSourceEventMoment.residual_trace_le)
  change |∑ g : WordMixTwoZeroFiber.G r, conditionalResponse b k w g.val| ≤ thirteenFullMassCap at h
  exact h

theorem conditional_twelve_pattern_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (w : OtherAssignments k) (j : Fin 4) :
    |∑ g : WordMixTwoZeroFiber.G r, conditionalPattern b k w j g.val| ≤
      twelvePatternFullMassCap := by
  have h01 : order j 0 ≠ order j 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) ((order j).injective h)
  have h23 : order j 2 ≠ order j 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) ((order j).injective h)
  have h := TwoZeroMass.three_residual_constant_mass_le
    (fun i => patternChannel j (order j i)) (fun i => affineEquiv k w (order j i))
    (fun g : WordMixTwoZeroFiber.G r => fun i => g.val (order j i)) (wordLaw (sourceInput b k))
    (WordMixTwoZeroPairInfo.coords_bijective r hr (order j 0) (order j 1) h01)
    (WordMixTwoZeroPairInfo.coords_bijective r hr (order j 2) (order j 3) h23)
    atomCap constantCap columnCap traceCap (11 / (30 * q))
    (by norm_num [atomCap, q]) (by norm_num [constantCap, q])
    (by norm_num [columnCap, q]) (by norm_num [traceCap, q]) (by norm_num [q])
    constant_column_product_le
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun x => by
      simpa only [order_zero, patternChannel, if_pos rfl, ite_true] using constant_column_le x)
    (fun x => by
      simpa only [patternChannel, if_neg (order_ne_zero j 2 (by decide))] using
        OneSourceEventMoment.residual_column_le x)
    (by simpa only [patternChannel, if_neg (order_ne_zero j 1 (by decide))] using
      OneSourceEventMoment.residual_trace_le)
    (by simpa only [patternChannel, if_neg (order_ne_zero j 3 (by decide))] using
      OneSourceEventMoment.residual_trace_le)
  have heq : (∑ g : WordMixTwoZeroFiber.G r, conditionalPattern b k w j g.val) =
      ∑ g : WordMixTwoZeroFiber.G r, ZeroFiberResponseEnergy.response
        (fun i => patternChannel j (order j i)) (fun i => affineEquiv k w (order j i))
        (fun g : WordMixTwoZeroFiber.G r => fun i => g.val (order j i))
        (wordLaw (sourceInput b k)) g := by
    apply Finset.sum_congr rfl
    intro g _
    exact TwoZeroTwelveMoment.conditionalPattern_eq_response (fun g : WordMixTwoZeroFiber.G r => g.val)
      b k w j g
  rw [heq]
  exact h

theorem actual_thirteen_full_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : b ≠ 0) :
    |∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) 13 g.val| ≤ thirteenFullMassCap := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  rw [actual_component_thirteen_eq_probability_mixture b k, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  exact ActualZeroMoment.abs_probability_sum_le (conditionWeight b k)
    (fun w => ∑ g : WordMixTwoZeroFiber.G r, conditionalResponse b k w g.val)
    thirteenFullMassCap (conditionWeight_nonnegative b k) (conditionWeight_total b k)
    (fun w => conditional_thirteen_mass_le r hr b k hk w)

theorem actual_twelve_full_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : b ≠ 0) :
    |∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) 12 g.val| ≤
      4 * twelvePatternFullMassCap := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  rw [actual_component_twelve_eq_probability_mixture b k, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  apply ActualZeroMoment.abs_probability_sum_le (conditionWeight b k) _ (4 * twelvePatternFullMassCap)
    (conditionWeight_nonnegative b k) (conditionWeight_total b k)
  intro w
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin 4, |∑ g : WordMixTwoZeroFiber.G r, conditionalPattern b k w j g.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, twelvePatternFullMassCap := Finset.sum_le_sum
      (fun j _ => conditional_twelve_pattern_mass_le r hr b k hk w j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]

end AES8.ActualTwoActiveMass
