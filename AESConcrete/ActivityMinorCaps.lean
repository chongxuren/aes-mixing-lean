import AESConcrete.ActivityMinorInput

/-!
# Physical selected-minor energy aggregation

Degree-zero input supports are bounded with exactly one Cauchy--Schwarz
multiplicity. Distinct physical output support pieces are orthogonal, so
their exact energies add. Boolean expansion terms have no such orthogonality.
The scalar equality is separate from both of these operator arguments.

Constructive mathematics only; no attacks or accepted historical-source edits.
Independent retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target are preserved. Compilation and independent
review remain required before admitting any candidate cap to the inventory.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinorCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput
open AESConcrete.ActivityMinorEnvelope
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Kernel-generalized input support aggregation. The output functions can
overlap; the exact orthogonality used here concerns the source support pieces. -/
theorem selected_output_energy_of_piece_energy
    (K : AES.WordState → AES.WordState → ℝ) (e b : Fin 5) (heb : e ≤ b)
    (C : ℝ) (hC : 0 ≤ C)
    (hpiece : ∀ (p : SelectedSupport e b) (f : AES.WordState → ℝ),
      (∑ y, action K (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤
        C * ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2)
    (f : AES.WordState → ℝ) :
    (∑ y, (∑ p : SelectedSupport e b,
      action K (supportIndexComponent (0 : AES.Word) p.val f) y) ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e b : ℝ) * C * ∑ x, f x ^ 2 := by
  let n : ℝ := Fintype.card (SelectedSupport e b)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ∑ y, n * ∑ p : SelectedSupport e b,
        action K (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 :=
      Finset.sum_le_sum (fun y _ => OrdinaryGraphCaps.sum_sq_le_card
        (fun p : SelectedSupport e b =>
          action K (supportIndexComponent (0 : AES.Word) p.val f) y))
    _ = n * ∑ p : SelectedSupport e b, ∑ y,
        action K (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ n * ∑ p : SelectedSupport e b,
        C * ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hn
      exact Finset.sum_le_sum (fun p _ => hpiece p f)
    _ = (n * C) * ∑ p : SelectedSupport e b, ∑ x,
        supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (n * C) * ∑ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hn hC)
      exact OrdinaryGraphCaps.selected_input_energy_le (0 : AES.Word)
        (by rw [AES.word_card]; norm_num) e b f
    _ = (ResidualIncidenceCoefficient.multiplicity e b : ℝ) * C * ∑ x, f x ^ 2 := by
      rw [show n = (ResidualIncidenceCoefficient.multiplicity e b : ℝ) by
        simp only [n, selectedSupport_card e b heb]]

/-- One actual selected physical output, after summing all actual
degree-zero input support pieces. `choose(4,b)` is charged exactly once. -/
theorem selected_refined_input_energy (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (hda : d ≤ a) (p : SelectedSupport d a)
    (b : Fin 5) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor d a p)
      (fun x => action (refinedKernel (0 : AES.Word) 0 b) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (Nat.choose 4 b.val : ℝ) * pieceBound d.val a.val b.val * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  have he := selected_output_energy_of_piece_energy (selectedStepKernel d a p)
    0 b (by omega) (pieceBound d.val a.val b.val) (pieceBound_nonneg _ _ _)
    (fun pIn g => selected_piece_energy d a hd hda p b pIn g) f
  simpa only [ResidualIncidenceCoefficient.multiplicity, Fin.val_zero,
    Nat.choose_zero_right, Nat.sub_zero, one_mul] using he

private theorem minorPair_types : ∀ i j : Fin 14, ActivityMinorScalar.minorPair i j →
    (((blockType i).1.val = 2 ∨ (blockType i).1.val = 3) ∧
      (blockType i).1 ≤ (blockType i).2 ∧ (blockType j).1 = 0) := by decide

/-- Exact physical output support aggregation, before the independent
finite scalar identity. Output counts are the actual support cardinalities. -/
theorem physicalBlock_envelope_energy (i j : Fin 14)
    (h : ActivityMinorScalar.minorPair i j) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (Fintype.card (SelectedSupport (blockType i).1 (blockType i).2) : ℝ) *
        (Nat.choose 4 ((blockType j).2.val) : ℝ) *
        pieceBound ((blockType i).1.val) ((blockType i).2.val) ((blockType j).2.val) *
          ∑ x, f x ^ 2 := by
  obtain ⟨hd, hda, hj⟩ := minorPair_types i j h
  have hi : (blockType i).1 ≠ 0 := by
    intro hi
    have hi' := congrArg Fin.val hi
    simp only [Fin.val_zero] at hi'
    rcases hd with hd | hd <;> omega
  rw [physicalBlock_selected_tensor_energy i j hi f]
  calc
    _ ≤ ∑ p : SelectedSupport (blockType i).1 (blockType i).2,
        (Nat.choose 4 ((blockType j).2.val) : ℝ) *
          pieceBound ((blockType i).1.val) ((blockType i).2.val) ((blockType j).2.val) *
            ∑ x, f x ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      unfold physicalInput
      rw [hj]
      exact selected_refined_input_energy (blockType i).1 (blockType i).2 hd hda p
        (blockType j).2 f
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The scalar envelope is now justified for the actual physical block,
with independent retained keys and the original coordinate indexing. -/
theorem physicalBlock_energy (i j : Fin 14)
    (h : ActivityMinorScalar.minorPair i j) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      ActivityMinorScalar.squaredBound i (blockType j).2 * ∑ x, f x ^ 2 := by
  have he := physicalBlock_envelope_energy i j h f
  rw [physicalEnvelope_eq i j h] at he
  exact he

end AESConcrete.ActivityMinorCaps
