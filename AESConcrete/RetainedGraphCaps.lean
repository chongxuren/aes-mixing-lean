import AESConcrete.SingletonResidual
import AESConcrete.RetainedGraphEnergy

/-!
# Physical aggregation of the full-active retained graph energy

The source is an arbitrary signed real function. The actual input support
multiplicity is charged once by Cauchy--Schwarz; the genuine physical output
support energies then add by orthogonality. Only after this physical argument
are the three unchanged certificate entries compared by exact arithmetic.

Candidate only: compilation, independent review and durable source/object
admission remain required. Accepted sources stay frozen. Constructive
mathematics only; no attacks or manuscript changes. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs and
the fixed 10/14/16 target remain unchanged. No return or full AES theorem is
asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RetainedGraphCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

/-- Selected-piece coefficient before either support aggregation. -/
def pieceSquaredBound (d b : Fin 5) : ℝ :=
  rho ^ (2 * b.val) * kappa ^ (d.val - b.val) / (q - 1) ^ (4 - d.val)

theorem pieceSquaredBound_nonneg (d b : Fin 5) : 0 ≤ pieceSquaredBound d b := by
  exact div_nonneg
    (mul_nonneg (pow_nonneg rho_nonneg _) (pow_nonneg kappa_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) _)

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- The actual input multiplicity is charged exactly once. In particular,
`e < b` does not change the arbitrary-signed-input interface. -/
theorem selected_refined_input_energy (d e b : Fin 5) (hbd : b ≤ d) (heb : e ≤ b)
    (p : SelectedSupport d 4) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor d 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) e b) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity e b : ℝ) *
        pieceSquaredBound d b * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel d 4 p) e b heb (pieceSquaredBound d b)
    (pieceSquaredBound_nonneg d b)
    (fun pIn g => RetainedGraphEnergy.selected_piece_energy d e b hbd p pIn g) f

/-- Orthogonal physical output energies add. No Boolean expansion terms are
assigned orthogonality, and the input multiplicity is not charged again. -/
theorem physicalBlock_graph_energy (i j : Fin 14)
    (hi : (blockType i).1 ≠ 0) (hfull : (blockType i).2 = 4)
    (heb : (blockType j).1 ≤ (blockType j).2)
    (hbd : (blockType j).2 ≤ (blockType i).1) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (Fintype.card (SelectedSupport (blockType i).1 4) : ℝ) *
        (ResidualIncidenceCoefficient.multiplicity (blockType j).1 (blockType j).2 : ℝ) *
          pieceSquaredBound (blockType i).1 (blockType j).2 * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy i j hi f, hfull]
  calc
    _ ≤ ∑ p : SelectedSupport (blockType i).1 4,
        (ResidualIncidenceCoefficient.multiplicity (blockType j).1 (blockType j).2 : ℝ) *
          pieceSquaredBound (blockType i).1 (blockType j).2 * ∑ x, f x ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact selected_refined_input_energy (blockType i).1 (blockType j).1
        (blockType j).2 hbd heb p f
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The three new locations, kept separate from the inherited inventory. -/
def retainedPair (i j : Fin 14) : Prop :=
  (i = 10 ∧ j = 4) ∨ (i = 12 ∧ j = 5) ∨ (i = 12 ∧ j = 8)

instance (i j : Fin 14) : Decidable (retainedPair i j) := by
  unfold retainedPair
  infer_instance

private theorem retainedPair_types : ∀ i j : Fin 14, retainedPair i j →
    ((blockType i).1 ≠ 0 ∧ (blockType i).2 = 4 ∧
      (blockType j).1 ≤ (blockType j).2 ∧ (blockType j).2 ≤ (blockType i).1) := by
  decide

/-- Actual output cardinality times actual input multiplicity times the
selected-piece coefficient. These factors have distinct analytic roles. -/
def physicalSquaredBound (i j : Fin 14) : ℝ :=
  (ResidualIncidenceCoefficient.multiplicity (blockType i).1 4 : ℝ) *
    (ResidualIncidenceCoefficient.multiplicity (blockType j).1 (blockType j).2 : ℝ) *
      pieceSquaredBound (blockType i).1 (blockType j).2

/-- The physical bound precedes and does not use the certificate comparison. -/
theorem physical_retained_graph_energy (i j : Fin 14) (h : retainedPair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      physicalSquaredBound i j * ∑ x, f x ^ 2 := by
  obtain ⟨hi, hfull, heb, hbd⟩ := retainedPair_types i j h
  have hda : (blockType i).1 ≤ (4 : Fin 5) := by
    have hd := (blockType i).1.isLt
    omega
  have he := physicalBlock_graph_energy i j hi hfull heb hbd f
  rw [selectedSupport_card (blockType i).1 4 hda] at he
  exact he

theorem physicalSquaredBound_10_4 :
    physicalSquaredBound 10 4 = 24 * pieceSquaredBound 2 1 := by
  -- Expose concrete types before arithmetic; norm_num leaves vector lookups opaque.
  change (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 4 : ℝ) *
    (ResidualIncidenceCoefficient.multiplicity (1 : Fin 5) 1 : ℝ) *
      pieceSquaredBound 2 1 = 24 * pieceSquaredBound 2 1
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem physicalSquaredBound_12_5 :
    physicalSquaredBound 12 5 = 48 * pieceSquaredBound 3 2 := by
  -- The source type (1,2) has multiplicity 12, not 18.
  change (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 4 : ℝ) *
    (ResidualIncidenceCoefficient.multiplicity (1 : Fin 5) 2 : ℝ) *
      pieceSquaredBound 3 2 = 48 * pieceSquaredBound 3 2
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem physicalSquaredBound_12_8 :
    physicalSquaredBound 12 8 = 24 * pieceSquaredBound 3 2 := by
  change (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 4 : ℝ) *
    (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 2 : ℝ) *
      pieceSquaredBound 3 2 = 24 * pieceSquaredBound 3 2
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- Exact rational scalar comparisons with the frozen certificate. This is
independent of the preceding arbitrary-signed physical energy proof. -/
theorem certificate_retained_bounds (i j : Fin 14) (h : retainedPair i j) :
    0 ≤ lambda * L i j ∧ physicalSquaredBound i j ≤ (lambda * L i j) ^ 2 := by
  -- Reuse the type-specific factors, keeping vector lookup reduction separate.
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [physicalSquaredBound_10_4]
    norm_num [pieceSquaredBound, rho, kappa, q,
      AESRound.Terminal.lambda, AESRound.Certificate.L]
  · rw [physicalSquaredBound_12_5]
    norm_num [pieceSquaredBound, rho, kappa, q,
      AESRound.Terminal.lambda, AESRound.Certificate.L]
  · rw [physicalSquaredBound_12_8]
    norm_num [pieceSquaredBound, rho, kappa, q,
      AESRound.Terminal.lambda, AESRound.Certificate.L]

theorem physical_retained_energy (i j : Fin 14) (h : retainedPair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (lambda * L i j) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_retained_graph_energy i j h f).trans
    (mul_le_mul_of_nonneg_right (certificate_retained_bounds i j h).2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_retained_step_cap (i j : Fin 14) (h : retainedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j :=
  kernelOperator_norm_le _ (certificate_retained_bounds i j h).1
    (physical_retained_energy i j h)

theorem system_retained_step_cap (i j : Fin 14) (h : retainedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_retained_step_cap i j h

end AESConcrete.RetainedGraphCaps
