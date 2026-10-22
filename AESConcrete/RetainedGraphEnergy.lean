import AESConcrete.HeterogeneousGraphEnergy
import AESConcrete.RetainedGraphMasks
import AESConcrete.ActivityMinorInput
import AESConcrete.UniformGraphScalar

/-!
# Signed selected-piece graph energy for full-active outputs

The free physical mask lies inside the actual retained residual labels. Only
those free labels receive residual operator estimates. The dependent retained
labels receive actual column estimates, and omitted constant labels receive
exact normalized column estimates. The actual input is an arbitrary signed
support component with its original counting energy.

This module adds no physical aggregation, cap or inventory entry.
It imports no SingletonResidual module. Independent retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and fixed 10/14/16 stay
unchanged.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.RetainedGraphEnergy
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates pullback_fiber_unique
  supportIndexComponent_supported)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.RetainedGraphMasks
open AESConcrete.NonzeroUniformGraphCap
  (nonzeroUniform nonzeroUniform_energy nonzeroConstantMatrix_rank_one)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

set_option maxRecDepth 100000

/-- The actual local output channel when every physical output is active. -/
def fullActiveLeg (d : Fin 5) (p : SelectedSupport d 4) (i : Fin 4) :
    AES.Word → AES.Word → ℝ :=
  if AES.maskBit p.val.val.1 i then residualMatrix AES.wordSuperboxKernel 0
    else constantMatrix 0

/-- A column coefficient is attached to its original physical label. -/
def columnCap (d : Fin 5) (p : SelectedSupport d 4) (i : Fin 4) : ℝ :=
  if AES.maskBit p.val.val.1 i then kappa else 1 / (q - 1)

theorem columnCap_nonneg (d : Fin 5) (p : SelectedSupport d 4) (i : Fin 4) :
    0 ≤ columnCap d p i := by
  unfold columnCap
  split_ifs
  · exact kappa_nonneg
  · exact div_nonneg zero_le_one (le_of_lt q_sub_one_pos)

/-- The original selected tensor, without changing any physical leg. -/
theorem selectedWordTensor_fullActive (d : Fin 5) (p : SelectedSupport d 4) :
    selectedWordTensor d 4 p = coordinateKernel (fullActiveLeg d p) := by
  unfold selectedWordTensor supportChannelTensor
  congr 1
  funext i y x
  have hz : AES.maskBit p.val.val.2 i ≠ true := fullActive_selectedZeros_empty d p i
  by_cases hm : AES.maskBit p.val.val.1 i = true <;>
    simp [supportChannelLeg, fullActiveLeg, hm, hz]

/--
Elementary omitted-vector estimate, independent of the singleton-source
estimates. The zero word is explicitly included in the two-case proof.
-/
theorem nonzeroUniform_sq_le (x : AES.Word) :
    nonzeroUniform x ^ 2 ≤ 1 / (q - 1) := by
  have hc : (Fintype.card AES.Word : ℝ) = q := by rw [AES.word_card]; rfl
  have hn : supportConstant false x ^ 2 ≤ (1 : ℝ) := by
    by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]
  unfold nonzeroUniform
  rw [div_pow, hc, Real.sq_sqrt (le_of_lt q_sub_one_pos)]
  exact div_le_div_of_nonneg_right hn (le_of_lt q_sub_one_pos)

/-- The output unit vector of an omitted constant coordinate has energy one,
so its genuine kernel-column energy is the squared input unit-vector value. -/
theorem constantMatrix_column_energy (v : AES.Word) :
    (∑ y, constantMatrix (0 : AES.Word) y v ^ 2) ≤ 1 / (q - 1) := by
  calc
    _ = nonzeroUniform v ^ 2 := by
      simp_rw [nonzeroConstantMatrix_rank_one AES.word_card_gt_one, mul_pow]
      rw [← Finset.sum_mul, nonzeroUniform_energy AES.word_card_gt_one, one_mul]
    _ ≤ _ := nonzeroUniform_sq_le v

/-- Only an actual retained label is assigned the small operator coefficient. -/
theorem fullActiveLeg_operator_energy (d : Fin 5) (p : SelectedSupport d 4)
    (i : Fin 4) (hi : selectedRetained d 4 p i) (f : AES.Word → ℝ) :
    (∑ y, action (fullActiveLeg d p i) f y ^ 2) ≤ rho ^ 2 * ∑ x, f x ^ 2 := by
  have hm : AES.maskBit p.val.val.1 i = true := hi
  simpa only [fullActiveLeg, hm, if_true, rho] using
    SharpDampedWordNorm.word_superbox_residual_energy f

/-- Every dependent label receives its own actual column coefficient. -/
theorem fullActiveLeg_column_energy (d : Fin 5) (p : SelectedSupport d 4)
    (i : Fin 4) (v : AES.Word) :
    (∑ y, fullActiveLeg d p i y v ^ 2) ≤ columnCap d p i := by
  by_cases hm : AES.maskBit p.val.val.1 i = true
  · simp only [fullActiveLeg, columnCap, hm, if_true]
    simpa only [kappa] using (AllColumnBound.actual_word_residual_column_energy_lt v).le
  · simp only [fullActiveLeg, columnCap, hm]
    exact constantMatrix_column_energy v

/-- Exact heterogeneous product on the actual dependent-label subtypes. -/
theorem dependent_column_product (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    (∏ j : OtherCoordinates (freeMask d b hbd p), columnCap d p j.val) =
      kappa ^ (d.val - b.val) / (q - 1) ^ (4 - d.val) := by
  let m := freeMask d b hbd p
  have hr : Fintype.card {j : OtherCoordinates m // AES.maskBit p.val.val.1 j.val = true} =
      d.val - b.val := by
    simpa only [← Nat.card_eq_fintype_card, DependentRetained, selectedRetained] using
      freeMask_dependentRetained_card d b hbd p
  have ho : Fintype.card {j : OtherCoordinates m // AES.maskBit p.val.val.1 j.val ≠ true} =
      4 - d.val := by
    simpa only [← Nat.card_eq_fintype_card, DependentOmitted, selectedRetained] using
      freeMask_dependentOmitted_card d b hbd p
  rw [Fintype.card_subtype] at hr ho
  change (∏ j : OtherCoordinates m,
    if AES.maskBit p.val.val.1 j.val then kappa else 1 / (q - 1)) = _
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hr, ho]
  simp only [div_pow, one_pow]
  ring

/-- Every actual selected source is supported on its full active mask. The
size is an actual source support count, regardless of its residual degree. -/
theorem source_activeMask_size (e b : Fin 5) (p : SelectedSupport e b) :
    AES.maskSize (maskComplement p.val.val.2) = b.val := by
  rw [maskComplement_size]
  have hp := p.property
  omega

/-- Arbitrary-signed-input selected-piece energy. The complete source support
and its exact counting energy are retained; no source-vector decomposition or
normalization by code cardinality is introduced. No physical cap is asserted. -/
theorem selected_piece_energy (d e b : Fin 5) (hbd : b ≤ d)
    (pOut : SelectedSupport d 4) (pIn : SelectedSupport e b)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedStepKernel d 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      (rho ^ (2 * b.val) * kappa ^ (d.val - b.val) / (q - 1) ^ (4 - d.val)) *
        ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  let m := freeMask d b hbd pOut
  let G := supportIndexComponent (0 : AES.Word) pIn.val f
  have hsize : AES.maskSize m = AES.maskSize (maskComplement pIn.val.val.2) :=
    (freeMask_size d b hbd pOut).trans (source_activeMask_size e b pIn).symm
  have hgraph := pullback_fiber_unique wordMixAddEquiv wordMixAddEquiv_zeroMDS
    (maskComplement pIn.val.val.2) m hsize G (supportIndexComponent_supported pIn.val f)
  have he := HeterogeneousGraphEnergy.coordinate_partial_graph_energy
    (fullActiveLeg d pOut) m (fun _ => rho) (fun j => columnCap d pOut j.val)
    (fun j => columnCap_nonneg d pOut j.val)
    (fun i g => fullActiveLeg_operator_energy d pOut i.val
      (freeMask_retained d b hbd pOut i.val i.property) g)
    (fun j v => fullActiveLeg_column_energy d pOut j.val v)
    (fun z => G (wordMixAddEquiv.symm z)) hgraph
  have hfree : (∏ _ : MaskCoordinates m, rho) ^ 2 = rho ^ (2 * b.val) := by
    simp only [Finset.prod_const, Finset.card_univ]
    rw [freeCoordinates_card d b hbd pOut, ← pow_mul, Nat.mul_comm]
  have hsource : (∑ z, G (wordMixAddEquiv.symm z) ^ 2) = ∑ x, G x ^ 2 :=
    wordMixAddEquiv.symm.toEquiv.sum_comp (fun x => G x ^ 2)
  rw [hfree, dependent_column_product d b hbd pOut, hsource] at he
  rw [selectedStepKernel_action, selectedWordTensor_fullActive]
  change (∑ y, action (coordinateKernel (fullActiveLeg d pOut))
    (fun z => G (wordMixAddEquiv.symm z)) y ^ 2) ≤ _
  exact he.trans_eq (by ring)

end AESConcrete.RetainedGraphEnergy
