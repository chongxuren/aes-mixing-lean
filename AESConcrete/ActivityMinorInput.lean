import AESConcrete.ActivityMinorTermBounds
import AESConcrete.ActivityMinorEnvelope
import AESConcrete.ActivityCodeGeometry
import AESConcrete.UniformSelectionCounting
import AESConcrete.UniformGraphCaps

/-!
# Signed input aggregation for the actual selected minor tensor

The singleton residual coefficient remains signed until its one energy square.
Boolean terms are aggregated by the triangle inequality, with the common exact
square root of the moment. Genuine input support orthogonality is used only by
the following physical aggregation layer. Accepted historical sources are frozen.

Constructive mathematics only; no attacks. Independent retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and the fixed 10/14/16 target
are unchanged. These candidate proofs require compilation and independent review.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinorInput
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorEnvelope
open AESConcrete.ActivityCodeGeometry
open AESConcrete.ActivityCodeScalar (q s)
open AESConcrete.MultiUniformExpansion
open AESConcrete.UniformSelectionCounting
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- The actual selected tensor after the physical input diffusion. -/
def selectedStepKernel (d a : Fin 5) (p : SelectedSupport d a) :
    AES.WordState → AES.WordState → ℝ :=
  fun y x => selectedWordTensor d a p y (wordMixAddEquiv x)

theorem selectedStepKernel_action (d a : Fin 5) (p : SelectedSupport d a)
    (f : AES.WordState → ℝ) :
    action (selectedStepKernel d a p) f =
      action (selectedWordTensor d a p) (fun x => f (wordMixAddEquiv.symm x)) :=
  FourResidualStep.input_permutation_action _ wordMixAddEquiv.toEquiv f

private theorem action_scale {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (c : ℝ) (f : X → ℝ) :
    action K (fun x => c * f x) = fun y => c * action K f y := by
  funext y
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Arbitrary output kernels preserve exactly the signed singleton factor
of the actual code pullback. No source normalization is inserted. -/
theorem expansionTerm_pullback_energy (K : AES.WordState → AES.WordState → ℝ)
    (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action K (fun x => expansionTerm r 0 σ h (wordMixAddEquiv.symm x)) y ^ 2) =
      (∑ y, action K (unitSubgroupIndicator (wordCode (selectionMask r 0 σ))) y ^ 2) *
        ∑ w, h w ^ 2 := by
  rw [expansionTerm_pullback_eq, action_scale]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, emptyTuple_energy]
  ring

/-- Each source expansion term receives the selected minor's actual code
energy bound; the arbitrary signed coefficient is squared exactly once. -/
theorem selected_expansionTerm_energy (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (hda : d ≤ a) (p : SelectedSupport d a)
    (r : Fin 16) (σ : Selection r 0)
    (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action (selectedStepKernel d a p) (expansionTerm r 0 σ h) y ^ 2) ≤
      termNorm d.val a.val (maskSize (selectionMask r 0 σ)) ^ 2 * ∑ w, h w ^ 2 := by
  rw [selectedStepKernel_action, expansionTerm_pullback_energy]
  exact mul_le_mul_of_nonneg_right
    (ActivityMinorTermBounds.selected_unitCode_energy d a hd hda p
      (selectionMask r 0 σ))
    (Finset.sum_nonneg (fun w _ => sq_nonneg (h w)))

private theorem word_sqrt_card : Real.sqrt (Fintype.card AES.Word : ℝ) = s := by
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num [s]

private theorem word_card_cast : (Fintype.card AES.Word : ℝ) = q := by
  rw [AES.word_card]
  norm_num [q]

/-- The common square root of the moment is factored outside the complete
signed input triangle sum before any squaring. -/
theorem weighted_termNorm_sum (d a b : ℕ) :
    (∑ t : Fin (b + 1), (Nat.choose b t.val : ℝ) * s ^ t.val *
      termNorm d a t.val) =
      (Real.sqrt (moment d) /
        (s ^ (4 - d) * Real.sqrt (q - 1) ^ (a - d))) * inputNumerator d a b := by
  unfold termNorm inputNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem sqrt_sub_one_pow_sq (n : ℕ) :
    (Real.sqrt (q - 1) ^ n) ^ 2 = (q - 1) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul,
    Real.sq_sqrt (le_of_lt ActivityCodeScalar.q_sub_one_pos)]

/-- Exact squaring of the common-moment norm, retaining odd denominator
powers without separate rounded square roots. -/
theorem common_norm_sq (d a b : ℕ) :
    ((Real.sqrt (moment d) /
      (s ^ (4 - d) * Real.sqrt (q - 1) ^ (a - d)) * inputNumerator d a b) /
        Real.sqrt (q - 1) ^ b) ^ 2 = pieceBound d a b := by
  rw [div_pow, mul_pow, div_pow, Real.sq_sqrt (moment_nonneg d), mul_pow,
    sqrt_sub_one_pow_sq, sqrt_sub_one_pow_sq]
  unfold pieceBound
  rw [show (s ^ (4 - d)) ^ 2 = s ^ (2 * (4 - d)) by
    rw [← pow_mul, Nat.mul_comm]]
  rw [pow_add]
  ring

/-- The complete normalized activity input expansion for one selected
physical output. Boolean terms are not assumed orthogonal. -/
theorem selected_multiUniform_energy (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (hda : d ≤ a) (p : SelectedSupport d a)
    (r : Fin 16) (h : (MaskCoordinates 0 → AES.Word) → ℝ) :
    (∑ y, action (selectedStepKernel d a p) (multiUniform r 0 h) y ^ 2) ≤
      pieceBound d.val a.val (Fintype.card (UniformPositions r 0)) * ∑ w, h w ^ 2 := by
  have hn : 1 < Fintype.card AES.Word := by rw [AES.word_card]; norm_num
  have he := multiUniform_action_energy (selectedStepKernel d a p) hn r 0 h
    (fun σ => termNorm d.val a.val (maskSize (selectionMask r 0 σ)))
    (fun _ => termNorm_nonneg _ _ _)
    (fun σ => selected_expansionTerm_energy d a hd hda p r σ h)
  rw [expansion_weighted_sum_by_size hn r 0 (termNorm d.val a.val),
    word_sqrt_card, word_card_cast, weighted_termNorm_sum, common_norm_sq] at he
  exact he

private theorem mask_zero_of_size_zero :
    ∀ E : Fin 16, maskSize E = 0 → E = 0 := by decide

/-- The same signed residual interface when its degree-zero mask is
presented abstractly rather than literally as the empty mask. -/
theorem selected_multiUniform_energy_of_mask_zero (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (hda : d ≤ a) (p : SelectedSupport d a)
    (r E : Fin 16) (hE : maskSize E = 0)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action (selectedStepKernel d a p) (multiUniform r E h) y ^ 2) ≤
      pieceBound d.val a.val (Fintype.card (UniformPositions r E)) * ∑ w, h w ^ 2 := by
  have hz := mask_zero_of_size_zero E hE
  subst E
  exact selected_multiUniform_energy d a hd hda p r h

/-- One genuine degree-zero input support, with its own exact counting
energy. This is the interface consumed by physical support aggregation. -/
theorem selected_piece_energy (d a : Fin 5)
    (hd : d.val = 2 ∨ d.val = 3) (hda : d ≤ a) (p : SelectedSupport d a)
    (b : Fin 5) (pIn : SelectedSupport 0 b) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedStepKernel d a p)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceBound d.val a.val b.val *
        ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, he⟩ := supportIndexComponent_multi_uniform pIn.val
    (by rw [AES.word_card]; norm_num) f
  have hzero : maskSize pIn.val.val.1 = 0 := by
    simpa using pIn.val.property.2
  have ht := selected_multiUniform_energy_of_mask_zero d a hd hda p
    pIn.val.val.2 pIn.val.val.1 hzero h
  rw [UniformGraphCaps.selected_uniformPositions_card 0 b pIn] at ht
  simp only [Fin.val_zero, Nat.sub_zero] at ht
  rw [he, hc]
  exact ht

end AESConcrete.ActivityMinorInput
