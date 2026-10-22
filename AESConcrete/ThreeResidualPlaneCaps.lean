import AESConcrete.ThreeResidualPlaneGeometry
import AESConcrete.ThreeActivePlaneEnergy
import AESConcrete.ActivityMinorInput

/-!
# Exact selected minor and signed plane energy for (11,11)

The actual input is an arbitrary signed supported state function; in
particular no separability or extra condition on a joint residual triple is
assumed. The selected support component supplies its genuine input zero. The
output zero is imposed by the original omitted zero-unit leg. The two zeros
define the actual ShortenedCode plane, not a cancellation endpoint.

The exact minor transport has no q-factor or nonzero-uniform denominator. Two
residual operators and one residual column give rho^4*kappa. Restricting the
original amplitude gives subenergy, not equality with the full triple.
Geometry, minor transport and analytic estimates have explicit interfaces;
physical aggregation, certificate comparison and operator caps are separate.

Constructive AES10/14/16.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeResidualPlaneCaps
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeResidualPlaneGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.NonzeroUniformGraphCap (zeroUnit)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

/-- Only actual input inactivity is required of the arbitrary signed source. -/
def InputSupported (pIn : SelectedSupport 3 3) (G : AES.WordState → ℝ) : Prop :=
  ∀ x, G x ≠ 0 → ∀ i, maskBit pIn.val.val.2 i = true → x i = 0

theorem component_supported (pIn : SelectedSupport 3 3) (f : AES.WordState → ℝ) :
    InputSupported pIn (supportIndexComponent (0 : AES.Word) pIn.val f) := by
  intro x hx i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero pIn.val i hi f x hx

/-- Every omitted leg is the actual zero-unit leg, with no uniform weight. -/
theorem omittedWeight_product (pOut : SelectedSupport 3 3) (x : AES.WordState) :
    (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut) j (x j.val)) =
      if ∀ i, maskBit pOut.val.val.2 i = true → x i = 0 then 1 else 0 := by
  by_cases hx : ∀ i, maskBit pOut.val.val.2 i = true → x i = 0
  · rw [if_pos hx]
    apply Finset.prod_eq_one
    intro j _
    have hj := nonretained_inactive pOut j.val j.property
    simp [nonzeroWeight, selectedZeros, hj, zeroUnit, supportConstant,
      identityKernel, hx j.val hj]
  · rw [if_neg hx]
    obtain ⟨i, hi, hxi⟩ : ∃ i, maskBit pOut.val.val.2 i = true ∧ x i ≠ 0 := by
      simpa using hx
    have hE := (inactive_iff_not_retained pOut i).mp hi
    apply Finset.prod_eq_zero
      (Finset.mem_univ (⟨i, hE⟩ : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1))
    simp [nonzeroWeight, selectedZeros, hi, zeroUnit, supportConstant,
      identityKernel, hxi]

/-- Exact restriction to the physical two-zero plane; there is no source weight. -/
theorem plane_supported_sum (pOut pIn : SelectedSupport 3 3) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 x → F x = 0) :
    (∑ x, F x) = ∑ c : PlaneCode pOut pIn, F c.val := by
  calc
    (∑ x, F x) = ∑ x, if graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · exact hF x hx
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _
        (by intro x; simp [ShortenedWeightedGeometry.shortenedSubgroup]) _

/-- Unnormalized response of the actual residual triple on the physical plane. -/
def response (pOut pIn : SelectedSupport 3 3) (G : AES.WordState → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => G c.val)

/-- The joint residual amplitude is arbitrary and need not factor. -/
def jointResponse (pOut pIn : SelectedSupport 3 3)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => h (residualTuple pOut pIn c))

/-- Exact original minor transport, before applying any analytic bound.
The input and output zero conditions are retained in the source subtype. -/
theorem minorResponse_eq (pOut pIn : SelectedSupport 3 3)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    minorResponse (selectedRetained 3 3 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) = response pOut pIn G := by
  unfold selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut) j
          (wordMixAddEquiv x j.val)) =
        if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0 :=
    omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x =>
    (∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)) *
      (if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) * G x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      by_cases hg : G x = 0
      · simp only [F, hg, mul_zero]
      · have hz : ∀ i, maskBit pIn.val.val.2 i = true → x i = 0 := hG x hg
        have ho : ¬ ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 :=
          fun ho => hx ⟨ho, hz⟩
        simp only [F, if_neg ho, mul_zero, zero_mul]
    rw [plane_supported_sum pOut pIn F hF]
    unfold response IndexedTripleEnergy.response
    apply Finset.sum_congr rfl
    intro c _
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    dsimp only [F]
    rw [if_pos ho, mul_one]
    unfold curve
    ring

/-- The unit omitted output vector preserves exact counting energy. -/
theorem selectedStep_energy_eq (pOut pIn : SelectedSupport 3 3)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut) G y ^ 2) =
      ∑ y, response pOut pIn G y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G hG]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn G y ^ 2)

/-- Two actual operator legs and one column leg bound the same signed source. -/
theorem response_energy (pOut pIn : SelectedSupport 3 3) (G : AES.WordState → ℝ) :
    (∑ y, response pOut pIn G y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ x, G x ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have he := ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (retainedCoordinates_card pOut) s (curve pOut pIn) (fun c => G c.val)
    (retained_pair_bijective pOut pIn s)
  exact he.trans (mul_le_mul_of_nonneg_left (plane_subenergy pOut pIn G)
    (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg))

/-- An arbitrary signed JOINT triple has only subenergy on the actual plane. -/
theorem joint_response_energy (pOut pIn : SelectedSupport 3 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, jointResponse pOut pIn h y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have he := ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (retainedCoordinates_card pOut) s (curve pOut pIn)
    (fun c => h (residualTuple pOut pIn c)) (retained_pair_bijective pOut pIn s)
  exact he.trans (mul_le_mul_of_nonneg_left (residual_subenergy pOut pIn h)
    (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg))

abbrev pieceSquaredBound : ℝ := rho ^ 4 * kappa

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg

/-- This stronger interface needs only actual input support, not residuality. -/
theorem selected_supported_energy (pOut pIn : SelectedSupport 3 3)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut) G y ^ 2) ≤
      pieceSquaredBound * ∑ x, G x ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn G hG]
  exact response_energy pOut pIn G

/-- The exact original support component supplies the supported-G premise. -/
theorem selected_piece_energy (pOut pIn : SelectedSupport 3 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 :=
  selected_supported_energy pOut pIn _ (component_supported pIn f)

end AESConcrete.ThreeResidualPlaneCaps
