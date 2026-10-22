import AESConcrete.DoubleUniformMinorResponse
import AESConcrete.DoubleUniformFourierEnergy
import AESConcrete.DoubleUniformLineEnergy

/-!
# Selected-piece lemmas for the double-uniform source

The original finite source sum is reindexed to the actual three single-zero
planes and three double-zero lines. Every term keeps the same arbitrary signed
residual amplitude, including its value at zero. The seven signed responses
are combined before squaring. A rational plane envelope follows from rho
squared divided by kappa being 6615/8, below 29 squared.

No cap or inventory increment is asserted. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct reference pairs and
fixed 10/14/16 stay unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
open AESConcrete.DoubleUniformShortening
open AESConcrete.DoubleUniformPlaneGeometry
open AESConcrete.DoubleUniformMinorResponse
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem wordMixHom_apply (x : AES.WordState) :
    wordMixAddEquiv.toAddMonoidHom x = wordMixAddEquiv x := rfl

/-- Selected-piece coefficient, before physical input/output multiplicities. -/
def pieceSquaredBound : ℝ :=
  rho ^ 2 * kappa ^ 2 * (q + 87 * s + 3) ^ 2 / (q - 1) ^ 3

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := by
  unfold pieceSquaredBound
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)) (sq_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) 3)

/-- Exact one-condition source restriction, before any energy inequality. -/
private theorem conditional_response_eq {S I V : Type*}
    [Fintype S] [Fintype I] [Fintype V] (P : S → Prop) [DecidablePred P]
    (T : V → V → ℝ) (c : S → I → V) (h : S → ℝ) (y : I → V) :
    (∑ x, if P x then h x * (∏ i, T (y i) (c x i)) else 0) =
      IndexedTripleEnergy.response T (fun x : {x // P x} => c x.val)
        (fun x => h x.val) y := by
  rw [← Finset.sum_filter]
  calc
    _ = ∑ x : {x // P x}, h x.val * (∏ i, T (y i) (c x.val i)) :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      unfold IndexedTripleEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Source transport keeps the finite instances on both presentations explicit. -/
private theorem response_reindex {C D I V : Type*}
    [Fintype C] [Fintype D] [Fintype I]
    (T : V → V → ℝ) (e : C ≃ D) (c : D → I → V) (h : D → ℝ) (y : I → V) :
    IndexedTripleEnergy.response T c h y =
      IndexedTripleEnergy.response T (fun x => c (e x)) (fun x => h (e x)) y := by
  unfold IndexedTripleEnergy.response
  exact (Equiv.sum_comp e (fun x => h x * ∏ i, T (y i) (c x i))).symm

/-- The raw full source keeps both original uniform word fibers. -/
theorem raw_full_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (retainedEquiv pOut pIn) (fun uv => h uv.1) := by
    funext y
    unfold WeightedResponse.rawResponse IndexedTripleEnergy.response residualKernel
    apply Finset.sum_congr rfl
    intro uv _
    have hc : retainedEquiv pOut pIn uv = curve pOut pIn uv := rfl
    rw [hc]
  rw [heq]
  exact DoubleUniformFourierEnergy.retained_fullResponse_energy pOut pIn h

/-- Either original uniform-input-zero restriction is the actual source plane. -/
theorem source_zero_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 j) y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 j) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (sourceZeroPlaneRetainedHom wordMixAddEquiv.toAddMonoidHom pIn j pOut.val.val.1)
        (fun uv => h uv.val.1) := by
    let e : sourceZeroPlane (V := AES.Word) pIn j ≃
        {uv : SourceDomain pIn // uv.2 j = 0} :=
      { toFun := fun uv => ⟨uv.val, uv.property⟩
        invFun := fun uv => ⟨uv.val, uv.property⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    have hcurve : (fun uv : sourceZeroPlane (V := AES.Word) pIn j =>
        curve pOut pIn uv.val) =
        (sourceZeroPlaneRetainedHom wordMixAddEquiv.toAddMonoidHom pIn j pOut.val.val.1 :
          sourceZeroPlane (V := AES.Word) pIn j → Retained pOut → AES.Word) := by
      funext uv i
      change wordMixAddEquiv (source pIn uv.val.1 uv.val.2) i.val =
        wordMixAddEquiv.toAddMonoidHom (source pIn uv.val.1 uv.val.2) i.val
      rw [wordMixHom_apply]
    funext y
    unfold WeightedResponse.zeroResponse residualKernel
    calc
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun uv : {uv : SourceDomain pIn // uv.2 j = 0} => curve pOut pIn uv.val)
          (fun uv => h uv.val.1) y :=
        conditional_response_eq (fun uv : SourceDomain pIn => uv.2 j = 0)
          (residualMatrix AES.wordSuperboxKernel 0) (curve pOut pIn) (fun uv => h uv.1) y
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun uv : sourceZeroPlane (V := AES.Word) pIn j => curve pOut pIn uv.val)
          (fun uv => h uv.val.1) y :=
        response_reindex (residualMatrix AES.wordSuperboxKernel 0) e _ _ y
      _ = _ := congrArg
        (fun c => IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          c (fun uv : sourceZeroPlane (V := AES.Word) pIn j => h uv.val.1) y) hcurve
  rw [heq]
  exact DoubleUniformFourierEnergy.retained_sourceZeroPlaneResponse_energy pOut pIn j h

/-- The omitted-output restriction is the actual shortened physical plane. -/
theorem omitted_zero_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have heq : WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (planeRetainedHom wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) pOut.val.val.1)
        (planeAmplitude wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) h) := by
    let e : zeroPlane wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) ≃
        {uv : SourceDomain pIn // omittedValue pOut pIn uv = 0} :=
      { toFun := fun uv => ⟨uv.val, by
          have hz := zeroPlane_condition wordMixAddEquiv.toAddMonoidHom
            pIn (omittedLabel pOut) uv
          rw [wordMixHom_apply] at hz
          exact hz⟩
        invFun := fun uv => ⟨uv.val, by
          change wordMixAddEquiv.toAddMonoidHom (source pIn uv.val.1 uv.val.2)
            (omittedLabel pOut) = 0
          rw [wordMixHom_apply]
          exact uv.property⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    have hcurve :
        (fun uv : zeroPlane wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) =>
          curve pOut pIn uv.val) =
        (planeRetainedHom wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) pOut.val.val.1 :
          zeroPlane wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) →
            Retained pOut → AES.Word) := by
      funext uv i
      change wordMixAddEquiv (source pIn uv.val.1 uv.val.2) i.val =
        wordMixAddEquiv.toAddMonoidHom (source pIn uv.val.1 uv.val.2) i.val
      rw [wordMixHom_apply]
    funext y
    unfold WeightedResponse.zeroResponse residualKernel
    calc
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun uv : {uv : SourceDomain pIn // omittedValue pOut pIn uv = 0} =>
            curve pOut pIn uv.val) (fun uv => h uv.val.1) y :=
        conditional_response_eq (fun uv : SourceDomain pIn => omittedValue pOut pIn uv = 0)
          (residualMatrix AES.wordSuperboxKernel 0) (curve pOut pIn) (fun uv => h uv.1) y
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun uv : zeroPlane wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) =>
            curve pOut pIn uv.val) (fun uv => h uv.val.1) y :=
        response_reindex (residualMatrix AES.wordSuperboxKernel 0) e _ _ y
      _ = _ := congrArg
        (fun c => IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          c (fun uv : zeroPlane wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) =>
            h uv.val.1) y) hcurve
  rw [heq]
  exact DoubleUniformFourierEnergy.retained_zeroPlaneResponse_energy pOut pIn h

/-- The two source-uniform zeros leave precisely the original residual axis. -/
theorem source_source_line_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) (h : AES.Word → ℝ) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
      (fun uv => uv.2 (uniformSecond pIn)) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have heq : TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
      (fun uv => uv.2 (uniformSecond pIn)) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun u : AES.Word => sourceMap wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 (u, 0)) h := by
    funext y
    have hzero (v : SourceUniformPositions pIn → AES.Word) :
        (v (uniformFirst pIn) = 0 ∧ v (uniformSecond pIn) = 0) ↔ v = 0 := by
      constructor
      · intro hv
        exact uniform_tuple_eq_zero pIn v hv.1 hv.2
      · intro hv
        simp only [hv, Pi.zero_apply, and_self]
    unfold TripleResponse.intersectionResponse IndexedTripleEnergy.response
    simp_rw [hzero]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    simp [residualKernel, curve, sourceMap]
  rw [heq]
  exact DoubleUniformLineEnergy.retained_residualSource_energy pOut pIn h

/-- Either source-uniform-zero and omitted-output-zero intersection is a line. -/
theorem source_output_line_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 j) (omittedValue pOut pIn) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have heq : TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 j) (omittedValue pOut pIn) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun c : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) j =>
          sourceMap wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 c.val.val)
        (fun c => h c.val.val.1) := by
    -- Flatten the two actual subgroup restrictions before transporting the sum.
    -- This avoids reducing nested concrete word subtypes during elaboration.
    let e : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) j ≃
        {uv : SourceDomain pIn // uv.2 j = 0 ∧ omittedValue pOut pIn uv = 0} :=
      { toFun := fun c => ⟨c.val.val, by
          constructor
          · exact c.property
          · have hz := zeroPlane_condition wordMixAddEquiv.toAddMonoidHom
              pIn (omittedLabel pOut) c.val
            rw [wordMixHom_apply] at hz
            exact hz⟩
        invFun := fun uv => ⟨⟨uv.val, by
          change wordMixAddEquiv.toAddMonoidHom (source pIn uv.val.1 uv.val.2)
            (omittedLabel pOut) = 0
          rw [wordMixHom_apply]
          exact uv.property.2⟩, uv.property.1⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    have hcurve :
        (fun c : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) j =>
          curve pOut pIn c.val.val) =
        (fun c : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) j =>
          sourceMap wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 c.val.val) := by
      funext c i
      change wordMixAddEquiv (source pIn c.val.val.1 c.val.val.2) i.val =
        wordMixAddEquiv.toAddMonoidHom (source pIn c.val.val.1 c.val.val.2) i.val
      rw [wordMixHom_apply]
    funext y
    unfold TripleResponse.intersectionResponse residualKernel
    calc
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun uv : {uv : SourceDomain pIn // uv.2 j = 0 ∧ omittedValue pOut pIn uv = 0} =>
            curve pOut pIn uv.val) (fun uv => h uv.val.1) y :=
        conditional_response_eq
          (fun uv : SourceDomain pIn => uv.2 j = 0 ∧ omittedValue pOut pIn uv = 0)
          (residualMatrix AES.wordSuperboxKernel 0) (curve pOut pIn) (fun uv => h uv.1) y
      _ = IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          (fun c : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn (omittedLabel pOut) j =>
            curve pOut pIn c.val.val) (fun c => h c.val.val.1) y :=
        response_reindex (residualMatrix AES.wordSuperboxKernel 0) e _ _ y
      _ = _ := congrArg
        (fun c => IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
          c (fun uv : sourceZeroOutputLine wordMixAddEquiv.toAddMonoidHom pIn
            (omittedLabel pOut) j => h uv.val.val.1) y) hcurve
  rw [heq]
  exact DoubleUniformLineEnergy.retained_sourceZeroOutputLine_energy pOut pIn j h

theorem rho_sq_div_kappa : rho ^ 2 / kappa = 6615 / 8 := by norm_num [rho, kappa]

theorem rho_sq_le_29_sq_mul_kappa : rho ^ 2 ≤ 29 ^ 2 * kappa := by
  norm_num [rho, kappa]

/-- The same rational envelope serves all three plane norms. -/
theorem plane_squared_safe : q * rho ^ 4 * kappa ≤ (29 * s * rho * kappa) ^ 2 := by
  calc
    _ = (q * rho ^ 2 * kappa) * rho ^ 2 := by ring
    _ ≤ (q * rho ^ 2 * kappa) * (29 ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (mul_nonneg (mul_nonneg (le_of_lt q_pos) (sq_nonneg rho)) kappa_nonneg)
    _ = _ := by rw [← s_sq]; ring

/-- All seven signed response norms are added before squaring. -/
theorem response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (h : AES.Word → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  let a : ℝ := rho * kappa
  let b : ℝ := 29 * s * a
  have ha : 0 ≤ a := mul_nonneg rho_nonneg kappa_nonneg
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) ha
  have ha_sq : a ^ 2 = rho ^ 2 * kappa ^ 2 := by dsimp [a]; ring
  have hsum : 0 ≤ ∑ u, h u ^ 2 := Finset.sum_nonneg (fun u _ => sq_nonneg (h u))
  have hplane : q * rho ^ 4 * kappa ≤ b ^ 2 :=
    plane_squared_safe.trans_eq (by dsimp [b, a]; ring)
  have hA : (∑ y, WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤ (q * a) ^ 2 * ∑ u, h u ^ 2 :=
    (raw_full_energy pOut pIn h).trans_eq (by rw [mul_pow, ha_sq]; ring)
  have hB : (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn)) y ^ 2) ≤
      b ^ 2 * ∑ u, h u ^ 2 :=
    (source_zero_energy pOut pIn (uniformFirst pIn) h).trans
      (mul_le_mul_of_nonneg_right hplane hsum)
  have hC : (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn)) y ^ 2) ≤
      b ^ 2 * ∑ u, h u ^ 2 :=
    (source_zero_energy pOut pIn (uniformSecond pIn) h).trans
      (mul_le_mul_of_nonneg_right hplane hsum)
  have hD : (∑ y, WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (omittedValue pOut pIn) y ^ 2) ≤ b ^ 2 * ∑ u, h u ^ 2 :=
    (omitted_zero_energy pOut pIn h).trans (mul_le_mul_of_nonneg_right hplane hsum)
  have hE : (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
      (fun uv => uv.2 (uniformSecond pIn)) y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (source_source_line_energy pOut pIn h).trans_eq (by rw [ha_sq])
  have hF : (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
      (omittedValue pOut pIn) y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (source_output_line_energy pOut pIn (uniformFirst pIn) h).trans_eq (by rw [ha_sq])
  have hG : (∑ y, TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn))
      (omittedValue pOut pIn) y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 :=
    (source_output_line_energy pOut pIn (uniformSecond pIn) h).trans_eq (by rw [ha_sq])
  have he := SevenResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun uv : SourceDomain pIn => h uv.1) (residualKernel pOut pIn)
    (fun uv => uv.2 (uniformFirst pIn)) (fun uv => uv.2 (uniformSecond pIn))
    (omittedValue pOut pIn) h (triple_zero_kernel pOut pIn)
    (q * a) b a (mul_nonneg (le_of_lt q_pos) ha) hb ha hA hB hC hD hE hF hG
  change (∑ y, response pOut pIn h y ^ 2) ≤ _ at he
  rw [DoubleUniformFourierEnergy.word_card_real] at he
  have hcoef : (q * a + 3 * b + 3 * a) ^ 2 / (q - 1) ^ 3 = pieceSquaredBound := by
    calc
      _ = a ^ 2 * (q + 87 * s + 3) ^ 2 / (q - 1) ^ 3 := by dsimp [b]; ring
      _ = _ := by rw [ha_sq]; rfl
  rw [hcoef] at he
  exact he

/--
Actual selected-step energy with the original support-component energy.
Physical support multiplicities are separate.
-/
theorem selected_piece_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, henergy, hresponse⟩ := selected_component_response pOut pIn f
  calc
    _ = ∑ y, response pOut pIn h y ^ 2 := hresponse
    _ ≤ pieceSquaredBound * ∑ u, h u ^ 2 := response_energy pOut pIn h
    _ = _ := by rw [henergy]

end AESConcrete.DoubleUniformCaps
