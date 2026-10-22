import AES8.Estimates.Byte.PaperByteLineBounds
import AESConcrete.ActualActivityPairBounds

/-!
# Activity-pair intervals from the printed byte resources

The physical response, label geometry and the nonuniform overlap estimates
retain their exact existing definitions. Only diagonal cubic energy and the
uniform mixed line/plane bound are rebuilt from PaperByteLineBounds. The
Walsh input is explicit in the conditional endpoint; the concrete endpoint
only instantiates the accepted input provider. No historical exact cube or
mixed-line theorem is called by the new interval proof.
Constructive source candidate only; no attacks or canonical/vendor/paper edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityPairBounds
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions marked_remaining)
open AESConcrete.ActivityGraphContraction
open AESConcrete.ActivityChoiceGeometry
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.ActualActivityPairBounds
open AESConcrete.ActivityPairIntervals (inInterval pairInterval concreteResources PairBounds)
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem scale_abs (x : ℝ) : |(4294967296 : ℝ)*x| = (4294967296 : ℝ)*|x| := by
  rw [abs_mul]
  norm_num

-- Exact identities only: these preserve the /256 line and /4096 plane scales.
private theorem response_line (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool) (hw : weight A b = 2)
    (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y = ShortenedLineBounds.normalizedResponse inverse
      (lineChoice out A r b hr hw).val.1 (lineChoice out A r b hr hw).val.2
      (markedPositions e) (fun i => leg (o i) false) y :=
  line_contraction_eq_normalized inverse out e A r b hr hw _ y

private theorem response_plane (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool) (hw : weight A b = 3)
    (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y =
      ShortenedPlaneResponse.normalizedPlaneResponse inverse e (planeChoice out A r b hr hw)
        (fun i => leg (o i) false) y :=
  plane_contraction_eq_normalized inverse out hout e A r b hr hw _ y

private theorem response_as_line (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool) (hw : weight A b = 2)
    (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y =
      DampedLineGram.lineResponse (fun i => leg (o i) false)
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          (lineChoice out A r b hr hw).val.1 (lineChoice out A r b hr hw).val.2
          (lineChoice out A r b hr hw).property.2 (markedPositions e)
          (marked_remaining e (lineChoice out A r b hr hw))) y := by
  exact (response_line inverse out e r hr o A b hw y).trans
    (ShortenedLineBounds.normalizedResponse_eq_line inverse _ _
      (lineChoice out A r b hr hw).property.2 (markedPositions e)
      (marked_remaining e (lineChoice out A r b hr hw)) _ y)

private theorem response_as_fourier_line (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (o : Fin 3 → Orientation)
    (A : Fin 16) (b : Bool) (hw : weight A b = 3) (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y =
      DampedLineGram.lineResponse (fun i => leg (o i) true)
        (ShortenedPlane.dualCoordinatePerm inverse out hout e
          (planeChoice out A r b hr hw)) y := by
  exact (response_plane inverse out hout e r hr o A b hw y).trans
    (ShortenedPlaneResponse.actual_plane_response_eq_fourier_leg inverse out hout e
      (planeChoice out A r b hr hw) o y)

theorem actualPair_diagonal_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool)
    (hw : weight A b = 2 ∨ weight A b = 3) :
    0 ≤ actualPair inverse e r o (A,b) (A,b) ∧
      actualPair inverse e r o (A,b) (A,b) ≤ ByteLineBounds.a3 := by
  constructor
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4294967296)
    exact Finset.sum_nonneg (fun y _ => mul_self_nonneg _)
  · rcases hw with hw | hw
    · let p := lineChoice out A r b hr hw
      unfold actualPair
      simp_rw [response_as_line inverse out e r hr o A b hw]
      simp only [← pow_two]
      exact PaperByteLineBounds.actual_line_energy_bound_of_walsh hWalsh o (fun _ => false) _
    · let p := planeChoice out A r b hr hw
      unfold actualPair
      simp_rw [response_as_fourier_line inverse out hout e r hr o A b hw]
      simp only [← pow_two]
      exact PaperByteLineBounds.actual_line_energy_bound_of_walsh hWalsh o (fun _ => true) _

theorem actualPair_mixed_uniform_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 3) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ ByteLineBounds.b3 := by
  let p := lineChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  rw [actualPair, scale_abs]
  simp_rw [response_as_line inverse out e r hr o A b hw,
    response_as_fourier_line inverse out hout e r hr o B c hv]
  exact PaperByteLineBounds.actual_mixed_line_pair_bound_of_walsh hWalsh o _ _

private theorem label_parameters : ∀ (A B : Fin 16) (b c : Bool),
    intersection A B b c ≤ weight A b ∧ intersection A B b c ≤ weight B c ∧
      weight A b + weight B c ≤ 5 + intersection A B b c := by decide

private theorem full_intersection_labels : ∀ (A B : Fin 16) (b c : Bool),
    weight A b = weight B c → intersection A B b c = weight A b → A = B ∧ b = c := by decide

private theorem intersection_swap : ∀ (A B : Fin 16) (b c : Bool),
    intersection A B b c = intersection B A c b := by decide

private theorem line_interval_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 2) :
    inInterval (pairInterval concreteResources 2 2 (intersection A B b c))
      (actualPair inverse e r o (A,b) (B,c)) := by
  have hjle := (label_parameters A B b c).1
  have hcases : intersection A B b c = 2 ∨ intersection A B b c = 1 ∨ intersection A B b c = 0 := by omega
  rcases hcases with hj | hj | hj
  · obtain ⟨hA, hb⟩ := full_intersection_labels A B b c (hw.trans hv.symm) (hj.trans hw.symm)
    subst B
    subst c
    simpa [inInterval, pairInterval, concreteResources, hj] using
      actualPair_diagonal_of_walsh hWalsh inverse out hout e r hr o A b (Or.inl hw)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_line_eta1 inverse out e r hr o A B b c hw hv hj)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_line_eta2 inverse out hout e r hr o A B b c hw hv hj)

private theorem plane_interval_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 3) (hv : weight B c = 3) :
    inInterval (pairInterval concreteResources 3 3 (intersection A B b c))
      (actualPair inverse e r o (A,b) (B,c)) := by
  rcases label_parameters A B b c with ⟨hjle, _, hunion⟩
  have hcases : intersection A B b c = 3 ∨ intersection A B b c = 2 ∨ intersection A B b c = 1 := by omega
  rcases hcases with hj | hj | hj
  · obtain ⟨hA, hb⟩ := full_intersection_labels A B b c (hw.trans hv.symm) (hj.trans hw.symm)
    subst B
    subst c
    simpa [inInterval, pairInterval, concreteResources, hj] using
      actualPair_diagonal_of_walsh hWalsh inverse out hout e r hr o A b (Or.inr hw)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_plane_eta1 inverse out hout e r hr o A B b c hw hv hj)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_plane_eta2 inverse out hout e r hr o A B b c hw hv hj)

private theorem mixed_interval_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 3) :
    inInterval (pairInterval concreteResources 2 3 (intersection A B b c))
      (actualPair inverse e r o (A,b) (B,c)) := by
  have hjle := (label_parameters A B b c).1
  have hcases : intersection A B b c = 2 ∨ intersection A B b c = 1 ∨ intersection A B b c = 0 := by omega
  rcases hcases with hj | hj | hj
  · simpa [pairInterval, concreteResources, hj] using
      actualPair_mixed_containment inverse out hout e r hr o A B b c hw hv hj
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_mixed_transverse inverse out hout e r hr o A B b c hw hv hj)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_mixed_uniform_of_walsh hWalsh inverse out hout e r hr o A B b c hw hv)

/-- The complete generic local-pair premise is proved for the actual
q-scaled physical graph contractions, with fixed ordinary residual legs. -/
theorem actual_pair_bounds_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) : PairBounds concreteResources (actualPair inverse e r o) := by
  intro A B b c
  change inInterval (pairInterval concreteResources (weight A b) (weight B c) (intersection A B b c))
    (actualPair inverse e r o (A,b) (B,c))
  by_cases hw : weight A b = 2 ∨ weight A b = 3
  · by_cases hv : weight B c = 2 ∨ weight B c = 3
    · rcases hw with hw | hw <;> rcases hv with hv | hv
      · simpa only [hw, hv] using line_interval_of_walsh hWalsh inverse out hout e r hr o A B b c hw hv
      · simpa only [hw, hv] using mixed_interval_of_walsh hWalsh inverse out hout e r hr o A B b c hw hv
      · have h := mixed_interval_of_walsh hWalsh inverse out hout e r hr o B A c b hv hw
        rw [← intersection_swap A B b c, actualPair_symmetric] at h
        simpa [pairInterval, hw, hv] using h
      · simpa only [hw, hv] using plane_interval_of_walsh hWalsh inverse out hout e r hr o A B b c hw hv
    · rw [actualPair_zero_right inverse out hout e r hr o A B b c hv]
      simp [inInterval, pairInterval, hv]
  · rw [actualPair_zero_left inverse out hout e r hr o A B b c hw]
    simp [inInterval, pairInterval, hw]

/-- Concrete specialization; the analytic input remains explicit above. -/
theorem actual_pair_bounds (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) : PairBounds concreteResources (actualPair inverse e r o) :=
  actual_pair_bounds_of_walsh PaperCitedByteBounds.concreteWalshBound inverse out hout e r hr o

#print axioms actualPair_diagonal_of_walsh
#print axioms actualPair_mixed_uniform_of_walsh
#print axioms actual_pair_bounds_of_walsh
#print axioms actual_pair_bounds
end AES8.PaperActivityPairBounds
