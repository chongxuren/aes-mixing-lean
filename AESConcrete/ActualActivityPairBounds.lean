import AESConcrete.ActivityChoiceGeometry
import AESConcrete.ActivityHighWeightVanishing
import AESConcrete.ActivityPairIntervals
import AESConcrete.ShortenedPlaneOverlap
import AESConcrete.ShortenedContainmentBounds

/-!
# Actual local activity pair intervals

The pair quantity is the q-scaled inner product of two actual remaining-
output contractions of graphResponse. All ordinary residual orientations
are fixed per marked leg and shared by the paired vectors. The physical
activity-to-zero-mask correspondence supplies every geometric hypothesis
of the actual line, plane, transverse, containment, and mixed bounds.

The local pair table is a conclusion. No pair interval, code intersection,
or operator bound is supplied as a premise. Constructive scope only; full
centered-word identification and the four-triple assembly remain separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActualActivityPairBounds
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions marked_remaining)
open AESConcrete.ActivityFrameContraction (contraction)
open AESConcrete.ActivityGraphContraction
open AESConcrete.ActivityPlaneContraction
open AESConcrete.ActivityHighWeightVanishing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.ActivityChoiceGeometry
open AESConcrete.ActivityPairIntervals (ActivityLabel inInterval pairInterval concreteResources PairBounds)

set_option maxRecDepth 100000

def actualResponse (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (o : Fin 3 → Orientation) (a : ActivityLabel) (y : Fin 3 → Byte) : ℝ :=
  contraction (graphResponse (byteDiffusionHom inverse) a.1 r (markedPositions e)
    (fun i => leg (o i) false) y) a.2

def actualPair (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (o : Fin 3 → Orientation) (a b : ActivityLabel) : ℝ :=
  (4294967296 : ℝ) * ∑ y : Fin 3 → Byte,
    actualResponse inverse e r o a y * actualResponse inverse e r o b y

theorem actualPair_symmetric (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (o : Fin 3 → Orientation) (a b : ActivityLabel) :
    actualPair inverse e r o a b = actualPair inverse e r o b a := by
  unfold actualPair
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

private theorem scale_abs (x : ℝ) : |(4294967296 : ℝ)*x| = (4294967296 : ℝ)*|x| := by
  rw [abs_mul]
  norm_num

private theorem label_parameters : ∀ (A B : Fin 16) (b c : Bool),
    intersection A B b c ≤ weight A b ∧ intersection A B b c ≤ weight B c ∧
      weight A b + weight B c ≤ 5 + intersection A B b c := by decide

private theorem full_intersection_labels : ∀ (A B : Fin 16) (b c : Bool),
    weight A b = weight B c → intersection A B b c = weight A b → A = B ∧ b = c := by decide

private theorem intersection_swap : ∀ (A B : Fin 16) (b c : Bool),
    intersection A B b c = intersection B A c b := by decide

private theorem labels_ne_of_intersection_lt (A B : Fin 16) (b c : Bool)
    (h : intersection A B b c < weight A b) : (A,b) ≠ (B,c) := by
  intro heq
  have hA := congrArg Prod.fst heq
  have hb := congrArg Prod.snd heq
  change A = B at hA
  change b = c at hb
  subst B
  subst c
  rw [intersection_self] at h
  omega

theorem actualResponse_zero (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool)
    (hw : ¬ (weight A b = 2 ∨ weight A b = 3)) (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y = 0 := by
  have hcases : weight A b ≤ 1 ∨ 4 ≤ weight A b := by omega
  rcases hcases with hlow | hhigh
  · exact actual_low_weight_contraction_zero inverse A r b hlow (markedPositions e) o (fun _ => false) y
  · exact actual_high_weight_contraction_zero inverse out hout e A r b
      (output_mask_disjoint out r hr b) hhigh o y

theorem actualPair_zero_left (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : ¬ (weight A b = 2 ∨ weight A b = 3)) :
    actualPair inverse e r o (A,b) (B,c) = 0 := by
  unfold actualPair
  simp_rw [actualResponse_zero inverse out hout e r hr o A b hw]
  simp

theorem actualPair_zero_right (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : ¬ (weight B c = 2 ∨ weight B c = 3)) :
    actualPair inverse e r o (A,b) (B,c) = 0 := by
  rw [actualPair_symmetric]
  exact actualPair_zero_left inverse out hout e r hr o B A c b hw

theorem actualPair_diagonal (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool)
    (hw : weight A b = 2 ∨ weight A b = 3) :
    0 ≤ actualPair inverse e r o (A,b) (A,b) ∧
      actualPair inverse e r o (A,b) (A,b) ≤ ByteLineBounds.a3 := by
  constructor
  · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 4294967296)
    exact Finset.sum_nonneg (fun y _ => mul_self_nonneg _)
  · rcases hw with hw | hw
    · let p := lineChoice out A r b hr hw
      have h := actual_line_contraction_energy inverse A r b hw (markedPositions e)
        (marked_remaining e p) o (fun _ => false)
      simpa only [actualPair, actualResponse, pow_two] using h
    · have h := actual_plane_contraction_energy inverse out hout e A r b
        (output_mask_disjoint out r hr b) hw o
      simpa only [actualPair, actualResponse, pow_two] using h

private theorem response_line (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool) (hw : weight A b = 2) (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y = ShortenedLineBounds.normalizedResponse inverse
      (lineChoice out A r b hr hw).val.1 (lineChoice out A r b hr hw).val.2
      (markedPositions e) (fun i => leg (o i) false) y :=
  line_contraction_eq_normalized inverse out e A r b hr hw _ y

private theorem response_plane (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A : Fin 16) (b : Bool) (hw : weight A b = 3) (y : Fin 3 → Byte) :
    actualResponse inverse e r o (A,b) y =
      ShortenedPlaneResponse.normalizedPlaneResponse inverse e (planeChoice out A r b hr hw)
        (fun i => leg (o i) false) y :=
  plane_contraction_eq_normalized inverse out hout e A r b hr hw _ y

theorem actualPair_line_eta1 (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 2) (hj : intersection A B b c = 1) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ LineOverlap.eta1 := by
  let p := lineChoice out A r b hr hw
  let q := lineChoice out B r c hr hv
  have hpq : p ≠ q := lineChoice_ne out A B r b c hr hw hv
    (labels_ne_of_intersection_lt A B b c (by omega))
  have hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2 := line_line_common_two r A B b c hw hv hj
  rw [actualPair, scale_abs]
  simp_rw [response_line inverse out e r hr o A b hw, response_line inverse out e r hr o B c hv]
  exact ShortenedPlaneOverlap.actual_shortened_line_same_flag_eta1 inverse out e p q hpq hcommon o (fun _ => false)

theorem actualPair_line_eta2 (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 2) (hj : intersection A B b c = 0) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ LineOverlap.eta2 := by
  let p := lineChoice out A r b hr hw
  let q := lineChoice out B r c hr hv
  have hpq : p ≠ q := lineChoice_ne out A B r b c hr hw hv
    (labels_ne_of_intersection_lt A B b c (by omega))
  rw [actualPair, scale_abs]
  simp_rw [response_line inverse out e r hr o A b hw, response_line inverse out e r hr o B c hv]
  exact ShortenedPlaneOverlap.actual_shortened_line_same_flag_eta2 inverse out hout e p q hpq o (fun _ => false)

theorem actualPair_plane_eta1 (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 3) (hv : weight B c = 3) (hj : intersection A B b c = 2) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ LineOverlap.eta1 := by
  let p := planeChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  have hpq : p ≠ q := planeChoice_ne out A B r b c hr hw hv
    (labels_ne_of_intersection_lt A B b c (by omega))
  have hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1 := plane_plane_common_one r A B b c hw hv hj
  rw [actualPair, scale_abs]
  simp_rw [response_plane inverse out hout e r hr o A b hw, response_plane inverse out hout e r hr o B c hv]
  exact ShortenedPlaneOverlap.actual_shortened_plane_pair_eta1 inverse out hout e p q hpq hcommon o

theorem actualPair_plane_eta2 (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 3) (hv : weight B c = 3) (hj : intersection A B b c = 1) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ LineOverlap.eta2 := by
  let p := planeChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  have hpq : p ≠ q := planeChoice_ne out A B r b c hr hw hv
    (labels_ne_of_intersection_lt A B b c (by omega))
  rw [actualPair, scale_abs]
  simp_rw [response_plane inverse out hout e r hr o A b hw, response_plane inverse out hout e r hr o B c hv]
  exact ShortenedPlaneOverlap.actual_shortened_plane_pair_eta2 inverse out hout e p q hpq o

theorem actualPair_mixed_containment (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 3) (hj : intersection A B b c = 2) :
    inInterval (ContainmentCodeBounds.z3-ContainmentCodeBounds.h3,
      ContainmentCodeBounds.z3+ContainmentCodeBounds.h3) (actualPair inverse e r o (A,b) (B,c)) := by
  let p := lineChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  have hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2 := mixed_common_two r A B b c hw hv hj
  unfold actualPair
  simp_rw [response_line inverse out e r hr o A b hw, response_plane inverse out hout e r hr o B c hv]
  exact ShortenedContainmentBounds.actual_line_plane_containment_interval inverse out hout e p q hcommon o

theorem actualPair_mixed_transverse (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 3) (hj : intersection A B b c = 1) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ MixedCodeBounds.f3 := by
  let p := lineChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  have hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1 := mixed_common_one r A B b c hw hv hj
  rw [actualPair, scale_abs]
  simp_rw [response_line inverse out e r hr o A b hw, response_plane inverse out hout e r hr o B c hv]
  exact ShortenedMixedBounds.actual_line_plane_transverse_bound inverse out hout e p q hcommon o

theorem actualPair_mixed_uniform (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) (A B : Fin 16) (b c : Bool)
    (hw : weight A b = 2) (hv : weight B c = 3) :
    |actualPair inverse e r o (A,b) (B,c)| ≤ ByteLineBounds.b3 := by
  let p := lineChoice out A r b hr hw
  let q := planeChoice out B r c hr hv
  rw [actualPair, scale_abs]
  simp_rw [response_line inverse out e r hr o A b hw, response_plane inverse out hout e r hr o B c hv]
  exact ShortenedPlaneResponse.actual_shortened_line_plane_pair_bound inverse out hout e p q o

private theorem line_interval (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
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
      actualPair_diagonal inverse out hout e r hr o A b (Or.inl hw)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_line_eta1 inverse out e r hr o A B b c hw hv hj)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_line_eta2 inverse out hout e r hr o A B b c hw hv hj)

private theorem plane_interval (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
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
      actualPair_diagonal inverse out hout e r hr o A b (Or.inr hw)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_plane_eta1 inverse out hout e r hr o A B b c hw hv hj)
  · simpa [inInterval, pairInterval, concreteResources, hj] using
      abs_le.mp (actualPair_plane_eta2 inverse out hout e r hr o A B b c hw hv hj)

private theorem mixed_interval (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
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
      abs_le.mp (actualPair_mixed_uniform inverse out hout e r hr o A B b c hw hv)

/-- The complete generic local-pair premise is proved for the actual
q-scaled physical graph contractions, with fixed ordinary residual legs. -/
theorem actual_pair_bounds (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (o : Fin 3 → Orientation) : PairBounds concreteResources (actualPair inverse e r o) := by
  intro A B b c
  change inInterval (pairInterval concreteResources (weight A b) (weight B c) (intersection A B b c))
    (actualPair inverse e r o (A,b) (B,c))
  by_cases hw : weight A b = 2 ∨ weight A b = 3
  · by_cases hv : weight B c = 2 ∨ weight B c = 3
    · rcases hw with hw | hw <;> rcases hv with hv | hv
      · simpa only [hw, hv] using line_interval inverse out hout e r hr o A B b c hw hv
      · simpa only [hw, hv] using mixed_interval inverse out hout e r hr o A B b c hw hv
      · have h := mixed_interval inverse out hout e r hr o B A c b hv hw
        rw [← intersection_swap A B b c, actualPair_symmetric] at h
        simpa [pairInterval, hw, hv] using h
      · simpa only [hw, hv] using plane_interval inverse out hout e r hr o A B b c hw hv
    · rw [actualPair_zero_right inverse out hout e r hr o A B b c hv]
      simp [inInterval, pairInterval, hv]
  · rw [actualPair_zero_left inverse out hout e r hr o A B b c hw]
    simp [inInterval, pairInterval, hw]

end AESConcrete.ActualActivityPairBounds
