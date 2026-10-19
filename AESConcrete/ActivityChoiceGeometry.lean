import AESConcrete.ActivityPlaneContraction
import AESConcrete.ShortenedLineBounds

/-!
# Physical zero masks of five-coordinate activity choices

The four input activity bits and one remaining-output bit have physical
zero masks given by inputZeroMask/outputZeroMask. Their complement relation
is proved here, including exact common-zero counts and injectivity for one
fixed remaining output coordinate. Weight-two labels yield actual line
choices; weight-three labels reuse the actual plane-choice constructor.

The additive common-zero identity is retained before natural subtraction,
so truncation cannot change the intended five-coordinate set arithmetic.
Constructive scope only. No pair estimate or final word identification is
assumed or added, and existing checked sources remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityChoiceGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions marked_remaining)
open AESConcrete.ActivityFrameContraction (contraction)
open AESConcrete.ActivityGraphContraction
open AESConcrete.ActivityPlaneContraction

set_option maxRecDepth 100000

def bit (b : Bool) : ℕ := if b then 1 else 0

def weight (a : Fin 16) (b : Bool) : ℕ := maskSize a + bit b

def intersection (a a' : Fin 16) (b b' : Bool) : ℕ :=
  maskSize (maskIntersection a a') + bit (b && b')

/-- Output-zero mask first, input-zero mask second, as in ShorteningChoice. -/
def zeroPair (r : Fin 4) (a : Fin 16) (b : Bool) : Fin 16 × Fin 16 :=
  (outputZeroMask r b, inputZeroMask a)

def commonZeros (r : Fin 4) (a a' : Fin 16) (b b' : Bool) : ℕ :=
  maskSize (maskIntersection (outputZeroMask r b) (outputZeroMask r b')) +
    maskSize (maskIntersection (inputZeroMask a) (inputZeroMask a'))

private theorem input_common_balance : ∀ a a' : Fin 16,
    maskSize (maskIntersection (inputZeroMask a) (inputZeroMask a')) + maskSize a + maskSize a' =
      4 + maskSize (maskIntersection a a') := by decide

private theorem output_common_balance : ∀ (r : Fin 4) (b b' : Bool),
    maskSize (maskIntersection (outputZeroMask r b) (outputZeroMask r b')) + bit b + bit b' =
      1 + bit (b && b') := by decide

private theorem outputZeroMask_injective : ∀ r : Fin 4, Function.Injective (outputZeroMask r) := by decide

theorem intersection_self : ∀ (a : Fin 16) (b : Bool), intersection a a b b = weight a b := by decide

/-- Exact balance between physical zero count and activity weight. -/
theorem zero_weight_balance (r : Fin 4) (a : Fin 16) (b : Bool) :
    maskSize (zeroPair r a b).1 + maskSize (zeroPair r a b).2 + weight a b = 5 :=
  constraint_balance a r b

/-- Complement inclusion-exclusion without any natural-number truncation. -/
theorem common_weight_balance (r : Fin 4) (a a' : Fin 16) (b b' : Bool) :
    commonZeros r a a' b b' + weight a b + weight a' b' = 5 + intersection a a' b b' := by
  have hi := input_common_balance a a'
  have ho := output_common_balance r b b'
  unfold commonZeros weight intersection
  omega

/-- Natural-number form of 5-w-v+j. The intersection is added before
subtraction, preserving the exact value when w+v exceeds five. -/
theorem commonZeros_eq (r : Fin 4) (a a' : Fin 16) (b b' : Bool) :
    commonZeros r a a' b b' = 5 + intersection a a' b b' - (weight a b + weight a' b') := by
  have h := common_weight_balance r a a' b b'
  omega

theorem commonZeros_int (r : Fin 4) (a a' : Fin 16) (b b' : Bool) :
    (commonZeros r a a' b b' : ℤ) =
      5 - (weight a b : ℤ) - (weight a' b' : ℤ) + (intersection a a' b b' : ℤ) := by
  have h := common_weight_balance r a a' b b'
  omega

/-- With the remaining output r fixed, different activity labels give
different physical zero-mask pairs. -/
theorem zeroPair_injective (r : Fin 4) :
    Function.Injective (fun p : Fin 16 × Bool => zeroPair r p.1 p.2) := by
  intro x y hxy
  apply Prod.ext
  · have h := congrArg (fun p : Fin 16 × Fin 16 => maskComplement p.2) hxy
    simpa only [zeroPair, inputZeroMask, maskComplement_involutive] using h
  · exact outputZeroMask_injective r (congrArg Prod.fst hxy)

theorem zeroPair_eq_iff (r : Fin 4) (a a' : Fin 16) (b b' : Bool) :
    zeroPair r a b = zeroPair r a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have hp : (a,b) = (a',b') := by
      apply zeroPair_injective r
      exact h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual line shortening derived from a weight-two activity label. -/
def lineChoice (out a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hweight : weight a b = 2) : ShorteningChoice out 3 :=
  ⟨zeroPair r a b, output_mask_disjoint out r hr b, by
    have h := zero_weight_balance r a b
    omega⟩

/-- Reuse the checked actual plane constructor at activity weight three. -/
def planeChoice (out a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hweight : weight a b = 3) : ShorteningChoice out 2 :=
  activityPlaneChoice out a r b (output_mask_disjoint out r hr b) hweight

theorem lineChoice_val (out a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 2) :
    (lineChoice out a r b hr hw).val = zeroPair r a b := rfl

theorem planeChoice_val (out a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 3) :
    (planeChoice out a r b hr hw).val = zeroPair r a b := rfl

theorem lineChoice_eq_iff (out a a' : Fin 16) (r : Fin 4) (b b' : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 2) (hw' : weight a' b' = 2) :
    lineChoice out a r b hr hw = lineChoice out a' r b' hr hw' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    apply (zeroPair_eq_iff r a a' b b').mp
    exact congrArg (fun p : ShorteningChoice out 3 => p.val) h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem planeChoice_eq_iff (out a a' : Fin 16) (r : Fin 4) (b b' : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 3) (hw' : weight a' b' = 3) :
    planeChoice out a r b hr hw = planeChoice out a' r b' hr hw' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    apply (zeroPair_eq_iff r a a' b b').mp
    exact congrArg (fun p : ShorteningChoice out 2 => p.val) h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem lineChoice_ne (out a a' : Fin 16) (r : Fin 4) (b b' : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 2) (hw' : weight a' b' = 2)
    (hne : (a,b) ≠ (a',b')) : lineChoice out a r b hr hw ≠ lineChoice out a' r b' hr hw' := by
  intro h
  obtain ⟨ha, hb⟩ := (lineChoice_eq_iff out a a' r b b' hr hw hw').mp h
  exact hne (Prod.ext ha hb)

theorem planeChoice_ne (out a a' : Fin 16) (r : Fin 4) (b b' : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 3) (hw' : weight a' b' = 3)
    (hne : (a,b) ≠ (a',b')) : planeChoice out a r b hr hw ≠ planeChoice out a' r b' hr hw' := by
  intro h
  obtain ⟨ha, hb⟩ := (planeChoice_eq_iff out a a' r b b' hr hw hw').mp h
  exact hne (Prod.ext ha hb)

theorem line_line_common_two (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 2) (hw' : weight a' b' = 2) (hj : intersection a a' b b' = 1) :
    commonZeros r a a' b b' = 2 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem line_line_common_one (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 2) (hw' : weight a' b' = 2) (hj : intersection a a' b b' = 0) :
    commonZeros r a a' b b' = 1 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem plane_plane_common_one (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 3) (hw' : weight a' b' = 3) (hj : intersection a a' b b' = 2) :
    commonZeros r a a' b b' = 1 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem plane_plane_common_zero (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 3) (hw' : weight a' b' = 3) (hj : intersection a a' b b' = 1) :
    commonZeros r a a' b b' = 0 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem mixed_common_two (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 2) (hw' : weight a' b' = 3) (hj : intersection a a' b b' = 2) :
    commonZeros r a a' b b' = 2 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem mixed_common_one (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 2) (hw' : weight a' b' = 3) (hj : intersection a a' b b' = 1) :
    commonZeros r a a' b b' = 1 := by
  have h := common_weight_balance r a a' b b'
  omega

theorem mixed_common_zero (r : Fin 4) (a a' : Fin 16) (b b' : Bool)
    (hw : weight a b = 2) (hw' : weight a' b' = 3) (hj : intersection a a' b b' = 0) :
    commonZeros r a a' b b' = 0 := by
  have h := common_weight_balance r a a' b b'
  omega

/-- Actual weight-two contractions equal the actual normalized line code
responses, with the fixed complementary coordinate r carried explicitly. -/
theorem line_contraction_eq_normalized (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 2)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    contraction (graphResponse (byteDiffusionHom inverse) a r (markedPositions e) T y) b =
      ShortenedLineBounds.normalizedResponse inverse
        (lineChoice out a r b hr hw).val.1 (lineChoice out a r b hr hw).val.2 (markedPositions e) T y := by
  let p := lineChoice out a r b hr hw
  rw [ShortenedLineBounds.normalizedResponse_eq_line inverse p.val.1 p.val.2 p.property.2
    (markedPositions e) (marked_remaining e p)]
  exact line_contraction_of_weight (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) a r b hw
    (markedPositions e) (marked_remaining e p) T y

theorem plane_contraction_eq_normalized (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hr : maskBit out r ≠ true) (hw : weight a b = 3)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    contraction (graphResponse (byteDiffusionHom inverse) a r (markedPositions e) T y) b =
      ShortenedPlaneResponse.normalizedPlaneResponse inverse e (planeChoice out a r b hr hw) T y :=
  plane_contraction_of_weight inverse out hout e a r b (output_mask_disjoint out r hr b) hw T y

end AESConcrete.ActivityChoiceGeometry
