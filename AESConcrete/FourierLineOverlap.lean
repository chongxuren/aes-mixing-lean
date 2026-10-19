import AESConcrete.LineOverlap

/-!
# Same-flag Fourier transport of actual line overlaps

The input-side Fourier flag conjugates the actual residual Gram.  The result
is the residual Gram of another permitted AES orientation, at the same physical
input labels.  This lifts the frozen ordinary-flag eta1/eta2 estimates without
altering the slopes or assuming residual/Fourier commutation.  Each leg may
choose its own orientation and Bool flag, shared by the compared responses.

Constructive proof support only; no attacks, manuscript edits, cross-orientation
pair estimate, or complete centered-word/mixing theorem is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FourierLineOverlap
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteGramFourier
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteLineBounds (residual leg)
open AESConcrete.DampedLineGram
open AESConcrete.LineOverlap (eta1 eta2 slopeEquiv)

/-- Fourier conjugation exchanges the ordinary and Fourier channel in each
of the two transpose classes.  Input labels are not relabeled. -/
def fourierMate : Orientation → Orientation
  | .ordinary => .fourier
  | .transposed => .fourierTransposed
  | .fourier => .ordinary
  | .fourierTransposed => .transposed

def effectiveOrientation (o : Orientation) (s : Bool) : Orientation :=
  if s then fourierMate o else o

theorem fourierMate_twice (o : Orientation) : fourierMate (fourierMate o) = o := by
  cases o <;> rfl

/-- Involutivity acts on the kernel, not on a claimed commutator with a
residual.  The proof uses the actual Fourier action twice on each side. -/
theorem byteConjugate_twice (T : Byte → Byte → ℝ) :
    byteConjugate (byteConjugate T) = T := by
  apply kernel_action_ext
  intro f
  simp only [byteConjugate, kernelCompose_action, byteFourier_twice]

theorem channel_fourierMate (o : Orientation) :
    channel (fourierMate o) = byteConjugate (channel o) := by
  cases o
  · exact squared_walsh_conjugate
  · change (fun y x => aesSquaredWalshChannel x y) =
      byteConjugate (fun y x => aesByteChannel x y)
    rw [byteConjugate_transpose, ← squared_walsh_conjugate]
  · change aesByteChannel = byteConjugate aesSquaredWalshChannel
    rw [squared_walsh_conjugate, byteConjugate_twice]
  · change (fun y x => aesByteChannel x y) =
      byteConjugate (fun y x => aesSquaredWalshChannel x y)
    rw [byteConjugate_transpose, squared_walsh_conjugate, byteConjugate_twice]

/-- The activity correction is included through the existing actual-channel
residual Gram theorem; channel conjugacy alone is not used as a substitute. -/
theorem actual_gram_fourierMate (o : Orientation) :
    residualGram (channel (fourierMate o)) =
      byteConjugate (residualGram (channel o)) := by
  exact residual_gram_conjugate (channel_resources o)
    (channel_resources (fourierMate o)) (channel_fourierMate o)

/-- The pair kernel of RF with itself is F G F.  This is a Gram identity;
it does not assert RF = FR or equality of the response vectors. -/
theorem leg_same_flag_gram (o : Orientation) (s : Bool) :
    crossGram (leg o s) (leg o s) =
      residualGram (channel (effectiveOrientation o s)) := by
  cases s
  · rfl
  · change crossGram (kernelCompose (residual o) byteFourierMatrix)
      (kernelCompose (residual o) byteFourierMatrix) =
        residualGram (channel (fourierMate o))
    rw [crossGram_compose_both _ _ _ byteFourier_symmetric]
    change byteConjugate (residualGram (channel o)) =
      residualGram (channel (fourierMate o))
    exact (actual_gram_fourierMate o).symm

/-- Equality of inner products in the original joint output space.  The same
per-leg orientation and flag occur in both compared responses; e and f are
unchanged, so later slope-ratio hypotheses retain their original meaning. -/
theorem same_flag_lineResponse_inner (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (o i) (s i)) e y *
      lineResponse (fun i => leg (o i) (s i)) f y) =
    ∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (effectiveOrientation (o i) (s i)) false) e y *
      lineResponse (fun i => leg (effectiveOrientation (o i) (s i)) false) f y := by
  rw [lineResponse_inner, lineResponse_inner]
  simp_rw [leg_same_flag_gram]
  rfl

/-- Actual q-scaled same-flag line pair with three distinct physical slope
ratios.  The response normalization is 1/256 and q is exactly 2^32. -/
theorem actual_line_pair_eta1 (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (a b : Fin 3 → Byte) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : Function.Injective (fun i => a i / b i)) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (o i) (s i)) (slopeEquiv a ha) y *
      lineResponse (fun i => leg (o i) (s i)) (slopeEquiv b hb) y| ≤ eta1 := by
  rw [same_flag_lineResponse_inner]
  exact LineOverlap.actual_line_pair_eta1
    (fun i => effectiveOrientation (o i) (s i)) a b ha hb hr

/-- Actual q-scaled same-flag pair of distinct lines.  A double physical
slope ratio is allowed, but a common ratio in all three legs is excluded. -/
theorem actual_line_pair_eta2 (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (a b : Fin 3 → Byte) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : ¬ (a 0 / b 0 = a 1 / b 1 ∧ a 1 / b 1 = a 2 / b 2)) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (o i) (s i)) (slopeEquiv a ha) y *
      lineResponse (fun i => leg (o i) (s i)) (slopeEquiv b hb) y| ≤ eta2 := by
  rw [same_flag_lineResponse_inner]
  exact LineOverlap.actual_line_pair_eta2
    (fun i => effectiveOrientation (o i) (s i)) a b ha hb hr

end AESConcrete.FourierLineOverlap
