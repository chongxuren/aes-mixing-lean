import AESConcrete.ActualSignedFrame
import AESConcrete.MarkedTripleContraction
import AESConcrete.MarkedTripleMasks
import AESConcrete.MarkedThreeCube
import AESConcrete.MixedMarkedPlaneOverlap
import AESConcrete.MixedMarkedPairBounds

/-!
# All actual signed three-mark pair endpoints

The raw mixed physical overlap estimates are transported through the exact
marked-coordinate output bijection and the actual /256 or /4096 frame
normalization. Physical input adjoints are retained on every leg. Actual
mask counts classify all surviving pairs into the six Hamming-distance
cases. No overlap endpoint remains an assumption of the final pairEstimate
theorem. The signed finite sum and centered HS bound are separate.
Constructive mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActualThreePairBounds
open AESMixing AESMixing.AES
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ActualSignedFrame (response scaledPair)
open AESConcrete.MarkedTripleContraction
open AESConcrete.MarkedTripleMasks
open AESConcrete.SurvivorRelabel (falseCount)
open AESConcrete.FrameHamming (distance)
open AESConcrete.MarkedThreeCube (pairEstimate)

abbrev Byte := BinaryWord 8
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def rawLine (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (e : Fin 3 ≃ Marked m) (s : Activity m → Bool) : (Fin 3 → Byte) → ℝ :=
  MixedCodeBounds.lineCodeResponse
    (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
    (fun i => ByteLineBounds.leg (tripleOrientation left right m e i) false)

def rawPlane (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (e : Fin 3 ≃ Marked m) (s : Activity m → Bool) : (Fin 3 → Byte) → ℝ :=
  MixedCodeBounds.planeCodeResponse
    (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
    (fun i => ByteLineBounds.leg (tripleOrientation left right m e i) false)

theorem zeroCount_eq_falseCount (m : GraphPosition → Bool) (s : Activity m → Bool) :
    maskSize (outputZeros m s) + maskSize (inputZeros m s) = falseCount s :=
  (MarkedBlockScale.zero_count m s).symm

theorem scaledPair_comm (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (s t : Activity m → Bool) :
    scaledPair left right inverse m s t = scaledPair left right inverse m t s := by
  unfold scaledPair
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact _root_.mul_comm _ _

theorem scaledPair_reindex (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (s t : Activity m → Bool) (e : Fin 3 ≃ Marked m)
    (F G : (Fin 3 → Byte) → ℝ)
    (hF : ∀ y, response left right inverse m s y = F (outputEquiv m e y))
    (hG : ∀ y, response left right inverse m t y = G (outputEquiv m e y)) :
    scaledPair left right inverse m s t = (4294967296 : ℝ) * ∑ y, F y * G y := by
  unfold scaledPair
  rw [pair_sum_reindex m e]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [hF,hG]
  simp only [Equiv.apply_symm_apply]

theorem scaledPair_line_line (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 3) (ht : falseCount t = 3) (e : Fin 3 ≃ Marked m) :
    scaledPair left right inverse m s t = (4294967296 : ℝ) *
      ∑ y, rawLine left right inverse m e s y * rawLine left right inverse m e t y := by
  apply scaledPair_reindex left right inverse m s t e
  · intro y
    exact actual_contractedResponse_eq_line left right inverse m hlen s
      ((zeroCount_eq_falseCount m s).trans hs) e y
  · intro y
    exact actual_contractedResponse_eq_line left right inverse m hlen t
      ((zeroCount_eq_falseCount m t).trans ht) e y

theorem scaledPair_plane_plane (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 2) (ht : falseCount t = 2) (e : Fin 3 ≃ Marked m) :
    scaledPair left right inverse m s t = (4294967296 : ℝ) *
      ∑ y, rawPlane left right inverse m e s y * rawPlane left right inverse m e t y := by
  apply scaledPair_reindex left right inverse m s t e
  · intro y
    exact actual_contractedResponse_eq_plane left right inverse m hlen s
      ((zeroCount_eq_falseCount m s).trans hs) e y
  · intro y
    exact actual_contractedResponse_eq_plane left right inverse m hlen t
      ((zeroCount_eq_falseCount m t).trans ht) e y

theorem scaledPair_line_plane (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 3) (ht : falseCount t = 2) (e : Fin 3 ≃ Marked m) :
    scaledPair left right inverse m s t = (4294967296 : ℝ) *
      ∑ y, rawLine left right inverse m e s y * rawPlane left right inverse m e t y := by
  apply scaledPair_reindex left right inverse m s t e
  · intro y
    exact actual_contractedResponse_eq_line left right inverse m hlen s
      ((zeroCount_eq_falseCount m s).trans hs) e y
  · intro y
    exact actual_contractedResponse_eq_plane left right inverse m hlen t
      ((zeroCount_eq_falseCount m t).trans ht) e y

theorem abs_q_mul (x : ℝ) : |(4294967296 : ℝ)*x| = (4294967296 : ℝ)*|x| := by
  rw [abs_mul]
  norm_num

theorem eq_of_distance_zero {I : Type*} [Fintype I] (s t : I → Bool) (h : distance s t = 0) : s=t := by
  funext i
  by_contra hne
  have hc : 0 < Fintype.card {i : I // s i ≠ t i} :=
    Fintype.card_pos_iff.mpr ⟨⟨i,hne⟩⟩
  change 0 < distance s t at hc
  omega

theorem actual_pairEstimate_line_plane (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : falseCount s = 3) (ht : falseCount t = 2)
    (e : Fin 3 ≃ Marked m) :
    pairEstimate (distance s t) (scaledPair left right inverse m s t) := by
  have hzs := (zeroCount_eq_falseCount m s).trans hs
  have hzt := (zeroCount_eq_falseCount m t).trans ht
  have hp := scaledPair_line_plane left right inverse m hlen s t hs ht e
  have hinj := triplePositions_injective m e
  have hms := triplePositions_remaining m s e
  have hmt := triplePositions_remaining m t e
  rcases triple_mixed_geometry m s t (Or.inr ⟨hs,ht⟩) with
    ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
  · have h := (MixedMarkedPairBounds.actual_containment_interval inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hmt hc (tripleOrientation left right m e)).1
    simpa only [pairEstimate,hd,hp,rawLine,rawPlane] using h
  · have h := MixedMarkedPairBounds.actual_transverse_bound inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hc (tripleOrientation left right m e)
    simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine,rawPlane] using h
  · have h := MixedMarkedPlaneResponse.actual_line_plane_pair_bound inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hmt (tripleOrientation left right m e)
    simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine,rawPlane] using h

/-- Every surviving pair of every physical three-mark block has the exact
endpoint required by its signed inverse-frame coefficient. -/
theorem actual_pairEstimate (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hsurv : ActualMarkedFrameBound.survives m s)
    (htsurv : ActualMarkedFrameBound.survives m t) :
    pairEstimate (distance s t) (scaledPair left right inverse m s t) := by
  let e : Fin 3 ≃ Marked m := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,hlen])
  have hinj := triplePositions_injective m e
  have hms := triplePositions_remaining m s e
  have hmt := triplePositions_remaining m t e
  rcases triple_survivor_falseCount m hlen s hsurv with hs | hs <;>
    rcases triple_survivor_falseCount m hlen t htsurv with ht | ht
  · have hzs := (zeroCount_eq_falseCount m s).trans hs
    have hzt := (zeroCount_eq_falseCount m t).trans ht
    have hp := scaledPair_plane_plane left right inverse m hlen s t hs ht e
    rcases triple_pair22_geometry m s t hs ht with
      ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
    · have heq := eq_of_distance_zero s t hd
      subst t
      have h := MixedMarkedPlaneResponse.actual_plane_energy_bound inverse
        (outputZeros m s) (inputZeros m s) hzs (triplePositions m e) hinj hms
        (tripleOrientation left right m e)
      simpa only [pairEstimate,FrameHamming.distance_self,hp,rawPlane,pow_two] using h
    · have h := MixedMarkedPlaneOverlap.actual_plane_pair_eta1 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt hc (tripleOrientation left right m e)
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawPlane] using h
    · have h := MixedMarkedPlaneOverlap.actual_plane_pair_eta2 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt (by change commonCount m s t ≤ 1; omega)
        (tripleOrientation left right m e)
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawPlane] using h
  · have h := actual_pairEstimate_line_plane left right inverse m hlen t s ht hs e
    rw [FrameHamming.distance_symmetric t s,scaledPair_comm left right inverse m t s] at h
    exact h
  · exact actual_pairEstimate_line_plane left right inverse m hlen s t hs ht e
  · have hzs := (zeroCount_eq_falseCount m s).trans hs
    have hzt := (zeroCount_eq_falseCount m t).trans ht
    have hp := scaledPair_line_line left right inverse m hlen s t hs ht e
    rcases triple_pair33_geometry m hlen s t hs ht with
      ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
    · have heq := eq_of_distance_zero s t hd
      subst t
      have h := MixedMarkedPlaneResponse.actual_line_energy_bound inverse
        (outputZeros m s) (inputZeros m s) hzs (triplePositions m e) hms
        (tripleOrientation left right m e)
      simpa only [pairEstimate,FrameHamming.distance_self,hp,rawLine,pow_two] using h
    · have h := MixedMarkedPlaneOverlap.actual_line_pair_eta1 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt
        (by change 2 ≤ commonCount m s t; omega) (by change 4 ≤ unionCount m s t; omega)
        (tripleOrientation left right m e)
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine] using h
    · have h := MixedMarkedPlaneOverlap.actual_line_pair_eta2 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt
        (by change 1 ≤ commonCount m s t; omega) (by change 4 ≤ unionCount m s t; omega)
        (tripleOrientation left right m e)
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine] using h

end AESConcrete.ActualThreePairBounds
