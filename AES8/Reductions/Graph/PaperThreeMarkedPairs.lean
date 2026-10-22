import AESConcrete.ActualThreePairBounds
import AES8.Reductions.Graph.PaperMixedMarkedPlaneResponse

/-!
# Independent byte orientations on the actual marked triple

Frozen paper f902bb94, lem:three-overlaps and localres:cubic. This leaf
retains the actual forward/inverse MixColumns graph but allows a separately
fixed permitted byte residual on each marked leg. The same map is used on
that leg for both activity choices. It transports the existing raw shortened
line/plane bounds through the exact /256 or /4096 frame normalization.

The organization and proof reuse the preserved ActualThreePairBounds leaf;
that predecessor's common left/right physical specialization is not used as
if it had the stronger per-leg quantifier. Scalar rounding belongs to the
separate paper endpoint leaf. Constructive bounds only; no attacks.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperThreeMarkedPairs
open AESConcrete
open AESMixing AESMixing.AES
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse
open AESConcrete.MarkedTripleContraction
open AESConcrete.MarkedTripleMasks
open AESConcrete.SurvivorRelabel (falseCount)
open AESConcrete.FrameHamming (distance)
open AESConcrete.MarkedThreeCube (pairEstimate)

abbrev Byte := BinaryWord 8
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def response (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (s : Activity m → Bool) : (Marked m → Byte) → ℝ :=
  MarkedBlockVectorization.contractedResponse m
    (fun p => ByteLineBounds.leg (o p) false)
    (graphCoordinate (byteDiffusionHom inverse)) s

def scaledPair (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (s t : Activity m → Bool) : ℝ :=
  (4294967296 : ℝ) * ∑ y, response inverse m o s y * response inverse m o t y

def rawLine (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (e : Fin 3 ≃ Marked m) (s : Activity m → Bool) : (Fin 3 → Byte) → ℝ :=
  MixedCodeBounds.lineCodeResponse
    (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
    (fun i => ByteLineBounds.leg (o (e i)) false)

def rawPlane (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (e : Fin 3 ≃ Marked m) (s : Activity m → Bool) : (Fin 3 → Byte) → ℝ :=
  MixedCodeBounds.planeCodeResponse
    (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
    (fun i => ByteLineBounds.leg (o (e i)) false)

theorem zeroCount_eq_falseCount (m : GraphPosition → Bool) (s : Activity m → Bool) :
    maskSize (outputZeros m s) + maskSize (inputZeros m s) = falseCount s :=
  (MarkedBlockScale.zero_count m s).symm

theorem scaledPair_comm (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (s t : Activity m → Bool) :
    scaledPair inverse m o s t = scaledPair inverse m o t s := by
  unfold scaledPair
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact _root_.mul_comm _ _

theorem scaledPair_reindex (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (s t : Activity m → Bool) (e : Fin 3 ≃ Marked m)
    (F G : (Fin 3 → Byte) → ℝ)
    (hF : ∀ y, response inverse m o s y = F (outputEquiv m e y))
    (hG : ∀ y, response inverse m o t y = G (outputEquiv m e y)) :
    scaledPair inverse m o s t = (4294967296 : ℝ) * ∑ y, F y * G y := by
  unfold scaledPair
  rw [pair_sum_reindex m e]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [hF,hG]
  simp only [Equiv.apply_symm_apply]

theorem scaledPair_line_line (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 3) (ht : falseCount t = 3) (e : Fin 3 ≃ Marked m) :
    scaledPair inverse m o s t = (4294967296 : ℝ) *
      ∑ y, rawLine inverse m o e s y * rawLine inverse m o e t y := by
  apply scaledPair_reindex inverse m o s t e
  · intro y
    exact contractedResponse_eq_line (byteDiffusionHom inverse) m hlen s
      ((zeroCount_eq_falseCount m s).trans hs)
      (fun p => ByteLineBounds.leg (o p) false) e y
  · intro y
    exact contractedResponse_eq_line (byteDiffusionHom inverse) m hlen t
      ((zeroCount_eq_falseCount m t).trans ht)
      (fun p => ByteLineBounds.leg (o p) false) e y

theorem scaledPair_plane_plane (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 2) (ht : falseCount t = 2) (e : Fin 3 ≃ Marked m) :
    scaledPair inverse m o s t = (4294967296 : ℝ) *
      ∑ y, rawPlane inverse m o e s y * rawPlane inverse m o e t y := by
  apply scaledPair_reindex inverse m o s t e
  · intro y
    exact contractedResponse_eq_plane (byteDiffusionHom inverse) m hlen s
      ((zeroCount_eq_falseCount m s).trans hs)
      (fun p => ByteLineBounds.leg (o p) false) e y
  · intro y
    exact contractedResponse_eq_plane (byteDiffusionHom inverse) m hlen t
      ((zeroCount_eq_falseCount m t).trans ht)
      (fun p => ByteLineBounds.leg (o p) false) e y

theorem scaledPair_line_plane (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 3) (ht : falseCount t = 2) (e : Fin 3 ≃ Marked m) :
    scaledPair inverse m o s t = (4294967296 : ℝ) *
      ∑ y, rawLine inverse m o e s y * rawPlane inverse m o e t y := by
  apply scaledPair_reindex inverse m o s t e
  · intro y
    exact contractedResponse_eq_line (byteDiffusionHom inverse) m hlen s
      ((zeroCount_eq_falseCount m s).trans hs)
      (fun p => ByteLineBounds.leg (o p) false) e y
  · intro y
    exact contractedResponse_eq_plane (byteDiffusionHom inverse) m hlen t
      ((zeroCount_eq_falseCount m t).trans ht)
      (fun p => ByteLineBounds.leg (o p) false) e y

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

theorem line_plane_pair_estimate (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : falseCount s = 3) (ht : falseCount t = 2)
    (e : Fin 3 ≃ Marked m) :
    pairEstimate (distance s t) (scaledPair inverse m o s t) := by
  have hzs := (zeroCount_eq_falseCount m s).trans hs
  have hzt := (zeroCount_eq_falseCount m t).trans ht
  have hp := scaledPair_line_plane inverse m o hlen s t hs ht e
  have hinj := triplePositions_injective m e
  have hms := triplePositions_remaining m s e
  have hmt := triplePositions_remaining m t e
  rcases triple_mixed_geometry m s t (Or.inr ⟨hs,ht⟩) with
    ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
  · have h := (MixedMarkedPairBounds.actual_containment_interval inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hmt hc ((fun i => o (e i)))).1
    simpa only [pairEstimate,hd,hp,rawLine,rawPlane] using h
  · have h := MixedMarkedPairBounds.actual_transverse_bound inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hc ((fun i => o (e i)))
    simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine,rawPlane] using h
  -- Route dependency: the complementary branch uses the printed Gram bound.
  -- Diagonal cubic branches also use the owned transport; other overlaps are separate.
  · have h := AES8.PaperMixedMarkedPlaneResponse.actual_line_plane_pair_bound inverse
      (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
      hzs hzt (triplePositions m e) hinj hms hmt ((fun i => o (e i)))
    simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine,rawPlane] using h

/-- Every surviving pair with an independently fixed orientation on each
marked leg has the exact endpoint for its signed inverse-frame coefficient. -/
theorem surviving_pair_estimate (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hsurv : ActualMarkedFrameBound.survives m s)
    (htsurv : ActualMarkedFrameBound.survives m t) :
    pairEstimate (distance s t) (scaledPair inverse m o s t) := by
  let e : Fin 3 ≃ Marked m := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,hlen])
  have hinj := triplePositions_injective m e
  have hms := triplePositions_remaining m s e
  have hmt := triplePositions_remaining m t e
  rcases triple_survivor_falseCount m hlen s hsurv with hs | hs <;>
    rcases triple_survivor_falseCount m hlen t htsurv with ht | ht
  · have hzs := (zeroCount_eq_falseCount m s).trans hs
    have hzt := (zeroCount_eq_falseCount m t).trans ht
    have hp := scaledPair_plane_plane inverse m o hlen s t hs ht e
    rcases triple_pair22_geometry m s t hs ht with
      ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
    · have heq := eq_of_distance_zero s t hd
      subst t
      have h := AES8.PaperMixedMarkedPlaneResponse.actual_plane_energy_bound inverse
        (outputZeros m s) (inputZeros m s) hzs (triplePositions m e) hinj hms
        ((fun i => o (e i)))
      simpa only [pairEstimate,FrameHamming.distance_self,hp,rawPlane,pow_two] using h
    · have h := MixedMarkedPlaneOverlap.actual_plane_pair_eta1 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt hc ((fun i => o (e i)))
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawPlane] using h
    · have h := MixedMarkedPlaneOverlap.actual_plane_pair_eta2 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt (by change commonCount m s t ≤ 1; omega)
        ((fun i => o (e i)))
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawPlane] using h
  · have h := line_plane_pair_estimate inverse m o hlen t s ht hs e
    rw [FrameHamming.distance_symmetric t s,scaledPair_comm inverse m o t s] at h
    exact h
  · exact line_plane_pair_estimate inverse m o hlen s t hs ht e
  · have hzs := (zeroCount_eq_falseCount m s).trans hs
    have hzt := (zeroCount_eq_falseCount m t).trans ht
    have hp := scaledPair_line_line inverse m o hlen s t hs ht e
    rcases triple_pair33_geometry m hlen s t hs ht with
      ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩ | ⟨hd,hc,hu⟩
    · have heq := eq_of_distance_zero s t hd
      subst t
      have h := AES8.PaperMixedMarkedPlaneResponse.actual_line_energy_bound inverse
        (outputZeros m s) (inputZeros m s) hzs (triplePositions m e) hms
        ((fun i => o (e i)))
      simpa only [pairEstimate,FrameHamming.distance_self,hp,rawLine,pow_two] using h
    · have h := MixedMarkedPlaneOverlap.actual_line_pair_eta1 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt
        (by change 2 ≤ commonCount m s t; omega) (by change 4 ≤ unionCount m s t; omega)
        ((fun i => o (e i)))
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine] using h
    · have h := MixedMarkedPlaneOverlap.actual_line_pair_eta2 inverse
        (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
        hzs hzt (triplePositions m e) hinj hms hmt
        (by change 1 ≤ commonCount m s t; omega) (by change 4 ≤ unionCount m s t; omega)
        (fun i => o (e i))
      simpa only [pairEstimate,hd,hp,abs_q_mul,rawLine] using h

/-- The positive containment upper endpoint is separate from pairEstimate,
which retains only the lower endpoint needed by its negative coefficient. -/
theorem line_plane_containment_interval (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : falseCount s = 3) (ht : falseCount t = 2)
    (hd : distance s t = 1) :
    ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 ≤ scaledPair inverse m o s t ∧
      scaledPair inverse m o s t ≤ ContainmentCodeBounds.z3+ContainmentCodeBounds.h3 := by
  let e : Fin 3 ≃ Marked m := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,hlen])
  have hc : commonCount m s t = 2 := by
    have h := distance_add_twice_common m s t
    omega
  have h := MixedMarkedPairBounds.actual_containment_interval inverse
    (outputZeros m s) (inputZeros m s) (outputZeros m t) (inputZeros m t)
    ((zeroCount_eq_falseCount m s).trans hs) ((zeroCount_eq_falseCount m t).trans ht)
    (triplePositions m e) (triplePositions_injective m e)
    (triplePositions_remaining m s e) (triplePositions_remaining m t e) hc
    (fun i => o (e i))
  rw [scaledPair_line_plane inverse m o hlen s t hs ht e]
  simpa only [rawLine,rawPlane] using h

theorem surviving_containment_interval (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hsurv : ActualMarkedFrameBound.survives m s)
    (htsurv : ActualMarkedFrameBound.survives m t) (hd : distance s t = 1) :
    ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 ≤ scaledPair inverse m o s t ∧
      scaledPair inverse m o s t ≤ ContainmentCodeBounds.z3+ContainmentCodeBounds.h3 := by
  have hc := distance_add_twice_common m s t
  rcases triple_survivor_falseCount m hlen s hsurv with hs | hs <;>
    rcases triple_survivor_falseCount m hlen t htsurv with ht | ht
  · omega
  · have hd' : distance t s = 1 := (FrameHamming.distance_symmetric t s).trans hd
    have h := line_plane_containment_interval inverse m o hlen t s ht hs hd'
    simpa only [scaledPair_comm inverse m o t s] using h
  · exact line_plane_containment_interval inverse m o hlen s t hs ht hd
  · omega

/-- The usual common left/right physical family is an exact specialization;
physical input legs retain the adjoint orientation. -/
theorem physical_response (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (y : Marked m → Byte) :
    response inverse m (ActualMarkedCodeMoment.markedOrientation left right m) s y =
      ActualSignedFrame.response left right inverse m s y := by
  unfold response ActualSignedFrame.response
  rw [ActualMarkedCodeMoment.actual_markedLeg]
  rfl

theorem physical_scaledPair (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    scaledPair inverse m (ActualMarkedCodeMoment.markedOrientation left right m) s t =
      ActualSignedFrame.scaledPair left right inverse m s t := by
  simp only [scaledPair, ActualSignedFrame.scaledPair, physical_response]

end AES8.PaperThreeMarkedPairs
