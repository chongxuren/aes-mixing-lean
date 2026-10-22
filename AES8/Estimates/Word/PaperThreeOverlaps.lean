import AES8.Estimates.Byte.PaperByteCubic
import AES8.Reductions.Graph.PaperThreeMarkedPairs

/-!
# Literal strict three-coordinate overlap table

Frozen paper f902bb94, lem:three-overlaps and localres:cubic. The byte
maps are fixed independently on the three marked graph positions. Both
activity choices must survive. The positive distance-one upper endpoint
comes from the full containment interval, not the signed pairEstimate
which intentionally retains only its lower endpoint.

Distances zero and five record the cubic diagonal and complementary
bounds. This leaf packages local estimates only; no startup, entry
inventory or full AES theorem is asserted. Constructive bounds; no attacks.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperThreeOverlaps
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.FrameHamming (distance)
open AESConcrete.MarkedThreeCube (pairEstimate)
open AES8.PaperThreeMarkedPairs (scaledPair)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def roundedEstimate (d : ℕ) (b : ℝ) : Prop :=
  match d with
  | 0 => b < PaperByteCubic.a0
  | 1 => (37/2000 : ℝ) < b ∧ b < (233/2000 : ℝ)
  | 2 => |b| < (61/20000 : ℝ)
  | 3 => |b| < (53/1000 : ℝ)
  | 4 => |b| < (23/1000 : ℝ)
  | 5 => |b| < PaperByteCubic.b0
  | _ => False

theorem containment_lower_rounding :
    (37/2000 : ℝ) < ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 := by
  norm_num [ContainmentCodeBounds.z3, ContainmentCodeBounds.h3,
    LineOverlap.delta, LineOverlap.offdiag]

theorem containment_upper_rounding :
    ContainmentCodeBounds.z3+ContainmentCodeBounds.h3 < (233/2000 : ℝ) := by
  norm_num [ContainmentCodeBounds.z3, ContainmentCodeBounds.h3,
    LineOverlap.delta, LineOverlap.offdiag]

theorem eta1_rounding : LineOverlap.eta1 < (61/20000 : ℝ) := by
  norm_num [LineOverlap.eta1, LineOverlap.delta, LineOverlap.offdiag]

theorem transverse_rounding : MixedCodeBounds.f3 < (53/1000 : ℝ) := by
  norm_num [MixedCodeBounds.f3, LineOverlap.delta, LineOverlap.offdiag]

theorem eta2_rounding : LineOverlap.eta2 < (23/1000 : ℝ) := by
  norm_num [LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag]

/-- Scalar rounding keeps the additional containment endpoint explicit. -/
theorem round_pair_estimate (d : ℕ) (hd : d ≤ 5) (b : ℝ)
    (hp : pairEstimate d b)
    (hupper : d = 1 → b ≤ ContainmentCodeBounds.z3+ContainmentCodeBounds.h3) :
    roundedEstimate d b := by
  interval_cases d
  · change b ≤ ByteLineBounds.a3 at hp
    exact hp.trans_lt PaperByteCubic.a3_lt
  · change ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 ≤ b at hp
    exact ⟨containment_lower_rounding.trans_le hp,
      (hupper rfl).trans_lt containment_upper_rounding⟩
  · change |b| ≤ LineOverlap.eta1 at hp
    exact hp.trans_lt eta1_rounding
  · change |b| ≤ MixedCodeBounds.f3 at hp
    exact hp.trans_lt transverse_rounding
  · change |b| ≤ LineOverlap.eta2 at hp
    exact hp.trans_lt eta2_rounding
  · change |b| ≤ ByteLineBounds.b3 at hp
    exact hp.trans_lt PaperByteCubic.b3_lt

theorem triple_distance_le (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool) :
    distance s t ≤ 5 := by
  have h := FrameHamming.distance_le_card s t
  rw [SurvivorRelabel.activity_card m 3 hlen] at h
  norm_num at h
  exact h

/-- The six strict cases include the four printed table rows and the two
cubic diagonal/complementary endpoints, with independent fixed byte maps. -/
theorem surviving_overlap_bounds (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : ActualMarkedFrameBound.survives m s)
    (ht : ActualMarkedFrameBound.survives m t) :
    roundedEstimate (distance s t) (scaledPair inverse m o s t) := by
  apply round_pair_estimate _ (triple_distance_le m hlen s t) _
    (PaperThreeMarkedPairs.surviving_pair_estimate inverse m o hlen s t hs ht)
  intro hd
  exact (PaperThreeMarkedPairs.surviving_containment_interval
    inverse m o hlen s t hs ht hd).2

theorem contained_overlap (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : ActualMarkedFrameBound.survives m s)
    (ht : ActualMarkedFrameBound.survives m t) (hd : distance s t = 1) :
    (37/2000 : ℝ) < scaledPair inverse m o s t ∧
      scaledPair inverse m o s t < (233/2000 : ℝ) := by
  have h := surviving_overlap_bounds inverse m o hlen s t hs ht
  simpa only [hd, roundedEstimate] using h

theorem diagonal_energy (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hs : ActualMarkedFrameBound.survives m s) :
    (4294967296 : ℝ) * (∑ y, PaperThreeMarkedPairs.response inverse m o s y^2) <
      PaperByteCubic.a0 := by
  have h := surviving_overlap_bounds inverse m o hlen s s hs hs
  simpa only [FrameHamming.distance_self, roundedEstimate,
    PaperThreeMarkedPairs.scaledPair, pow_two] using h

theorem complementary_distance (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hc : ∀ p, s p ≠ t p) : distance s t = 5 := by
  have h : distance s t = Fintype.card (Activity m) := by
    simp [distance, Fintype.card_subtype, hc]
  rw [SurvivorRelabel.activity_card m 3 hlen] at h
  norm_num at h
  exact h

theorem complementary_overlap (inverse : Bool) (m : GraphPosition → Bool)
    (o : Marked m → Orientation) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : ActualMarkedFrameBound.survives m s)
    (ht : ActualMarkedFrameBound.survives m t) (hc : ∀ p, s p ≠ t p) :
    |scaledPair inverse m o s t| < PaperByteCubic.b0 := by
  have h := surviving_overlap_bounds inverse m o hlen s t hs ht
  simpa only [complementary_distance m hlen s t hc, roundedEstimate] using h

/-- The standard left/right family is an exact specialization of the
owned independent-leg overlap theorem, including physical input adjoints. -/
theorem physical_overlap_bounds (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s t : Activity m → Bool) (hs : ActualMarkedFrameBound.survives m s)
    (ht : ActualMarkedFrameBound.survives m t) :
    roundedEstimate (distance s t) (ActualSignedFrame.scaledPair left right inverse m s t) := by
  have h := surviving_overlap_bounds inverse m
    (ActualMarkedCodeMoment.markedOrientation left right m) hlen s t hs ht
  rw [PaperThreeMarkedPairs.physical_scaledPair] at h
  exact h

end AES8.PaperThreeOverlaps
