import AESConcrete.ActualSignedFrame
import AESConcrete.MarkedThreeCube

/-!
# Signed coefficient assembly for actual three-mark blocks

The remaining premise lists the six actual pair estimates. The finite
survivor sum and signed frame coefficients are discharged here. This
conditional interface is intended to be instantiated by the physical
mixed-coordinate overlap theorems, not assumed as a concrete resource.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SignedThreeAssembly
open AESMixing
open ByteOrientations (Orientation)
open MarkedBlockVectorization (Marked Activity)
open ActualMarkedFrameBound (Surviving survives centeredPattern)
open ActualSignedFrame (scaledPair)
open SurvivorRelabel FrameHamming MarkedThreeCube
open HilbertSchmidtEnergy (hs)

attribute [local instance] Classical.propDecidable

def HasPairEstimates (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) : Prop :=
  ∀ s t : Surviving m, pairEstimate (distance s.val t.val)
    (scaledPair left right inverse m s.val t.val)

theorem survivor_cost_sum (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) :
    (∑ s : Surviving m, ∑ t : Surviving m,
      (256/255 : ℝ)^Fintype.card (Activity m) * pairCost (distance s.val t.val)) =
        signedCubeBound (Activity m) := by
  have hrow (s : Activity m → Bool) :
      (∑ t : Surviving m, pairCost (distance s t.val)) =
      ∑ t : Activity m → Bool, if cubeSurvives 3 t then pairCost (distance s t) else 0 := by
    simpa only [survives_iff_cube, hlen] using
      sum_subtype_eq_sum_ite (survives m) (fun t => pairCost (distance s t))
  have hout := sum_subtype_eq_sum_ite (survives m)
    (fun s : Activity m → Bool => ∑ t : Surviving m, pairCost (distance s t.val))
  have huniv (f g : Fintype (Activity m → Bool)) :
      @Finset.univ (Activity m → Bool) f = @Finset.univ (Activity m → Bool) g :=
    congrArg (fun a : Fintype (Activity m → Bool) => a.elems) (Subsingleton.elim f g)
  simp only [← Finset.mul_sum]
  unfold signedCubeBound
  apply congrArg ((256/255 : ℝ)^Fintype.card (Activity m) * ·)
  calc
    _ = ∑ s : Activity m → Bool, if cubeSurvives 3 s then
        (∑ t : Activity m → Bool, if cubeSurvives 3 t then pairCost (distance s t) else 0)
        else 0 := by
      simpa only [hrow, survives_iff_cube, hlen] using hout
    _ = _ := by
      apply Finset.sum_congr (huniv _ _)
      intro s _
      by_cases hs : cubeSurvives 3 s
      · simp only [hs, ↓reduceIte]
        exact Finset.sum_congr (huniv _ _) (fun _ _ => rfl)
      · simp only [hs, ↓reduceIte]

theorem centered_energy_lt_twenty_two (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (hpair : HasPairEstimates left right inverse m) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 < 22 := by
  have hm : ∃ p, m p = true := by
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (Marked m) by omega)
    exact ⟨p.val,p.property⟩
  have hcard : Fintype.card (Activity m) = 5 := by
    simpa using activity_card m 3 hlen
  have hp (s t : Surviving m) : ActivityFrame.frameInverse s.val t.val *
      scaledPair left right inverse m s.val t.val ≤
      (256/255 : ℝ)^Fintype.card (Activity m) * pairCost (distance s.val t.val) := by
    rw [frameInverse_eq_distance, mul_assoc]
    apply mul_le_mul_of_nonneg_left
      (coefficient_mul_le_cost _ (by simpa only [hcard] using distance_le_card s.val t.val)
        _ (hpair s t))
    positivity
  have he := ActualSignedFrame.centered_energy_le_signed_caps left right inverse m hm
    (fun s t => (256/255 : ℝ)^Fintype.card (Activity m) * pairCost (distance s.val t.val)) hp
  rw [survivor_cost_sum m hlen] at he
  let e : Activity m ≃ Fin 5 := Fintype.equivOfCardEq (by simpa using hcard)
  rw [signedCubeBound_equiv e, signedCubeBound_fin_five] at he
  exact he.trans_lt MarkedThreeNumbers.groupedBound_lt_twenty_two

end AESConcrete.SignedThreeAssembly
