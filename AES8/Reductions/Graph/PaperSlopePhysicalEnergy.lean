import AES8.Reductions.Graph.PaperSlopeEnergyLabels
import AES8.Math.PaperFrameExactEnergy
import AES8.Math.PaperSlopeResponseGram

/-! Exact energy of the actual diffused signed input frame synthesis.
MDS removes all but twenty physical triples at each of the six output pairs.
The remaining inverse metric is retained until its signs cancel exactly. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopePhysicalEnergy
open AESMixing WordActivityFrame PaperActivityInputCoordinates
open PaperSlopeLinearGraph PaperSlopeEnergyLabels PaperSlopeCoincidenceMatrix
open PaperSlopePhysicalContraction PaperSlopePhysicalFamily
open PaperSlopeCoincidences PaperSlopeOutputFrame PaperSlopeResponseGram
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def signedDiffusion (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (u : Interior → ℝ) (y : Fin 4 → F) : ℝ :=
  ∑ A : Interior, ((-1 : ℝ)^A.val.card * u A) * diffusionColumn L (inputBits A) y

def choiceResponse (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (p : Fin 6) (c : FullChoice) (y : F × F) : ℝ :=
  contraction (graphCode L.toLinearMap).toAddSubgroup
    (outputPos (firstOutput p)) (outputPos (secondOutput p)) (uniformOf p c) y

theorem partialAnalysis_signedDiffusion
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (u : Interior → ℝ)
    (p : Fin 6) (b : Fin 2 → Bool) (y : F × F) :
    partialAnalysis 0 (outputPair p)
      (action (productProjection 0 (residualMask (outputPair p))) (signedDiffusion L u))
      (outsideBits p b) (retainedLabel p y) =
        ∑ A : Interior, ((-1 : ℝ)^A.val.card * u A) * choiceResponse L p (A,b) y := by
  have he (A : Interior) :
      choiceResponse L p (A,b) y =
        partialAnalysis 0 (outputPair p)
          (action (productProjection 0 (residualMask (outputPair p)))
            (diffusionColumn L (inputBits A))) (outsideBits p b) (retainedLabel p y) := by
    unfold choiceResponse
    rw [contraction_eq_partialAnalysis L (output_distinct p) _ (uniformOf_disjoint p (A,b)),
      uniformOf_inputFrame]
    change partialAnalysis 0 (outputPair p)
      (action (productProjection 0 (residualMask (outputPair p)))
        (diffusionColumn L (inputBits A)))
      (fun j : ↥((outputPair p)ᶜ) => outputFrame (uniformOf p (A,b)) j.val)
      (retainedLabel p y) = _
    rw [uniformOf_outputFrame]
  simp_rw [he]
  simp_rw [PaperActivityInputAnalysis.partialAnalysis_projected
    (PaperSlopeLineGram.card_gt_one (K := F))]
  unfold action signedDiffusion
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro x _
  ring

def choiceTerm (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (u : Interior → ℝ)
    (p : Fin 6) (y : F × F) (c d : FullChoice) : ℝ :=
  (((-1 : ℝ)^c.1.val.card * u c.1) * choiceResponse L p c y) *
    (((-1 : ℝ)^d.1.val.card * u d.1) * choiceResponse L p d y) *
      frameInverse F (outsideBits p c.2) (outsideBits p d.2)

theorem projected_energy_choices
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (u : Interior → ℝ) (p : Fin 6) :
    (∑ x : Fin 4 → F,
      (action (productProjection 0 (residualMask (outputPair p))) (signedDiffusion L u) x)^2) =
        ∑ y : F × F, ∑ c : FullChoice, ∑ d : FullChoice, choiceTerm L u p y c d := by
  rw [PaperFrameExactEnergy.projected_energy 0 (PaperSlopeLineGram.card_gt_one (K := F))]
  rw [← (retainedLabelEquiv F p).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (outsideBitsEquiv p).sum_comp]
  simp only [outsideBitsEquiv_apply]
  calc
    _ = ∑ b : Fin 2 → Bool, ∑ d : Fin 2 → Bool,
        (∑ A : Interior, ((-1 : ℝ)^A.val.card * u A) * choiceResponse L p (A,b) y) *
        (∑ B : Interior, ((-1 : ℝ)^B.val.card * u B) * choiceResponse L p (B,d) y) *
        frameInverse F (outsideBits p b) (outsideBits p d) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← (outsideBitsEquiv p).sum_comp]
      simp only [outsideBitsEquiv_apply]
      change (∑ d : Fin 2 → Bool,
        partialAnalysis 0 (outputPair p)
          (action (productProjection 0 (residualMask (outputPair p))) (signedDiffusion L u))
          (outsideBits p b) (retainedLabel p y) *
        partialAnalysis 0 (outputPair p)
          (action (productProjection 0 (residualMask (outputPair p))) (signedDiffusion L u))
          (outsideBits p d) (retainedLabel p y) *
        frameInverse F (outsideBits p b) (outsideBits p d)) = _
      simp_rw [partialAnalysis_signedDiffusion]
    _ = ∑ b : Fin 2 → Bool, ∑ d : Fin 2 → Bool,
        ∑ A : Interior, ∑ B : Interior, choiceTerm L u p y (A,b) (B,d) := by
      simp only [Finset.sum_mul,Finset.mul_sum,choiceTerm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = ∑ b : Fin 2 → Bool, ∑ A : Interior,
        ∑ d : Fin 2 → Bool, ∑ B : Interior, choiceTerm L u p y (A,b) (B,d) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ A : Interior, ∑ b : Fin 2 → Bool,
        ∑ d : Fin 2 → Bool, ∑ B : Interior, choiceTerm L u p y (A,b) (B,d) := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [FullChoice,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

theorem sum_restrict {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P]
    (f : X → ℝ) (h : ∀ x, ¬ P x → f x = 0) :
    (∑ x : X, f x) = ∑ x : {x : X // P x}, f x.val := by
  calc
    _ = ∑ x : X, if P x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x
      · simp [hx]
      · simp [hx,h x hx]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem choiceResponse_vanishes (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (p : Fin 6) (c : FullChoice) (hc : (uniformOf p c).card ≠ 3) (y : F × F) :
    choiceResponse L p c y = 0 := by
  exact contraction_vanishes _ hL
    (fun h => output_distinct p (outputPos_injective h)) _ (uniformOf_disjoint p c) hc y

theorem projected_energy_survivors
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (u : Interior → ℝ) (p : Fin 6) :
    (∑ x : Fin 4 → F,
      (action (productProjection 0 (residualMask (outputPair p))) (signedDiffusion L u) x)^2) =
        ∑ y : F × F, ∑ k : Fin 20, ∑ l : Fin 20,
          choiceTerm L u p y (tripleChoice p k).val (tripleChoice p l).val := by
  rw [projected_energy_choices]
  apply Finset.sum_congr rfl
  intro y _
  rw [sum_restrict (fun c : FullChoice => (uniformOf p c).card = 3)
    (fun c => ∑ d : FullChoice, choiceTerm L u p y c d) (by
      intro c hc
      simp only [choiceTerm,choiceResponse_vanishes L hL p c hc y,mul_zero,zero_mul,
        Finset.sum_const_zero])]
  rw [← (triplesEquiv p).sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ d : FullChoice, choiceTerm L u p y (tripleChoice p k).val d) = _
  rw [sum_restrict (fun d : FullChoice => (uniformOf p d).card = 3)
    (fun d => choiceTerm L u p y (tripleChoice p k).val d) (by
      intro d hd
      simp only [choiceTerm,choiceResponse_vanishes L hL p d hd y,mul_zero,zero_mul])]
  exact ((triplesEquiv p).sum_comp _).symm

theorem inverse_outside (hq : Fintype.card F = 256) (p : Fin 6)
    (b d : Fin 2 → Bool) :
    frameInverse F (outsideBits p b) (outsideBits p d) =
      AESConcrete.ActivityFrame.frameInverse b d := by
  unfold WordActivityFrame.frameInverse
  rw [← (outsideEquiv p).prod_comp]
  simp only [outsideBits,Equiv.symm_apply_apply,AESConcrete.ActivityFrame.frameInverse]
  apply Finset.prod_congr rfl
  intro i _
  have hs : Real.sqrt (256 : ℝ) = 16 := by
    rw [show (256 : ℝ) = (16 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  norm_num [wordInverse,eta,xi,q,hq,hs,AESConcrete.ActivityFrame.byteInverse]

theorem survivor_term (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hq : Fintype.card F = 256) (u : Interior → ℝ)
    (p : Fin 6) (k l : Fin 20) (y : F × F) :
    choiceTerm L u p y (tripleChoice p k).val (tripleChoice p l).val =
      u (inputIndex p k) * u (inputIndex p l) * (256/255 : ℝ)^2 *
        (1/16 : ℝ)^outputDistance p k l *
        (PaperSlopeLineGram.response (physicalSlope (graphCode L.toLinearMap) hL p k) y *
          PaperSlopeLineGram.response (physicalSlope (graphCode L.toLinearMap) hL p l) y) := by
  have hc (j : Fin 20) : choiceResponse L p (tripleChoice p j).val y =
      PaperSlopeLineGram.response (physicalSlope (graphCode L.toLinearMap) hL p j) y := by
    unfold choiceResponse
    rw [uniformOf_tripleChoice,firstOutput_eq,secondOutput_eq,physical_contraction_eq]
  unfold choiceTerm
  rw [hc k,hc l]
  change (inputSign p k * u (inputIndex p k) * _) *
    (inputSign p l * u (inputIndex p l) * _) *
    frameInverse F (outsideBits p (outputBits p k)) (outsideBits p (outputBits p l)) = _
  rw [inverse_outside hq]
  calc
    _ = u (inputIndex p k) * u (inputIndex p l) *
        (inputSign p k * inputSign p l *
          AESConcrete.ActivityFrame.frameInverse (outputBits p k) (outputBits p l)) *
        (PaperSlopeLineGram.response (physicalSlope (graphCode L.toLinearMap) hL p k) y *
          PaperSlopeLineGram.response (physicalSlope (graphCode L.toLinearMap) hL p l) y) := by ring
    _ = _ := by rw [signed_inverse]; ring

theorem degree2_energy_pairs (f : (Fin 4 → F) → ℝ) :
    (∑ x : Fin 4 → F, degreeComponent 0 2 f x^2) =
      ∑ p : Fin 6, ∑ x : Fin 4 → F,
        (action (productProjection 0 (residualMask (outputPair p))) f x)^2 := by
  rw [PaperActivityArrayResidual.component_positions]
  rw [orthogonal_family_energy _ (by
    intro p r hpr
    exact productProjection_orthogonal 0 (PaperSlopeLineGram.card_gt_one (K := F))
      p.val r.val (fun h => hpr (Subtype.ext h)) f f)]
  exact (pairsEquiv.sum_comp (fun p : PaperActivityArrayResidual.Position 2 =>
    ∑ x : Fin 4 → F, (action (productProjection 0 p.val) f x)^2)).symm

/-- The genuine degree-two output energy is the Gram of its actual physical
line responses. The only code hypothesis is the original MDS predicate. -/
theorem degree2_energy_responseGram
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hq : Fintype.card F = 256) (u : Interior → ℝ) :
    (∑ x : Fin 4 → F, degreeComponent 0 2 (signedDiffusion L u) x^2) =
      responseGram (physicalSlope (graphCode L.toLinearMap) hL) u := by
  rw [degree2_energy_pairs]
  unfold responseGram
  apply Finset.sum_congr rfl
  intro p _
  rw [projected_energy_survivors L hL u p]
  simp_rw [survivor_term L hL hq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem degree2_energy_scaledGram
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (hL : PaperMDSGram.IsMDS (graphCode L.toLinearMap).toAddSubgroup 4)
    (hq : Fintype.card F = 256)
    (hclasses : SameSlopeClasses (graphCode L.toLinearMap) hL) (u : Interior → ℝ) :
    (256 : ℝ)^2 * (∑ x : Fin 4 → F, degreeComponent 0 2 (signedDiffusion L u) x^2) =
      PaperSlopeClassGram.scaledGram u := by
  rw [degree2_energy_responseGram L hL hq]
  exact responseGram_eq hq _ (physicalSlope_ne_zero _ hL) hclasses u

end AES8.PaperSlopePhysicalEnergy
