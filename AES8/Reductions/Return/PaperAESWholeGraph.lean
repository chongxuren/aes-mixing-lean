import AES8.Reductions.Return.PaperWholeGraphReturn
import AES8.Reductions.Return.PaperWordGraphDuality

/-!
# Physical marked-graph whole-return estimate

The two shortened physical graphs choose their representations independently.
This leaf joins the exact raw graph identities to the mixed whole-graph bound.
The grouped-state activity expansion and support lift remain separate.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESWholeGraph
open AESMixing AESConcrete
open PaperMDSGram PaperWordGraphDuality
open AESConcrete.WordFourierCore AESConcrete.WordFourierVariants

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def chosenCode {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (e : Bool) :=
  if e then dual C else C

def chosenDimension (n d : ℕ) (e : Bool) := if e then n-d else d

theorem chosenCode_isMDS {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (d : ℕ) (hd : d ≤ i+m) (hC : IsMDS C d) (e : Bool) :
    IsMDS (chosenCode C e) (chosenDimension (i+m) d e) := by
  cases e
  · exact hC
  · simpa only [chosenCode, chosenDimension, if_true, Fintype.card_sum,
      Fintype.card_fin] using annihilator_isMDS AESConcrete.WordFourierCore.wordPairing C d (by simpa using hd) hC

theorem chosenK_eq {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (d : ℕ) (e : Bool) :
    chosenK C d e = PaperGraphResponseMatrix.rawGraphMatrix (chosenCode C e)
      (PaperGraphResponseMatrix.graphCoefficient i m (chosenDimension (i+m) d e)) := by
  cases e <;> rfl

theorem reduced_choice (n d : ℕ) (hd : d ≤ n) :
    chosenDimension n d (decide (2*d > n)) = min d (n-d) := by
  unfold chosenDimension
  split_ifs <;> simp_all only [decide_eq_true_eq] <;> omega

theorem bitF_comp_self (n : ℕ) (e : Bool) :
    kernelCompose (bitF n e) (bitF n e) = identityKernel := by
  cases e
  · exact compose_identity_left _
  · exact F_comp_self n

/-- Literal original matrix, with outside and middle residual maps once each. -/
def originalReturn {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ) :=
  kernelCompose (coordinateKernel (fun _ : Fin i => baseResidual false))
    (kernelCompose (K CL dL)
      (kernelCompose (coordinateKernel (fun _ : Fin m => baseResidual false))
        (transpose (K CR dR))))

/-- Literal same return in the independently chosen graph coordinates. -/
def chosenReturn {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ) (eL eR : Bool) :=
  PaperWholeGraphReturn.rawReturn (chosenCode CL eL) (chosenCode CR eR)
    (PaperGraphResponseMatrix.graphCoefficient i m (chosenDimension (i+m) dL eL))
    (PaperGraphResponseMatrix.graphCoefficient j m (chosenDimension (j+m) dR eR)) eL eR

theorem middle_mixed (m : ℕ) (eL eR : Bool) :
    kernelCompose (kernelCompose (bitF m eL)
      (coordinateKernel (fun _ : Fin m => baseResidual false))) (bitF m eR) =
    coordinateKernel (fun _ : Fin m => PaperWordMixedGram.mixed false eL eR) := by
  cases eL <;> cases eR <;>
    simp only [bitF, F, Bool.false_eq_true, if_false, if_true,
      compose_identity_left, compose_identity_right, coordinateKernel_compose,
      PaperWordMixedGram.mixed, PaperWordGraphDuality.compose_assoc]

theorem original_eq_chosen {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool) :
    originalReturn CL CR dL dR =
      kernelCompose (bitF i eL)
        (kernelCompose (chosenReturn CL CR dL dR eL eR) (bitF j eR)) := by
  let mid := coordinateKernel (fun _ : Fin m => baseResidual false)
  let core := kernelCompose (K CL dL) (kernelCompose mid (transpose (K CR dR)))
  have he := two_graph_duality CL CR dL dR hL hR hCL hCR mid eL eR
  simp only [mid, middle_mixed] at he
  have hi : core = kernelCompose (bitF i eL)
      (kernelCompose (kernelCompose (chosenK CL dL eL)
        (kernelCompose (coordinateKernel (fun _ : Fin m => PaperWordMixedGram.mixed false eL eR))
          (transpose (chosenK CR dR eR)))) (bitF j eR)) := by
    have h := congrArg (fun A => kernelCompose (bitF i eL) (kernelCompose A (bitF j eR))) he
    simp only [compose_assoc, ← compose_assoc (bitF i eL) (bitF i eL),
      bitF_comp_self, compose_identity_left] at h
    simp only [← compose_assoc, compose_identity_right] at h
    simpa only [mid, middle_mixed, core, compose_assoc] using h
  unfold originalReturn
  change kernelCompose (coordinateKernel (fun _ : Fin i => baseResidual false)) core = _
  rw [hi, ← compose_assoc, outside_variant_transport, compose_assoc]
  congr 1
  simp only [chosenReturn, PaperWholeGraphReturn.rawReturn,
    PaperWholeGraphReturn.leftWordMatrix, PaperGraphResponseMatrix.leftMatrix,
    ← chosenK_eq, compose_assoc]
  rfl

/-- Unscaled whole-graph coefficient, before the comparison table's Q^3. -/
def wholeFactor (i j m s t : ℕ) : ℝ :=
  Real.rpow (4294967296 : ℝ)
    (((i : ℝ)+(j : ℝ)+2*(m : ℝ)-8-(s : ℝ)-(min j t : ℕ))/2) *
  PaperWordMixedGram.tau^s *
  Real.rpow PaperWordMixedGram.delta (((i : ℝ)+(m : ℝ)-2*(s : ℝ))/2)

theorem wholeFactor_nonneg (i j m s t : ℕ) : 0 ≤ wholeFactor i j m s t := by
  unfold wholeFactor
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (pow_nonneg (by norm_num [PaperWordMixedGram.tau]) _))
    (Real.rpow_nonneg PaperWordMixedGram.delta_nonneg _)

theorem chosen_real_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hs : chosenDimension (i+m) dL eL = s)
    (ht : chosenDimension (j+m) dR eR = t)
    (hfit : 2*s ≤ i+m) (htm : t ≤ m) (f : (Fin j → AES.Word) → ℝ) :
    (∑ y, action (chosenReturn CL CR dL dR eL eR) f y ^ 2) ≤
      wholeFactor i j m s t ^ 2 * ∑ x, f x ^ 2 := by
  have hCs : IsMDS (chosenCode CL eL) s := hs ▸ chosenCode_isMDS CL dL hL hCL eL
  have hCt : IsMDS (chosenCode CR eR) t := ht ▸ chosenCode_isMDS CR dR hR hCR eR
  unfold chosenReturn
  rw [hs, ht]
  have h := PaperWholeGraphReturn.rawReturn_energy (chosenCode CL eL)
    (chosenCode CR eR) s t hCs hCt hfit htm
    (PaperGraphResponseMatrix.graphCoefficient i m s)
    (PaperGraphResponseMatrix.graphCoefficient j m t) eL eR f
  rw [PaperWholeGraphReturn.whole_coefficient_identity i j m s t hfit] at h
  exact h

/-- Outside Fourier isometries preserve the actual whole-return energy. -/
theorem original_real_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hs : chosenDimension (i+m) dL eL = s)
    (ht : chosenDimension (j+m) dR eR = t)
    (hfit : 2*s ≤ i+m) (htm : t ≤ m) (f : (Fin j → AES.Word) → ℝ) :
    (∑ y, action (originalReturn CL CR dL dR) f y ^ 2) ≤
      wholeFactor i j m s t ^ 2 * ∑ x, f x ^ 2 := by
  rw [original_eq_chosen CL CR dL dR hL hR hCL hCR eL eR]
  simp only [kernelCompose_action]
  rw [bitF_energy]
  have h := chosen_real_energy CL CR dL dR s t hL hR hCL hCR eL eR hs ht hfit htm
    (action (bitF j eR) f)
  rw [bitF_energy] at h
  exact h

theorem original_complex_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hs : chosenDimension (i+m) dL eL = s)
    (ht : chosenDimension (j+m) dR eR = t)
    (hfit : 2*s ≤ i+m) (htm : t ≤ m) (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖PaperKernelBounds.kernelAction
      (fun y x => (originalReturn CL CR dL dR y x : ℂ)) f y‖ ^ 2) ≤
      wholeFactor i j m s t ^ 2 * ∑ x, ‖f x‖ ^ 2 :=
  PaperWholeGraphReturn.complex_energy_of_real _ _
    (original_real_energy CL CR dL dR s t hL hR hCL hCR eL eR hs ht hfit htm) f

theorem original_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hs : chosenDimension (i+m) dL eL = s)
    (ht : chosenDimension (j+m) dR eR = t)
    (hfit : 2*s ≤ i+m) (htm : t ≤ m) :
    ‖PaperKernelBounds.kernelOperator
      (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤ wholeFactor i j m s t := by
  apply (sq_le_sq₀ (norm_nonneg _) (wholeFactor_nonneg _ _ _ _ _)).mp
  exact PaperKernelBounds.operator_norm_sq_le_of_energy _ _ (sq_nonneg _)
    (original_complex_energy CL CR dL dR s t hL hR hCL hCR eL eR hs ht hfit htm)

/-- The whole-return coefficient after the specified smaller-dimension choices. -/
theorem reduced_original_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ)
    (hi : i ≤ 4) (hj : j ≤ 4) (hm : 3 ≤ m)
    (hL0 : 0 < dL) (hL : dL < i+m) (hR0 : 0 < dR) (hR : dR < j+m)
    (hCL : IsMDS CL dL) (hCR : IsMDS CR dR) :
    ‖PaperKernelBounds.kernelOperator
      (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      wholeFactor i j m (min dL (i+m-dL)) (min dR (j+m-dR)) := by
  exact original_norm CL CR dL dR _ _ hL.le hR.le hCL hCR
    (decide (2*dL > i+m)) (decide (2*dR > j+m))
    (reduced_choice _ _ hL.le) (reduced_choice _ _ hR.le)
    (reduced_dimensions i m dL hi hm hL0 hL).2.2.1
    (reduced_dimensions j m dR hj hm hR0 hR).2.1

/-- Physical marked-coordinate matrix, before support/activity expansion. -/
def physicalReturn {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m) :=
  kernelCompose (coordinateKernel (fun _ : Fin i => baseResidual false))
    (kernelCompose
      (fun y x => PaperWordGraphCode.graphContraction ML UL
        (fun a => Sum.elim y x (eL a)))
      (kernelCompose (coordinateKernel (fun _ : Fin m => baseResidual false))
        (fun x y => PaperWordGraphCode.graphContraction MR UR
          (fun a => Sum.elim y x (eR a)))))

theorem physicalReturn_eq {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hL : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hR : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hLm : dL ≤ ML.card) (hRm : dR ≤ MR.card) :
    physicalReturn ML UL MR UR eL eR =
      originalReturn (physicalCode ML UL eL) (physicalCode MR UR eR) dL dR := by
  unfold physicalReturn originalReturn
  simp_rw [physical_graph_matrix ML UL hdL eL dL hL hLm,
    physical_graph_matrix MR UR hdR eR dR hR hRm]
  rfl

theorem physical_norm {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hi : i ≤ 4) (hj : j ≤ 4) (hm : 3 ≤ m)
    (hL0 : 0 < dL) (hL : dL < i+m) (hR0 : 0 < dR) (hR : dR < j+m) :
    ‖PaperKernelBounds.kernelOperator
      (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤
      wholeFactor i j m (min dL (i+m-dL)) (min dR (j+m-dR)) := by
  have hcL : ML.card = i+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr eL
  have hcR : MR.card = j+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr eR
  rw [physicalReturn_eq ML UL MR UR eL eR hdL hdR dL dR hLdim hRdim
    (by omega) (by omega)]
  exact reduced_original_norm _ _ dL dR hi hj hm hL0 hL hR0 hR
    (physicalCode_isMDS ML UL eL dL hLdim) (physicalCode_isMDS MR UR eR dR hRdim)

end AES8.PaperAESWholeGraph
