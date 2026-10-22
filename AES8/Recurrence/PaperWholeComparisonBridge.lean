import AES8.Recurrence.PaperComparisonPowers
import AES8.Reductions.Return.PaperAESWholeGraph

/-! Exact Q^3 scaling of the literal physical whole-return norm.
This identifies the whole-graph candidate only; grouped-state expansion,
activity weights and selection against overlap candidates are separate. -/
noncomputable section
namespace AES8.PaperWholeComparisonBridge
open AES8.PaperComparison AES8.PaperComparisonPowers AES8.PaperAESWholeGraph

set_option autoImplicit false

theorem whole_product (i j m s t : ℕ) (hfit : 2*s ≤ i+m) :
    (q : ℝ)^3 * wholeFactor i j m s t =
      (wholeGraph i j m s (min j t) : ℝ) := by
  rw [wholeGraph_eq _ _ _ _ _ hfit]
  unfold wholeFactor wholeCoefficient
  have hq : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  have hδ : AES8.PaperWordMixedGram.delta = (E : ℝ)^2/(q : ℝ) := by
    norm_num [AES8.PaperWordMixedGram.delta,E,q]
  have hτ : AES8.PaperWordMixedGram.tau = 300/(q : ℝ) := by
    norm_num [AES8.PaperWordMixedGram.tau,q]
  have hQ : (4294967296 : ℝ) = (q : ℝ) := by norm_num [q]
  rw [hδ, hτ, hQ]
  have hp : (q : ℝ)^3 = Real.rpow (q : ℝ) (3 : ℝ) :=
    (Real.rpow_natCast (q : ℝ) 3).symm
  rw [hp]
  have he : (3 : ℝ)+((i : ℝ)+j+2*m-8-s-(min j t : ℕ))/2 =
      ((i : ℝ)+j+2*m-2-s-(min j t : ℕ))/2 := by ring
  calc
    _ = (Real.rpow (q : ℝ) 3 * Real.rpow (q : ℝ)
      (((i : ℝ)+j+2*m-8-s-(min j t : ℕ))/2)) *
      (300/(q : ℝ))^s * Real.rpow ((E : ℝ)^2/(q : ℝ))
      (((i : ℝ)+m-2*s)/2) := by ring
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hq, he]

theorem scaled_physical_norm {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hi : i ≤ 4) (hj : j ≤ 4) (hm : 3 ≤ m)
    (hL0 : 0 < dL) (hL : dL < i+m) (hR0 : 0 < dR) (hR : dR < j+m) :
    (q : ℝ)^3 * ‖PaperKernelBounds.kernelOperator
      (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤
      (wholeGraph i j m (min dL (i+m-dL)) (min j (min dR (j+m-dR))) : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (physical_norm ML UL MR UR eL eR hdL hdR dL dR hLdim hRdim hi hj hm hL0 hL hR0 hR)
    (show 0 ≤ (q : ℝ)^3 by norm_num [q])
  rw [whole_product i j m _ _
    (PaperWordGraphDuality.reduced_dimensions i m dL hi hm hL0 hL).2.2.1] at h
  exact h

end AES8.PaperWholeComparisonBridge
