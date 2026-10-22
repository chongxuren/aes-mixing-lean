import AES8.Math.PaperActivityInputCoordinates
import AES8.Math.PaperActivityMinorTransport

/-! Full projection followed by frame analysis is the literal physical
residual/frame analysis map. This is a finite kernel identity. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputAnalysis
open AESMixing WordActivityFrame PaperActivityMinorTransport PaperActivityInputCoordinates
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

def extend (S : Finset J) (a : ↥(Sᶜ) → Bool) (j : J) : Bool :=
  if hj : j ∈ S then false else a ⟨j,Finset.mem_compl.mpr hj⟩

theorem frame_activity (hV : 1 < Fintype.card V) (b : Bool) (x : V) :
    (∑ u, wordFrame 0 b u * activityMatrix 0 u x) = wordFrame 0 b x :=
  frame_left (activityMatrix_pointed 0 hV) b x

theorem partialAnalysis_projected (hV : 1 < Fintype.card V)
    (S : Finset J) (a : ↥(Sᶜ) → Bool) (f : (J → V) → ℝ) (y : S → V) :
    partialAnalysis 0 S (action (productProjection 0 (residualMask S)) f) a y =
      action (analysis S (extend S a)) f y := by
  unfold partialAnalysis action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  apply congrArg (fun r : ℝ => r * f x)
  simp_rw [projection_split (0 : V) S]
  have he (u : ↥(Sᶜ) → V) :
      frameColumn 0 a u *
      ((∏ j : S, residualProjection (0 : V) (((split S).symm (y,u)) j.val) (x j.val)) *
      (∏ j : ↥(Sᶜ), activityMatrix 0 (((split S).symm (y,u)) j.val) (x j.val))) =
      (∏ j : S, residualProjection 0 (y j) (x j.val)) *
      ∏ j : ↥(Sᶜ), wordFrame 0 (a j) (u j) * activityMatrix 0 (u j) (x j.val) := by
    have hret : (∏ j : S, residualProjection (0 : V) (((split S).symm (y,u)) j.val) (x j.val)) =
        ∏ j : S, residualProjection 0 (y j) (x j.val) := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [split,Equiv.coe_fn_symm_mk,dif_pos j.property]
    have hout : (∏ j : ↥(Sᶜ), activityMatrix (0 : V)
        (((split S).symm (y,u)) j.val) (x j.val)) =
        ∏ j : ↥(Sᶜ), activityMatrix 0 (u j) (x j.val) := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [split,Equiv.coe_fn_symm_mk,dif_neg (Finset.mem_compl.mp j.property)]
    rw [hret,hout,Finset.prod_mul_distrib]
    unfold frameColumn
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (j : ↥(Sᶜ)) (v : V) =>
    wordFrame 0 (a j) v * activityMatrix 0 v (x j.val))]
  simp_rw [frame_activity hV]
  unfold analysis
  conv_rhs => rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr (by ext; simp)
    intro j _
    simp only [dif_pos j.property]
  · let e : {j : J // j ∉ S} ≃ ↥(Sᶜ) :=
      Equiv.subtypeEquivRight (fun j => Finset.mem_compl.symm)
    rw [← e.prod_comp (fun j : ↥(Sᶜ) => wordFrame (0 : V) (a j) (x j.val))]
    apply Finset.prod_congr rfl
    intro j _
    simp only [dif_neg j.property,extend]
    rfl

end AES8.PaperActivityInputAnalysis
