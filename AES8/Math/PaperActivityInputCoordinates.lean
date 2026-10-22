import AES8.Math.PaperActivityInputAssembly

/-! Counting-coordinate splitting and tensor-frame reconstruction of a fixed
residual-position projection. These equalities carry arbitrary joint inputs.
No code, AES response, or quantitative operator cap is part of this leaf. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputCoordinates
open AESMixing WordActivityFrame PaperActivityInputAssembly PaperActivityInputArithmetic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]

def split (S : Finset J) : (J → V) ≃ ((S → V) × (↥(Sᶜ) → V)) where
  toFun x := (fun j => x j.val, fun j => x j.val)
  invFun x j := if hj : j ∈ S then x.1 ⟨j,hj⟩ else x.2 ⟨j,Finset.mem_compl.mpr hj⟩
  left_inv x := by funext j; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext j
    · simp only [dif_pos j.property]
    · simp only [dif_neg (Finset.mem_compl.mp j.property)]

def residualMask (S : Finset J) (j : J) : Bool := decide (j ∈ S)

theorem projection_split (z : V) (S : Finset J) (y x : J → V) :
    productProjection z (residualMask S) y x =
      (∏ j : S, residualProjection z (y j.val) (x j.val)) *
      (∏ j : ↥(Sᶜ), activityMatrix z (y j.val) (x j.val)) := by
  unfold productProjection
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr (by ext; simp)
    intro j _
    simp only [degreePiece, residualMask, decide_eq_true j.property, if_true]
  · let e : {j : J // j ∉ S} ≃ ↥(Sᶜ) :=
      Equiv.subtypeEquivRight (fun j => Finset.mem_compl.symm)
    rw [← e.prod_comp (fun j : ↥(Sᶜ) => activityMatrix z (y j.val) (x j.val))]
    apply Finset.prod_congr rfl
    intro j _
    simp only [degreePiece, residualMask, decide_eq_false j.property, Bool.false_eq_true, if_false]
    rfl

def partialAnalysis (z : V) (S : Finset J) (f : (J → V) → ℝ)
    (a : ↥(Sᶜ) → Bool) (y : S → V) : ℝ :=
  ∑ u : ↥(Sᶜ) → V, frameColumn z a u * f ((split S).symm (y,u))

def partialCoefficients (z : V) (S : Finset J) (f : (J → V) → ℝ)
    (y : S → V) (a : ↥(Sᶜ) → Bool) : ℝ :=
  ∑ b : ↥(Sᶜ) → Bool, frameInverse V a b *
    ∑ x : S → V, (∏ j : S, residualProjection z (y j) (x j)) *
      partialAnalysis z S f b x

/-- The projected output lies in the actual activity-frame range in every
retained fiber. The inverse Gram occurs once, without an independence rule. -/
theorem projection_frame_range (z : V) (hV : 1 < Fintype.card V)
    (S : Finset J) (f : (J → V) → ℝ) (y : S → V) (u : ↥(Sᶜ) → V) :
    action (productProjection z (residualMask S)) f ((split S).symm (y,u)) =
      ∑ a : ↥(Sᶜ) → Bool, frameColumn z a u * partialCoefficients z S f y a := by
  unfold action
  rw [← (split S).symm.sum_comp (fun x =>
    productProjection z (residualMask S) ((split S).symm (y,u)) x * f x)]
  simp only [Fintype.sum_prod_type]
  simp_rw [projection_split z S]
  have hs (x : S → V) (v : ↥(Sᶜ) → V) :
      (∏ j : S, residualProjection z (((split S).symm (y,u)) j.val)
        (((split S).symm (x,v)) j.val)) =
        ∏ j : S, residualProjection z (y j) (x j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [split, Equiv.coe_fn_symm_mk, dif_pos j.property]
  have ho (x : S → V) (v : ↥(Sᶜ) → V) :
      (∏ j : ↥(Sᶜ), activityMatrix z (((split S).symm (y,u)) j.val)
        (((split S).symm (x,v)) j.val)) =
        ∏ j : ↥(Sᶜ), activityMatrix z (u j) (v j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [split, Equiv.coe_fn_symm_mk, dif_neg (Finset.mem_compl.mp j.property)]
  simp_rw [hs,ho,frame_projection z hV]
  unfold partialCoefficients partialAnalysis
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (↥(Sᶜ) → V)))
    (t := (Finset.univ : Finset (↥(Sᶜ) → Bool)))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (S → V)))
    (t := (Finset.univ : Finset (↥(Sᶜ) → Bool)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm (s := (Finset.univ : Finset (S → V)))
    (t := (Finset.univ : Finset (↥(Sᶜ) → Bool)))]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- The activity-frame analysis controls every fixed residual-position
projection; the projected output need not be a product distribution. -/
theorem projected_energy_le_analysis (S : Finset J)
    (hn : Fintype.card ↥(Sᶜ) ≤ 6) (f : (J → AES.Word) → ℝ) :
    (∑ y, action (productProjection (0 : AES.Word) (residualMask S)) f y ^ 2) ≤
      loss * ∑ y : S → AES.Word, ∑ a : ↥(Sᶜ) → Bool,
        partialAnalysis 0 S (action (productProjection 0 (residualMask S)) f) a y ^ 2 := by
  let g := action (productProjection (0 : AES.Word) (residualMask S)) f
  rw [← (split S).symm.sum_comp (fun y => g y ^ 2), Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have hr (u : ↥(Sᶜ) → AES.Word) : g ((split S).symm (y,u)) =
      synthesize (partialCoefficients 0 S f y) u :=
    projection_frame_range 0 AESConcrete.AES.word_card_gt_one S f y u
  have h := analysis_energy_lower hn (partialCoefficients 0 S f y)
  change (∑ u, g ((split S).symm (y,u)) ^ 2) ≤ _
  simp_rw [hr]
  change _ ≤ loss * ∑ a, analyze (fun u => g ((split S).symm (y,u))) a ^ 2
  simpa only [hr] using h

end AES8.PaperActivityInputCoordinates
