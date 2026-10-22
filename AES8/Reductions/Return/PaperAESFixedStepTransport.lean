import AES8.Reductions.Return.PaperAESFixedStepBounds
import AES8.Reductions.Return.PaperWordGraphDuality
import AESConcrete.WordMixedCentering

/-!
# Fixed-step residual and Fourier transport

The operator is the actual marked AES graph contraction with output residual
maps and input residual projections. The zero/full physical graph branches
are evaluated directly. Fourier transport is equality of kernels and uses
proved isometries, not an extra target operator-norm hypothesis.
Constructive proof validation only; no attacks or numerical searches.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESFixedStepTransport
open AESMixing PaperMDSGram PaperKernelBounds
open PaperWordGraphCode PaperWordGraphDuality PaperAESIncidence
open AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

/-- The raw marked sum retains every physical zero/uniform frame coordinate. -/
def physicalGraph {i j : ℕ} (M U : Finset Position) (e : M ≃ Fin i ⊕ Fin j)
    (y : Fin i → AES.Word) (x : Fin j → AES.Word) : ℝ :=
  graphContraction M U (fun a => Sum.elim y x (e a))

def R (i : ℕ) (adjoint : Bool) :=
  coordinateKernel (fun _ : Fin i => baseResidual adjoint)

/-- The literal fixed-position residual step, before multiplication by Q. -/
def physicalStep {i j : ℕ} (M U : Finset Position) (e : M ≃ Fin i ⊕ Fin j)
    (adjoint : Bool) : (Fin i → AES.Word) → (Fin j → AES.Word) → ℝ :=
  kernelCompose (R i adjoint) (kernelCompose (physicalGraph M U e) (P j))

theorem P_norm (n : ℕ) : ‖kernelOperator (P n)‖ ≤ 1 := by
  have hp : P n = productProjection (0 : AES.Word) (fun _ : Fin n => true) := by
    funext y x
    simp only [P, productProjection, coordinateKernel, degreePiece, if_true]
  have he (f : (Fin n → AES.Word) → ℝ) :
      (∑ y, action (P n) f y ^ 2) ≤ ∑ x, f x ^ 2 := by
    rw [hp]
    exact
      productProjection_energy_le (0 : AES.Word)
        (by rw [AESConcrete.WordFourierCore.word_card]; norm_num)
        (fun _ : Fin n => true) f
  have hn := operator_norm_sq_le_of_energy (P n) 1 (by norm_num)
    (fun f => by simpa only [Real.norm_eq_abs, sq_abs, kernelAction, action, one_mul] using he f)
  nlinarith [norm_nonneg (kernelOperator (P n))]

theorem bitF_norm (n : ℕ) (b : Bool) : ‖kernelOperator (bitF n b)‖ ≤ 1 := by
  have hn := operator_norm_sq_le_of_energy (bitF n b) 1 (by norm_num)
    (fun f => by
      simpa only [Real.norm_eq_abs, sq_abs, kernelAction, action, one_mul] using
        (bitF_energy n b f).le)
  nlinarith [norm_nonneg (kernelOperator (bitF n b))]

theorem bitF_comp_self (n : ℕ) (b : Bool) :
    kernelCompose (bitF n b) (bitF n b) = identityKernel := by
  cases b
  · simp only [bitF, Bool.false_eq_true, if_false, compose_identity_left]
  · exact F_comp_self n

/-- The raw code may be replaced by either representation with outside
Fourier factors retained explicitly. -/
theorem step_representation {i j : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin j) → AES.Word)) (d : ℕ)
    (hd : d ≤ i + j) (hC : IsMDS C d) (adjoint b : Bool) :
    kernelCompose (R i adjoint) (kernelCompose (K C d) (P j)) =
      kernelCompose (bitF i b)
        (kernelCompose (kernelCompose
          (coordinateKernel (fun _ : Fin i => variant adjoint b)) (chosenK C d b))
          (kernelCompose (bitF j b) (P j))) := by
  have hK : K C d = kernelCompose (bitF i b)
      (kernelCompose (chosenK C d b) (bitF j b)) := by
    rw [← chosen_transport C d hd hC b, ← compose_assoc, bitF_comp_self, compose_identity_left]
  rw [hK]
  calc
    _ = kernelCompose (kernelCompose (R i adjoint) (bitF i b))
        (kernelCompose (chosenK C d b) (kernelCompose (bitF j b) (P j))) := by
      simp only [compose_assoc]
    _ = _ := by
      rw [R, outside_variant_transport]
      simp only [compose_assoc]

/-- Composition by a proved contraction loses no norm. -/
theorem compose_norm_le_right {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq B] [DecidableEq D] (T : A → B → ℝ) (U : B → D → ℝ)
    (hU : ‖kernelOperator U‖ ≤ 1) :
    ‖kernelOperator (kernelCompose T U)‖ ≤ ‖kernelOperator T‖ := by
  rw [PaperAESIncidence.kernelOperator_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hU (norm_nonneg (kernelOperator T)))

theorem compose_norm_le_left {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D]
    (T : A → B → ℝ) (U : B → D → ℝ) (hT : ‖kernelOperator T‖ ≤ 1) :
    ‖kernelOperator (kernelCompose T U)‖ ≤ ‖kernelOperator U‖ := by
  rw [PaperAESIncidence.kernelOperator_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (norm_nonneg (kernelOperator U)))

/-- Kernel norm transport without any encoded-step norm premise. -/
theorem step_representation_norm {i j : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin j) → AES.Word)) (d : ℕ)
    (hd : d ≤ i + j) (hC : IsMDS C d) (adjoint b : Bool) :
    ‖kernelOperator (kernelCompose (R i adjoint) (kernelCompose (K C d) (P j)))‖ ≤
      ‖kernelOperator (kernelCompose
        (coordinateKernel (fun _ : Fin i => variant adjoint b)) (chosenK C d b))‖ := by
  rw [step_representation C d hd hC adjoint b]
  apply (compose_norm_le_left _ _ (bitF_norm i b)).trans
  apply compose_norm_le_right
  exact (compose_norm_le_right _ _ (P_norm j)).trans (bitF_norm j b)

/-- The proper branch of the literal physical contraction is exactly K. -/
theorem physicalGraph_eq_K {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card) :
    physicalGraph M U e = K (physicalCode M U e) d := by
  funext y x
  exact physical_graph_matrix M U hd e d hdim hlarge y x

/-- Relabeling marked coordinates preserves the exact zero tuple. -/
theorem relabeled_zero_iff {i j : ℕ} (M : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (a : Fin i → AES.Word) (b : Fin j → AES.Word) :
    (fun p : M => Sum.elim a b (e p)) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · funext k
      obtain ⟨p, hp⟩ := e.surjective (Sum.inl k)
      simpa only [hp, Sum.elim_inl, Pi.zero_apply] using congrFun h p
    · funext k
      obtain ⟨p, hp⟩ := e.surjective (Sum.inr k)
      simpa only [hp, Sum.elim_inr, Pi.zero_apply] using congrFun h p
  · rintro ⟨rfl, rfl⟩
    funext p
    cases e p <;> rfl

theorem R_zero_column (adjoint : Bool) (y : AES.Word) : baseResidual adjoint y 0 = 0 := by
  rw [baseResidual_eq]
  exact AESConcrete.pointed_residual_zero_column
    (AESConcrete.WordOrientationClosure.word_kernel_pointed _ _ _) y

theorem R_row_sum (adjoint : Bool) (y : AES.Word) : (∑ x, baseResidual adjoint y x) = 0 := by
  rw [baseResidual_eq]
  exact AESConcrete.WordMixedCentering.residual_row_sum _
    (AESConcrete.WordOrientationClosure.word_kernel_pointed _ _ _) y

theorem tensor_R_zero_column {i : ℕ} (hi : 0 < i) (adjoint : Bool)
    (y : Fin i → AES.Word) : R i adjoint y 0 = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hi⟩ : Fin i))
  exact R_zero_column adjoint (y ⟨0, hi⟩)

theorem tensor_R_row_sum {i : ℕ} (hi : 0 < i) (adjoint : Bool)
    (y : Fin i → AES.Word) : (∑ x, R i adjoint y x) = 0 := by
  unfold R coordinateKernel
  rw [← Fintype.prod_sum]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hi⟩ : Fin i))
  exact R_row_sum adjoint (y ⟨0, hi⟩)

theorem tensor_P_zero_row {j : ℕ} (hj : 0 < j) (x : Fin j → AES.Word) : P j 0 x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hj⟩ : Fin j))
  exact residualProjection_zero_row (0 : AES.Word) (x ⟨0, hj⟩)

theorem tensor_P_column_sum {j : ℕ} (hj : 0 < j) (x : Fin j → AES.Word) :
    (∑ b, P j b x) = 0 := by
  unfold P coordinateKernel
  rw [← Fintype.prod_sum (fun k v => residualProjection (0 : AES.Word) v (x k))]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hj⟩ : Fin j))
  have hs (b : AES.Word) : residualProjection (0 : AES.Word) b (x ⟨0, hj⟩) =
      residualProjection (0 : AES.Word) (x ⟨0, hj⟩) b :=
    degreePiece_symmetric (0 : AES.Word) true b (x ⟨0, hj⟩)
  simp_rw [hs]
  exact residual_row_sum (x ⟨0, hj⟩)

/-- Too many zeros: the concrete point-supported graph is killed even if
one of the two residual coordinate sides is empty. -/
theorem physicalStep_zero_branch {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hn : 0 < i + j)
    (hZ : 4 ≤ (zeroPositions M U).card) (adjoint : Bool) :
    physicalStep M U e adjoint = 0 := by
  have hG : physicalGraph M U e = fun a b =>
      if a = 0 then if b = 0 then WordActivityFrame.xi AES.Word ^ U.card else 0 else 0 := by
    funext a b
    rw [physicalGraph, graphContraction_zero_branch M U hZ]
    simp only [relabeled_zero_iff M e a b]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [ha, hb]
  funext y x
  rw [physicalStep, hG]
  have he : kernelCompose (R i adjoint)
      (kernelCompose (fun a b => if a = 0 then if b = 0 then
        WordActivityFrame.xi AES.Word ^ U.card else 0 else 0) (P j)) y x =
      R i adjoint y 0 * (WordActivityFrame.xi AES.Word ^ U.card * P j 0 x) := by
    simp [kernelCompose, ite_mul, mul_ite]
  rw [he]
  by_cases hi : 0 < i
  · rw [tensor_R_zero_column hi, zero_mul]
    rfl
  · have hj : 0 < j := by omega
    rw [tensor_P_zero_row hj, mul_zero, mul_zero]
    rfl

/-- Full marked image: both residual tensors have zero constant response
whenever their side is nonempty; the other side may be the singleton. -/
theorem physicalStep_full_branch {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hn : 0 < i + j)
    (hfull : (zeroPositions M U).card + M.card ≤ 4) (adjoint : Bool) :
    physicalStep M U e adjoint = 0 := by
  let c : ℝ := WordActivityFrame.xi AES.Word ^ U.card *
    (Fintype.card AES.Word : ℝ) ^ (4 - ((zeroPositions M U).card + M.card))
  have hG : physicalGraph M U e = fun _ _ => c := by
    funext a b
    exact graphContraction_full_branch M U hfull _
  funext y x
  rw [physicalStep, hG]
  have he : kernelCompose (R i adjoint) (kernelCompose (fun _ _ => c) (P j)) y x =
      (∑ a, R i adjoint y a) * (c * ∑ b, P j b x) := by
    simp only [kernelCompose, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [he]
  by_cases hi : 0 < i
  · rw [tensor_R_row_sum hi, zero_mul]
    rfl
  · have hj : 0 < j := by omega
    rw [tensor_P_column_sum hj, mul_zero, mul_zero]
    rfl

end AES8.PaperAESFixedStepTransport
