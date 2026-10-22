import AES8.Reductions.Return.PaperAESReturnMiddle

/-! Outside physical residual/frame contraction preserves the exact signed
shared-middle expansion. The inverse metric occurs once. No norm is asserted. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnIdentification
open AESMixing AESMixing.AES
open PaperActivityMinorTransport PaperActivityFrameJoin
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

/-- Actual outside contraction, on the full physical coordinates. -/
def outsideContract {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (K : WordState → WordState → ℝ) :
    (Fin i → AES.Word) → (Fin j → AES.Word) → ℝ :=
  kernelCompose (fun y => analysis O (fun k => decide (k ∈ A)) (fun p => y (eo p)))
    (kernelCompose K
      (fun a x => synthesis I (fun k => decide (k ∈ B)) a (fun p => x (ei p))))

def contractedBranch {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (c : Fin 4) (s t : Bool) :=
  outsideContract O I A B eo ei (PhysicalZeroPattern.frameReturnKernel c s t)

def contractedFour {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) :=
  outsideContract O I A B eo ei PhysicalZeroPattern.fourReturnKernel

theorem outside_add {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (K L : WordState → WordState → ℝ) :
    outsideContract O I A B eo ei (fun y x => K y x + L y x) =
      outsideContract O I A B eo ei K + outsideContract O I A B eo ei L := by
  funext y x
  simp only [outsideContract, kernelCompose, add_mul, mul_add,
    Finset.sum_add_distrib, Pi.add_apply]

theorem outside_smul {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (a : ℝ) (K : WordState → WordState → ℝ) :
    outsideContract O I A B eo ei (fun y x => a * K y x) =
      fun y x => a * outsideContract O I A B eo ei K y x := by
  funext y x
  simp only [outsideContract, kernelCompose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem outside_sum {i j : ℕ} {N : Type*} [Fintype N]
    (O I A B : Finset (Fin 4)) (eo : O ≃ Fin i) (ei : I ≃ Fin j)
    (K : N → WordState → WordState → ℝ) :
    outsideContract O I A B eo ei (fun y x => ∑ n, K n y x) =
      fun y x => ∑ n, outsideContract O I A B eo ei (K n) y x := by
  funext y x
  simp only [outsideContract, kernelCompose, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ z : WordState, ∑ n : N, ∑ w : WordState,
        analysis O (fun k => decide (k ∈ A)) (fun p => y (eo p)) z *
          (K n z w * synthesis I (fun k => decide (k ∈ B)) w (fun p => x (ei p))) := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

abbrev FrameLabel := Fin 4 × Bool × Bool

/-- Exact signed expansion of the actual contracted high return. Inverse
weights occur once, after both physical legs share the middle projection. -/
theorem contracted_highReturn_expansion {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) :
    outsideContract O I A B eo ei ReturnCentering.physicalReturnKernel =
      fun y x => (∑ l : FrameLabel, WordActivityFrame.wordInverse AES.Word l.2.1 l.2.2 *
        contractedBranch O I A B eo ei l.1 l.2.1 l.2.2 y x) +
          contractedFour O I A B eo ei y x := by
  have he : ReturnCentering.physicalReturnKernel = fun y x =>
      (∑ l : FrameLabel, WordActivityFrame.wordInverse AES.Word l.2.1 l.2.2 *
        PhysicalZeroPattern.frameReturnKernel l.1 l.2.1 l.2.2 y x) +
        PhysicalZeroPattern.fourReturnKernel y x := by
    funext y x
    simpa only [Fintype.sum_prod_type] using
      PhysicalZeroPattern.physicalReturnKernel_frame_expansion y x
  rw [he, outside_add, outside_sum]
  simp_rw [outside_smul]
  rfl

/-- The source-proved centered execution acts on arbitrary signed joint input. -/
theorem outside_highReturn_action {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (f : (Fin j → AES.Word) → ℝ) :
    action (outsideContract O I A B eo ei ReturnCentering.physicalReturnKernel) f =
      action (fun y => analysis O (fun k => decide (k ∈ A)) (fun p => y (eo p)))
        (TransferAssembly.highReturn
          (action (fun a x => synthesis I (fun k => decide (k ∈ B)) a
            (fun p => x (ei p))) f)) := by
  rw [outsideContract, kernelCompose_action, kernelCompose_action,
    ← ReturnCentering.highReturn_eq_physical_action]

end AES8.PaperAESReturnIdentification
