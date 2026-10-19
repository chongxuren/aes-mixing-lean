import AESConcrete.HilbertSchmidtEnergy
import AESMixing.DegreeAdjoint

/-!
# Exact Hilbert--Schmidt decomposition into actual degree blocks

Both sides of a matrix use the actual orthogonal degree projections.
Counting-measure entry energy is retained throughout; no block norm or
trace estimate is an assumption of the decomposition identity.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.DegreeHilbertSchmidt
open AESMixing
open HilbertSchmidtEnergy (hs hs_sq)

variable {V : Type*} [Fintype V] [DecidableEq V]

def block (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (degreeKernel z i) (kernelCompose K (degreeKernel z j))

theorem block_action (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5)
    (f : (Fin 4 → V) → ℝ) :
    action (block z K i j) f = degreeComponent z i (action K (degreeComponent z j f)) := by
  simp only [block, kernelCompose_action, degreeKernel_action]

theorem right_block_row (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (j : Fin 5) (y x : (Fin 4 → V)) :
    kernelCompose K (degreeKernel z j) y x = degreeComponent z j (K y) x := by
  rw [← degreeKernel_action]
  unfold kernelCompose action
  apply Finset.sum_congr rfl
  intro v _
  rw [degreeKernel_symmetric z j v x, mul_comm]

theorem block_entry (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) (y x : (Fin 4 → V)) :
    block z K i j y x =
      degreeComponent z i (fun v => degreeComponent z j (K v) x) y := by
  change action (degreeKernel z i) (fun v => kernelCompose K (degreeKernel z j) v x) y = _
  simp only [right_block_row, degreeKernel_action]

theorem block_hs_pythagoras (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 5, hs (block z K i j)^2) = hs K^2 := by
  simp_rw [hs_sq, block_entry]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : Fin 5, ∑ x : (Fin 4 → V), ∑ i : Fin 5,
        ∑ y : (Fin 4 → V), degreeComponent z i (fun v => degreeComponent z j (K v) x) y^2 := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Finset.sum_comm (f := fun y x =>
        degreeComponent z _ (fun v => degreeComponent z j (K v) x) y^2)]
      exact Finset.sum_comm
    _ = ∑ j : Fin 5, ∑ x : (Fin 4 → V), ∑ y : (Fin 4 → V), degreeComponent z j (K y) x^2 := by
      simp_rw [degreeComponent_pythagoras z hn]
    _ = ∑ y : (Fin 4 → V), ∑ j : Fin 5, ∑ x : (Fin 4 → V), degreeComponent z j (K y) x^2 := by
      simp_rw [Finset.sum_comm (f := fun x y => degreeComponent z _ (K y) x^2)]
      exact Finset.sum_comm
    _ = ∑ y : (Fin 4 → V), ∑ x : (Fin 4 → V), K y x^2 := by
      simp_rw [degreeComponent_pythagoras z hn]

theorem degree_inner_resolution (z : V) (hn : 1 < Fintype.card V)
    (f g : (Fin 4 → V) → ℝ) :
    (∑ h : Fin 5, ∑ y : (Fin 4 → V), degreeComponent z h f y * degreeComponent z h g y) =
      ∑ y : (Fin 4 → V), f y * g y := by
  have hi (h : Fin 5) : degreeComponent z h (degreeComponent z h g) =
      degreeComponent z h g := by
    simp only [← degreeKernel_action, ← kernelCompose_action, degreeKernel_compose z hn]
  simp_rw [degreeComponent_inner, hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  exact congrArg (f y * ·) (congrFun (degreeComponent_decomposition z g) y)

theorem block_gram_entry (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (i j : Fin 5) (x t : (Fin 4 → V)) :
    block z (gram K) i j x t = ∑ y : (Fin 4 → V),
      kernelCompose K (degreeKernel z i) y x * kernelCompose K (degreeKernel z j) y t := by
  have h := kernel_bilinear K K (fun a => degreeKernel z i a x)
    (fun a => degreeKernel z j a t)
  change (∑ y : (Fin 4 → V),
    kernelCompose K (degreeKernel z i) y x * kernelCompose K (degreeKernel z j) y t) = _ at h
  rw [h]
  unfold block kernelCompose gram
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [degreeKernel_symmetric z i a x]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem gram_block_identity (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) (x t : (Fin 4 → V)) :
    block z (gram K) i j x t =
      ∑ h : Fin 5, ∑ y : (Fin 4 → V), block z K h i y x * block z K h j y t := by
  rw [block_gram_entry]
  simp_rw [block_entry, right_block_row]
  exact (degree_inner_resolution z hn
    (fun y => degreeComponent z i (K y) x)
    (fun y => degreeComponent z j (K y) t)).symm

end AESConcrete.DegreeHilbertSchmidt
