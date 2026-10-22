import AES8.Reductions.Return.PaperAESActivityIdentification
import AES8.Reductions.Return.PaperAESFixedStep

/-!
# Paper bounds on the literal grouped-state activity contraction

This adapter transports the already-proved graph estimate through a kernel
equality. Uniform counts concern only omitted physical coordinates. No extra
q normalization is inserted, and neither empty retained side is discarded.
Constructive proofs only; no attacks, numerical searches or manuscript edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityStepBound
open AESMixing PaperKernelBounds PaperWordGraphCode PaperWordGraphDuality
open PaperAESActivityIdentification PaperAESFixedStepTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

theorem uniform_card (O I A B : Finset (Fin 4)) :
    (uniform O I A B).card = (A \ O).card + (B \ I).card := by
  simp [uniform, Nat.add_comm]

/-- Literal proper-branch normalization, before residual maps. The graph
coefficient is exactly one normalized full-uniform factor per selected leg. -/
theorem proper_graph_coefficient {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (d : ℕ)
    (hdim : (zeroPositions (marked O I) (uniform O I A B)).card + d = 4)
    (hlarge : d ≤ (marked O I).card) (y : Fin i → AES.Word) (x : Fin j → AES.Word) :
    physicalGraph (marked O I) (uniform O I A B) (markedEquiv O I eo ei) y x =
      WordActivityFrame.xi AES.Word ^ ((A \ O).card + (B \ I).card) *
        if (fun p : marked O I => Sum.elim y x (markedEquiv O I eo ei p)) ∈
          markedCode (marked O I) (uniform O I A B) then 1 else 0 := by
  rw [physicalGraph, graphContraction_eq _ _ d hdim hlarge, uniform_card, frame_scalar_rpow]

theorem contracted_real_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : 0 < i+j) (adjoint : Bool) :
    (4294967296 : ℝ) * ‖kernelOperator (contracted O I A B eo ei adjoint)‖ ≤
      PaperComparisonPowers.paperStepGraph i (A \ O).card j (B \ I).card := by
  rw [contracted_eq_physicalStep]
  exact PaperAESFixedStep.physical_real_norm _ _ _
    (marked_uniform_disjoint O I A B) hn _ _ (uniform_card O I A B) adjoint

theorem contracted_scaled_real_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : 0 < i+j) (adjoint : Bool) :
    ‖kernelOperator (fun y x => (4294967296 : ℝ) * contracted O I A B eo ei adjoint y x)‖ ≤
      PaperComparisonPowers.paperStepGraph i (A \ O).card j (B \ I).card := by
  rw [contracted_eq_physicalStep]
  exact PaperAESFixedStep.scaled_real_norm _ _ _
    (marked_uniform_disjoint O I A B) hn _ _ (uniform_card O I A B) adjoint

/-- The existing rational step array now bounds the actual contracted step,
on arbitrary complex joint inputs, including i=0 or j=0. -/
theorem contracted_stepGraph_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : 0 < i+j) (adjoint : Bool) :
    ‖kernelOperator (fun y x =>
      (((4294967296 : ℝ) * contracted O I A B eo ei adjoint y x : ℝ) : ℂ))‖ ≤
      (PaperComparison.stepGraph i (A \ O).card j (B \ I).card : ℝ) := by
  rw [contracted_eq_physicalStep]
  exact PaperAESFixedStep.physical_stepGraph_norm _ _ _
    (marked_uniform_disjoint O I A B) hn _ _ (uniform_card O I A B) adjoint

theorem contracted_complex_energy {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : 0 < i+j) (adjoint : Bool)
    (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖kernelAction (fun y x =>
      (((4294967296 : ℝ) * contracted O I A B eo ei adjoint y x : ℝ) : ℂ)) f y‖ ^ 2) ≤
      PaperComparisonPowers.paperStepGraph i (A \ O).card j (B \ I).card ^ 2 *
        ∑ x, ‖f x‖ ^ 2 := by
  rw [contracted_eq_physicalStep]
  exact PaperAESFixedStep.physical_complex_energy _ _ _
    (marked_uniform_disjoint O I A B) hn _ _ (uniform_card O I A B) adjoint f

theorem contracted_degree_one_zero {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : i+j = 1) (adjoint : Bool) :
    contracted O I A B eo ei adjoint = 0 := by
  rw [contracted_eq_physicalStep]
  exact PaperAESFixedStep.degree_one_zero _ _ _ hn adjoint

end AES8.PaperAESActivityStepBound
