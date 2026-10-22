import AES8.Math.PaperRestrictedDiffusion

/-!
# Original-coordinate labels for the diffusion marginal

This final semantic transport removes the graph's right-copy labels from the
statement. Both the joint marginal and its counting-measure residual energy
are preserved by the proved coordinate equivalence.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedDiffusion
open AESMixing PaperMDSGram

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Original marked coordinates and their physical graph output labels. -/
def outputEquiv (observed : Finset I) : observed ≃ outputs observed where
  toFun i := ⟨Sum.inr i.val, by simpa using i.property⟩
  invFun i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl i => exact False.elim (mem_outputs_inl observed i hi)
    | inr i => exact ⟨i, (mem_outputs_inr observed i).mp hi⟩
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl i => exact False.elim (mem_outputs_inl observed i hi)
    | inr i => rfl

/-- The same joint probability marginal, now on the original observed indices. -/
def paperJointMarginal (L : (I → V) →+ (I → V)) (active zeros observed : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) (y : observed → V) : ℝ :=
  jointMarginal L active zeros observed mu event
    (AESConcrete.FiniteTensorEnergy.indexTupleEquiv (V := V) (outputEquiv observed) y)

/-- Expanded probability formula with actual original output coordinates. -/
theorem paperJointMarginal_apply (L : (I → V) →+ (I → V))
    (active zeros observed : Finset I) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (y : observed → V) :
    paperJointMarginal L active zeros observed mu event y =
      ∑ x : I → V, if (∀ i ∉ active, x i = 0) ∧ (∀ i ∈ zeros, L x i = 0) ∧
          event x ∧ (fun i : observed => L x i.val) = y
        then productWeight active mu x else 0 := by
  let E := AESConcrete.FiniteTensorEnergy.indexTupleEquiv (V := V) (outputEquiv observed)
  have hm (x : I → V) : markedCoordinates L observed x =
      E (fun i : observed => L x i.val) := by
    apply E.symm.injective
    funext i
    simp only [E, AESConcrete.FiniteTensorEnergy.indexTupleEquiv, Equiv.coe_fn_mk,
      Equiv.symm_apply_apply]
    rfl
  unfold paperJointMarginal jointMarginal
  change (∑ x : I → V, if admissible L active zeros x ∧ event x ∧
      markedCoordinates L observed x = E y then productWeight active mu x else 0) = _
  simp_rw [hm, E.injective.eq_iff]
  simp only [admissible, and_assoc]

/-- Counting-measure energy is invariant under the physical output relabeling. -/
theorem joint_action_energy_eq (L : (I → V) →+ (I → V))
    (active zeros observed : Finset I) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (R : V → V → ℝ) :
    (∑ y : observed → V, action (coordinateKernel (fun _ : observed => R))
      (paperJointMarginal L active zeros observed mu event) y ^ 2) =
      ∑ y : outputs observed → V, action (coordinateKernel (fun _ : outputs observed => R))
        (jointMarginal L active zeros observed mu event) y ^ 2 := by
  let e := outputEquiv observed
  let E := AESConcrete.FiniteTensorEnergy.indexTupleEquiv (V := V) e
  have hk : coordinateKernel (fun _ : observed => R) =
      reindexKernel E (coordinateKernel (fun _ : outputs observed => R)) := by
    funext y x
    have hp := e.prod_comp (fun i => R (E y i) (E x i))
    simpa only [coordinateKernel, reindexKernel, E,
      AESConcrete.FiniteTensorEnergy.indexTupleEquiv, Equiv.coe_fn_mk,
      Equiv.symm_apply_apply] using hp
  have hf : paperJointMarginal L active zeros observed mu event ∘ E.symm =
      jointMarginal L active zeros observed mu event := by
    funext y
    exact congrArg (jointMarginal L active zeros observed mu event) (E.apply_symm_apply y)
  rw [hk]
  simp_rw [reindexKernel_action, hf]
  exact E.sum_comp (fun y => action (coordinateKernel (fun _ : outputs observed => R))
    (jointMarginal L active zeros observed mu event) y ^ 2)

/-- Literal residual action on the original joint probability marginal, with
the paper's exact `p^(2z) (rho*nu²)^min(w-z,j) delta^(j-min(w-z,j))` bound. -/
theorem paper_pointed_restricted_energy [Nontrivial V]
    (L : (I → V) →+ (I → V)) (hMDS : IsMDS (graph L) (Fintype.card I))
    (active zeros observed : Finset I) (hd : Disjoint zeros observed)
    (hz : zeros.card ≤ active.card)
    (mu : I → V → ℝ) (event : (I → V) → Prop)
    (S : V → V → ℝ) (hS : PointedBistochastic S 0) (hq : 1 < Fintype.card V)
    (p rho nu : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho)
    (hoperator : ∀ g : V → ℝ,
      (∑ y, action (residualMatrix S 0) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hchannel : ∀ a : V, a ≠ 0 → (∑ b, S b a ^ 2) ≤ rho) :
    (∑ y : observed → V,
      action (coordinateKernel (fun _ : observed => residualMatrix S 0))
        (paperJointMarginal L active zeros observed mu event) y ^ 2) ≤
      p ^ (2 * zeros.card) * (rho * nu ^ 2) ^ min (active.card - zeros.card) observed.card *
        (rho - 1 / (Fintype.card V - 1 : ℝ)) ^
          (observed.card - min (active.card - zeros.card) observed.card) := by
  rw [joint_action_energy_eq]
  exact actual_pointed_restricted_energy L hMDS active zeros observed hd hz mu event
    S hS hq p rho nu hp hmu hmass hpoint hcollision hoperator hchannel

end AES8.PaperRestrictedDiffusion
