import AES8.Math.PaperRestrictedDiffusionGeometry
import AES8.Math.PaperRestrictedResidual

/-!
# Residual energy of the actual additive diffusion experiment

The displayed joint marginal is a sum over original input tuples, weighted by
the original active product laws. Inactive inputs, specified output zeros and
any further input event are literal indicators. Exact finite-sum identities
transport it to the MDS graph; no desired energy bound or source
parameterization is assumed. The output labels are the physical right-copy
labels `outputs observed`, whose cardinality is proved to be `observed.card`.
No restriction renormalizes the event mass. Constructive mathematics only;
no attacks, numerical instantiation, or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedDiffusion
open AESMixing PaperMDSGram PaperMDSFiber PaperRestrictedSource PaperRestrictedResponse
open AESConcrete.RestrictedMarginalEnergy

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Original laws live on input labels only; output entries are unused. -/
def liftedLaw (mu : I → V → ℝ) : (I ⊕ I) → V → ℝ :=
  Sum.elim mu (fun _ _ => 1)

/-- The actual active product weight on the original input tuple. -/
def productWeight (active : Finset I) (mu : I → V → ℝ) (x : I → V) : ℝ :=
  ∏ i ∈ active, mu i (x i)

/-- Physical marked outputs of the original additive map. -/
def markedCoordinates (L : (I → V) →+ (I → V)) (observed : Finset I) (x : I → V) :
    outputs observed → V := fun i => Sum.elim (fun _ => 0) (L x) i.val

/-- Literal joint-event marginal under the original independent active laws.
Inactive inputs are fixed to zero. No conditional-probability denominator occurs. -/
def jointMarginal (L : (I → V) →+ (I → V)) (active zeros observed : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) (y : outputs observed → V) : ℝ :=
  ∑ x : I → V, if admissible L active zeros x ∧ event x ∧ markedCoordinates L observed x = y
    then productWeight active mu x else 0

theorem density_eq_product (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop)
    (c : Fiber (graph L) (fixed active zeros) 0) :
    density (graph L) (fixed active zeros) (inputs active) 0 (liftedLaw mu)
      (fun c => event (original L active zeros c)) c =
      if event (original L active zeros c) then
        productWeight active mu (original L active zeros c) else 0 := by
  simp [density, inputs, liftedLaw, productWeight, original_apply]

theorem observe_eq_actual (L : (I → V) →+ (I → V)) (active zeros observed : Finset I)
    (c : Fiber (graph L) (fixed active zeros) 0) :
    observe (graph L) (fixed active zeros) (outputs observed) 0 c =
      markedCoordinates L observed (original L active zeros c) := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl i => exact False.elim (mem_outputs_inl observed i hi)
  | inr i => exact (original_output L active zeros c i).symm

/-- Exact finite restriction identity; signs of the test weight are arbitrary. -/
theorem sum_subtype_eq_restriction {X M : Type*} [Fintype X] [AddCommMonoid M]
    (P : X → Prop) [DecidablePred P] (f : X → M) :
    (∑ x : {x : X // P x}, f x.val) = ∑ x : X, if P x then f x else 0 := by
  classical
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Every weighted graph-source sum is the literal original experiment sum. -/
theorem weighted_sum_eq_actual (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) (test : (I → V) → ℝ) :
    (∑ c : Fiber (graph L) (fixed active zeros) 0,
      test (original L active zeros c) *
        density (graph L) (fixed active zeros) (inputs active) 0 (liftedLaw mu)
          (fun c => event (original L active zeros c)) c) =
      ∑ x : I → V, if admissible L active zeros x then
        test x * (if event x then productWeight active mu x else 0) else 0 := by
  simp_rw [density_eq_product]
  calc
    _ = ∑ x : {x : I → V // admissible L active zeros x},
        test x.val * (if event x.val then productWeight active mu x.val else 0) :=
      (fiberEquiv L active zeros).sum_comp
        (fun x => test x.val * (if event x.val then productWeight active mu x.val else 0))
    _ = _ := sum_subtype_eq_restriction (admissible L active zeros)
      (fun x => test x * (if event x then productWeight active mu x else 0))

/-- The graph marginal equals the original joint-event marginal pointwise. -/
theorem marginal_eq_joint (L : (I → V) →+ (I → V)) (active zeros observed : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) :
    marginal (observe (graph L) (fixed active zeros) (outputs observed) 0)
      (density (graph L) (fixed active zeros) (inputs active) 0 (liftedLaw mu)
        (fun c => event (original L active zeros c))) =
      jointMarginal L active zeros observed mu event := by
  funext y
  have hw := weighted_sum_eq_actual L active zeros mu event
    (fun x => if markedCoordinates L observed x = y then (1 : ℝ) else 0)
  simp only [ite_mul, one_mul, zero_mul] at hw
  unfold marginal
  simp_rw [observe_eq_actual]
  rw [hw]
  unfold jointMarginal
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : admissible L active zeros x <;> by_cases he : event x <;>
    by_cases hy : markedCoordinates L observed x = y <;> simp [ha, he, hy]

/-- The source-response tensor is exactly the residual action on the actual
joint probability marginal, including its event mass. -/
theorem response_eq_joint_action (L : (I → V) →+ (I → V))
    (active zeros observed : Finset I) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (R : V → V → ℝ) :
    response (graph L) (fixed active zeros) (outputs observed) 0 (fun _ => R)
      (density (graph L) (fixed active zeros) (inputs active) 0 (liftedLaw mu)
        (fun c => event (original L active zeros c))) =
      action (coordinateKernel (fun _ : outputs observed => R))
        (jointMarginal L active zeros observed mu event) := by
  rw [response_eq_marginal_action, marginal_eq_joint]

/-- Lemma `lem:marginals` (b) for an actual additive `n`-coordinate MDS map.
Every source law and the further event refer to original input tuples. The
paper exponents follow from exact coordinate cardinalities, with no marginal
energy, source parameterization or output independence supplied as a premise. -/
theorem actual_pointed_restricted_energy [Nontrivial V]
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
    (∑ y : outputs observed → V,
      action (coordinateKernel (fun _ : outputs observed => residualMatrix S 0))
        (jointMarginal L active zeros observed mu event) y ^ 2) ≤
      p ^ (2 * zeros.card) * (rho * nu ^ 2) ^ min (active.card - zeros.card) observed.card *
        (rho - 1 / (Fintype.card V - 1 : ℝ)) ^
          (observed.card - min (active.card - zeros.card) observed.card) := by
  have hc := cardinal_substitution active zeros hz
  have lift {P : (V → ℝ) → Prop} (h : ∀ i ∈ active, P (mu i)) :
      ∀ i ∈ inputs active, P (liftedLaw mu i) := by
    intro i hi
    cases i with
    | inl i => exact h i ((mem_inputs_inl active i).mp hi)
    | inr i => exact False.elim (mem_inputs_inr active i hi)
  have hb := PaperRestrictedResidual.pointed_restricted_response_energy
    (graph L) (Fintype.card I) (by simp) hMDS
    (fixed active zeros) (inputs active) (outputs observed)
    (fixed_inputs_disjoint active zeros) (fixed_outputs_disjoint active zeros observed hd)
    (inputs_outputs_disjoint active observed) hc.1
    (by rw [inputs_card, hc.2.1]; omega) 0 (liftedLaw mu)
    (fun c => event (original L active zeros c)) S hS hq p rho nu hp
    (lift (P := fun f => ∀ x, 0 ≤ f x) hmu)
    (lift (P := fun f => (∑ x, f x) = 1) hmass)
    (lift (P := fun f => ∀ x, f x ≤ p) hpoint)
    (lift (P := fun f => (∑ x, f x ^ 2) ≤ rho) hcollision) hoperator hchannel
  rw [response_eq_joint_action] at hb
  rw [inputs_card, hc.2.2, hc.2.1, outputs_card] at hb
  exact hb

end AES8.PaperRestrictedDiffusion
