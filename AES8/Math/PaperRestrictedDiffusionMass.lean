import AES8.Math.PaperRestrictedDiffusionLabels
import AES8.Math.PaperRestrictedZeroEvents

/-!
# Actual zero-event probabilities for additive MDS diffusion

The original product law has mass one, with only active input laws sampled
and all inactive inputs fixed to zero. Its joint-event mass is transported
exactly to the graph source. Both collision/point exponents and impossibility
at `z ≥ w` then follow from the proved generic MDS-fiber estimates. Nonzero
support is used only for impossibility. Further events remain unnormalized.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedDiffusion
open PaperMDSGram PaperMDSFiber PaperRestrictedSource

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Original independent active law, embedded into all original inputs by
setting the inactive inputs to zero. -/
def originalLaw (active : Finset I) (mu : I → V → ℝ) (x : I → V) : ℝ :=
  if ∀ i ∉ active, x i = 0 then productWeight active mu x else 0

def inactiveEquiv (active : Finset I) :
    {x : I → V // ∀ i ∉ active, x i = 0} ≃ (active → V) where
  toFun x := fun i => x.val i.val
  invFun x := ⟨fun i => if hi : i ∈ active then x ⟨i, hi⟩ else 0, by
    intro i hi
    simp only [dif_neg hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ active
    · simp only [dif_pos hi]
    · simp only [dif_neg hi]
      exact (x.property i hi).symm
  right_inv x := by
    funext i
    simp only [dif_pos i.property]

theorem originalLaw_nonneg (active : Finset I) (mu : I → V → ℝ)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x) (x : I → V) :
    0 ≤ originalLaw active mu x := by
  unfold originalLaw productWeight
  split_ifs
  · exact Finset.prod_nonneg (fun i hi => hmu i hi _)
  · exact le_rfl

/-- Normalization of the actual original input law follows from the original
independent normalized factors, rather than a restricted-law assumption. -/
theorem originalLaw_mass_one (active : Finset I) (mu : I → V → ℝ)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1) :
    (∑ x : I → V, originalLaw active mu x) = 1 := by
  change (∑ x : I → V, if ∀ i ∉ active, x i = 0 then productWeight active mu x else 0) = 1
  rw [← sum_subtype_eq_restriction (fun x : I → V => ∀ i ∉ active, x i = 0)]
  have hp (x : {x : I → V // ∀ i ∉ active, x i = 0}) :
      productWeight active mu x.val = AESConcrete.RestrictedProductDensity.productDensity
        (fun i : active => mu i.val) (inactiveEquiv active x) := by
    exact (Finset.prod_coe_sort active (fun i => mu i (x.val i))).symm
  simp_rw [hp]
  rw [(inactiveEquiv active).sum_comp]
  exact AESConcrete.RestrictedProductDensity.productDensity_mass_one _
    (fun i => hmass i.val i.property)

/-- Literal probability of the specified output zeros and any further input
indicator under the original active product law. -/
def eventMass (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) : ℝ :=
  ∑ x : I → V, if admissible L active zeros x ∧ event x then productWeight active mu x else 0

theorem indicator_commute (A B : Prop) [Decidable A] [Decidable B] (weight : ℝ) :
    (if A ∧ B then weight else 0) = if B then (if A then weight else 0) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, and_self,
    true_and, false_and, if_true, if_false]

theorem eventMass_eq_originalLaw (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) :
    eventMass L active zeros mu event =
      ∑ x : I → V, if (∀ i ∈ zeros, L x i = 0) ∧ event x then originalLaw active mu x else 0 := by
  unfold eventMass originalLaw admissible
  apply Finset.sum_congr rfl
  intro x _
  simpa only [and_assoc] using indicator_commute (∀ i ∉ active, x i = 0)
    ((∀ i ∈ zeros, L x i = 0) ∧ event x) (productWeight active mu x)

/-- The original-label marginal is literally the joint-event probability
under the normalized original active input law. -/
theorem paperJointMarginal_eq_originalLaw (L : (I → V) →+ (I → V))
    (active zeros observed : Finset I) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (y : observed → V) :
    paperJointMarginal L active zeros observed mu event y =
      ∑ x : I → V, if (∀ i ∈ zeros, L x i = 0) ∧ event x ∧
          (fun i : observed => L x i.val) = y then originalLaw active mu x else 0 := by
  rw [paperJointMarginal_apply]
  unfold originalLaw
  apply Finset.sum_congr rfl
  intro x _
  exact indicator_commute (∀ i ∉ active, x i = 0)
    ((∀ i ∈ zeros, L x i = 0) ∧ event x ∧ (fun i : observed => L x i.val) = y)
    (productWeight active mu x)

/-- The exact code-fiber source mass is the original joint-event probability. -/
theorem graph_mass_eq_eventMass (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (event : (I → V) → Prop) :
    (∑ c : Fiber (graph L) (fixed active zeros) 0,
      density (graph L) (fixed active zeros) (inputs active) 0 (liftedLaw mu)
        (fun c => event (original L active zeros c)) c) = eventMass L active zeros mu event := by
  have hw := weighted_sum_eq_actual L active zeros mu event (fun _ => 1)
  simp only [one_mul] at hw
  rw [hw]
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : admissible L active zeros x <;> by_cases he : event x <;> simp [ha, he]

/-- Move a property of original active laws to the actual graph input labels. -/
theorem lift_active_laws (active : Finset I) (mu : I → V → ℝ)
    {P : (V → ℝ) → Prop} (h : ∀ i ∈ active, P (mu i)) :
    ∀ i ∈ inputs active, P (liftedLaw mu i) := by
  intro i hi
  cases i with
  | inl i => exact h i ((mem_inputs_inl active i).mp hi)
  | inr i => exact False.elim (mem_inputs_inr active i hi)

/-- Both specified-zero mass branches with the paper's exact exponents, now
on the original additive diffusion experiment and any further event. -/
theorem actual_event_mass_le (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hz : zeros.card < active.card) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho) :
    eventMass L active zeros mu event ≤
      rho ^ min zeros.card (active.card - zeros.card) * p ^ (2 * zeros.card - active.card) := by
  have hc := cardinal_substitution active zeros hz.le
  rw [← graph_mass_eq_eventMass]
  exact PaperRestrictedZeroEvents.paper_mass_le (graph L) (Fintype.card I)
    active.card zeros.card (by simp) hMDS (fixed active zeros) (inputs active)
    (fixed_inputs_disjoint active zeros) hc.1 (inputs_card active) hc.2.1 hz
    0 (liftedLaw mu) (fun c => event (original L active zeros c)) p rho hp hrho
    (lift_active_laws active mu (P := fun f => ∀ x, 0 ≤ f x) hmu)
    (lift_active_laws active mu (P := fun f => (∑ x, f x) = 1) hmass)
    (lift_active_laws active mu (P := fun f => ∀ x, f x ≤ p) hpoint)
    (lift_active_laws active mu (P := fun f => (∑ x, f x ^ 2) ≤ rho) hcollision)

/-- At least as many output zeros as active inputs forces zero event mass.
Only here is support off zero used; a single active law vanishing at zero
already suffices. -/
theorem actual_event_mass_eq_zero (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hz : active.card ≤ zeros.card) (mu : I → V → ℝ)
    (hzero : ∃ i ∈ active, mu i 0 = 0) (event : (I → V) → Prop) :
    eventMass L active zeros mu event = 0 := by
  have hfixed : Fintype.card I ≤ (fixed active zeros).card := by
    rw [fixed_card]
    have ha : active.card ≤ Fintype.card I := Finset.card_le_univ active
    omega
  rw [← graph_mass_eq_eventMass]
  apply PaperRestrictedZeroEvents.mass_eq_zero_of_prescribed_zero (graph L)
    (Fintype.card I) (by simp) hMDS (fixed active zeros) (inputs active) hfixed
  obtain ⟨i, hi, hzi⟩ := hzero
  exact ⟨Sum.inl i, (mem_inputs_inl active i).mpr hi, hzi⟩

/-- The simpler mass cap in part (a), retaining the original event mass. -/
theorem actual_event_mass_le_simple (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hz0 : 0 < zeros.card) (hz : zeros.card < active.card)
    (mu : I → V → ℝ) (event : (I → V) → Prop) (p rho : ℝ)
    (hrho : 0 ≤ rho) (hrhop : rho ≤ p)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho) :
    eventMass L active zeros mu event ≤ rho * p ^ (zeros.card - 1) := by
  have hb := actual_event_mass_le L hMDS active zeros hz mu event p rho
    (hrho.trans hrhop) hrho hmu hmass hpoint hcollision
  have hs := PaperRestrictedZeroEvents.zero_event_factor_le_simple zeros.card
    (active.card - zeros.card) hz0 (by omega) rho p hrho hrhop
  rw [show zeros.card - (active.card - zeros.card) = 2 * zeros.card - active.card by omega] at hs
  exact hb.trans hs

/-- The paper's piecewise specified-zero cap. -/
def zeroEventBound (w z : ℕ) (p rho : ℝ) : ℝ :=
  if w ≤ z then 0 else rho ^ min z (w - z) * p ^ (2 * z - w)

/-- Part (a), including impossibility, on the normalized original product
law. The paper's nonzero active support enters only in the impossible case. -/
theorem paper_zero_event_mass_bound (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hactive : active.Nonempty) (mu : I → V → ℝ) (event : (I → V) → Prop)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho)
    (hsupport : ∀ i ∈ active, mu i 0 = 0) :
    eventMass L active zeros mu event ≤ zeroEventBound active.card zeros.card p rho := by
  by_cases hz : active.card ≤ zeros.card
  · obtain ⟨i, hi⟩ := hactive
    rw [actual_event_mass_eq_zero L hMDS active zeros hz mu ⟨i, hi, hsupport i hi⟩ event]
    simp only [zeroEventBound, if_pos hz, le_refl]
  · rw [zeroEventBound, if_neg hz]
    exact actual_event_mass_le L hMDS active zeros (by omega) mu event p rho hp hrho
      hmu hmass hpoint hcollision

end AES8.PaperRestrictedDiffusion
