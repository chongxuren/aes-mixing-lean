import AES8.Math.PaperRestrictedMarginal
import AESConcrete.WordColumnBounds

/-!
# The general min(d,j) residual response on an MDS fiber

Combines both response branches and derives the residual column constant
`rho - 1/(q-1)` from the actual pointed stochastic channel. The source laws,
the channel, all coordinate sets and the further indicator remain arbitrary.
This is the code-fiber form of part (b) of `lem:marginals`; transporting the
paper's four-coordinate diffusion experiment to this graph is separate.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedResidual
open AESMixing PaperMDSGram PaperMDSFiber PaperRestrictedSource PaperRestrictedResponse

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Both branches use the same literal response and retain arbitrary events. -/
theorem restricted_response_energy_min (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs observed : Finset K)
    (hfi : Disjoint fixed inputs) (hfo : Disjoint fixed observed)
    (hio : Disjoint inputs observed) (hfixed : fixed.card ≤ k)
    (hinputs : k - fixed.card ≤ inputs.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (T : K → V → V → ℝ) (p rho nu delta : ℝ) (hp : 0 ≤ p) (hdelta : 0 ≤ delta)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho)
    (hoperator : ∀ i ∈ observed, ∀ g : V → ℝ,
      (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ i ∈ observed, ∀ x, (∑ y, T i y x ^ 2) ≤ delta) :
    (∑ y : observed → V, response C fixed observed target T
      (density C fixed inputs target mu event) y ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) *
        (rho * nu ^ 2) ^ min (k - fixed.card) observed.card *
          delta ^ (observed.card - min (k - fixed.card) observed.card) := by
  by_cases hj : observed.card ≤ k - fixed.card
  · rw [Nat.min_eq_right hj, Nat.sub_self, pow_zero, mul_one]
    exact PaperRestrictedMarginal.restricted_response_energy_low C k hk hMDS
      fixed inputs observed hfi hfo hio hfixed hinputs hj target mu event T p rho nu hp
      hmu hmass hpoint hcollision hoperator
  · have hd : k - fixed.card ≤ observed.card := by omega
    rw [Nat.min_eq_left hd]
    exact restricted_response_energy_high C k hk hMDS fixed inputs observed
      hfi hfo hfixed hinputs hd target mu event T p rho nu delta hp hdelta
      hmu hpoint hcollision hoperator hcolumn

/-- The residual column cap is derived, including its nonnegativity and the
vanishing zero column. A nonzero alphabet element exists under `Nontrivial`. -/
theorem residual_column_bound [Nontrivial V]
    (S : V → V → ℝ) (hS : PointedBistochastic S 0) (hq : 1 < Fintype.card V)
    (rho : ℝ) (hcollision : ∀ a : V, a ≠ 0 → (∑ b, S b a ^ 2) ≤ rho) :
    0 ≤ rho - 1 / (Fintype.card V - 1 : ℝ) ∧
    ∀ a : V, (∑ b, residualMatrix S 0 b a ^ 2) ≤
      rho - 1 / (Fintype.card V - 1 : ℝ) := by
  have hn (a : V) (ha : a ≠ 0) : (∑ b, residualMatrix S 0 b a ^ 2) ≤
      rho - 1 / (Fintype.card V - 1 : ℝ) := by
    rw [AESConcrete.pointed_residual_column_energy_exact hS hq a ha]
    exact sub_le_sub_right (hcollision a ha) _
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  have hdelta := (Finset.sum_nonneg (fun b _ => sq_nonneg (residualMatrix S 0 b a))).trans (hn a ha)
  refine ⟨hdelta, ?_⟩
  intro b
  by_cases hb : b = 0
  · subst b
    simpa only [AESConcrete.pointed_residual_zero_column hS, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] using hdelta
  · exact hn b hb

/-- Paper part (b), on literal prescribed-coordinate MDS fibers. The exponent
is `min(d,j)`, and `rho - 1/(q-1)` is proved from channel collision rather than
supplied as a residual estimate. All norms use counting-measure energy. -/
theorem pointed_restricted_response_energy [Nontrivial V]
    (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs observed : Finset K)
    (hfi : Disjoint fixed inputs) (hfo : Disjoint fixed observed)
    (hio : Disjoint inputs observed) (hfixed : fixed.card ≤ k)
    (hinputs : k - fixed.card ≤ inputs.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (S : V → V → ℝ) (hS : PointedBistochastic S 0) (hq : 1 < Fintype.card V)
    (p rho nu : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho)
    (hoperator : ∀ g : V → ℝ,
      (∑ y, action (residualMatrix S 0) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hchannel : ∀ a : V, a ≠ 0 → (∑ b, S b a ^ 2) ≤ rho) :
    (∑ y : observed → V, response C fixed observed target (fun _ => residualMatrix S 0)
      (density C fixed inputs target mu event) y ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) *
        (rho * nu ^ 2) ^ min (k - fixed.card) observed.card *
          (rho - 1 / (Fintype.card V - 1 : ℝ)) ^
            (observed.card - min (k - fixed.card) observed.card) := by
  obtain ⟨hd, hc⟩ := residual_column_bound S hS hq rho hchannel
  exact restricted_response_energy_min C k hk hMDS fixed inputs observed hfi hfo hio
    hfixed hinputs target mu event (fun _ => residualMatrix S 0) p rho nu
    (rho - 1 / (Fintype.card V - 1 : ℝ)) hp hd hmu hmass hpoint hcollision
    (fun _ _ => hoperator) (fun _ _ => hc)

end AES8.PaperRestrictedResidual
